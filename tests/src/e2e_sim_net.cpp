#include "e2e_sim_net.hpp"
#include "message.h"
#include <algorithm>
#include <array>
#include <cassert>
#include <cstring>
#include <limits>
#include <new>
#include <utility>

namespace e2e {
namespace {

constexpr std::uint8_t header_type_mask = 63U;
constexpr std::uint8_t header_gossip    = 7U;
constexpr std::uint8_t header_scout     = 8U;
constexpr std::size_t  header_size      = 18U;
constexpr std::size_t  max_fault_copies = 1024U;
constexpr std::size_t  registry_size    = 8U;

std::array<sim_net_t*, registry_size> g_registry{};          // NOLINT(*-non-const-global-variables)
std::size_t                           g_registry_count = 0U; // NOLINT(*-non-const-global-variables)

sim_node_t* node_from(cy_platform_t* const platform)
{
    return reinterpret_cast<sim_node_t*>(platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
}

const sim_node_t* node_from_const(const cy_platform_t* const platform)
{
    return reinterpret_cast<const sim_node_t*>(platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
}

const sim_subject_reader_t* find_reader(const sim_node_t& node, const std::uint32_t subject_id)
{
    const sim_subject_reader_t* reader = node.readers;
    while (reader != nullptr) {
        if (reader->base.subject_id == subject_id) {
            return reader;
        }
        reader = reader->next;
    }
    return nullptr;
}

std::size_t find_node_index_by_id(const sim_net_t& net, const std::uint64_t node_id)
{
    for (std::size_t i = 0U; i < sim_node_count; i++) {
        if (net.nodes.at(i).node_id == node_id) {
            return i;
        }
    }
    return sim_node_count;
}

std::size_t find_node_index_by_cy(const sim_net_t& net, const cy_t* const cy)
{
    for (std::size_t i = 0U; i < sim_node_count; i++) {
        if (net.nodes.at(i).cy == cy) {
            return i;
        }
    }
    return sim_node_count;
}

bool flatten_fragments(const cy_bytes_t message, std::vector<unsigned char>& out)
{
    std::size_t       total = 0U;
    const cy_bytes_t* frag  = &message;
    while (frag != nullptr) {
        if ((frag->size > 0U) && (frag->data == nullptr)) {
            return false;
        }
        if (frag->size > (SIZE_MAX - total)) {
            return false;
        }
        total += frag->size;
        frag = frag->next;
    }

    try {
        out.assign(total, 0U);
    } catch (const std::bad_alloc&) {
        return false;
    }

    std::size_t offset = 0U;
    frag               = &message;
    while (frag != nullptr) {
        if (frag->size > 0U) {
            std::memcpy(out.data() + offset, frag->data, frag->size);
            offset += frag->size;
        }
        frag = frag->next;
    }
    return true;
}

std::uint64_t read_u64(const std::vector<unsigned char>& data, const std::size_t offset)
{
    if ((offset > data.size()) || ((data.size() - offset) < 8U)) {
        return 0U;
    }
    std::uint64_t out = 0U;
    for (std::size_t i = 0U; i < 8U; i++) {
        out |= static_cast<std::uint64_t>(data.at(offset + i)) << (i * 8U);
    }
    return out;
}

cy_us_t saturating_add(const cy_us_t lhs, const cy_us_t rhs)
{
    if (rhs <= 0) {
        return lhs;
    }
    const cy_us_t max_value = std::numeric_limits<cy_us_t>::max();
    if (lhs > (max_value - rhs)) {
        return max_value;
    }
    return lhs + rhs;
}

std::size_t effective_header_size(const frame_info_t& frame)
{
    if (frame.wire.empty()) {
        return 0U;
    }
    switch (frame.header_type) {
        case header_gossip:
        case header_scout: {
            if (frame.wire.size() < header_size) {
                return frame.wire.size();
            }
            const std::size_t name_len = frame.wire.at(17U);
            const std::size_t end      = header_size + name_len;
            return (end <= frame.wire.size()) ? end : frame.wire.size();
        }
        default:
            return std::min<std::size_t>(header_size, frame.wire.size());
    }
}

void frame_parse(frame_info_t& frame)
{
    frame.header_type    = frame.wire.empty() ? 0U : static_cast<std::uint8_t>(frame.wire.front() & header_type_mask);
    frame.has_tag        = false;
    frame.tag            = 0U;
    frame.has_topic_hash = false;
    frame.topic_hash     = 0U;

    if (frame.wire.size() >= header_size) {
        if (frame.header_type <= 6U) {
            frame.has_tag = true;
            frame.tag     = read_u64(frame.wire, 2U);
        }
        if (frame.header_type <= 2U) {
            frame.has_topic_hash = true;
            frame.topic_hash     = read_u64(frame.wire, 10U);
        } else if (frame.header_type == header_gossip) {
            frame.has_topic_hash = true;
            frame.topic_hash     = read_u64(frame.wire, 5U);
        }
    } else if ((frame.header_type == header_gossip) && (frame.wire.size() >= 13U)) {
        frame.has_topic_hash = true;
        frame.topic_hash     = read_u64(frame.wire, 5U);
    }

    const std::size_t hdr_size = effective_header_size(frame);
    frame.payload.clear();
    if (hdr_size < frame.wire.size()) {
        frame.payload.assign(frame.wire.begin() + static_cast<std::ptrdiff_t>(hdr_size), frame.wire.end());
    }
}

bool registry_insert(sim_net_t* const net)
{
    if (g_registry_count >= g_registry.size()) {
        return false;
    }
    g_registry.at(g_registry_count++) = net;
    return true;
}

void registry_remove(const sim_net_t* const net)
{
    for (std::size_t i = 0U; i < g_registry_count; i++) {
        if (g_registry.at(i) != net) {
            continue;
        }
        for (std::size_t j = i + 1U; j < g_registry_count; j++) {
            g_registry.at(j - 1U) = g_registry.at(j);
        }
        g_registry.at(g_registry_count - 1U) = nullptr;
        g_registry_count--;
        break;
    }
}

sim_net_t* registry_find_by_cy(const cy_t* const cy)
{
    for (std::size_t i = 0U; i < g_registry_count; i++) {
        sim_net_t* const net = g_registry.at(i);
        if ((net != nullptr) && (find_node_index_by_cy(*net, cy) < sim_node_count)) {
            return net;
        }
    }
    return nullptr;
}

void capture_async_error(sim_net_t&          net,
                         const std::size_t   node_index,
                         const cy_err_t      error,
                         const std::uint16_t line_number,
                         const bool          has_topic,
                         const std::uint64_t topic_hash)
{
    async_error_capture_t out{};
    out.node_index  = node_index;
    out.error       = error;
    out.line_number = line_number;
    out.has_topic   = has_topic;
    out.topic_hash  = topic_hash;
    try {
        net.async_errors.push_back(out);
    } catch (const std::bad_alloc&) {
        // Ignore OOM while logging diagnostics in the test harness.
        return;
    }
}

bool capture_push(sim_net_t& net, const frame_capture_t& capture)
{
    try {
        net.captures.push_back(capture);
    } catch (const std::bad_alloc&) {
        return false;
    }
    return true;
}

bool queue_push(sim_net_t& net, const queued_frame_t& frame)
{
    try {
        net.queue.push_back(frame);
    } catch (const std::bad_alloc&) {
        return false;
    }
    return true;
}

cy_err_t enqueue_frame(sim_node_t&                       src,
                       const std::size_t                 dst_index,
                       const bool                        p2p,
                       const std::uint32_t               subject_id,
                       const cy_prio_t                   priority,
                       const std::vector<unsigned char>& wire)
{
    sim_net_t&   net = *src.network;
    frame_info_t base{};
    base.source       = src.index;
    base.destination  = dst_index;
    base.p2p          = p2p;
    base.subject_id   = subject_id;
    base.priority     = priority;
    base.send_time    = src.now;
    base.deliver_time = src.now;
    base.wire         = wire;
    frame_parse(base);

    const fault_effect_t effect = (net.faults != nullptr) ? fault_plan_evaluate(*net.faults, base) : fault_effect_t{};
    const std::size_t    copies = effect.drop ? 1U : std::min<std::size_t>(max_fault_copies, 1U + effect.duplicates);

    for (std::size_t copy_index = 0U; copy_index < copies; copy_index++) {
        frame_info_t item = base;
        item.sequence     = ++net.next_sequence;
        item.deliver_time =
          saturating_add(saturating_add(item.send_time, effect.delay), static_cast<cy_us_t>(copy_index));

        frame_capture_t capture{};
        capture.frame      = item;
        capture.dropped    = effect.drop;
        capture.copy_index = copy_index;
        if (!capture_push(net, capture)) {
            return CY_ERR_MEMORY;
        }

        if (!effect.drop) {
            queued_frame_t queued{};
            queued.frame = item;
            if (!queue_push(net, queued)) {
                return CY_ERR_MEMORY;
            }
        }
    }
    return CY_OK;
}

cy_err_t enqueue_subject(sim_node_t&                       src,
                         const std::uint32_t               subject_id,
                         const cy_prio_t                   priority,
                         const std::vector<unsigned char>& wire)
{
    const sim_net_t& net          = *src.network;
    const bool       is_broadcast = subject_id == cy_broadcast_subject_id(&src.platform);

    cy_err_t result = CY_OK;
    for (std::size_t i = 0U; i < sim_node_count; i++) {
        if (i == src.index) {
            continue;
        }
        if (!is_broadcast && (find_reader(net.nodes.at(i), subject_id) == nullptr)) {
            continue;
        }
        const cy_err_t err = enqueue_frame(src, i, false, subject_id, priority, wire);
        if ((result == CY_OK) && (err != CY_OK)) {
            result = err;
        }
    }
    return result;
}

cy_err_t enqueue_p2p(sim_node_t&                       src,
                     const std::uint64_t               destination_node_id,
                     const cy_prio_t                   priority,
                     const std::vector<unsigned char>& wire)
{
    const sim_net_t&  net = *src.network;
    const std::size_t ix  = find_node_index_by_id(net, destination_node_id);
    if (ix >= sim_node_count) {
        return CY_OK;
    }
    return enqueue_frame(src, ix, true, 0U, priority, wire);
}

void deliver_frame(sim_net_t& net, const queued_frame_t& frame)
{
    sim_node_t& dst = net.nodes.at(frame.frame.destination);
    dst.now         = std::max(dst.now, frame.frame.deliver_time);

    cy_message_t* const msg = cy_test_message_make(&dst.message_heap, frame.frame.wire.data(), frame.frame.wire.size());
    if (msg == nullptr) {
        capture_async_error(net, dst.index, CY_ERR_MEMORY, 0U, false, 0U);
        return;
    }

    cy_message_ts_t mts{};
    mts.timestamp = frame.frame.deliver_time;
    mts.content   = msg;

    cy_lane_t lane{};
    lane.id   = net.nodes.at(frame.frame.source).node_id;
    lane.prio = frame.frame.priority;
    std::memset(lane.p2p.state, 0, sizeof(lane.p2p.state));
    const std::size_t copy_size = std::min(sizeof(lane.p2p.state), sizeof(lane.id));
    std::memcpy(lane.p2p.state, &lane.id, copy_size);

    if (frame.frame.p2p) {
        cy_on_message(&dst.platform, lane, nullptr, mts);
        return;
    }

    const sim_subject_reader_t* const reader = find_reader(dst, frame.frame.subject_id);
    if (reader != nullptr) {
        cy_on_message(&dst.platform, lane, &reader->base, mts);
    } else {
        cy_message_refcount_dec(msg);
    }
}

extern "C" cy_subject_writer_t* sim_subject_writer_new(cy_platform_t* const platform, const std::uint32_t subject_id)
{
    sim_node_t* const self = node_from(platform);
    auto* const       out =
      static_cast<sim_subject_writer_t*>(guarded_heap_alloc(&self->core_heap, sizeof(sim_subject_writer_t)));
    if (out != nullptr) {
        out->base.subject_id = subject_id;
    }
    return (out != nullptr) ? &out->base : nullptr;
}

extern "C" void sim_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    sim_node_t* const self = node_from(platform);
    guarded_heap_free(&self->core_heap, writer);
}

extern "C" cy_err_t sim_subject_writer_send(cy_platform_t* const       platform,
                                            cy_subject_writer_t* const writer,
                                            const cy_us_t              deadline,
                                            const cy_prio_t            priority,
                                            const cy_bytes_t           message)
{
    (void)deadline;
    if (writer == nullptr) {
        return CY_ERR_ARGUMENT;
    }
    sim_node_t* const          self = node_from(platform);
    std::vector<unsigned char> wire;
    if (!flatten_fragments(message, wire)) {
        return CY_ERR_ARGUMENT;
    }
    self->subject_send_count++;
    return enqueue_subject(*self, writer->subject_id, priority, wire);
}

extern "C" cy_subject_reader_t* sim_subject_reader_new(cy_platform_t* const platform,
                                                       const std::uint32_t  subject_id,
                                                       const std::size_t    extent)
{
    sim_node_t* const self = node_from(platform);
    auto* const       out =
      static_cast<sim_subject_reader_t*>(guarded_heap_alloc(&self->core_heap, sizeof(sim_subject_reader_t)));
    if (out != nullptr) {
        out->base.subject_id = subject_id;
        out->extent          = extent;
        out->next            = self->readers;
        self->readers        = out;
    }
    return (out != nullptr) ? &out->base : nullptr;
}

extern "C" void sim_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    sim_node_t* const self = node_from(platform);
    auto* const       ptr =
      reinterpret_cast<sim_subject_reader_t*>(reader); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
    sim_subject_reader_t** p = &self->readers;
    while (*p != nullptr) {
        if (*p == ptr) {
            *p = ptr->next;
            break;
        }
        p = &(*p)->next;
    }
    guarded_heap_free(&self->core_heap, reader);
}

extern "C" cy_err_t sim_p2p_send(cy_platform_t* const   platform,
                                 const cy_lane_t* const lane,
                                 const cy_us_t          deadline,
                                 const cy_bytes_t       message)
{
    (void)deadline;
    if (lane == nullptr) {
        return CY_ERR_ARGUMENT;
    }
    sim_node_t* const          self = node_from(platform);
    std::vector<unsigned char> wire;
    if (!flatten_fragments(message, wire)) {
        return CY_ERR_ARGUMENT;
    }
    self->p2p_send_count++;
    return enqueue_p2p(*self, lane->id, lane->prio, wire);
}

extern "C" void sim_p2p_extent_set(cy_platform_t* const platform, const std::size_t extent)
{
    (void)platform;
    (void)extent;
}

extern "C" cy_err_t sim_spin(cy_platform_t* const platform, const cy_us_t deadline)
{
    (void)platform;
    (void)deadline;
    return CY_OK;
}

extern "C" cy_us_t sim_now(cy_platform_t* const platform) { return node_from_const(platform)->now; }

extern "C" void* sim_realloc(cy_platform_t* const platform, void* const ptr, const std::size_t size)
{
    sim_node_t* const self = node_from(platform);
    return guarded_heap_realloc(&self->core_heap, ptr, size);
}

extern "C" std::uint64_t sim_random(cy_platform_t* const platform)
{
    sim_node_t* const self = node_from(platform);
    self->random_state     = (self->random_state * UINT64_C(6364136223846793005)) + UINT64_C(1);
    return self->random_state;
}

extern "C" void sim_on_async_error(cy_t* const         cy,
                                   cy_topic_t* const   topic,
                                   const cy_err_t      error,
                                   const std::uint16_t line_number)
{
    sim_net_t* const net = registry_find_by_cy(cy);
    if (net == nullptr) {
        return;
    }
    const std::size_t node_index = find_node_index_by_cy(*net, cy);
    capture_async_error(
      *net, node_index, error, line_number, topic != nullptr, (topic != nullptr) ? cy_topic_hash(topic) : 0U);
}

} // namespace

cy_err_t sim_net_init(sim_net_t& self, const std::uint32_t subject_id_modulus, const std::uint64_t random_seed_base)
{
    self                    = sim_net_t{};
    self.subject_id_modulus = subject_id_modulus;
    if (!registry_insert(&self)) {
        return CY_ERR_CAPACITY;
    }

    for (std::size_t i = 0U; i < sim_node_count; i++) {
        sim_node_t& node = self.nodes.at(i);
        node             = sim_node_t{};

        guarded_heap_init(&node.core_heap, UINT64_C(0xABC0000000000000) + i);
        guarded_heap_init(&node.message_heap, UINT64_C(0xDEF0000000000000) + i);

        node.network      = &self;
        node.index        = i;
        node.node_id      = i + 1U;
        node.now          = 0;
        node.random_state = random_seed_base + (i * UINT64_C(0x9E3779B97F4A7C15));

        node.vtable.subject_writer_new     = sim_subject_writer_new;
        node.vtable.subject_writer_destroy = sim_subject_writer_destroy;
        node.vtable.subject_writer_send    = sim_subject_writer_send;
        node.vtable.subject_reader_new     = sim_subject_reader_new;
        node.vtable.subject_reader_destroy = sim_subject_reader_destroy;
        node.vtable.p2p_send               = sim_p2p_send;
        node.vtable.p2p_extent_set         = sim_p2p_extent_set;
        node.vtable.spin                   = sim_spin;
        node.vtable.now                    = sim_now;
        node.vtable.realloc                = sim_realloc;
        node.vtable.random                 = sim_random;

        node.platform.cy                 = nullptr;
        node.platform.subject_id_modulus = subject_id_modulus;
        node.platform.vtable             = &node.vtable;

        node.cy = cy_new(&node.platform);
        if (node.cy == nullptr) {
            sim_net_deinit(self);
            return CY_ERR_MEMORY;
        }
        cy_async_error_handler_set(node.cy, sim_on_async_error);
    }
    return CY_OK;
}

void sim_net_deinit(sim_net_t& self)
{
    for (std::size_t i = 0U; i < sim_node_count; i++) {
        sim_node_t& node = self.nodes.at(i);
        if (node.cy != nullptr) {
            cy_destroy(node.cy);
            node.cy = nullptr;
        }
        node.readers = nullptr;
        node.network = nullptr;
    }
    self.queue.clear();
    self.faults = nullptr;
    registry_remove(&self);
}

void sim_net_faults_set(sim_net_t& self, const fault_plan_t* const faults) { self.faults = faults; }

cy_t* sim_net_cy(sim_net_t& self, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    return self.nodes.at(node_index).cy;
}

const cy_t* sim_net_cy(const sim_net_t& self, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    return self.nodes.at(node_index).cy;
}

cy_platform_t* sim_net_platform(sim_net_t& self, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    return &self.nodes.at(node_index).platform;
}

const cy_platform_t* sim_net_platform(const sim_net_t& self, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    return &self.nodes.at(node_index).platform;
}

void sim_net_node_now_set(sim_net_t& self, const std::size_t node_index, const cy_us_t now)
{
    assert(node_index < sim_node_count);
    self.nodes.at(node_index).now = now;
}

cy_us_t sim_net_node_now(const sim_net_t& self, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    return self.nodes.at(node_index).now;
}

std::uint64_t sim_net_node_id(const sim_net_t& self, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    return self.nodes.at(node_index).node_id;
}

cy_err_t sim_net_spin_node(sim_net_t& self, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    return cy_spin_once(self.nodes.at(node_index).cy);
}

cy_err_t sim_net_spin_node_until(sim_net_t& self, const std::size_t node_index, const cy_us_t now)
{
    sim_net_node_now_set(self, node_index, now);
    return sim_net_spin_node(self, node_index);
}

void sim_net_deliver_due(sim_net_t& self, const cy_us_t now_limit)
{
    while (true) {
        std::size_t best = self.queue.size();
        for (std::size_t i = 0U; i < self.queue.size(); i++) {
            const queued_frame_t& candidate = self.queue.at(i);
            if (candidate.frame.deliver_time > now_limit) {
                continue;
            }
            const bool better = (best >= self.queue.size()) ||
                                (candidate.frame.deliver_time < self.queue.at(best).frame.deliver_time) ||
                                ((candidate.frame.deliver_time == self.queue.at(best).frame.deliver_time) &&
                                 (candidate.frame.sequence < self.queue.at(best).frame.sequence));
            if (better) {
                best = i;
            }
        }
        if (best >= self.queue.size()) {
            break;
        }
        const queued_frame_t frame = self.queue.at(best);
        self.queue.erase(self.queue.begin() + static_cast<std::ptrdiff_t>(best));
        deliver_frame(self, frame);
    }
}

std::size_t sim_net_pending_frames(const sim_net_t& self) { return self.queue.size(); }

const std::vector<frame_capture_t>& sim_net_captures(const sim_net_t& self) { return self.captures; }

const std::vector<async_error_capture_t>& sim_net_async_errors(const sim_net_t& self) { return self.async_errors; }

void sim_net_clear_captures(sim_net_t& self)
{
    self.captures.clear();
    self.async_errors.clear();
}

guarded_heap_t& sim_net_core_heap(sim_net_t& self, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    return self.nodes.at(node_index).core_heap;
}

const guarded_heap_t& sim_net_core_heap(const sim_net_t& self, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    return self.nodes.at(node_index).core_heap;
}

guarded_heap_t& sim_net_message_heap(sim_net_t& self, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    return self.nodes.at(node_index).message_heap;
}

const guarded_heap_t& sim_net_message_heap(const sim_net_t& self, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    return self.nodes.at(node_index).message_heap;
}

} // namespace e2e
