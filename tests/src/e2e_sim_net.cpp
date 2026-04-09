#include "e2e_sim_net.hpp"
#include "message.h"
#include <algorithm>
#include <array>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <string>
#include <new>
#include <utility>

namespace e2e {
namespace {

constexpr std::uint8_t header_gossip    = 8U;
constexpr std::uint8_t header_scout     = 9U;
constexpr std::size_t  header_size      = 24U;
constexpr std::size_t  max_fault_copies = 1024U;

void enforce(const bool expr)
{
    if (!expr) {
        std::abort();
    }
}

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
    for (std::size_t i = 0U; i < net.nodes.size(); i++) {
        if (net.nodes.at(i).node_id == node_id) {
            return i;
        }
    }
    return net.nodes.size();
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
            const std::size_t name_len = frame.wire.at(23U);
            const std::size_t end      = header_size + name_len;
            return (end <= frame.wire.size()) ? end : frame.wire.size();
        }
        default:
            return std::min<std::size_t>(header_size, frame.wire.size());
    }
}

void frame_parse(frame_info_t& frame)
{
    frame.header_type    = frame.wire.empty() ? 0U : static_cast<std::uint8_t>(frame.wire.front());
    frame.has_tag        = false;
    frame.tag            = 0U;
    frame.has_topic_hash = false;
    frame.topic_hash     = 0U;

    if (frame.wire.size() >= header_size) {
        if (frame.header_type <= 3U) {
            frame.has_tag = true;
            frame.tag     = read_u64(frame.wire, 16U);
        } else if (frame.header_type <= 7U) {
            frame.has_tag = true;
            frame.tag     = frame.wire.at(1U);
        }
        if ((frame.header_type <= 7U) || (frame.header_type == header_gossip)) {
            frame.has_topic_hash = true;
            frame.topic_hash     = read_u64(frame.wire, 8U);
        }
    } else if ((frame.header_type == header_gossip) && (frame.wire.size() >= 16U)) {
        frame.has_topic_hash = true;
        frame.topic_hash     = read_u64(frame.wire, 8U);
    }

    const std::size_t hdr_size = effective_header_size(frame);
    frame.payload.clear();
    if (hdr_size < frame.wire.size()) {
        frame.payload.assign(frame.wire.begin() + static_cast<std::ptrdiff_t>(hdr_size), frame.wire.end());
    }
}

sim_node_t* node_from_diag(cy_diag_t* const diag)
{
    if (diag == nullptr) {
        return nullptr;
    }
    return static_cast<sim_node_t*>(diag->user_context.ptr[0]);
}

void capture_diag(sim_net_t&          net,
                  const std::size_t   node_index,
                  const diag_kind_t   kind,
                  cy_topic_t* const   topic,
                  const std::uint32_t subject_id,
                  const std::uint32_t evictions,
                  const std::uint64_t gossip_hash,
                  const cy_err_t      error,
                  const std::uint16_t line_number,
                  const cy_str_t      name)
{
    diag_capture_t out{};
    out.node_index  = node_index;
    out.kind        = kind;
    out.has_topic   = topic != nullptr;
    out.topic_hash  = (topic != nullptr) ? cy_topic_hash(topic) : 0U;
    out.subject_id  = subject_id;
    out.evictions   = evictions;
    out.gossip_hash = gossip_hash;
    out.error       = error;
    out.line_number = line_number;
    out.name_len    = std::min<std::size_t>(name.len, CY_TOPIC_NAME_MAX);
    if ((out.name_len > 0U) && (name.str != nullptr)) {
        std::memcpy(out.name.data(), name.str, out.name_len);
    }
    out.name.at(out.name_len) = '\0';
    try {
        net.diag_captures.push_back(out);
    } catch (const std::bad_alloc&) {
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

bool op_fault_capture_push(sim_net_t& net, const op_fault_capture_t& capture)
{
    try {
        net.op_fault_captures.push_back(capture);
    } catch (const std::bad_alloc&) {
        return false;
    }
    return true;
}

op_fault_effect_t op_fault_evaluate_and_capture(sim_node_t& self, op_info_t op)
{
    sim_net_t& net = *self.network;
    op.sequence    = ++net.next_operation_sequence;

    const op_fault_effect_t effect =
      (net.op_faults != nullptr) ? op_fault_plan_evaluate(*net.op_faults, op) : op_fault_effect_t{};

    op_fault_capture_t capture{};
    capture.op     = op;
    capture.failed = effect.fail;
    capture.error  = effect.error;
    (void)op_fault_capture_push(net, capture);
    return effect;
}

cy_err_t enqueue_frame(sim_node_t&                       src,
                       const std::size_t                 dst_index,
                       const bool                        unicast,
                       const std::uint32_t               subject_id,
                       const cy_prio_t                   priority,
                       const std::vector<unsigned char>& wire)
{
    sim_net_t&   net = *src.network;
    frame_info_t base{};
    base.source       = src.index;
    base.destination  = dst_index;
    base.unicast      = unicast;
    base.subject_id   = subject_id;
    base.priority     = priority;
    base.send_time    = src.now;
    base.deliver_time = src.now;
    base.wire         = wire;
    frame_parse(base);

    const fault_effect_t effect =
      (net.frame_faults != nullptr) ? fault_plan_evaluate(*net.frame_faults, base) : fault_effect_t{};
    const std::size_t copies = effect.drop ? 1U : std::min<std::size_t>(max_fault_copies, 1U + effect.duplicates);

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
    const bool       is_broadcast = subject_id == 0x1FFFFUL;

    cy_err_t result = CY_OK;
    for (std::size_t i = 0U; i < net.nodes.size(); i++) {
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

cy_err_t enqueue_unicast(sim_node_t&                       src,
                         const std::uint64_t               destination_node_id,
                         const cy_prio_t                   priority,
                         const std::vector<unsigned char>& wire)
{
    const sim_net_t&  net = *src.network;
    const std::size_t ix  = find_node_index_by_id(net, destination_node_id);
    if (ix >= net.nodes.size()) {
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
        capture_diag(
          net, dst.index, diag_kind_t::async_error, nullptr, 0U, 0U, 0U, CY_ERR_MEMORY, 0U, cy_str_t{ 0, nullptr });
        return;
    }

    cy_message_ts_t mts{};
    mts.timestamp = frame.frame.deliver_time;
    mts.content   = msg;

    cy_lane_t lane{};
    lane.id   = net.nodes.at(frame.frame.source).node_id;
    lane.prio = frame.frame.priority;
    std::memset(lane.ctx.state, 0, sizeof(lane.ctx.state));
    const std::size_t copy_size = std::min(sizeof(lane.ctx.state), sizeof(lane.id));
    std::memcpy(lane.ctx.state, &lane.id, copy_size);

    if (frame.frame.unicast) {
        cy_on_message(&dst.platform, lane, nullptr, mts);
        return;
    }

    const sim_subject_reader_t* const reader = find_reader(dst, frame.frame.subject_id);
    if (reader != nullptr) {
        cy_on_message(&dst.platform, lane, &reader->base.subject_id, mts);
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
        const auto ins       = self->active_writer_subjects.insert(subject_id);
        enforce(ins.second);
    }
    return (out != nullptr) ? &out->base : nullptr;
}

extern "C" void sim_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    sim_node_t* const self   = node_from(platform);
    const auto        erased = self->active_writer_subjects.erase(writer->subject_id);
    enforce(erased == 1U);

    guarded_heap_free(&self->core_heap, writer);
}

extern "C" cy_err_t sim_subject_writer_send(cy_platform_t* const       platform,
                                            cy_subject_writer_t* const writer,
                                            const cy_us_t              deadline,
                                            const cy_prio_t            priority,
                                            const cy_bytes_t           message)
{
    if (writer == nullptr) {
        return CY_ERR_ARGUMENT;
    }
    sim_node_t* const self = node_from(platform);

    op_info_t op{};
    op.node_index                     = self->index;
    op.kind                           = op_kind_t::subject_send;
    op.deadline                       = deadline;
    const op_fault_effect_t op_effect = op_fault_evaluate_and_capture(*self, op);
    if (op_effect.fail) {
        return op_effect.error;
    }

    std::vector<unsigned char> wire;
    if (!flatten_fragments(message, wire)) {
        return CY_ERR_ARGUMENT;
    }
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
        const auto ins       = self->active_reader_subjects.insert(subject_id);
        enforce(ins.second);
    }
    return (out != nullptr) ? &out->base : nullptr;
}

extern "C" void sim_subject_reader_extent_set(cy_platform_t* const       platform,
                                              cy_subject_reader_t* const reader,
                                              const std::size_t          extent)
{
    enforce(node_from(platform)->active_reader_subjects.count(reader->subject_id) == 1U);
    auto* const r =
      reinterpret_cast<sim_subject_reader_t*>(reader); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
    r->extent = extent;
}

extern "C" void sim_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    sim_node_t* const self   = node_from(platform);
    const auto        erased = self->active_reader_subjects.erase(reader->subject_id);
    enforce(erased == 1U);

    auto* const ptr =
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

extern "C" cy_err_t sim_unicast_send(cy_platform_t* const   platform,
                                     const cy_lane_t* const lane,
                                     const cy_us_t          deadline,
                                     const cy_bytes_t       message)
{
    if (lane == nullptr) {
        return CY_ERR_ARGUMENT;
    }
    sim_node_t* const self = node_from(platform);

    op_info_t op{};
    op.node_index                     = self->index;
    op.kind                           = op_kind_t::unicast_send;
    op.deadline                       = deadline;
    op.has_lane_id                    = true;
    op.lane_id                        = lane->id;
    const op_fault_effect_t op_effect = op_fault_evaluate_and_capture(*self, op);
    if (op_effect.fail) {
        return op_effect.error;
    }

    std::vector<unsigned char> wire;
    if (!flatten_fragments(message, wire)) {
        return CY_ERR_ARGUMENT;
    }
    return enqueue_unicast(*self, lane->id, lane->prio, wire);
}

extern "C" void sim_unicast_extent_set(cy_platform_t* const platform, const std::size_t extent)
{
    (void)platform;
    (void)extent;
}

extern "C" cy_err_t sim_spin(cy_platform_t* const platform, const cy_us_t deadline)
{
    sim_node_t* const self = node_from(platform);

    op_info_t op{};
    op.node_index = self->index;
    op.kind       = op_kind_t::spin;
    op.deadline   = deadline;

    const op_fault_effect_t op_effect = op_fault_evaluate_and_capture(*self, op);
    if (op_effect.fail) {
        return op_effect.error;
    }
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

extern "C" void sim_on_diag_async_error(cy_diag_t* const    diag,
                                        cy_topic_t* const   topic,
                                        const cy_err_t      error,
                                        const std::uint16_t line_number)
{
    sim_node_t* const node = node_from_diag(diag);
    if ((node == nullptr) || (node->network == nullptr)) {
        return;
    }
    capture_diag(*node->network,
                 node->index,
                 diag_kind_t::async_error,
                 topic,
                 0U,
                 0U,
                 0U,
                 error,
                 line_number,
                 cy_str_t{ 0, nullptr });
}

extern "C" void sim_on_diag_topic_reallocated(cy_diag_t* const    diag,
                                              cy_topic_t* const   topic,
                                              const std::uint32_t subject_id,
                                              const std::uint32_t evictions)
{
    sim_node_t* const node = node_from_diag(diag);
    if ((node == nullptr) || (node->network == nullptr)) {
        return;
    }
    capture_diag(*node->network,
                 node->index,
                 diag_kind_t::topic_reallocated,
                 topic,
                 subject_id,
                 evictions,
                 0U,
                 CY_OK,
                 0U,
                 cy_str_t{ 0, nullptr });
}

extern "C" void sim_on_diag_topic_created(cy_diag_t* const diag, cy_topic_t* const topic)
{
    sim_node_t* const node = node_from_diag(diag);
    if ((node == nullptr) || (node->network == nullptr)) {
        return;
    }
    capture_diag(
      *node->network, node->index, diag_kind_t::topic_created, topic, 0U, 0U, 0U, CY_OK, 0U, cy_str_t{ 0, nullptr });
}

extern "C" void sim_on_diag_topic_destroyed(cy_diag_t* const diag, cy_topic_t* const topic)
{
    sim_node_t* const node = node_from_diag(diag);
    if ((node == nullptr) || (node->network == nullptr)) {
        return;
    }
    capture_diag(
      *node->network, node->index, diag_kind_t::topic_destroyed, topic, 0U, 0U, 0U, CY_OK, 0U, cy_str_t{ 0, nullptr });
}

extern "C" void sim_on_diag_gossip_processed(cy_diag_t* const    diag,
                                             cy_topic_t* const   topic,
                                             const cy_str_t      name,
                                             const std::uint64_t hash)
{
    sim_node_t* const node = node_from_diag(diag);
    if ((node == nullptr) || (node->network == nullptr)) {
        return;
    }
    capture_diag(*node->network, node->index, diag_kind_t::gossip_processed, topic, 0U, 0U, hash, CY_OK, 0U, name);
}

const cy_diag_vtable_t sim_diag_vtable = {
    .async_error       = sim_on_diag_async_error,
    .topic_created     = sim_on_diag_topic_created,
    .topic_destroyed   = sim_on_diag_topic_destroyed,
    .topic_reallocated = sim_on_diag_topic_reallocated,
    .gossip_processed  = sim_on_diag_gossip_processed,
};

} // namespace

cy_err_t sim_net_init(sim_net_t& self, const std::uint32_t subject_id_modulus, const std::uint64_t random_seed_base)
{
    sim_net_config_t config{};
    config.node_count         = sim_node_count;
    config.subject_id_modulus = subject_id_modulus;
    config.random_seed_base   = random_seed_base;
    return sim_net_init_ex(self, config);
}

cy_err_t sim_net_init_ex(sim_net_t& self, const sim_net_config_t& config)
{
    if (config.node_count == 0U) {
        return CY_ERR_ARGUMENT;
    }

    self                    = sim_net_t{};
    self.subject_id_modulus = config.subject_id_modulus;
    try {
        self.nodes.resize(config.node_count);
    } catch (const std::bad_alloc&) {
        return CY_ERR_MEMORY;
    }
    for (std::size_t i = 0U; i < self.nodes.size(); i++) {
        sim_node_t& node = self.nodes.at(i);
        node             = sim_node_t{};

        guarded_heap_init(&node.core_heap, UINT64_C(0xABC0000000000000) + i);
        guarded_heap_init(&node.message_heap, UINT64_C(0xDEF0000000000000) + i);

        node.network      = &self;
        node.index        = i;
        node.node_id      = i + 1U;
        node.now          = 0;
        node.random_state = config.random_seed_base + (i * UINT64_C(0x9E3779B97F4A7C15));

        node.vtable.subject_writer_new        = sim_subject_writer_new;
        node.vtable.subject_writer_destroy    = sim_subject_writer_destroy;
        node.vtable.subject_writer_send       = sim_subject_writer_send;
        node.vtable.subject_reader_new        = sim_subject_reader_new;
        node.vtable.subject_reader_extent_set = sim_subject_reader_extent_set;
        node.vtable.subject_reader_destroy    = sim_subject_reader_destroy;
        node.vtable.unicast                   = sim_unicast_send;
        node.vtable.unicast_extent_set        = sim_unicast_extent_set;
        node.vtable.spin                      = sim_spin;
        node.vtable.now                       = sim_now;
        node.vtable.realloc                   = sim_realloc;
        node.vtable.random                    = sim_random;

        node.platform.cy                 = nullptr;
        node.platform.subject_id_modulus = config.subject_id_modulus;
        node.platform.vtable             = &node.vtable;

        const std::string home = "node" + std::to_string(i);
        node.cy                = cy_new(&node.platform, cy_str(home.c_str()), cy_str_t{ 0, nullptr });
        if (node.cy == nullptr) {
            sim_net_deinit(self);
            return CY_ERR_MEMORY;
        }
        node.diag_listener =
          cy_diag_t{ .next = nullptr, .user_context = CY_USER_CONTEXT_EMPTY, .vtable = &sim_diag_vtable };
        node.diag_listener.user_context.ptr[0] = &node;
        cy_diag_add(node.cy, &node.diag_listener);
    }
    return CY_OK;
}

void sim_net_deinit(sim_net_t& self)
{
    for (sim_node_t& node : self.nodes) {
        if (node.cy != nullptr) {
            cy_destroy(node.cy);
            node.cy = nullptr;
        }
        node.readers = nullptr;
        node.network = nullptr;
    }
    self.queue.clear();
    self.frame_faults = nullptr;
    self.op_faults    = nullptr;
}

void sim_net_faults_set(sim_net_t& self, const fault_plan_t* const frame_faults) { self.frame_faults = frame_faults; }

void sim_net_faults_set(sim_net_t& self, const fault_plan_t* const frame_faults, const op_fault_plan_t* const op_faults)
{
    self.frame_faults = frame_faults;
    self.op_faults    = op_faults;
}

void sim_net_op_faults_set(sim_net_t& self, const op_fault_plan_t* const op_faults) { self.op_faults = op_faults; }

cy_t* sim_net_cy(sim_net_t& self, const std::size_t node_index)
{
    enforce(node_index < self.nodes.size());
    return self.nodes.at(node_index).cy;
}

const cy_t* sim_net_cy(const sim_net_t& self, const std::size_t node_index)
{
    enforce(node_index < self.nodes.size());
    return self.nodes.at(node_index).cy;
}

cy_platform_t* sim_net_platform(sim_net_t& self, const std::size_t node_index)
{
    enforce(node_index < self.nodes.size());
    return &self.nodes.at(node_index).platform;
}

const cy_platform_t* sim_net_platform(const sim_net_t& self, const std::size_t node_index)
{
    enforce(node_index < self.nodes.size());
    return &self.nodes.at(node_index).platform;
}

void sim_net_node_now_set(sim_net_t& self, const std::size_t node_index, const cy_us_t now)
{
    enforce(node_index < self.nodes.size());
    self.nodes.at(node_index).now = now;
}

std::uint64_t sim_net_node_id(const sim_net_t& self, const std::size_t node_index)
{
    enforce(node_index < self.nodes.size());
    return self.nodes.at(node_index).node_id;
}

std::size_t sim_net_node_count(const sim_net_t& self) { return self.nodes.size(); }

cy_err_t sim_net_spin_node(sim_net_t& self, const std::size_t node_index)
{
    enforce(node_index < self.nodes.size());
    return cy_spin_once(self.nodes.at(node_index).cy);
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

const std::vector<diag_capture_t>& sim_net_diag_captures(const sim_net_t& self) { return self.diag_captures; }

const std::vector<op_fault_capture_t>& sim_net_op_fault_captures(const sim_net_t& self)
{
    return self.op_fault_captures;
}

void sim_net_clear_captures(sim_net_t& self)
{
    self.captures.clear();
    self.diag_captures.clear();
    self.op_fault_captures.clear();
}

guarded_heap_t& sim_net_core_heap(sim_net_t& self, const std::size_t node_index)
{
    enforce(node_index < self.nodes.size());
    return self.nodes.at(node_index).core_heap;
}

const guarded_heap_t& sim_net_core_heap(const sim_net_t& self, const std::size_t node_index)
{
    enforce(node_index < self.nodes.size());
    return self.nodes.at(node_index).core_heap;
}

guarded_heap_t& sim_net_message_heap(sim_net_t& self, const std::size_t node_index)
{
    enforce(node_index < self.nodes.size());
    return self.nodes.at(node_index).message_heap;
}

const guarded_heap_t& sim_net_message_heap(const sim_net_t& self, const std::size_t node_index)
{
    enforce(node_index < self.nodes.size());
    return self.nodes.at(node_index).message_heap;
}

} // namespace e2e
