#include <cy_platform.h>
#include <unity.h>
#include "gossip_test_utils.hpp"
#include "guarded_heap.h"
#include "helpers.h"
#include "message.h"
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <set>
#include <string>
#include <vector>

namespace {
constexpr std::uint8_t header_type_msg_be = 0U;
constexpr std::size_t  header_bytes       = 24U;
constexpr std::size_t  max_wire_size      = 256U;
constexpr std::size_t  max_nodes          = 16U;

struct sim_subject_writer_t
{
    cy_subject_writer_t base{};
};

struct sim_subject_reader_t
{
    cy_subject_reader_t   base{};
    std::size_t           extent{ 0U };
    sim_subject_reader_t* next{ nullptr };
};

struct sim_network_t;

struct sim_node_t final
{
    cy_platform_t        platform{};
    cy_platform_vtable_t vtable{};
    guarded_heap_t       core_heap{};
    guarded_heap_t       message_heap{};

    sim_network_t* network{ nullptr };
    std::size_t    index{ 0U };
    std::uint64_t  node_id{ 0U };
    cy_t*          cy{ nullptr };

    cy_us_t       now{ 0 };
    std::uint64_t random_state{ UINT64_C(0x0123456789ABCDEF) };

    sim_subject_reader_t* readers{ nullptr };

    std::size_t subject_send_count{ 0U };
    std::size_t unicast_send_count{ 0U };

    std::uint64_t last_msg_be_hash{ 0U };
    std::uint32_t last_msg_be_subject_id{ 0U };

    std::set<std::uint32_t> active_reader_subjects;
    std::set<std::uint32_t> active_writer_subjects;
};

struct sim_event_t
{
    cy_us_t                                  deliver_at{ 0 };
    std::uint64_t                            order{ 0U };
    std::size_t                              src_index{ 0U };
    std::size_t                              dst_index{ 0U };
    bool                                     unicast{ false };
    std::uint32_t                            subject_id{ 0U };
    cy_prio_t                                prio{ cy_prio_nominal };
    std::size_t                              size{ 0U };
    std::array<unsigned char, max_wire_size> data{};
};

struct sim_network_t final
{
    std::array<sim_node_t, max_nodes> nodes{};
    std::size_t                       node_count{ 0U };
    std::vector<sim_event_t>          queue{};
    std::uint64_t                     order_counter{ 0U };
    std::uint32_t                     drop_mod{ 0U };
    cy_us_t                           max_delay{ 0 };
};

sim_node_t* node_from(cy_platform_t* const platform)
{
    return reinterpret_cast<sim_node_t*>(platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
}

const sim_node_t* node_from_const(const cy_platform_t* const platform)
{
    return reinterpret_cast<const sim_node_t*>(platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
}

using gossip_test::flatten_fragments;

std::uint64_t read_u64(const unsigned char* const data, const std::size_t offset)
{
    std::uint64_t out = 0U;
    for (std::size_t i = 0U; i < 8U; i++) {
        out |= static_cast<std::uint64_t>(data[offset + i]) << (i * 8U);
    }
    return out;
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

std::size_t find_node_index_by_id(const sim_network_t& net, const std::uint64_t node_id)
{
    for (std::size_t i = 0U; i < net.node_count; i++) {
        if (net.nodes.at(i).node_id == node_id) {
            return i;
        }
    }
    return net.node_count;
}

void queue_event(sim_network_t&                                  net,
                 const sim_node_t&                               src,
                 const std::size_t                               dst_index,
                 const bool                                      unicast,
                 const std::uint32_t                             subject_id,
                 const cy_prio_t                                 prio,
                 const std::array<unsigned char, max_wire_size>& data,
                 const std::size_t                               size)
{
    net.order_counter++;
    const std::uint64_t order = net.order_counter;
    if ((net.drop_mod > 0U) && ((order % net.drop_mod) == 0U)) {
        return;
    }
    const auto    delay_mod = static_cast<std::uint64_t>(net.max_delay + 1);
    const cy_us_t delay     = (delay_mod > 0U) ? static_cast<cy_us_t>(order % delay_mod) : 0;

    sim_event_t ev{};
    ev.deliver_at = src.now + delay;
    ev.order      = order;
    ev.src_index  = src.index;
    ev.dst_index  = dst_index;
    ev.unicast    = unicast;
    ev.subject_id = subject_id;
    ev.prio       = prio;
    ev.size       = size;
    ev.data       = data;
    net.queue.push_back(ev);
}

void enqueue_subject(sim_node_t&                                     src,
                     const std::uint32_t                             subject_id,
                     const cy_prio_t                                 prio,
                     const std::array<unsigned char, max_wire_size>& data,
                     const std::size_t                               size)
{
    sim_network_t& net          = *src.network;
    const bool     is_broadcast = subject_id == 0x1FFFFUL;
    for (std::size_t i = 0U; i < net.node_count; i++) {
        if (i == src.index) {
            continue;
        }
        if (is_broadcast || (find_reader(net.nodes.at(i), subject_id) != nullptr)) {
            queue_event(net, src, i, false, subject_id, prio, data, size);
        }
    }
}

void enqueue_unicast(sim_node_t&                                     src,
                     const std::uint64_t                             dst_id,
                     const cy_prio_t                                 prio,
                     const std::array<unsigned char, max_wire_size>& data,
                     const std::size_t                               size)
{
    sim_network_t&    net       = *src.network;
    const std::size_t dst_index = find_node_index_by_id(net, dst_id);
    if (dst_index < net.node_count) {
        queue_event(net, src, dst_index, true, 0U, prio, data, size);
    }
}

extern "C" cy_subject_writer_t* sim_subject_writer_new(cy_platform_t* const platform, const std::uint32_t subject_id)
{
    sim_node_t* const self = node_from(platform);
    auto* const       out =
      static_cast<sim_subject_writer_t*>(guarded_heap_alloc(&self->core_heap, sizeof(sim_subject_writer_t)));
    if (out != nullptr) {
        out->base.subject_id = subject_id;
        TEST_ASSERT_EQUAL_INT(0U, self->active_writer_subjects.count(subject_id));
        self->active_writer_subjects.insert(subject_id);
    }
    return (out != nullptr) ? &out->base : nullptr;
}

extern "C" void sim_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    sim_node_t* const self = node_from(platform);
    TEST_ASSERT_EQUAL_INT(1U, self->active_writer_subjects.erase(writer->subject_id));
    guarded_heap_free(&self->core_heap, writer);
}

extern "C" cy_err_t sim_subject_writer_send(cy_platform_t* const       platform,
                                            cy_subject_writer_t* const writer,
                                            const cy_us_t              deadline,
                                            const cy_prio_t            priority,
                                            const cy_bytes_t           message)
{
    (void)deadline;
    sim_node_t* const self = node_from(platform);
    self->subject_send_count++;

    std::array<unsigned char, max_wire_size> data{};
    const std::size_t                        size = flatten_fragments(message, data.data(), data.size());

    if ((writer != nullptr) && (size >= header_bytes) && (data[0] == header_type_msg_be)) {
        self->last_msg_be_hash       = read_u64(data.data(), 8U);
        self->last_msg_be_subject_id = writer->subject_id;
    }
    enqueue_subject(*self, (writer != nullptr) ? writer->subject_id : 0U, priority, data, size);
    return CY_OK;
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
        TEST_ASSERT_EQUAL_INT(0U, self->active_reader_subjects.count(subject_id));
        self->active_reader_subjects.insert(subject_id);
    }
    return (out != nullptr) ? &out->base : nullptr;
}

extern "C" void sim_subject_reader_extent_set(cy_platform_t* const       platform,
                                              cy_subject_reader_t* const reader,
                                              const std::size_t          extent)
{
    sim_node_t* const self = node_from(platform);
    TEST_ASSERT_EQUAL_INT(1U, self->active_reader_subjects.count(reader->subject_id));
    auto* const r = reinterpret_cast<sim_subject_reader_t*>(reader); // NOLINT(*-reinterpret-cast)
    r->extent     = extent;
}

extern "C" void sim_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    sim_node_t* const self = node_from(platform);
    TEST_ASSERT_EQUAL_INT(1U, self->active_reader_subjects.erase(reader->subject_id));
    auto* const            r   = reinterpret_cast<sim_subject_reader_t*>(reader); // NOLINT(*-reinterpret-cast)
    sim_subject_reader_t** cur = &self->readers;
    while (*cur != nullptr) {
        if (*cur == r) {
            *cur = r->next;
            break;
        }
        cur = &(*cur)->next;
    }
    guarded_heap_free(&self->core_heap, reader);
}

extern "C" cy_err_t sim_unicast_send(cy_platform_t* const   platform,
                                     const cy_lane_t* const lane,
                                     const cy_us_t          deadline,
                                     const cy_bytes_t       message)
{
    (void)deadline;
    sim_node_t* const self = node_from(platform);
    self->unicast_send_count++;

    std::array<unsigned char, max_wire_size> data{};
    const std::size_t                        size = flatten_fragments(message, data.data(), data.size());
    enqueue_unicast(
      *self, (lane != nullptr) ? lane->id : 0U, (lane != nullptr) ? lane->prio : cy_prio_nominal, data, size);
    return CY_OK;
}

extern "C" void sim_unicast_extent_set(cy_platform_t* const platform, const std::size_t extent)
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
    (void)cy;
    (void)topic;
    (void)error;
    (void)line_number;
    TEST_FAIL_MESSAGE("Unexpected async error in simulation");
}

void network_node_init(sim_network_t& net, const std::size_t index)
{
    sim_node_t& node = net.nodes.at(index);
    node             = sim_node_t{};
    guarded_heap_init(&node.core_heap, UINT64_C(0xABC0000000000000) + index);
    guarded_heap_init(&node.message_heap, UINT64_C(0xDEF0000000000000) + index);

    node.network      = &net;
    node.index        = index;
    node.node_id      = index + 1U;
    node.now          = 0;
    node.readers      = nullptr;
    node.random_state = UINT64_C(0x1020304050607080) + index;

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

    node.platform.vtable             = &node.vtable;
    node.platform.subject_id_modulus = static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit);
    node.platform.cy                 = nullptr;
    const std::string home           = "node" + std::to_string(index);
    node.cy                          = cy_new(&node.platform, cy_str(home.c_str()), cy_str_t{ 0, nullptr });
    TEST_ASSERT_NOT_NULL(node.cy);
    cy_async_error_handler_set(node.cy, sim_on_async_error);
}

void network_node_deinit(sim_node_t& node)
{
    if (node.cy != nullptr) {
        cy_destroy(node.cy);
        node.cy = nullptr;
    }
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&node.core_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&node.core_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&node.message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&node.message_heap));
}

void network_init(sim_network_t&      net,
                  const std::size_t   node_count,
                  const std::uint32_t drop_mod,
                  const cy_us_t       max_delay)
{
    TEST_ASSERT((node_count > 0U) && (node_count <= max_nodes));
    net            = sim_network_t{};
    net.node_count = node_count;
    net.drop_mod   = drop_mod;
    net.max_delay  = max_delay;
    for (std::size_t i = 0U; i < net.node_count; i++) {
        network_node_init(net, i);
    }
}

void network_deinit(sim_network_t& net)
{
    net.queue.clear();
    for (std::size_t i = 0U; i < net.node_count; i++) {
        network_node_deinit(net.nodes.at(i));
    }
}

void deliver_event(sim_network_t& net, const sim_event_t& ev)
{
    sim_node_t& dst         = net.nodes.at(ev.dst_index);
    dst.now                 = std::max(dst.now, ev.deliver_at);
    cy_message_t* const msg = cy_test_message_make(&dst.message_heap, ev.data.data(), ev.size);
    TEST_ASSERT_NOT_NULL(msg);

    cy_message_ts_t mts{};
    mts.timestamp = ev.deliver_at;
    mts.content   = msg;

    cy_lane_t lane{};
    lane.id           = net.nodes.at(ev.src_index).node_id;
    lane.prio         = ev.prio;
    lane.ctx.state[0] = static_cast<unsigned char>(lane.id & 0xFFU);

    if (ev.unicast) {
        cy_on_message(&dst.platform, lane, nullptr, mts);
    } else {
        const sim_subject_reader_t* const reader = find_reader(dst, ev.subject_id);
        if (reader != nullptr) {
            cy_on_message(&dst.platform, lane, &reader->base.subject_id, mts);
        } else {
            cy_message_refcount_dec(msg);
        }
    }
}

void network_deliver_due(sim_network_t& net, const cy_us_t now)
{
    while (true) {
        std::size_t best = net.queue.size();
        for (std::size_t i = 0U; i < net.queue.size(); i++) {
            const sim_event_t& ev = net.queue.at(i);
            if (ev.deliver_at > now) {
                continue;
            }
            const bool better =
              (best >= net.queue.size()) || (ev.deliver_at < net.queue.at(best).deliver_at) ||
              ((ev.deliver_at == net.queue.at(best).deliver_at) && (ev.order < net.queue.at(best).order));
            if (better) {
                best = i;
            }
        }
        if (best >= net.queue.size()) {
            break;
        }
        const sim_event_t ev = net.queue.at(best);
        net.queue.erase(net.queue.begin() + static_cast<std::ptrdiff_t>(best));
        deliver_event(net, ev);
    }
}

void network_spin_all(sim_network_t& net, const cy_us_t now)
{
    network_deliver_due(net, now);
    for (std::size_t i = 0U; i < net.node_count; i++) {
        net.nodes.at(i).now = now;
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(net.nodes.at(i).cy));
    }
    network_deliver_due(net, now);
}

void network_run(sim_network_t& net, const cy_us_t start, const cy_us_t end, const cy_us_t step)
{
    TEST_ASSERT(step > 0);
    for (cy_us_t t = start; t <= end; t += step) {
        network_spin_all(net, t);
    }
    network_deliver_due(net, end);
}

void inject_gossip(sim_node_t&         node,
                   const std::uint64_t remote_id,
                   const std::uint8_t  ttl,
                   const std::int8_t   lage,
                   const std::uint64_t hash,
                   const std::uint32_t evictions,
                   const char* const   name,
                   const cy_us_t       timestamp)
{
    std::array<unsigned char, max_wire_size> wire{};
    const std::size_t size = make_gossip_header(wire.data(), wire.size(), ttl, lage, hash, evictions, cy_str(name));
    TEST_ASSERT_TRUE(size > 0U);
    cy_message_t* const msg = cy_test_message_make(&node.message_heap, wire.data(), size);
    TEST_ASSERT_NOT_NULL(msg);

    cy_message_ts_t mts{};
    mts.timestamp = timestamp;
    mts.content   = msg;
    cy_lane_t lane{};
    lane.id           = remote_id;
    lane.prio         = cy_prio_nominal;
    lane.ctx.state[0] = static_cast<unsigned char>(remote_id & 0xFFU);
    cy_on_message(&node.platform, lane, nullptr, mts);
}

std::uint32_t publish_and_get_subject_id(sim_node_t& node, cy_publisher_t* const pub, const std::uint64_t expected_hash)
{
    static const unsigned char payload = 0x42U;
    const cy_bytes_t           msg     = { .size = 1U, .data = &payload, .next = nullptr };

    node.last_msg_be_hash       = 0U;
    node.last_msg_be_subject_id = 0U;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, node.now + 100'000, msg));
    TEST_ASSERT_EQUAL_UINT64(expected_hash, node.last_msg_be_hash);
    TEST_ASSERT_TRUE(node.last_msg_be_subject_id > 0U);
    return node.last_msg_be_subject_id;
}

void test_api_gossip_sim_two_node_convergence_with_drop_and_reorder()
{
    sim_network_t net{};
    network_init(net, 2U, 5U, 20'000);

    static const char* const       topic_name = "sim/gossip/converge/topic";
    std::array<cy_publisher_t*, 2> pubs{};
    for (std::size_t i = 0U; i < 2U; i++) {
        pubs.at(i) = cy_advertise(net.nodes.at(i).cy, cy_str(topic_name));
        TEST_ASSERT_NOT_NULL(pubs.at(i));
    }
    const cy_topic_t* const topic0 = cy_topic_find_by_name(net.nodes.at(0).cy, cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(topic0);
    const std::uint64_t hash = cy_topic_hash(topic0);

    inject_gossip(net.nodes.at(0), UINT64_C(0x7001), 4U, 8, hash, 7U, topic_name, 1'000'000);
    network_run(net, 1'000'000, 20'000'000, 100'000);

    std::array<std::uint32_t, 2> subject_id{};
    for (std::size_t i = 0U; i < 2U; i++) {
        net.nodes.at(i).now = 20'100'000 + static_cast<cy_us_t>(i);
        subject_id.at(i)    = publish_and_get_subject_id(net.nodes.at(i), pubs.at(i), hash);
    }
    TEST_ASSERT_EQUAL_UINT32(subject_id.at(0), subject_id.at(1));

    for (cy_publisher_t* const pub : pubs) {
        cy_unadvertise(pub);
    }
    network_deinit(net);
}

void test_api_gossip_sim_sixteen_node_convergence_with_churn_like_delivery()
{
    sim_network_t net{};
    network_init(net, 16U, 7U, 50'000);

    static const char* const        topic_name = "sim/gossip/large/topic";
    std::array<cy_publisher_t*, 16> pubs{};
    for (std::size_t i = 0U; i < 16U; i++) {
        pubs.at(i) = cy_advertise(net.nodes.at(i).cy, cy_str(topic_name));
        TEST_ASSERT_NOT_NULL(pubs.at(i));
    }
    const cy_topic_t* const topic0 = cy_topic_find_by_name(net.nodes.at(0).cy, cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(topic0);
    const std::uint64_t hash = cy_topic_hash(topic0);

    for (std::size_t i = 0U; i < net.node_count; i++) {
        if ((i % 2U) != 0U) {
            inject_gossip(
              net.nodes.at(i), UINT64_C(0x8000) + i, 6U, 9, hash, 9U, topic_name, 2'000'000 + static_cast<cy_us_t>(i));
        }
    }
    network_run(net, 2'000'000, 30'000'000, 100'000);

    std::array<std::uint32_t, 16> subject_id{};
    for (std::size_t i = 0U; i < net.node_count; i++) {
        net.nodes.at(i).now = 30'100'000 + static_cast<cy_us_t>(i);
        subject_id.at(i)    = publish_and_get_subject_id(net.nodes.at(i), pubs.at(i), hash);
    }
    for (std::size_t i = 1U; i < net.node_count; i++) {
        TEST_ASSERT_EQUAL_UINT32(subject_id.at(0), subject_id.at(i));
    }

    for (cy_publisher_t* const pub : pubs) {
        cy_unadvertise(pub);
    }
    network_deinit(net);
}

void test_api_gossip_sim_stale_replay_after_convergence_keeps_subject_id_stable()
{
    sim_network_t net{};
    network_init(net, 8U, 6U, 40'000);

    static const char* const       topic_name = "sim/gossip/replay/stable/topic";
    std::array<cy_publisher_t*, 8> pubs{};
    for (std::size_t i = 0U; i < net.node_count; i++) {
        pubs.at(i) = cy_advertise(net.nodes.at(i).cy, cy_str(topic_name));
        TEST_ASSERT_NOT_NULL(pubs.at(i));
    }

    const cy_topic_t* const topic0 = cy_topic_find_by_name(net.nodes.at(0).cy, cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(topic0);
    const std::uint64_t hash = cy_topic_hash(topic0);

    for (std::size_t i = 0U; i < net.node_count; i++) {
        inject_gossip(net.nodes.at(i),
                      UINT64_C(0x9000) + i,
                      6U,
                      static_cast<std::int8_t>(8 + (i % 2U)),
                      hash,
                      static_cast<std::uint32_t>(5U + (i % 3U)),
                      topic_name,
                      3'000'000 + static_cast<cy_us_t>(i));
    }
    network_run(net, 3'000'000, 36'000'000, 100'000);

    std::array<std::uint32_t, 8> subject_id_before{};
    for (std::size_t i = 0U; i < net.node_count; i++) {
        net.nodes.at(i).now     = 36'100'000 + static_cast<cy_us_t>(i);
        subject_id_before.at(i) = publish_and_get_subject_id(net.nodes.at(i), pubs.at(i), hash);
    }
    for (std::size_t i = 1U; i < net.node_count; i++) {
        TEST_ASSERT_EQUAL_UINT32(subject_id_before.at(0), subject_id_before.at(i));
    }

    for (std::size_t i = 0U; i < net.node_count; i++) {
        inject_gossip(
          net.nodes.at(i), UINT64_C(0xA000) + i, 6U, 0, hash, 0U, topic_name, 36'200'000 + static_cast<cy_us_t>(i));
    }
    network_run(net, 36'200'000, 48'000'000, 100'000);

    std::array<std::uint32_t, 8> subject_id_after{};
    for (std::size_t i = 0U; i < net.node_count; i++) {
        net.nodes.at(i).now    = 48'100'000 + static_cast<cy_us_t>(i);
        subject_id_after.at(i) = publish_and_get_subject_id(net.nodes.at(i), pubs.at(i), hash);
    }
    for (std::size_t i = 0U; i < net.node_count; i++) {
        TEST_ASSERT_EQUAL_UINT32(subject_id_before.at(0), subject_id_after.at(i));
    }

    for (cy_publisher_t* const pub : pubs) {
        cy_unadvertise(pub);
    }
    network_deinit(net);
}
} // namespace

extern "C" void setUp()
{
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
    cy_test_message_reset_counters();
}

extern "C" void tearDown() { TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count()); }

int main()
{
    UNITY_BEGIN();
    RUN_TEST(test_api_gossip_sim_two_node_convergence_with_drop_and_reorder);
    RUN_TEST(test_api_gossip_sim_sixteen_node_convergence_with_churn_like_delivery);
    RUN_TEST(test_api_gossip_sim_stale_replay_after_convergence_keeps_subject_id_stable);
    return UNITY_END();
}
