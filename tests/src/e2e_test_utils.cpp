#include "e2e_test_utils.hpp"
#include "message.h"
#include <array>
#include <cstdint>
#include <unity.h>

namespace e2e {
namespace {

void write_u32(std::array<unsigned char, 4>& out, const std::uint32_t value)
{
    for (std::size_t i = 0U; i < 4U; i++) {
        out.at(i) = static_cast<unsigned char>((value >> (i * 8U)) & 0xFFU);
    }
}

void write_u64(std::array<unsigned char, 8>& out, const std::uint64_t value)
{
    for (std::size_t i = 0U; i < 8U; i++) {
        out.at(i) = static_cast<unsigned char>((value >> (i * 8U)) & 0xFFU);
    }
}

std::uint32_t read_u32(const std::array<unsigned char, 4>& in)
{
    std::uint32_t out = 0U;
    for (std::size_t i = 0U; i < 4U; i++) {
        out |= static_cast<std::uint32_t>(in.at(i)) << (i * 8U);
    }
    return out;
}

std::uint64_t read_u64(const std::array<unsigned char, 8>& in)
{
    std::uint64_t out = 0U;
    for (std::size_t i = 0U; i < 8U; i++) {
        out |= static_cast<std::uint64_t>(in.at(i)) << (i * 8U);
    }
    return out;
}

cy_err_t drive_round_vector(sim_net_t& net, const std::vector<cy_us_t>& now_by_node)
{
    const std::size_t count = sim_net_node_count(net);
    if ((count == 0U) || (now_by_node.size() != count)) {
        return CY_ERR_ARGUMENT;
    }

    cy_us_t now_limit = now_by_node.front();
    for (std::size_t i = 0U; i < count; i++) {
        sim_net_node_now_set(net, i, now_by_node.at(i));
        now_limit = std::max(now_limit, now_by_node.at(i));
    }

    sim_net_deliver_due(net, now_limit);
    for (std::size_t i = 0U; i < count; i++) {
        const cy_err_t err = sim_net_spin_node(net, i);
        if (err != CY_OK) {
            return err;
        }
    }
    sim_net_deliver_due(net, now_limit);
    return CY_OK;
}

void assert_no_async_errors(const sim_net_t& net) { TEST_ASSERT_EQUAL_size_t(0U, sim_net_async_errors(net).size()); }

void assert_node_heap_clean(const sim_net_t& net, const std::size_t node_index)
{
    TEST_ASSERT_TRUE(node_index < sim_net_node_count(net));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&sim_net_core_heap(net, node_index)));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&sim_net_core_heap(net, node_index)));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&sim_net_message_heap(net, node_index)));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&sim_net_message_heap(net, node_index)));
}

} // namespace

extern "C" void on_arrival_capture(cy_future_t* const sub)
{
    const cy_arrival_t arrival = cy_arrival_move(sub);
    if (arrival.message.content == nullptr) {
        return;
    }
    auto* const capture = static_cast<arrival_capture_t*>(cy_future_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(capture);

    std::array<unsigned char, 32> bytes{};
    const std::size_t             size = cy_message_read(arrival.message.content, 0U, bytes.size(), bytes.data());
    app_payload_t                 payload{};
    if (!app_payload_unpack(bytes.data(), size, payload)) {
        capture->malformed++;
        cy_message_refcount_dec(arrival.message.content);
        return;
    }
    capture->samples.push_back(arrival_sample_t{
      .publisher_id = payload.publisher_id,
      .sequence     = payload.sequence,
      .topic_hash   = arrival.breadcrumb.topic_hash,
    });
    cy_message_refcount_dec(arrival.message.content);
}

std::array<unsigned char, 12> app_payload_pack(const std::uint32_t publisher_id, const std::uint64_t sequence)
{
    std::array<unsigned char, 12> out{};
    std::array<unsigned char, 4>  pub_bytes{};
    std::array<unsigned char, 8>  seq_bytes{};
    write_u32(pub_bytes, publisher_id);
    write_u64(seq_bytes, sequence);
    for (std::size_t i = 0U; i < 4U; i++) {
        out.at(i) = pub_bytes.at(i);
    }
    for (std::size_t i = 0U; i < 8U; i++) {
        out.at(4U + i) = seq_bytes.at(i);
    }
    return out;
}

bool app_payload_unpack(const unsigned char* const bytes, const std::size_t size, app_payload_t& out)
{
    if ((bytes == nullptr) || (size < 12U)) {
        return false;
    }
    std::array<unsigned char, 4> pub_bytes{};
    std::array<unsigned char, 8> seq_bytes{};
    for (std::size_t i = 0U; i < 4U; i++) {
        pub_bytes.at(i) = bytes[i];
    }
    for (std::size_t i = 0U; i < 8U; i++) {
        seq_bytes.at(i) = bytes[4U + i];
    }
    out.publisher_id = read_u32(pub_bytes);
    out.sequence     = read_u64(seq_bytes);
    return true;
}

bool app_payload_unpack(const std::vector<unsigned char>& bytes, app_payload_t& out)
{
    return app_payload_unpack(bytes.data(), bytes.size(), out);
}

cy_err_t drive_round_all(sim_net_t& net, const cy_us_t now)
{
    const std::size_t count = sim_net_node_count(net);
    if (count == 0U) {
        return CY_ERR_ARGUMENT;
    }
    return drive_round_vector(net, std::vector<cy_us_t>(count, now));
}

cy_err_t drive_round(sim_net_t& net, const cy_us_t now_a, const cy_us_t now_b)
{
    const std::size_t count = sim_net_node_count(net);
    if (count < 2U) {
        return CY_ERR_ARGUMENT;
    }
    const cy_us_t        fallback = std::max(now_a, now_b);
    std::vector<cy_us_t> now_by_node(count, fallback);
    now_by_node.at(sim_node_a) = now_a;
    now_by_node.at(sim_node_b) = now_b;
    return drive_round_vector(net, now_by_node);
}

void assert_no_queued_frames(const sim_net_t& net) { TEST_ASSERT_EQUAL_size_t(0U, sim_net_pending_frames(net)); }

void assert_no_live_messages() { TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count()); }

void assert_all_node_heaps_clean(const sim_net_t& net)
{
    for (std::size_t i = 0U; i < sim_net_node_count(net); i++) {
        assert_node_heap_clean(net, i);
    }
}

void assert_quiescent(const sim_net_t& net)
{
    assert_no_async_errors(net);
    assert_no_queued_frames(net);
    assert_no_live_messages();
}

} // namespace e2e
