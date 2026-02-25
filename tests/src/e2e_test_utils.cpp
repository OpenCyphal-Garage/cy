#include "e2e_test_utils.hpp"
#include "message.h"
#include <array>
#include <cassert>
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

} // namespace

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

cy_err_t drive_round(sim_net_t& net)
{
    return drive_round(net, sim_net_node_now(net, sim_node_a), sim_net_node_now(net, sim_node_b));
}

cy_err_t drive_round(sim_net_t& net, const cy_us_t now_a, const cy_us_t now_b)
{
    sim_net_node_now_set(net, sim_node_a, now_a);
    sim_net_node_now_set(net, sim_node_b, now_b);

    const cy_us_t now = (now_a > now_b) ? now_a : now_b;
    sim_net_deliver_due(net, now);
    const cy_err_t err_a = sim_net_spin_node(net, sim_node_a);
    if (err_a != CY_OK) {
        return err_a;
    }
    const cy_err_t err_b = sim_net_spin_node(net, sim_node_b);
    if (err_b != CY_OK) {
        return err_b;
    }
    sim_net_deliver_due(net, now);
    return CY_OK;
}

cy_err_t drive_until(sim_net_t&                   net,
                     const cy_us_t                start_time,
                     const cy_us_t                step,
                     const std::size_t            max_rounds,
                     const std::function<bool()>& done)
{
    if ((step <= 0) || (!done)) {
        return CY_ERR_ARGUMENT;
    }
    cy_us_t now = start_time;
    for (std::size_t i = 0U; i < max_rounds; i++) {
        const cy_err_t err = drive_round(net, now, now);
        if (err != CY_OK) {
            return err;
        }
        if (done()) {
            return CY_OK;
        }
        now += step;
    }
    return CY_ERR_CAPACITY;
}

invariant_counters_t invariant_snapshot(const sim_net_t& net)
{
    invariant_counters_t out{};
    out.message_live_count    = cy_test_message_live_count();
    out.message_destroy_count = cy_test_message_destroy_count();
    out.queued_frames         = sim_net_pending_frames(net);
    out.async_errors          = sim_net_async_errors(net).size();

    for (std::size_t i = 0U; i < sim_node_count; i++) {
        out.core_heap_fragments.at(i)    = guarded_heap_allocated_fragments(&sim_net_core_heap(net, i));
        out.core_heap_bytes.at(i)        = guarded_heap_allocated_bytes(&sim_net_core_heap(net, i));
        out.message_heap_fragments.at(i) = guarded_heap_allocated_fragments(&sim_net_message_heap(net, i));
        out.message_heap_bytes.at(i)     = guarded_heap_allocated_bytes(&sim_net_message_heap(net, i));
    }
    return out;
}

void assert_no_async_errors(const sim_net_t& net) { TEST_ASSERT_EQUAL_size_t(0U, sim_net_async_errors(net).size()); }

void assert_no_queued_frames(const sim_net_t& net) { TEST_ASSERT_EQUAL_size_t(0U, sim_net_pending_frames(net)); }

void assert_no_live_messages() { TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count()); }

void assert_node_heap_clean(const sim_net_t& net, const std::size_t node_index)
{
    assert(node_index < sim_node_count);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&sim_net_core_heap(net, node_index)));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&sim_net_core_heap(net, node_index)));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&sim_net_message_heap(net, node_index)));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&sim_net_message_heap(net, node_index)));
}

void assert_all_heaps_clean(const sim_net_t& net)
{
    assert_node_heap_clean(net, sim_node_a);
    assert_node_heap_clean(net, sim_node_b);
}

void assert_quiescent(const sim_net_t& net)
{
    assert_no_async_errors(net);
    assert_no_queued_frames(net);
    assert_no_live_messages();
}

} // namespace e2e
