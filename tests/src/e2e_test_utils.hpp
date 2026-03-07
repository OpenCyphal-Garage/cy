#pragma once

#include "e2e_sim_net.hpp"
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <vector>

namespace e2e {

struct app_payload_t final
{
    std::uint32_t publisher_id{ 0U };
    std::uint64_t sequence{ 0U };
};

struct invariant_counters_t final
{
    std::size_t                             message_live_count{ 0U };
    std::size_t                             message_destroy_count{ 0U };
    std::size_t                             queued_frames{ 0U };
    std::size_t                             async_errors{ 0U };
    std::array<std::size_t, sim_node_count> core_heap_fragments{};
    std::array<std::size_t, sim_node_count> core_heap_bytes{};
    std::array<std::size_t, sim_node_count> message_heap_fragments{};
    std::array<std::size_t, sim_node_count> message_heap_bytes{};
};

std::array<unsigned char, 12> app_payload_pack(std::uint32_t publisher_id, std::uint64_t sequence);
bool                          app_payload_unpack(const unsigned char* bytes, std::size_t size, app_payload_t& out);
bool                          app_payload_unpack(const std::vector<unsigned char>& bytes, app_payload_t& out);

/// Generalized deterministic event-loop step for all nodes at the same timestamp.
cy_err_t drive_round_all(sim_net_t& net, cy_us_t now);

/// Generalized deterministic event-loop step where each node has its own current time.
cy_err_t drive_round_vector(sim_net_t& net, const std::vector<cy_us_t>& now_by_node);

/// One deterministic event-loop step:
/// deliver due -> spin node A -> spin node B -> deliver due.
cy_err_t drive_round(sim_net_t& net);
cy_err_t drive_round(sim_net_t& net, cy_us_t now_a, cy_us_t now_b);

cy_err_t drive_until(sim_net_t&                   net,
                     cy_us_t                      start_time,
                     cy_us_t                      step,
                     std::size_t                  max_rounds,
                     const std::function<bool()>& done);

invariant_counters_t invariant_snapshot(const sim_net_t& net);

void assert_no_async_errors(const sim_net_t& net);
void assert_no_queued_frames(const sim_net_t& net);
void assert_no_live_messages();
void assert_node_heap_clean(const sim_net_t& net, std::size_t node_index);
void assert_all_heaps_clean(const sim_net_t& net);
void assert_all_node_heaps_clean(const sim_net_t& net);
void assert_quiescent(const sim_net_t& net);

} // namespace e2e
