#pragma once

#include "e2e_sim_net.hpp"
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

namespace e2e {

struct app_payload_t final
{
    std::uint32_t publisher_id{ 0U };
    std::uint64_t sequence{ 0U };
};

std::array<unsigned char, 12> app_payload_pack(std::uint32_t publisher_id, std::uint64_t sequence);
bool                          app_payload_unpack(const unsigned char* bytes, std::size_t size, app_payload_t& out);
bool                          app_payload_unpack(const std::vector<unsigned char>& bytes, app_payload_t& out);

/// Generalized deterministic event-loop step for all nodes at the same timestamp.
cy_err_t drive_round_all(sim_net_t& net, cy_us_t now);

/// One deterministic event-loop step:
/// deliver due -> spin node A -> spin node B -> deliver due.
cy_err_t drive_round(sim_net_t& net);
cy_err_t drive_round(sim_net_t& net, cy_us_t now_a, cy_us_t now_b);

void assert_no_queued_frames(const sim_net_t& net);
void assert_no_live_messages();
void assert_all_node_heaps_clean(const sim_net_t& net);
void assert_quiescent(const sim_net_t& net);

} // namespace e2e
