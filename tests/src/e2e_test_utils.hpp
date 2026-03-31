#pragma once

#include "e2e_sim_net.hpp"
#include <algorithm>
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

// Common arrival capture types shared across E2E tests.
struct arrival_sample_t final
{
    std::uint32_t publisher_id{ 0U };
    std::uint64_t sequence{ 0U };
    std::uint64_t topic_hash{ 0U };
};

struct arrival_capture_t final
{
    std::vector<arrival_sample_t> samples{};
    std::size_t                   malformed{ 0U };
};

// Subscriber callback that unpacks app_payload and captures into arrival_capture_t.
// Stores topic_hash from the breadcrumb; callers that don't need it simply ignore it.
extern "C" void on_arrival_capture(cy_future_t* sub);

inline std::size_t count_by_publisher(const arrival_capture_t& capture, const std::uint32_t publisher_id)
{
    return static_cast<std::size_t>(std::ranges::count_if(
      capture.samples, [publisher_id](const arrival_sample_t& s) { return s.publisher_id == publisher_id; }));
}

/// Generalized deterministic event-loop step for all nodes at the same timestamp.
cy_err_t drive_round_all(sim_net_t& net, cy_us_t now);

/// One deterministic event-loop step:
/// deliver due -> spin node A -> spin node B -> deliver due.
cy_err_t drive_round(sim_net_t& net, cy_us_t now_a, cy_us_t now_b);

void assert_no_queued_frames(const sim_net_t& net);
void assert_no_live_messages();
void assert_all_node_heaps_clean(const sim_net_t& net);
void assert_quiescent(const sim_net_t& net);

} // namespace e2e
