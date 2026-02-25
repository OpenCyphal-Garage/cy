#pragma once

#include <cy_platform.h>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <vector>

namespace e2e {

/// Captured metadata of one candidate/actual wire frame in the two-node simulation.
struct frame_info_t final
{
    std::uint64_t sequence{ 0U };
    std::size_t   source{ 0U };
    std::size_t   destination{ 0U };

    bool          p2p{ false };
    std::uint32_t subject_id{ 0U };
    cy_prio_t     priority{ cy_prio_nominal };

    cy_us_t send_time{ 0 };
    cy_us_t deliver_time{ 0 };

    std::uint8_t  header_type{ 0U };
    bool          has_tag{ false };
    std::uint64_t tag{ 0U };
    bool          has_topic_hash{ false };
    std::uint64_t topic_hash{ 0U };

    std::vector<unsigned char> payload{};
    std::vector<unsigned char> wire{};
};

using frame_predicate_t = std::function<bool(const frame_info_t&)>;

enum class fault_action_t : std::uint8_t
{
    drop,
    delay,
    duplicate,
};

struct fault_rule_t final
{
    fault_action_t    action{ fault_action_t::drop };
    frame_predicate_t predicate{};
    cy_us_t           delay{ 0 };
    std::size_t       duplicates{ 0U };
};

struct fault_plan_t final
{
    std::vector<fault_rule_t> rules{};
};

struct fault_effect_t final
{
    bool        drop{ false };
    cy_us_t     delay{ 0 };
    std::size_t duplicates{ 0U };
};

void fault_plan_add_drop(fault_plan_t& plan, frame_predicate_t predicate);
void fault_plan_add_delay(fault_plan_t& plan, cy_us_t delay, frame_predicate_t predicate);
void fault_plan_add_duplicate(fault_plan_t& plan, std::size_t duplicates, frame_predicate_t predicate);

fault_effect_t fault_plan_evaluate(const fault_plan_t& plan, const frame_info_t& frame);

frame_predicate_t fault_predicate_all();
frame_predicate_t fault_predicate_none();
frame_predicate_t fault_predicate_direction(std::size_t source, std::size_t destination);
frame_predicate_t fault_predicate_header_type(std::uint8_t header_type);
frame_predicate_t fault_predicate_tag(std::uint64_t tag);
frame_predicate_t fault_predicate_topic_hash(std::uint64_t topic_hash);
frame_predicate_t fault_predicate_subject_id(std::uint32_t subject_id);
frame_predicate_t fault_predicate_send_time(cy_us_t min_inclusive, cy_us_t max_inclusive);
frame_predicate_t fault_predicate_every_nth(std::size_t every_n, std::size_t phase = 0U);
frame_predicate_t fault_predicate_not(frame_predicate_t predicate);
frame_predicate_t fault_predicate_all_of(std::vector<frame_predicate_t> predicates);
frame_predicate_t fault_predicate_any_of(std::vector<frame_predicate_t> predicates);

} // namespace e2e
