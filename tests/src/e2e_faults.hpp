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

enum class op_kind_t : std::uint8_t
{
    subject_send,
    p2p_send,
    spin,
};

struct op_info_t final
{
    std::uint64_t sequence{ 0U };
    std::size_t   node_index{ 0U };
    op_kind_t     kind{ op_kind_t::subject_send };

    cy_us_t now{ 0 };
    cy_us_t deadline{ 0 };

    bool          has_subject_id{ false };
    std::uint32_t subject_id{ 0U };

    bool          has_lane_id{ false };
    std::uint64_t lane_id{ 0U };
    cy_prio_t     priority{ cy_prio_nominal };
};

using op_predicate_t = std::function<bool(const op_info_t&)>;

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

enum class op_fault_action_t : std::uint8_t
{
    fail,
    spin_delay,
};

struct op_fault_rule_t final
{
    op_fault_action_t action{ op_fault_action_t::fail };
    op_predicate_t    predicate{};
    cy_err_t          error{ CY_ERR_MEDIA };
    cy_us_t           delay{ 0 };
};

struct op_fault_plan_t final
{
    std::vector<op_fault_rule_t> rules{};
};

struct op_fault_effect_t final
{
    bool     fail{ false };
    cy_err_t error{ CY_OK };
    cy_us_t  spin_delay{ 0 };
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

void op_fault_plan_add_fail(op_fault_plan_t& plan, cy_err_t error, op_predicate_t predicate);
void op_fault_plan_add_spin_delay(op_fault_plan_t& plan, cy_us_t delay, op_predicate_t predicate);

op_fault_effect_t op_fault_plan_evaluate(const op_fault_plan_t& plan, const op_info_t& op);

op_predicate_t op_fault_predicate_all();
op_predicate_t op_fault_predicate_none();
op_predicate_t op_fault_predicate_node(std::size_t node_index);
op_predicate_t op_fault_predicate_kind(op_kind_t kind);
op_predicate_t op_fault_predicate_subject_id(std::uint32_t subject_id);
op_predicate_t op_fault_predicate_lane_id(std::uint64_t lane_id);
op_predicate_t op_fault_predicate_deadline(cy_us_t min_inclusive, cy_us_t max_inclusive);
op_predicate_t op_fault_predicate_every_nth(std::size_t every_n, std::size_t phase = 0U);
op_predicate_t op_fault_predicate_not(op_predicate_t predicate);
op_predicate_t op_fault_predicate_all_of(std::vector<op_predicate_t> predicates);
op_predicate_t op_fault_predicate_any_of(std::vector<op_predicate_t> predicates);

} // namespace e2e
