#include "e2e_faults.hpp"
#include <algorithm>
#include <limits>
#include <memory>
#include <utility>

namespace e2e {
namespace {

bool predicate_match(const frame_predicate_t& predicate, const frame_info_t& frame)
{
    return predicate ? predicate(frame) : true;
}

bool predicate_match(const op_predicate_t& predicate, const op_info_t& op) { return predicate ? predicate(op) : true; }

cy_us_t saturating_add_delay(const cy_us_t a, const cy_us_t b)
{
    if (b <= 0) {
        return a;
    }
    const cy_us_t max_value = std::numeric_limits<cy_us_t>::max();
    if (a > (max_value - b)) {
        return max_value;
    }
    return a + b;
}

std::size_t saturating_add_duplicates(const std::size_t a, const std::size_t b)
{
    const std::size_t max_value = std::numeric_limits<std::size_t>::max();
    if (a > (max_value - b)) {
        return max_value;
    }
    return a + b;
}

cy_err_t normalize_error(const cy_err_t error) { return (error == CY_OK) ? CY_ERR_MEDIA : error; }

} // namespace

void fault_plan_add_drop(fault_plan_t& plan, frame_predicate_t predicate)
{
    fault_rule_t rule{};
    rule.action    = fault_action_t::drop;
    rule.predicate = std::move(predicate);
    plan.rules.push_back(std::move(rule));
}

void fault_plan_add_delay(fault_plan_t& plan, const cy_us_t delay, frame_predicate_t predicate)
{
    fault_rule_t rule{};
    rule.action    = fault_action_t::delay;
    rule.predicate = std::move(predicate);
    rule.delay     = (delay > 0) ? delay : 0;
    plan.rules.push_back(std::move(rule));
}

void fault_plan_add_duplicate(fault_plan_t& plan, const std::size_t duplicates, frame_predicate_t predicate)
{
    fault_rule_t rule{};
    rule.action     = fault_action_t::duplicate;
    rule.predicate  = std::move(predicate);
    rule.duplicates = duplicates;
    plan.rules.push_back(std::move(rule));
}

fault_effect_t fault_plan_evaluate(const fault_plan_t& plan, const frame_info_t& frame)
{
    fault_effect_t out{};
    for (const fault_rule_t& rule : plan.rules) {
        if (!predicate_match(rule.predicate, frame)) {
            continue;
        }
        switch (rule.action) {
            case fault_action_t::drop:
                out.drop = true;
                break;
            case fault_action_t::delay:
                out.delay = saturating_add_delay(out.delay, rule.delay);
                break;
            case fault_action_t::duplicate:
                out.duplicates = saturating_add_duplicates(out.duplicates, rule.duplicates);
                break;
        }
    }
    return out;
}

frame_predicate_t fault_predicate_direction(const std::size_t source, const std::size_t destination)
{
    return [source, destination](const frame_info_t& frame) {
        return (frame.source == source) && (frame.destination == destination);
    };
}

frame_predicate_t fault_predicate_header_type(const std::uint8_t header_type)
{
    return [header_type](const frame_info_t& frame) { return frame.header_type == header_type; };
}

frame_predicate_t fault_predicate_send_time(const cy_us_t min_inclusive, const cy_us_t max_inclusive)
{
    return [min_inclusive, max_inclusive](const frame_info_t& frame) {
        return (frame.send_time >= min_inclusive) && (frame.send_time <= max_inclusive);
    };
}

frame_predicate_t fault_predicate_every_nth(const std::size_t every_n, const std::size_t phase)
{
    if (every_n == 0U) {
        return [](const frame_info_t&) { return false; };
    }
    const auto counter = std::make_shared<std::size_t>(0U);
    return [counter, every_n, phase](const frame_info_t&) {
        const std::size_t value = *counter;
        *counter                = value + 1U;
        return (value % every_n) == (phase % every_n);
    };
}

frame_predicate_t fault_predicate_all_of(std::vector<frame_predicate_t> predicates)
{
    return [predicates = std::move(predicates)](const frame_info_t& frame) {
        return std::ranges::all_of(
          predicates, [&frame](const frame_predicate_t& predicate) { return predicate_match(predicate, frame); });
    };
}

frame_predicate_t fault_predicate_any_of(std::vector<frame_predicate_t> predicates)
{
    return [predicates = std::move(predicates)](const frame_info_t& frame) {
        return std::ranges::any_of(
          predicates, [&frame](const frame_predicate_t& predicate) { return predicate_match(predicate, frame); });
    };
}

void op_fault_plan_add_fail(op_fault_plan_t& plan, const cy_err_t error, op_predicate_t predicate)
{
    op_fault_rule_t rule{};
    rule.action    = op_fault_action_t::fail;
    rule.predicate = std::move(predicate);
    rule.error     = normalize_error(error);
    plan.rules.push_back(std::move(rule));
}

op_fault_effect_t op_fault_plan_evaluate(const op_fault_plan_t& plan, const op_info_t& op)
{
    op_fault_effect_t out{};
    for (const op_fault_rule_t& rule : plan.rules) {
        if (!predicate_match(rule.predicate, op)) {
            continue;
        }
        switch (rule.action) {
            case op_fault_action_t::fail:
                out.fail  = true;
                out.error = normalize_error(rule.error);
                break;
        }
    }
    if (out.fail && (out.error == CY_OK)) {
        out.error = CY_ERR_MEDIA;
    }
    return out;
}

op_predicate_t op_fault_predicate_all()
{
    return [](const op_info_t&) { return true; };
}

op_predicate_t op_fault_predicate_node(const std::size_t node_index)
{
    return [node_index](const op_info_t& op) { return op.node_index == node_index; };
}

op_predicate_t op_fault_predicate_kind(const op_kind_t kind)
{
    return [kind](const op_info_t& op) { return op.kind == kind; };
}

op_predicate_t op_fault_predicate_deadline(const cy_us_t min_inclusive, const cy_us_t max_inclusive)
{
    return [min_inclusive, max_inclusive](const op_info_t& op) {
        return (op.deadline >= min_inclusive) && (op.deadline <= max_inclusive);
    };
}

op_predicate_t op_fault_predicate_every_nth(const std::size_t every_n, const std::size_t phase)
{
    if (every_n == 0U) {
        return [](const op_info_t&) { return false; };
    }
    const auto counter = std::make_shared<std::size_t>(0U);
    return [counter, every_n, phase](const op_info_t&) {
        const std::size_t value = *counter;
        *counter                = value + 1U;
        return (value % every_n) == (phase % every_n);
    };
}

op_predicate_t op_fault_predicate_all_of(std::vector<op_predicate_t> predicates)
{
    return [predicates = std::move(predicates)](const op_info_t& op) {
        return std::ranges::all_of(predicates,
                                   [&op](const op_predicate_t& predicate) { return predicate_match(predicate, op); });
    };
}

} // namespace e2e
