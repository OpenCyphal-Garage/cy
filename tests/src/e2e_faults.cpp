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

frame_predicate_t fault_predicate_all()
{
    return [](const frame_info_t&) { return true; };
}

frame_predicate_t fault_predicate_none()
{
    return [](const frame_info_t&) { return false; };
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

frame_predicate_t fault_predicate_tag(const std::uint64_t tag)
{
    return [tag](const frame_info_t& frame) { return frame.has_tag && (frame.tag == tag); };
}

frame_predicate_t fault_predicate_topic_hash(const std::uint64_t topic_hash)
{
    return [topic_hash](const frame_info_t& frame) { return frame.has_topic_hash && (frame.topic_hash == topic_hash); };
}

frame_predicate_t fault_predicate_subject_id(const std::uint32_t subject_id)
{
    return [subject_id](const frame_info_t& frame) { return frame.subject_id == subject_id; };
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
        return fault_predicate_none();
    }
    const auto counter = std::make_shared<std::size_t>(0U);
    return [counter, every_n, phase](const frame_info_t&) {
        const std::size_t value = *counter;
        *counter                = value + 1U;
        return (value % every_n) == (phase % every_n);
    };
}

frame_predicate_t fault_predicate_not(frame_predicate_t predicate)
{
    return [predicate = std::move(predicate)](const frame_info_t& frame) { return !predicate_match(predicate, frame); };
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

} // namespace e2e
