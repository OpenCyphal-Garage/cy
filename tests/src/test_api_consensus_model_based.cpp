#include <cy_platform.h>
#include <unity.h>
#include "e2e_faults.hpp"
#include "e2e_sim_net.hpp"
#include "e2e_scenario_utils.hpp"
#include "e2e_test_utils.hpp"
#include "message.h"
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <iomanip>
#include <ranges>
#include <sstream>
#include <string>
#include <vector>

namespace {

constexpr cy_us_t step_us                    = 1'000;
constexpr cy_us_t publish_deadline_us        = 250'000;
constexpr cy_us_t topic_discovery_timeout_us = 8'000'000;

struct arrival_sample_t final
{
    std::uint32_t publisher_id{ 0U };
    std::uint64_t sequence{ 0U };
};

struct arrival_capture_t final
{
    std::vector<arrival_sample_t> samples{};
    std::size_t                   malformed{ 0U };
};

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

    e2e::app_payload_t payload{};
    if (!e2e::app_payload_unpack(bytes.data(), size, payload)) {
        capture->malformed++;
        cy_message_refcount_dec(arrival.message.content);
        return;
    }

    capture->samples.push_back(arrival_sample_t{ .publisher_id = payload.publisher_id, .sequence = payload.sequence });
    cy_message_refcount_dec(arrival.message.content);
}

void cleanup_case(e2e::sim_net_t&                     net,
                  cy_us_t&                            now,
                  const std::vector<cy_future_t*>&    subscribers,
                  const std::vector<cy_publisher_t*>& publishers)
{
    e2e::cleanup_case(net, now, {}, subscribers, publishers, step_us, 100'000, 100'000U);
}

void publish_best_effort(cy_publisher_t* const pub,
                         const std::uint32_t   publisher_id,
                         const std::uint64_t   sequence,
                         const cy_us_t         now)
{
    const auto       payload = e2e::app_payload_pack(publisher_id, sequence);
    const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, now + publish_deadline_us, msg));
}

bool wait_until_topics_known(e2e::sim_net_t& net,
                             cy_us_t&        now,
                             const cy_str_t  topic_a,
                             const cy_str_t  topic_b,
                             const cy_us_t   timeout)
{
    const cy_us_t deadline = now + timeout;
    while (now <= deadline) {
        const bool known = (cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_a), topic_a) != nullptr) &&
                           (cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_a), topic_b) != nullptr) &&
                           (cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_b), topic_a) != nullptr) &&
                           (cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_b), topic_b) != nullptr);
        if (known) {
            return true;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
    }
    return false;
}

std::size_t count_by_publisher(const arrival_capture_t& capture, const std::uint32_t publisher_id)
{
    const auto count = std::ranges::count_if(
      capture.samples, [publisher_id](const arrival_sample_t& sample) { return sample.publisher_id == publisher_id; });
    return static_cast<std::size_t>(count);
}

std::string make_topic_name(const std::string& prefix, const std::uint64_t hash)
{
    std::ostringstream out;
    out << prefix << '#' << std::hex << std::nouppercase << std::setfill('0') << std::setw(16) << hash;
    return out.str();
}

void configure_faults(e2e::fault_plan_t& faults, const std::uint64_t seed)
{
    const auto every_delay = static_cast<std::size_t>(2U + (seed % 5U));
    const auto phase_delay = static_cast<std::size_t>((seed / 5U) % every_delay);
    const auto delay_us    = static_cast<cy_us_t>(3000U + ((seed % 7U) * 2000U));

    const auto every_dup = static_cast<std::size_t>(5U + (seed % 5U));
    const auto phase_dup = static_cast<std::size_t>((seed / 13U) % every_dup);

    const auto every_drop = static_cast<std::size_t>(19U + (seed % 7U));
    const auto phase_drop = static_cast<std::size_t>((seed / 17U) % every_drop);

    e2e::fault_plan_add_delay(
      faults,
      delay_us,
      e2e::fault_predicate_all_of(
        { e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(0U), e2e::fault_predicate_header_type(7U) }),
          e2e::fault_predicate_every_nth(every_delay, phase_delay) }));

    e2e::fault_plan_add_duplicate(
      faults,
      1U,
      e2e::fault_predicate_all_of(
        { e2e::fault_predicate_header_type(7U), e2e::fault_predicate_every_nth(every_dup, phase_dup) }));

    e2e::fault_plan_add_drop(
      faults,
      e2e::fault_predicate_all_of(
        { e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(0U), e2e::fault_predicate_header_type(7U) }),
          e2e::fault_predicate_every_nth(every_drop, phase_drop) }));
}

void run_seed_case(const std::uint64_t seed)
{
    constexpr std::uint32_t pub_id_a = 4301U;
    constexpr std::uint32_t pub_id_b = 4302U;

    const std::uint64_t hash_a = UINT64_C(0x1000000000100000) + (seed * UINT64_C(0x1000));
    const std::uint64_t hash_b = hash_a + static_cast<std::uint64_t>(CY_SUBJECT_ID_MODULUS_17bit);

    const std::string topic_a = make_topic_name("e2e/model/collide/a/", hash_a);
    const std::string topic_b = make_topic_name("e2e/model/collide/b/", hash_b);
    const cy_str_t    topic_a_name{ .len = topic_a.size(), .str = topic_a.c_str() };
    const cy_str_t    topic_b_name{ .len = topic_b.size(), .str = topic_b.c_str() };

    e2e::fault_plan_t faults{};
    configure_faults(faults, seed);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), seed));
    e2e::sim_net_faults_set(net, &faults);

    arrival_capture_t capture_a{};
    arrival_capture_t capture_b{};

    cy_future_t* const sub_a = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/model/collide/>"), 64U);
    cy_future_t* const sub_b = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str("e2e/model/collide/>"), 64U);
    TEST_ASSERT_NOT_NULL(sub_a);
    TEST_ASSERT_NOT_NULL(sub_b);

    cy_user_context_t ctx_a = CY_USER_CONTEXT_EMPTY;
    ctx_a.ptr[0]            = &capture_a;
    cy_future_context_set(sub_a, ctx_a);
    cy_future_callback_set(sub_a, on_arrival_capture);

    cy_user_context_t ctx_b = CY_USER_CONTEXT_EMPTY;
    ctx_b.ptr[0]            = &capture_b;
    cy_future_context_set(sub_b, ctx_b);
    cy_future_callback_set(sub_b, on_arrival_capture);

    cy_publisher_t* const pub_a = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), topic_a_name);
    cy_publisher_t* const pub_b = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_b), topic_b_name);
    TEST_ASSERT_NOT_NULL(pub_a);
    TEST_ASSERT_NOT_NULL(pub_b);

    cy_us_t now = 0;
    TEST_ASSERT_TRUE(wait_until_topics_known(net, now, topic_a_name, topic_b_name, topic_discovery_timeout_us));

    for (std::uint64_t seq = 1U; seq <= 32U; seq++) {
        e2e::set_now(net, now);
        publish_best_effort(pub_a, pub_id_a, seq, now);
        publish_best_effort(pub_b, pub_id_b, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 8'000;
    }
    e2e::drive_for(net, now, 450'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, capture_a.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, capture_b.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture_a, pub_id_b) >= 2U);
    TEST_ASSERT_TRUE(count_by_publisher(capture_b, pub_id_a) >= 2U);

    cleanup_case(net, now, { sub_a, sub_b }, { pub_a, pub_b });
}

void test_api_consensus_model_seed_sweep_collisions_and_faults()
{
    static constexpr std::array<std::uint64_t, 8> seeds = {
        UINT64_C(0x5101), UINT64_C(0x5102), UINT64_C(0x5103), UINT64_C(0x5104),
        UINT64_C(0x5105), UINT64_C(0x5106), UINT64_C(0x5107), UINT64_C(0x5108),
    };

    for (const std::uint64_t seed : seeds) {
        run_seed_case(seed);
    }
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
    RUN_TEST(test_api_consensus_model_seed_sweep_collisions_and_faults);
    return UNITY_END();
}
