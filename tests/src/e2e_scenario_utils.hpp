#pragma once

#include "e2e_sim_net.hpp"
#include "e2e_test_utils.hpp"
#include <algorithm>
#include <cstddef>
#include <vector>
#include <unity.h>

namespace e2e {

inline void set_now(sim_net_t& net, const cy_us_t now)
{
    sim_net_node_now_set(net, sim_node_a, now);
    sim_net_node_now_set(net, sim_node_b, now);
}

inline void set_now_all(sim_net_t& net, const cy_us_t now)
{
    for (std::size_t i = 0U; i < sim_net_node_count(net); i++) {
        sim_net_node_now_set(net, i, now);
    }
}

inline void drive_for(sim_net_t&    net,
                      cy_us_t&      now,
                      const cy_us_t duration,
                      const cy_us_t step_us,
                      const bool    allow_spin_media_failures = false)
{
    const cy_us_t end = now + duration;
    while (now < end) {
        const cy_err_t err = drive_round(net, now, now);
        if (allow_spin_media_failures && (err == CY_ERR_MEDIA)) {
            now += step_us;
            continue;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, err);
        now += step_us;
    }
}

inline void drain_queue(sim_net_t& net, cy_us_t& now, const cy_us_t step_us, const std::size_t guard_limit)
{
    std::size_t guard = 0U;
    while (sim_net_pending_frames(net) > 0U) {
        TEST_ASSERT_EQUAL_INT(CY_OK, drive_round(net, now, now));
        now += step_us;
        guard++;
        TEST_ASSERT_TRUE(guard < guard_limit);
    }
}

inline void drive_for_all(sim_net_t&    net,
                          cy_us_t&      now,
                          const cy_us_t duration,
                          const cy_us_t step_us,
                          const bool    allow_spin_media_failures = false)
{
    const cy_us_t end = now + duration;
    while (now < end) {
        const cy_err_t err = drive_round_all(net, now);
        if (allow_spin_media_failures && (err == CY_ERR_MEDIA)) {
            now += step_us;
            continue;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, err);
        now += step_us;
    }
}

inline void drain_queue_all(sim_net_t& net, cy_us_t& now, const cy_us_t step_us, const std::size_t guard_limit)
{
    std::size_t guard = 0U;
    while (sim_net_pending_frames(net) > 0U) {
        TEST_ASSERT_EQUAL_INT(CY_OK, drive_round_all(net, now));
        now += step_us;
        guard++;
        TEST_ASSERT_TRUE(guard < guard_limit);
    }
}

inline bool wait_all_futures(sim_net_t&                       net,
                             cy_us_t&                         now,
                             const std::vector<cy_future_t*>& futures,
                             const cy_us_t                    timeout,
                             const cy_us_t                    step_us,
                             const bool                       allow_spin_media_failures = false)
{
    const cy_us_t end = now + timeout;
    while (now <= end) {
        bool all_done = true;
        for (cy_future_t* const fut : futures) {
            TEST_ASSERT_NOT_NULL(fut);
            if (!cy_future_done(fut)) {
                all_done = false;
                break;
            }
        }
        if (all_done) {
            return true;
        }

        const cy_err_t err = drive_round(net, now, now);
        if (allow_spin_media_failures && (err == CY_ERR_MEDIA)) {
            now += step_us;
            continue;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, err);
        now += step_us;
    }
    return false;
}

inline void assert_future_error(const std::vector<cy_future_t*>& futures, const cy_err_t expected_error)
{
    for (cy_future_t* const fut : futures) {
        TEST_ASSERT_NOT_NULL(fut);
        TEST_ASSERT_TRUE(cy_future_done(fut));
        TEST_ASSERT_EQUAL_INT(expected_error, cy_future_error(fut));
    }
}

inline void destroy_futures(const std::vector<cy_future_t*>& futures)
{
    for (cy_future_t* const fut : futures) {
        if (fut != nullptr) {
            cy_future_destroy(fut);
        }
    }
}

inline void destroy_subscribers(const std::vector<cy_future_t*>& subscribers) { destroy_futures(subscribers); }

inline void unadvertise_publishers(const std::vector<cy_publisher_t*>& publishers)
{
    for (cy_publisher_t* const pub : publishers) {
        if (pub != nullptr) {
            cy_unadvertise(pub);
        }
    }
}

inline void cleanup_case(sim_net_t&                          net,
                         cy_us_t&                            now,
                         const std::vector<cy_future_t*>&    futures,
                         const std::vector<cy_future_t*>&    subscribers,
                         const std::vector<cy_publisher_t*>& publishers,
                         const cy_us_t                       step_us,
                         const cy_us_t                       settle_us,
                         const std::size_t                   guard_limit)
{
    destroy_futures(futures);
    destroy_subscribers(subscribers);
    drive_for(net, now, settle_us, step_us);

    unadvertise_publishers(publishers);
    drive_for(net, now, settle_us, step_us);

    drain_queue(net, now, step_us, guard_limit);
    assert_quiescent(net);

    sim_net_deinit(net);
    assert_all_node_heaps_clean(net);
    assert_no_live_messages();
}

} // namespace e2e
