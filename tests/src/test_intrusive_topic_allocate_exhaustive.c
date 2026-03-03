#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
#include <limits.h>
#include <stdio.h>
#include <string.h>

typedef struct
{
    cy_subject_writer_t base;
} test_subject_writer_t;

typedef struct
{
    cy_subject_reader_t base;
    size_t              extent;
} test_subject_reader_t;

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    guarded_heap_t       heap;
    cy_t*                cy;
    cy_us_t              now;

    bool fail_subject_writer_new;
    bool fail_subject_reader_new;

    size_t subject_reader_destroy_count;
    size_t subject_writer_destroy_count;
    size_t async_error_count;

    uint64_t random_state;
} fixture_t;

typedef struct
{
    uint64_t    hash;
    uint32_t    evictions;
    int_fast8_t lage;
} model_topic_t;

typedef struct
{
    model_topic_t topics[8];
    bool          in_index[8];
    size_t        count;
    uint32_t      subject_id_modulus;
} model_state_t;

typedef struct
{
    size_t      topic_count;
    size_t      hash_family;
    uint64_t    hash_nonce;
    uint32_t    initial_evictions[8];
    int_fast8_t lages[8];
    size_t      insertion_order[8];
    size_t      target_index;
    uint32_t    requested_evictions;
} case_spec_t;

static fixture_t* fixture_from(cy_platform_t* const platform) { return (fixture_t*)platform; }

static cy_us_t fixture_now(cy_platform_t* const platform) { return fixture_from(platform)->now; }

static void* fixture_realloc(cy_platform_t* const platform, void* const ptr, const size_t size)
{
    fixture_t* const self = fixture_from(platform);
    return guarded_heap_realloc(&self->heap, ptr, size);
}

static uint64_t fixture_random(cy_platform_t* const platform)
{
    fixture_t* const self = fixture_from(platform);
    self->random_state    = (self->random_state * UINT64_C(6364136223846793005)) + UINT64_C(1);
    return self->random_state;
}

static cy_subject_writer_t* fixture_subject_writer_new(cy_platform_t* const platform, const uint32_t subject_id)
{
    fixture_t* const self = fixture_from(platform);
    if (self->fail_subject_writer_new) {
        return NULL;
    }
    test_subject_writer_t* const out = (test_subject_writer_t*)guarded_heap_alloc(&self->heap, sizeof(*out));
    if (out != NULL) {
        out->base.subject_id = subject_id;
    }
    return (out != NULL) ? &out->base : NULL;
}

static void fixture_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    fixture_t* const self = fixture_from(platform);
    self->subject_writer_destroy_count++;
    guarded_heap_free(&self->heap, writer);
}

static cy_err_t fixture_subject_writer_send(cy_platform_t* const       platform,
                                            cy_subject_writer_t* const writer,
                                            const cy_us_t              deadline,
                                            const cy_prio_t            priority,
                                            const cy_bytes_t           message)
{
    (void)platform;
    (void)writer;
    (void)deadline;
    (void)priority;
    (void)message;
    return CY_OK;
}

static cy_subject_reader_t* fixture_subject_reader_new(cy_platform_t* const platform,
                                                       const uint32_t       subject_id,
                                                       const size_t         extent)
{
    fixture_t* const self = fixture_from(platform);
    if (self->fail_subject_reader_new) {
        return NULL;
    }
    test_subject_reader_t* const out = (test_subject_reader_t*)guarded_heap_alloc(&self->heap, sizeof(*out));
    if (out != NULL) {
        out->base.subject_id = subject_id;
        out->extent          = extent;
    }
    return (out != NULL) ? &out->base : NULL;
}

static void fixture_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    fixture_t* const self = fixture_from(platform);
    self->subject_reader_destroy_count++;
    guarded_heap_free(&self->heap, reader);
}

static cy_err_t fixture_p2p_send(cy_platform_t* const   platform,
                                 const cy_lane_t* const lane,
                                 const cy_us_t          deadline,
                                 const cy_bytes_t       message)
{
    (void)platform;
    (void)lane;
    (void)deadline;
    (void)message;
    return CY_OK;
}

static void fixture_p2p_extent_set(cy_platform_t* const platform, const size_t extent)
{
    (void)platform;
    (void)extent;
}

static cy_err_t fixture_spin(cy_platform_t* const platform, const cy_us_t deadline)
{
    (void)platform;
    (void)deadline;
    return CY_OK;
}

static void fixture_on_async_error(cy_t* const cy, cy_topic_t* const topic, const cy_err_t error, const uint16_t line)
{
    (void)topic;
    (void)error;
    (void)line;
    fixture_t* const self = fixture_from(cy->platform);
    self->async_error_count++;
}

static void fixture_init(fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->heap, UINT64_C(0xD00DFEEDBADC0FFE));

    self->platform.vtable               = &self->vtable;
    self->platform.subject_id_modulus   = (uint32_t)CY_SUBJECT_ID_MODULUS_17bit;
    self->vtable.subject_writer_new     = fixture_subject_writer_new;
    self->vtable.subject_writer_destroy = fixture_subject_writer_destroy;
    self->vtable.subject_writer_send    = fixture_subject_writer_send;
    self->vtable.subject_reader_new     = fixture_subject_reader_new;
    self->vtable.subject_reader_destroy = fixture_subject_reader_destroy;
    self->vtable.p2p_send               = fixture_p2p_send;
    self->vtable.p2p_extent_set         = fixture_p2p_extent_set;
    self->vtable.spin                   = fixture_spin;
    self->vtable.now                    = fixture_now;
    self->vtable.realloc                = fixture_realloc;
    self->vtable.random                 = fixture_random;
    self->random_state                  = UINT64_C(0xA5A5A5A55A5A5A5A);
    self->now                           = (cy_us_t)(1000 * MEGA);

    self->cy = cy_new(&self->platform);
    TEST_ASSERT_NOT_NULL(self->cy);
    cy_async_error_handler_set(self->cy, fixture_on_async_error);
}

static void fixture_deinit(fixture_t* const self)
{
    if (self->cy != NULL) {
        TEST_ASSERT_TRUE(wkv_is_empty(&self->cy->subscribers_by_name));
        TEST_ASSERT_TRUE(wkv_is_empty(&self->cy->subscribers_by_pattern));
        TEST_ASSERT_NULL(self->cy->response_futures_by_tag);
        for (cy_topic_t* topic = cy_topic_iter_first(self->cy); topic != NULL; topic = cy_topic_iter_next(topic)) {
            TEST_ASSERT_EQUAL_UINT32(0U, topic->pub_count);
            TEST_ASSERT_NULL(topic->pub_futures_by_tag);
            TEST_ASSERT_NULL(topic->couplings);
        }
        cy_destroy(self->cy);
        self->cy = NULL;
    }
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&self->heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&self->heap));
}

static cy_topic_t* fixture_make_topic(fixture_t* const  self,
                                      const char* const name,
                                      const uint64_t    hash,
                                      const uint32_t    evictions,
                                      const int_fast8_t lage)
{
    cy_topic_t*    out = NULL;
    const cy_err_t er  = topic_new(self->cy, &out, cy_str(name), hash, evictions, lage);
    TEST_ASSERT_EQUAL_INT(CY_OK, er);
    TEST_ASSERT_NOT_NULL(out);
    return out;
}

static uint64_t hash_for_case(const uint32_t modulus,
                              const size_t   family,
                              const size_t   logical_index,
                              const uint64_t nonce)
{
    const uint64_t base = UINT64_C(0x1000000000100000) + (nonce * UINT64_C(0x100000));
    switch (family) {
        case 0U:
            return base + ((uint64_t)logical_index * (uint64_t)modulus);
        case 1U:
            return base + ((uint64_t)logical_index * (uint64_t)modulus) +
                   ((uint64_t)(logical_index + 1U) * UINT64_C(257));
        default:
            return base + ((uint64_t)(logical_index / 2U) * (uint64_t)modulus) +
                   ((logical_index & 1U) ? UINT64_C(113) : 0U);
    }
}

static void build_age_profile(const size_t profile, const size_t topic_count, int_fast8_t out_lages[8])
{
    for (size_t i = 0U; i < topic_count; i++) {
        switch (profile) {
            case 0U:
                out_lages[i] = 3;
                break;
            case 1U:
                out_lages[i] = (int_fast8_t)i;
                break;
            case 2U:
                out_lages[i] = (int_fast8_t)(topic_count - 1U - i);
                break;
            default:
                out_lages[i] = (int_fast8_t)(1U + (i / 2U));
                break;
        }
    }
}

static bool model_left_wins(const model_state_t* const self, const size_t left, const size_t right)
{
    const int_fast8_t l_lage = self->topics[left].lage;
    const int_fast8_t r_lage = self->topics[right].lage;
    if (l_lage != r_lage) {
        return l_lage > r_lage;
    }
    return self->topics[left].hash < self->topics[right].hash;
}

static int model_find_occupant(const model_state_t* const self, const uint32_t sid, const int exclude)
{
    for (size_t i = 0U; i < self->count; i++) {
        if (!self->in_index[i] || ((int)i == exclude)) {
            continue;
        }
        const uint32_t this_sid =
          topic_subject_id_impl(self->topics[i].hash, self->topics[i].evictions, self->subject_id_modulus);
        if (this_sid == sid) {
            return (int)i;
        }
    }
    return -1;
}

static void model_allocate(model_state_t* const self, const size_t topic_index, const uint32_t requested_evictions)
{
    size_t   current = topic_index;
    uint32_t wanted  = requested_evictions;

    for (size_t step = 0U; step < 2048U; step++) {
        self->in_index[current] = false; // Mirrors cavl2_remove_if() on every recursion level.

        const uint32_t new_sid = topic_subject_id_impl(self->topics[current].hash, wanted, self->subject_id_modulus);
        const int      that    = model_find_occupant(self, new_sid, (int)current);
        const bool     victory = (that < 0) || model_left_wins(self, current, (size_t)that);

        if (victory) {
            if (that >= 0) {
                self->in_index[(size_t)that] = false;
            }
            self->topics[current].evictions = wanted;
            self->in_index[current]         = true;

            if (that >= 0) {
                current = (size_t)that;
                wanted  = self->topics[current].evictions + 1U;
                continue;
            }
            return;
        }

        wanted++;
    }

    TEST_FAIL_MESSAGE("Model allocator exceeded recursion-equivalent step budget");
}

static void assert_runtime_subject_index_unique(cy_topic_t* const topics[8],
                                                const size_t      topic_count,
                                                const char* const context)
{
    for (size_t i = 0U; i < topic_count; i++) {
        TEST_ASSERT_FALSE_MESSAGE(is_pinned(topics[i]->hash), context);
        const uint32_t sid_i = topic_subject_id(topics[i]);
        for (size_t j = i + 1U; j < topic_count; j++) {
            const uint32_t sid_j = topic_subject_id(topics[j]);
            TEST_ASSERT_TRUE_MESSAGE(sid_i != sid_j, context);
        }
    }
}

static void assert_runtime_matches_model(fixture_t* const           fix,
                                         cy_topic_t* const          topics[8],
                                         const model_state_t* const model,
                                         const char* const          context)
{
    assert_runtime_subject_index_unique(topics, model->count, context);

    for (size_t i = 0U; i < model->count; i++) {
        const uint32_t expected_ev = model->topics[i].evictions;
        const uint32_t expected_sid =
          topic_subject_id_impl(model->topics[i].hash, expected_ev, model->subject_id_modulus);

        TEST_ASSERT_EQUAL_UINT32_MESSAGE(expected_ev, topics[i]->evictions, context);
        TEST_ASSERT_EQUAL_UINT32_MESSAGE(expected_sid, topic_subject_id(topics[i]), context);

        cy_topic_t* const by_sid = topic_find_by_subject_id(fix->cy, expected_sid);
        TEST_ASSERT_TRUE_MESSAGE(by_sid == topics[i], context);
    }
}

static uint64_t prng_next(uint64_t* const state)
{
    *state = (*state * UINT64_C(6364136223846793005)) + UINT64_C(1);
    return *state;
}

static size_t rand_bounded(uint64_t* const state, const size_t bound)
{
    if (bound == 0U) {
        return 0U;
    }
    return (size_t)(prng_next(state) % bound);
}

static void shuffle_indices(uint64_t* const state, size_t* const out, const size_t n)
{
    for (size_t i = 0U; i < n; i++) {
        out[i] = i;
    }
    for (size_t i = n; i > 1U; i--) {
        const size_t j   = rand_bounded(state, i);
        const size_t tmp = out[i - 1U];
        out[i - 1U]      = out[j];
        out[j]           = tmp;
    }
}

static size_t pow_u(const size_t base, const size_t exp)
{
    size_t out = 1U;
    for (size_t i = 0U; i < exp; i++) {
        out *= base;
    }
    return out;
}

static size_t fill_high_eviction_domain(const uint32_t modulus, uint32_t out[6])
{
    out[0] = 0U;
    out[1] = modulus / 2U;
    out[2] = (modulus / 2U) + 1U;
    out[3] = modulus - 1U;
    out[4] = modulus;
    out[5] = UINT32_MAX - 4096U;
    return 6U;
}

static void run_topic_allocate_case(const case_spec_t* const spec, const char* const context)
{
    fixture_t fix;
    fixture_init(&fix);

    const uint32_t modulus = fix.cy->platform->subject_id_modulus;

    uint64_t hashes[8] = { 0 };
    for (size_t i = 0U; i < spec->topic_count; i++) {
        hashes[i] = hash_for_case(modulus, spec->hash_family, i, spec->hash_nonce);
    }

    cy_topic_t* topics[8] = { NULL };
    for (size_t order_pos = 0U; order_pos < spec->topic_count; order_pos++) {
        const size_t idx = spec->insertion_order[order_pos];
        char         name[40];
        (void)snprintf(name, sizeof(name), "alloc/exh/%zu", idx);
        topics[idx] = fixture_make_topic(&fix, name, hashes[idx], spec->initial_evictions[idx], spec->lages[idx]);
    }

    for (size_t i = 0U; i < spec->topic_count; i++) {
        TEST_ASSERT_NOT_NULL_MESSAGE(topics[i], context);
    }

    model_state_t model;
    memset(&model, 0, sizeof(model));
    model.count              = spec->topic_count;
    model.subject_id_modulus = modulus;
    for (size_t i = 0U; i < model.count; i++) {
        model.topics[i].hash      = topics[i]->hash;
        model.topics[i].evictions = topics[i]->evictions;
        model.topics[i].lage      = topic_lage(topics[i], fix.now);
        model.in_index[i]         = !is_pinned(topics[i]->hash);
    }

    model_allocate(&model, spec->target_index, spec->requested_evictions);

    topic_allocate(topics[spec->target_index], spec->requested_evictions, fix.now);

    assert_runtime_matches_model(&fix, topics, &model, context);

    fixture_deinit(&fix);
}

static void test_topic_allocate_bounded_exhaustive_oracle_equivalence(void)
{
    size_t case_count = 0U;

    for (size_t topic_count = 1U; topic_count <= 3U; topic_count++) {
        for (size_t family = 0U; family < 2U; family++) {
            for (size_t age_profile = 0U; age_profile < 4U; age_profile++) {
                const size_t total_ev_codes = pow_u(3U, topic_count);
                for (size_t ev_code = 0U; ev_code < total_ev_codes; ev_code++) {
                    for (size_t target = 0U; target < topic_count; target++) {
                        for (uint32_t requested = 0U; requested <= 3U; requested++) {
                            case_spec_t spec;
                            memset(&spec, 0, sizeof(spec));
                            spec.topic_count         = topic_count;
                            spec.hash_family         = family;
                            spec.hash_nonce          = 0U;
                            spec.target_index        = target;
                            spec.requested_evictions = requested;

                            build_age_profile(age_profile, topic_count, spec.lages);
                            for (size_t i = 0U; i < topic_count; i++) {
                                spec.insertion_order[i] = i;
                            }

                            size_t tmp = ev_code;
                            for (size_t i = 0U; i < topic_count; i++) {
                                spec.initial_evictions[i] = (uint32_t)(tmp % 3U);
                                tmp /= 3U;
                            }

                            char context[160];
                            (void)snprintf(context,
                                           sizeof(context),
                                           "exh #%zu n=%zu fam=%zu age=%zu ev=%zu target=%zu req=%u",
                                           case_count,
                                           topic_count,
                                           family,
                                           age_profile,
                                           ev_code,
                                           target,
                                           requested);
                            run_topic_allocate_case(&spec, context);
                            case_count++;
                        }
                    }
                }
            }
        }
    }

    printf("topic_allocate exhaustive bounded cases: %zu\n", case_count);
}

static void test_topic_allocate_seeded_probabilistic_oracle_equivalence(void)
{
    static const uint64_t seeds[] = {
        UINT64_C(0xA001), UINT64_C(0xA002), UINT64_C(0xA003), UINT64_C(0xA004), UINT64_C(0xA005), UINT64_C(0xA006),
        UINT64_C(0xA007), UINT64_C(0xA008), UINT64_C(0xA009), UINT64_C(0xA00A), UINT64_C(0xA00B), UINT64_C(0xA00C),
        UINT64_C(0xA00D), UINT64_C(0xA00E), UINT64_C(0xA00F), UINT64_C(0xA010),
    };

    size_t case_count = 0U;
    for (size_t seed_index = 0U; seed_index < (sizeof(seeds) / sizeof(seeds[0])); seed_index++) {
        uint64_t state = seeds[seed_index];

        for (size_t scenario = 0U; scenario < 64U; scenario++) {
            case_spec_t spec;
            memset(&spec, 0, sizeof(spec));

            spec.topic_count = 1U + rand_bounded(&state, 8U);
            spec.hash_family = rand_bounded(&state, 3U);
            spec.hash_nonce  = seeds[seed_index] ^ (uint64_t)scenario;

            for (size_t i = 0U; i < spec.topic_count; i++) {
                spec.initial_evictions[i] = (uint32_t)rand_bounded(&state, 8U);
                spec.lages[i]             = (int_fast8_t)rand_bounded(&state, 9U);
            }

            shuffle_indices(&state, spec.insertion_order, spec.topic_count);

            spec.target_index        = rand_bounded(&state, spec.topic_count);
            spec.requested_evictions = (uint32_t)rand_bounded(&state, 16U);

            char context[128];
            (void)snprintf(context,
                           sizeof(context),
                           "seed=%llu scenario=%zu n=%zu target=%zu req=%u",
                           (unsigned long long)seeds[seed_index],
                           scenario,
                           spec.topic_count,
                           spec.target_index,
                           spec.requested_evictions);

            run_topic_allocate_case(&spec, context);
            case_count++;
        }
    }

    printf("topic_allocate probabilistic seeded cases: %zu\n", case_count);
}

static void test_topic_allocate_high_eviction_bounded_exhaustive_oracle_equivalence(void)
{
    static const uint32_t modulus = (uint32_t)CY_SUBJECT_ID_MODULUS_17bit;
    uint32_t              ev_domain[6];
    const size_t          ev_domain_count = fill_high_eviction_domain(modulus, ev_domain);
    size_t                case_count      = 0U;

    for (size_t topic_count = 1U; topic_count <= 3U; topic_count++) {
        for (size_t family = 0U; family < 2U; family++) {
            for (size_t age_profile = 0U; age_profile < 2U; age_profile++) {
                const size_t total_ev_codes = pow_u(ev_domain_count, topic_count);
                for (size_t ev_code = 0U; ev_code < total_ev_codes; ev_code++) {
                    for (size_t target = 0U; target < topic_count; target++) {
                        for (size_t requested_index = 0U; requested_index < ev_domain_count; requested_index++) {
                            case_spec_t spec;
                            memset(&spec, 0, sizeof(spec));
                            spec.topic_count         = topic_count;
                            spec.hash_family         = family;
                            spec.hash_nonce          = UINT64_C(0xBEEF0000) + (uint64_t)age_profile;
                            spec.target_index        = target;
                            spec.requested_evictions = ev_domain[requested_index];

                            build_age_profile(age_profile, topic_count, spec.lages);
                            for (size_t i = 0U; i < topic_count; i++) {
                                spec.insertion_order[i] = i;
                            }

                            size_t tmp = ev_code;
                            for (size_t i = 0U; i < topic_count; i++) {
                                spec.initial_evictions[i] = ev_domain[tmp % ev_domain_count];
                                tmp /= ev_domain_count;
                            }

                            char context[224];
                            (void)snprintf(context,
                                           sizeof(context),
                                           "high-ev #%zu n=%zu fam=%zu age=%zu code=%zu target=%zu req_idx=%zu",
                                           case_count,
                                           topic_count,
                                           family,
                                           age_profile,
                                           ev_code,
                                           target,
                                           requested_index);
                            run_topic_allocate_case(&spec, context);
                            case_count++;
                        }
                    }
                }
            }
        }
    }

    printf("topic_allocate high-eviction exhaustive bounded cases: %zu\n", case_count);
}

static void test_topic_allocate_same_subject_id_reallocation_exhaustive(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const uint32_t    modulus = fix.cy->platform->subject_id_modulus;
    const uint64_t    hash    = UINT64_C(0x1000000000300000);
    cy_topic_t* const topic   = fixture_make_topic(&fix, "alloc/exh/same-subject", hash, 0U, LAGE_MIN);
    TEST_ASSERT_NOT_NULL(topic);

    for (uint32_t evictions = 0U; evictions < modulus; evictions++) {
        const uint32_t mirror = (evictions == 0U) ? 0U : (modulus - evictions);

        topic_allocate(topic, evictions, fix.now);
        const uint32_t sid_before = topic_subject_id(topic);
        topic_allocate(topic, mirror, fix.now);
        const uint32_t sid_after = topic_subject_id(topic);

        TEST_ASSERT_EQUAL_UINT32(sid_before, sid_after);
        TEST_ASSERT_EQUAL_UINT32(mirror, topic->evictions);
        TEST_ASSERT_TRUE(topic_find_by_subject_id(fix.cy, sid_after) == topic);
    }

    fixture_deinit(&fix);
}

static void test_topic_allocate_same_subject_id_reallocation_near_uint32_max_exhaustive(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const uint32_t    modulus = fix.cy->platform->subject_id_modulus;
    const uint64_t    hash  = UINT32_MAX; // Keep hash low enough to avoid uint64 sum overflow at evictions=UINT32_MAX.
    cy_topic_t* const topic = fixture_make_topic(&fix, "alloc/exh/same-subject-near-max", hash, 0U, LAGE_MIN);
    TEST_ASSERT_NOT_NULL(topic);

    for (uint32_t i = 0U; i < 4096U; i++) {
        const uint32_t old_evictions = UINT32_MAX - i;
        const uint32_t residue       = old_evictions % modulus;
        const uint32_t mirror        = (residue == 0U) ? 0U : (modulus - residue);

        topic_allocate(topic, old_evictions, fix.now);
        const uint32_t sid_old = topic_subject_id(topic);

        topic_allocate(topic, mirror, fix.now);
        const uint32_t sid_mirror = topic_subject_id(topic);

        TEST_ASSERT_EQUAL_UINT32(sid_old, sid_mirror);
        TEST_ASSERT_EQUAL_UINT32(mirror, topic->evictions);
        TEST_ASSERT_TRUE(topic_find_by_subject_id(fix.cy, sid_mirror) == topic);

        topic_allocate(topic, old_evictions, fix.now);
        TEST_ASSERT_EQUAL_UINT32(sid_old, topic_subject_id(topic));
    }

    fixture_deinit(&fix);
}

static void test_topic_allocate_displacement_transfers_writer_handle(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const uint64_t p    = (uint64_t)fix.cy->platform->subject_id_modulus;
    const uint64_t base = UINT64_C(0x1000000000200000);

    cy_topic_t* const winner = fixture_make_topic(&fix, "alloc/transfer/winner", base, 0U, 6);
    cy_topic_t* const loser  = fixture_make_topic(&fix, "alloc/transfer/loser", base + p, 0U, 1);

    loser->pub_writer = fixture_subject_writer_new(&fix.platform, topic_subject_id(loser));
    TEST_ASSERT_NOT_NULL(loser->pub_writer);
    cy_subject_writer_t* const moved = loser->pub_writer;

    topic_allocate(winner, loser->evictions, fix.now);

    TEST_ASSERT_TRUE(winner->pub_writer == moved);
    TEST_ASSERT_NULL(loser->pub_writer);

    fixture_deinit(&fix);
}

static void test_topic_allocate_reader_recovery_after_subject_reader_new_failure(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_subscriber_t* const sub = cy_subscribe(fix.cy, cy_str("alloc/exh/reader/failure"), 64U);
    TEST_ASSERT_NOT_NULL(sub);

    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("alloc/exh/reader/failure"));
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_NOT_NULL(topic->sub_reader);

    fix.fail_subject_reader_new = true;
    topic_allocate(topic, topic->evictions + 1U, fix.now);
    TEST_ASSERT_NULL(topic->sub_reader);
    TEST_ASSERT_TRUE(fix.async_error_count > 0U);

    fix.fail_subject_reader_new = false;
    topic_sync_subject_reader(topic);
    TEST_ASSERT_NOT_NULL(topic->sub_reader);

    cy_unsubscribe(sub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(fix.cy));

    fixture_deinit(&fix);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_topic_allocate_bounded_exhaustive_oracle_equivalence);
    RUN_TEST(test_topic_allocate_seeded_probabilistic_oracle_equivalence);
    RUN_TEST(test_topic_allocate_high_eviction_bounded_exhaustive_oracle_equivalence);
    RUN_TEST(test_topic_allocate_same_subject_id_reallocation_exhaustive);
    RUN_TEST(test_topic_allocate_same_subject_id_reallocation_near_uint32_max_exhaustive);
    RUN_TEST(test_topic_allocate_displacement_transfers_writer_handle);
    RUN_TEST(test_topic_allocate_reader_recovery_after_subject_reader_new_failure);
    return UNITY_END();
}
