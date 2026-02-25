#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
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

    size_t fail_alloc_count;
    size_t fail_alloc_size;

    size_t subject_reader_destroy_count;
    size_t subject_writer_destroy_count;
    size_t async_error_count;
} fixture_t;

static fixture_t* fixture_from(cy_platform_t* const platform) { return (fixture_t*)platform; }

static cy_us_t fixture_now(cy_platform_t* const platform) { return fixture_from(platform)->now; }

static void* fixture_realloc(cy_platform_t* const platform, void* const ptr, const size_t size)
{
    fixture_t* const self = fixture_from(platform);
    if ((ptr == NULL) && (size > 0U) && (self->fail_alloc_count > 0U) &&
        ((self->fail_alloc_size == 0U) || (self->fail_alloc_size == size))) {
        self->fail_alloc_count--;
        return NULL;
    }
    return guarded_heap_realloc(&self->heap, ptr, size);
}

static uint64_t fixture_random(cy_platform_t* const platform)
{
    (void)platform;
    return UINT64_C(0xA5A5A5A55A5A5A5A);
}

static cy_subject_writer_t* fixture_subject_writer_new(cy_platform_t* const platform, const uint32_t subject_id)
{
    fixture_t* const             self = fixture_from(platform);
    test_subject_writer_t* const out  = (test_subject_writer_t*)guarded_heap_alloc(&self->heap, sizeof(*out));
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
    fixture_t* const             self = fixture_from(platform);
    test_subject_reader_t* const out  = (test_subject_reader_t*)guarded_heap_alloc(&self->heap, sizeof(*out));
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
    guarded_heap_init(&self->heap, UINT64_C(0xCAFEBABE12345678));
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
    self->cy                            = cy_new(&self->platform);
    TEST_ASSERT_NOT_NULL(self->cy);
    cy_async_error_handler_set(self->cy, fixture_on_async_error);
}

static void fixture_deinit(fixture_t* const self)
{
    if (self->cy != NULL) {
        TEST_ASSERT_TRUE(wkv_is_empty(&self->cy->subscribers_by_name));
        TEST_ASSERT_TRUE(wkv_is_empty(&self->cy->subscribers_by_pattern));
        TEST_ASSERT_NULL(self->cy->request_futures_by_tag);
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
    cy_topic_t*    topic = NULL;
    const cy_err_t er    = topic_new(self->cy, &topic, cy_str(name), hash, evictions, lage);
    TEST_ASSERT_EQUAL_INT(CY_OK, er);
    TEST_ASSERT_NOT_NULL(topic);
    return topic;
}

static cy_topic_t* fixture_make_explicit_topic(fixture_t* const self, const char* const name, const uint64_t hash)
{
    cy_topic_t* const topic = fixture_make_topic(self, name, hash, 0U, LAGE_MIN);
    topic->pub_count        = 1U;
    topic_sync_implicit(topic);
    return topic;
}

static void assert_subject_index_unique(const cy_t* const cy)
{
    uint32_t   prev  = 0U;
    bool       first = true;
    cy_tree_t* p     = cavl2_min(cy->topics_by_subject_id);
    while (p != NULL) {
        const cy_topic_t* const topic = CAVL2_TO_OWNER(p, cy_topic_t, index_subject_id);
        const uint32_t          sid   = topic_subject_id(topic);
        if (!first) {
            TEST_ASSERT_TRUE(sid > prev);
        }
        prev  = sid;
        first = false;
        p     = cavl2_next_greater(p);
    }
}

typedef struct
{
    cy_future_t base;
    bool        done;
    cy_tree_t** index_owner;
    size_t*     cancel_count;
    size_t*     finalize_count;
} fake_future_t;

static cy_future_status_t fake_future_status(const cy_future_t* const base)
{
    const fake_future_t* const self = (const fake_future_t*)base;
    return self->done ? cy_future_success : cy_future_pending;
}

static size_t fake_future_result(cy_future_t* const base, const size_t storage_size, void* const storage)
{
    (void)base;
    (void)storage_size;
    (void)storage;
    return 0U;
}

static void fake_future_cancel(cy_future_t* const base)
{
    fake_future_t* const self = (fake_future_t*)base;
    self->done                = true;
    if (self->cancel_count != NULL) {
        (*self->cancel_count)++;
    }
}

static void fake_future_timeout(cy_future_t* const base, const cy_us_t now)
{
    (void)base;
    (void)now;
}

static void fake_future_finalize(cy_future_t* const base)
{
    fake_future_t* const self = (fake_future_t*)base;
    if ((self->index_owner != NULL) && cavl2_is_inserted(*self->index_owner, &self->base.index)) {
        cavl2_remove(self->index_owner, &self->base.index);
    }
    if (self->finalize_count != NULL) {
        (*self->finalize_count)++;
    }
}

static const cy_future_vtable_t fake_future_vtable = { .status   = fake_future_status,
                                                       .result   = fake_future_result,
                                                       .cancel   = fake_future_cancel,
                                                       .timeout  = fake_future_timeout,
                                                       .finalize = fake_future_finalize };

static fake_future_t* make_fake_future(cy_t* const       cy,
                                       size_t* const     cancel_count,
                                       size_t* const     finalize_count,
                                       const bool        done,
                                       const uint64_t    key,
                                       cy_tree_t** const index)
{
    fake_future_t* const out = (fake_future_t*)future_new(cy, &fake_future_vtable, sizeof(fake_future_t));
    if (out != NULL) {
        out->done           = done;
        out->index_owner    = index;
        out->cancel_count   = cancel_count;
        out->finalize_count = finalize_count;
        TEST_ASSERT_TRUE(future_index_insert(&out->base, index, key));
    }
    return out;
}

static void test_cy_destroy_null_is_noop(void) { cy_destroy(NULL); }

static void test_cy_destroy_empty_instance_cleans_all_resources(void)
{
    fixture_t fix;
    fixture_init(&fix);
    TEST_ASSERT_TRUE(fix.platform.cy == fix.cy);

    cy_destroy(fix.cy);
    fix.cy = NULL;

    TEST_ASSERT_NULL(fix.platform.cy);
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_reader_destroy_count);
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_writer_destroy_count);
    fixture_deinit(&fix);
}

static void test_cy_destroy_after_user_unsubscribes_and_spins(void)
{
    fixture_t fix;
    fixture_init(&fix);

    static const char* const topic_name = "destroy/deferred/subscriber/*";
    cy_subscriber_t* const   sub        = cy_subscribe(fix.cy, cy_str(topic_name), 128U);
    TEST_ASSERT_NOT_NULL(sub);
    TEST_ASSERT_FALSE(wkv_is_empty(&fix.cy->subscribers_by_name));
    TEST_ASSERT_FALSE(wkv_is_empty(&fix.cy->subscribers_by_pattern));

    cy_unsubscribe(sub); // Deferred destruction event is now pending.
    TEST_ASSERT_FALSE(wkv_is_empty(&fix.cy->subscribers_by_name));
    TEST_ASSERT_FALSE(wkv_is_empty(&fix.cy->subscribers_by_pattern));

    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(fix.cy));
    TEST_ASSERT_TRUE(wkv_is_empty(&fix.cy->subscribers_by_name));
    TEST_ASSERT_TRUE(wkv_is_empty(&fix.cy->subscribers_by_pattern));

    cy_destroy(fix.cy);
    fix.cy = NULL;

    TEST_ASSERT_NULL(fix.platform.cy);
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_reader_destroy_count); // broadcast reader only
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_writer_destroy_count); // broadcast writer
    fixture_deinit(&fix);
}

static void test_cy_destroy_after_user_destroys_futures(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_topic_t* const topic =
      fixture_make_topic(&fix, "destroy/futures/topic", UINT64_C(0x1000000000000B00), 0U, LAGE_MIN);
    TEST_ASSERT_NOT_NULL(topic);

    size_t cancel_topic      = 0U;
    size_t finalize_topic    = 0U;
    size_t cancel_request    = 0U;
    size_t finalize_request  = 0U;
    size_t cancel_response   = 0U;
    size_t finalize_response = 0U;

    fake_future_t* const fut_topic =
      make_fake_future(fix.cy, &cancel_topic, &finalize_topic, false, UINT64_C(0xA001), &topic->pub_futures_by_tag);
    fake_future_t* const fut_request = make_fake_future(
      fix.cy, &cancel_request, &finalize_request, false, UINT64_C(0xA002), &fix.cy->request_futures_by_tag);
    fake_future_t* const fut_response = make_fake_future(
      fix.cy, &cancel_response, &finalize_response, true, UINT64_C(0xA003), &fix.cy->response_futures_by_tag);
    TEST_ASSERT_NOT_NULL(fut_topic);
    TEST_ASSERT_NOT_NULL(fut_request);
    TEST_ASSERT_NOT_NULL(fut_response);

    cy_future_destroy(&fut_topic->base);
    cy_future_destroy(&fut_request->base);
    cy_future_destroy(&fut_response->base);
    TEST_ASSERT_NULL(topic->pub_futures_by_tag);
    TEST_ASSERT_NULL(fix.cy->request_futures_by_tag);
    TEST_ASSERT_NULL(fix.cy->response_futures_by_tag);

    cy_destroy(fix.cy);
    fix.cy = NULL;

    TEST_ASSERT_NULL(fix.platform.cy);
    TEST_ASSERT_EQUAL_size_t(1U, cancel_topic);
    TEST_ASSERT_EQUAL_size_t(1U, finalize_topic);
    TEST_ASSERT_EQUAL_size_t(1U, cancel_request);
    TEST_ASSERT_EQUAL_size_t(1U, finalize_request);
    TEST_ASSERT_EQUAL_size_t(0U, cancel_response); // already materialized
    TEST_ASSERT_EQUAL_size_t(1U, finalize_response);
    fixture_deinit(&fix);
}

static void test_cy_destroy_handles_missing_broadcast_handles(void)
{
    fixture_t fix;
    fixture_init(&fix);

    TEST_ASSERT_NOT_NULL(fix.cy->broad_reader);
    TEST_ASSERT_NOT_NULL(fix.cy->broad_writer);
    fix.vtable.subject_reader_destroy(&fix.platform, fix.cy->broad_reader);
    fix.cy->broad_reader = NULL;
    fix.vtable.subject_writer_destroy(&fix.platform, fix.cy->broad_writer);
    fix.cy->broad_writer = NULL;

    cy_destroy(fix.cy);
    fix.cy = NULL;

    TEST_ASSERT_NULL(fix.platform.cy);
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_reader_destroy_count);
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_writer_destroy_count);
    fixture_deinit(&fix);
}

static void test_topic_new_rejects_invalid_name(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_topic_t  fake  = { 0 };
    cy_topic_t* topic = &fake;
    TEST_ASSERT_EQUAL_INT(CY_ERR_NAME,
                          topic_new(fix.cy, &topic, (cy_str_t){ .len = 0U, .str = "" }, UINT64_C(0x101), 0U, LAGE_MIN));
    TEST_ASSERT_NULL(topic);

    char overlong[CY_TOPIC_NAME_MAX + 2U];
    memset(overlong, 'a', sizeof(overlong));
    overlong[sizeof(overlong) - 1U] = '\0';

    topic = &fake;
    TEST_ASSERT_EQUAL_INT(
      CY_ERR_NAME,
      topic_new(
        fix.cy, &topic, (cy_str_t){ .len = CY_TOPIC_NAME_MAX + 1U, .str = overlong }, UINT64_C(0x102), 0U, LAGE_MIN));
    TEST_ASSERT_NULL(topic);
    TEST_ASSERT_EQUAL_size_t(0U, cavl_count(fix.cy->topics_by_hash));
    fixture_deinit(&fix);
}

static void test_topic_new_error_oom_topic_object(void)
{
    fixture_t fix;
    fixture_init(&fix);
    fix.fail_alloc_size  = sizeof(cy_topic_t);
    fix.fail_alloc_count = 1U;

    cy_topic_t  fake = { 0 };
    cy_topic_t* out  = &fake;
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY,
                          topic_new(fix.cy, &out, cy_str("topic/new/oom/topic-object"), UINT64_C(0x110), 0U, LAGE_MIN));
    TEST_ASSERT_NULL(out);
    TEST_ASSERT_EQUAL_size_t(0U, cavl_count(fix.cy->topics_by_hash));
    TEST_ASSERT_NULL(cy_topic_find_by_name(fix.cy, cy_str("topic/new/oom/topic-object")));
    fixture_deinit(&fix);
}

static void test_topic_new_error_oom_topic_name(void)
{
    fixture_t fix;
    fixture_init(&fix);

    static const char* const name = "topic/new/oom/topic-name";
    fix.fail_alloc_size           = strlen(name) + 1U;
    fix.fail_alloc_count          = 1U;

    cy_topic_t  fake = { 0 };
    cy_topic_t* out  = &fake;
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, topic_new(fix.cy, &out, cy_str(name), UINT64_C(0x111), 0U, LAGE_MIN));
    TEST_ASSERT_NULL(out);
    TEST_ASSERT_EQUAL_size_t(0U, cavl_count(fix.cy->topics_by_hash));
    TEST_ASSERT_NULL(cy_topic_find_by_name(fix.cy, cy_str(name)));
    fixture_deinit(&fix);
}

static void test_topic_new_error_oom_name_index_node(void)
{
    fixture_t fix;
    fixture_init(&fix);

    static const char* const name = "topic/new/oom/name-index";
    fix.fail_alloc_count          = 3U; // topic object, topic name, then WKV node for topics_by_name

    cy_topic_t  fake = { 0 };
    cy_topic_t* out  = &fake;
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, topic_new(fix.cy, &out, cy_str(name), UINT64_C(0x112), 0U, LAGE_MIN));
    TEST_ASSERT_NULL(out);
    TEST_ASSERT_EQUAL_size_t(0U, cavl_count(fix.cy->topics_by_hash));
    TEST_ASSERT_NULL(cy_topic_find_by_name(fix.cy, cy_str(name)));
    fixture_deinit(&fix);
}

static void test_topic_new_error_duplicate_name(void)
{
    fixture_t fix;
    fixture_init(&fix);

    static const char* const name = "topic/new/error/dup-name";
    const uint64_t           hash = topic_hash(cy_str(name));
    cy_topic_t* const        mine = fixture_make_topic(&fix, name, hash, 0U, LAGE_MIN);
    TEST_ASSERT_NOT_NULL(mine);

    cy_topic_t* out = mine;
    TEST_ASSERT_EQUAL_INT(CY_ERR_NAME, topic_new(fix.cy, &out, cy_str(name), hash, 0U, LAGE_MIN));
    TEST_ASSERT_NULL(out);
    TEST_ASSERT_TRUE(cy_topic_find_by_name(fix.cy, cy_str(name)) == mine);
    TEST_ASSERT_EQUAL_size_t(1U, cavl_count(fix.cy->topics_by_hash));
    fixture_deinit(&fix);
}

static void test_topic_new_error_duplicate_hash_rolls_back_name_index(void)
{
    fixture_t fix;
    fixture_init(&fix);

    static const char* const existing_name = "topic/new/error/dup-hash/existing";
    static const char* const failing_name  = "topic/new/error/dup-hash/failing";
    static const uint64_t    hash          = UINT64_C(0x130);

    cy_topic_t* const mine = fixture_make_topic(&fix, existing_name, hash, 0U, LAGE_MIN);
    TEST_ASSERT_NOT_NULL(mine);

    cy_topic_t* out = mine;
    TEST_ASSERT_EQUAL_INT(CY_ERR_NAME, topic_new(fix.cy, &out, cy_str(failing_name), hash, 0U, LAGE_MIN));
    TEST_ASSERT_NULL(out);
    const wkv_node_t* const existing_node = wkv_get(&fix.cy->topics_by_name, cy_str(existing_name));
    TEST_ASSERT_NOT_NULL(existing_node);
    TEST_ASSERT_TRUE(existing_node->value == mine);
    TEST_ASSERT_NULL(wkv_get(&fix.cy->topics_by_name, cy_str(failing_name)));
    TEST_ASSERT_TRUE(cy_topic_find_by_hash(fix.cy, hash) == mine);
    TEST_ASSERT_EQUAL_size_t(1U, cavl_count(fix.cy->topics_by_hash));
    fixture_deinit(&fix);
}

static void test_left_wins_and_topic_merge_lage(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const uint64_t    base = UINT64_C(0x1000000000000100);
    cy_topic_t* const mine = fixture_make_topic(&fix, "alloc/leftwins", base, 0U, LAGE_MIN);
    topic_merge_lage(mine, 10 * MEGA, 5);
    TEST_ASSERT_TRUE(left_wins(mine, 10 * MEGA, 1, base + 1U));
    TEST_ASSERT_TRUE(left_wins(mine, 10 * MEGA, 5, base + 2U));
    TEST_ASSERT_FALSE(left_wins(mine, 10 * MEGA, 5, base - 1U));

    const cy_us_t origin_before = mine->ts_origin;
    topic_merge_lage(mine, 10 * MEGA, 1);
    TEST_ASSERT_TRUE(mine->ts_origin <= origin_before);
    fixture_deinit(&fix);
}

static void test_on_gossip_known_topic_divergence_paths(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const uint64_t    h1 = UINT64_C(0x1000000000000200);
    const uint64_t    h2 = UINT64_C(0x1000000000000300);
    cy_topic_t* const t1 = fixture_make_explicit_topic(&fix, "alloc/divergence/a", h1);
    cy_topic_t* const t2 = fixture_make_explicit_topic(&fix, "alloc/divergence/b", h2);

    topic_merge_lage(t1, 50 * MEGA, 5);
    const uint32_t ev_before = t1->evictions;
    TEST_ASSERT_TRUE(on_gossip_known_topic(fix.cy, 50 * MEGA, t1, ev_before + 1U, 1));
    TEST_ASSERT_EQUAL_UINT32(ev_before, t1->evictions);
    TEST_ASSERT_TRUE(is_listed(&fix.cy->list_gossip_urgent, &t1->list_gossip_urgent));

    topic_merge_lage(t2, 60 * MEGA, 1);
    TEST_ASSERT_FALSE(on_gossip_known_topic(fix.cy, 60 * MEGA, t2, t2->evictions + 3U, 8));
    TEST_ASSERT_EQUAL_UINT32(3U, t2->evictions);
    TEST_ASSERT_TRUE(topic_lage(t2, 60 * MEGA) >= 4);

    schedule_gossip(t1);
    schedule_gossip(t2);
    TEST_ASSERT_FALSE(on_gossip_known_topic(fix.cy, 70 * MEGA, t1, t1->evictions, topic_lage(t1, 70 * MEGA)));
    TEST_ASSERT_TRUE(fix.cy->list_gossip.head == &t1->list_gossip);
    t1->pub_count = 0U;
    t2->pub_count = 0U;
    topic_sync_implicit(t1);
    topic_sync_implicit(t2);
    fixture_deinit(&fix);
}

static void test_on_gossip_unknown_topic_collision_paths(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const uint64_t    base   = UINT64_C(0x1000000000000400);
    const uint64_t    remote = base + (uint64_t)fix.cy->platform->subject_id_modulus;
    cy_topic_t* const mine   = fixture_make_topic(&fix, "alloc/collision", base, 0U, LAGE_MIN);
    topic_merge_lage(mine, 100 * MEGA, 4);

    TEST_ASSERT_TRUE(on_gossip_unknown_topic(fix.cy, 100 * MEGA, remote, mine->evictions, 1));
    TEST_ASSERT_TRUE(is_listed(&fix.cy->list_gossip_urgent, &mine->list_gossip_urgent));

    const uint32_t before = mine->evictions;
    TEST_ASSERT_FALSE(on_gossip_unknown_topic(fix.cy, 110 * MEGA, remote, before, 8));
    TEST_ASSERT_TRUE(mine->evictions > before);
    fixture_deinit(&fix);
}

static void test_topic_allocate_recursive_chain_converges_and_writer_transfers(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const uint64_t p    = (uint64_t)fix.cy->platform->subject_id_modulus;
    const uint64_t base = UINT64_C(0x1000000000000500);

    cy_topic_t* const t1 = fixture_make_topic(&fix, "alloc/chain/1", base, 0U, LAGE_MIN);
    cy_topic_t* const t2 = fixture_make_topic(&fix, "alloc/chain/2", base + p, 0U, LAGE_MIN);
    cy_topic_t* const t3 = fixture_make_topic(&fix, "alloc/chain/3", base + (2U * p), 0U, LAGE_MIN);

    assert_subject_index_unique(fix.cy);
    TEST_ASSERT_NOT_EQUAL(topic_subject_id(t1), topic_subject_id(t2));
    TEST_ASSERT_NOT_EQUAL(topic_subject_id(t1), topic_subject_id(t3));
    TEST_ASSERT_NOT_EQUAL(topic_subject_id(t2), topic_subject_id(t3));

    t2->pub_writer = fixture_subject_writer_new(&fix.platform, topic_subject_id(t2));
    TEST_ASSERT_NOT_NULL(t2->pub_writer);
    topic_merge_lage(t1, 200 * MEGA, 8);
    topic_merge_lage(t2, 200 * MEGA, 1);
    topic_allocate(t1, t2->evictions, 200 * MEGA); // force collision with displaced t2
    TEST_ASSERT_NOT_NULL(t1->pub_writer);
    TEST_ASSERT_NULL(t2->pub_writer);
    assert_subject_index_unique(fix.cy);
    fixture_deinit(&fix);
}

static void test_topic_destroy_removes_indexes_and_lists_and_handles(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const uint64_t    h                            = UINT64_C(0x1000000000000600);
    cy_topic_t* const topic                        = fixture_make_explicit_topic(&fix, "destroy/indexes", h);
    const uint64_t    hash                         = topic->hash;
    const uint32_t    sid                          = topic_subject_id(topic);
    char              name[CY_TOPIC_NAME_MAX + 1U] = { 0 };
    memcpy(name, topic->name, cy_topic_name(topic).len);

    schedule_gossip_urgent(topic);
    topic->pub_writer = fixture_subject_writer_new(&fix.platform, sid);
    topic->sub_reader = fixture_subject_reader_new(&fix.platform, sid, 123U);
    TEST_ASSERT_NOT_NULL(topic->pub_writer);
    TEST_ASSERT_NOT_NULL(topic->sub_reader);

    topic->pub_count = 0U;
    topic_destroy(topic);
    TEST_ASSERT_NULL(cy_topic_find_by_hash(fix.cy, hash));
    TEST_ASSERT_NULL(cy_topic_find_by_name(fix.cy, cy_str(name)));
    TEST_ASSERT_NULL(topic_find_by_subject_id(fix.cy, sid));
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_writer_destroy_count);
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_reader_destroy_count);
    fixture_deinit(&fix);
}

static void test_topic_destroy_clears_associations_and_dedup(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const uint64_t    h     = UINT64_C(0x1000000000000700);
    cy_topic_t* const topic = fixture_make_topic(&fix, "destroy/states", h, 0U, LAGE_MIN);

    association_factory_context_t fac1 = { .topic = topic, .remote_id = UINT64_C(1) };
    association_factory_context_t fac2 = { .topic = topic, .remote_id = UINT64_C(2) };
    TEST_ASSERT_NOT_NULL(cavl2_find_or_insert(
      &topic->assoc_by_remote_id, &fac1.remote_id, association_cavl_compare, &fac1, association_cavl_factory));
    TEST_ASSERT_NOT_NULL(cavl2_find_or_insert(
      &topic->assoc_by_remote_id, &fac2.remote_id, association_cavl_compare, &fac2, association_cavl_factory));
    TEST_ASSERT_EQUAL_size_t(2U, topic->assoc_count);

    dedup_factory_context_t dctx1 = { .owner = topic, .remote_id = UINT64_C(11), .tag = UINT64_C(22), .now = 1000 };
    dedup_factory_context_t dctx2 = { .owner = topic, .remote_id = UINT64_C(12), .tag = UINT64_C(23), .now = 1000 };
    TEST_ASSERT_NOT_NULL(cavl2_find_or_insert(
      &topic->sub_index_dedup_by_remote_id, &dctx1.remote_id, dedup_cavl_compare, &dctx1, dedup_factory));
    TEST_ASSERT_NOT_NULL(cavl2_find_or_insert(
      &topic->sub_index_dedup_by_remote_id, &dctx2.remote_id, dedup_cavl_compare, &dctx2, dedup_factory));
    dedup_t* const dd1 = CAVL2_TO_OWNER(
      cavl2_find(topic->sub_index_dedup_by_remote_id, &dctx1.remote_id, dedup_cavl_compare), dedup_t, index_remote_id);
    dedup_t* const dd2 = CAVL2_TO_OWNER(
      cavl2_find(topic->sub_index_dedup_by_remote_id, &dctx2.remote_id, dedup_cavl_compare), dedup_t, index_remote_id);
    TEST_ASSERT_NOT_NULL(dd1);
    TEST_ASSERT_NOT_NULL(dd2);
    dedup_update(dd1, topic, dctx1.tag, 1000);
    dedup_update(dd2, topic, dctx2.tag, 1001);
    TEST_ASSERT_NOT_NULL(topic->sub_list_dedup_by_recency.head);
    TEST_ASSERT_NOT_NULL(topic->sub_index_dedup_by_remote_id);

    topic_destroy(topic);
    fixture_deinit(&fix);
}

static void test_topic_destroy_error_rollback_like_path_on_coupling_oom(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const uint64_t    h                            = UINT64_C(0x1000000000000800);
    cy_topic_t* const topic                        = fixture_make_topic(&fix, "destroy/rollback", h, 0U, LAGE_MIN);
    const uint64_t    hash                         = topic->hash;
    const uint32_t    sid                          = topic_subject_id(topic);
    char              name[CY_TOPIC_NAME_MAX + 1U] = { 0 };
    memcpy(name, topic->name, cy_topic_name(topic).len);

    subscriber_root_t root                = { 0 };
    wkv_node_t        pattern_node        = { 0 };
    root.cy                               = fix.cy;
    root.index_pattern                    = &pattern_node; // non-NULL means pattern root
    static const wkv_substitution_t subst = { .str = { .len = 1U, .str = "x" }, .ordinal = 0U, .next = NULL };

    fix.fail_alloc_size  = sizeof(cy_topic_coupling_t) + sizeof(cy_substitution_t);
    fix.fail_alloc_count = 1U;
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, topic_couple(topic, &root, 1U, &subst));

    topic_destroy(topic);
    TEST_ASSERT_NULL(cy_topic_find_by_hash(fix.cy, hash));
    TEST_ASSERT_NULL(cy_topic_find_by_name(fix.cy, cy_str(name)));
    TEST_ASSERT_NULL(topic_find_by_subject_id(fix.cy, sid));
    fixture_deinit(&fix);
}

static void test_topic_destroy_updates_topic_iter_safely(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const uint64_t    h1   = UINT64_C(0x1000000000000900);
    const uint64_t    h2   = UINT64_C(0x1000000000000A00);
    cy_topic_t* const t1   = fixture_make_topic(&fix, "destroy/iter/1", h1, 0U, LAGE_MIN);
    cy_topic_t* const t2   = fixture_make_topic(&fix, "destroy/iter/2", h2, 0U, LAGE_MIN);
    cy_topic_t* const next = cy_topic_iter_next(t1);
    fix.cy->topic_iter     = t1;
    topic_destroy(t1);
    TEST_ASSERT_TRUE(fix.cy->topic_iter == next);
    TEST_ASSERT_NOT_NULL(cy_topic_find_by_hash(fix.cy, t2->hash));
    fixture_deinit(&fix);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_cy_destroy_null_is_noop);
    RUN_TEST(test_cy_destroy_empty_instance_cleans_all_resources);
    RUN_TEST(test_cy_destroy_after_user_unsubscribes_and_spins);
    RUN_TEST(test_cy_destroy_after_user_destroys_futures);
    RUN_TEST(test_cy_destroy_handles_missing_broadcast_handles);
    RUN_TEST(test_topic_new_rejects_invalid_name);
    RUN_TEST(test_topic_new_error_oom_topic_object);
    RUN_TEST(test_topic_new_error_oom_topic_name);
    RUN_TEST(test_topic_new_error_oom_name_index_node);
    RUN_TEST(test_topic_new_error_duplicate_name);
    RUN_TEST(test_topic_new_error_duplicate_hash_rolls_back_name_index);
    RUN_TEST(test_left_wins_and_topic_merge_lage);
    RUN_TEST(test_on_gossip_known_topic_divergence_paths);
    RUN_TEST(test_on_gossip_unknown_topic_collision_paths);
    RUN_TEST(test_topic_allocate_recursive_chain_converges_and_writer_transfers);
    RUN_TEST(test_topic_destroy_removes_indexes_and_lists_and_handles);
    RUN_TEST(test_topic_destroy_clears_associations_and_dedup);
    RUN_TEST(test_topic_destroy_error_rollback_like_path_on_coupling_oom);
    RUN_TEST(test_topic_destroy_updates_topic_iter_safely);
    return UNITY_END();
}
