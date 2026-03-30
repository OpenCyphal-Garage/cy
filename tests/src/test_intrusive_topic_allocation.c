#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
#include "intrusive_fixture_utils.h"
#include <string.h>

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    guarded_heap_t       heap;
    cy_t*                cy;
    cy_us_t              now;

    size_t fail_alloc_count;
    size_t fail_alloc_size;
    bool   fail_subject_send;
    bool   fail_subject_writer_new;
    bool   fail_subject_reader_new;

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
    fixture_t* const self = fixture_from(platform);
    if (self->fail_subject_writer_new) {
        return NULL;
    }
    return intrusive_subject_writer_new(&self->heap, subject_id);
}

static void fixture_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    fixture_t* const self = fixture_from(platform);
    self->subject_writer_destroy_count++;
    intrusive_subject_writer_destroy(&self->heap, writer);
}

static cy_err_t fixture_subject_writer_send(cy_platform_t* const       platform,
                                            cy_subject_writer_t* const writer,
                                            const cy_us_t              deadline,
                                            const cy_prio_t            priority,
                                            const cy_bytes_t           message)
{
    fixture_t* const self = fixture_from(platform);
    (void)writer;
    (void)deadline;
    (void)priority;
    (void)message;
    return self->fail_subject_send ? CY_ERR_MEDIA : CY_OK;
}

static cy_subject_reader_t* fixture_subject_reader_new(cy_platform_t* const platform,
                                                       const uint32_t       subject_id,
                                                       const size_t         extent)
{
    fixture_t* const self = fixture_from(platform);
    if (self->fail_subject_reader_new) {
        return NULL;
    }
    return intrusive_subject_reader_new(&self->heap, subject_id, extent);
}

static void fixture_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    fixture_t* const self = fixture_from(platform);
    self->subject_reader_destroy_count++;
    intrusive_subject_reader_destroy(&self->heap, reader);
}

static cy_err_t fixture_unicast_send(cy_platform_t* const   platform,
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

static void fixture_unicast_extent_set(cy_platform_t* const platform, const size_t extent)
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
    self->platform.subject_id_modulus   = (uint32_t)CY_SUBJECT_ID_MODULUS_16bit;
    self->vtable.subject_writer_new     = fixture_subject_writer_new;
    self->vtable.subject_writer_destroy = fixture_subject_writer_destroy;
    self->vtable.subject_writer_send    = fixture_subject_writer_send;
    self->vtable.subject_reader_new     = fixture_subject_reader_new;
    self->vtable.subject_reader_destroy = fixture_subject_reader_destroy;
    self->vtable.unicast                = fixture_unicast_send;
    self->vtable.unicast_extent_set     = fixture_unicast_extent_set;
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
        TEST_ASSERT_NULL(self->cy->respond_futures_by_tag);
        for (cy_topic_t* topic = cy_topic_iter_first(self->cy); topic != NULL; topic = cy_topic_iter_next(topic)) {
            TEST_ASSERT_EQUAL_UINT32(0U, topic->pub_count);
            TEST_ASSERT_NULL(topic->pub_futures_by_tag);
            TEST_ASSERT_NULL(topic->couplings);
        }
        cy_destroy(self->cy);
        self->cy = NULL;
    }
    intrusive_assert_heap_clean(&self->heap);
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
    cy_future_t* const       sub        = cy_subscribe(fix.cy, cy_str(topic_name), 128U);
    TEST_ASSERT_NOT_NULL(sub);
    TEST_ASSERT_FALSE(wkv_is_empty(&fix.cy->subscribers_by_name));
    TEST_ASSERT_FALSE(wkv_is_empty(&fix.cy->subscribers_by_pattern));

    cy_future_destroy(sub); // Deferred destruction event is now pending.
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

static void test_cy_advertise_client_validation_oom_and_extent_growth(void)
{
    fixture_t fix;
    fixture_init(&fix);

    TEST_ASSERT_NULL(cy_advertise_client(NULL, cy_str("topic/ad/null/cy"), 0U));

    char overlong[CY_TOPIC_NAME_MAX + 2U];
    memset(overlong, 'a', sizeof(overlong));
    overlong[sizeof(overlong) - 1U] = '\0';
    TEST_ASSERT_NULL(cy_advertise_client(fix.cy, (cy_str_t){ .len = CY_TOPIC_NAME_MAX + 1U, .str = overlong }, 0U));
    TEST_ASSERT_NULL(cy_advertise_client(fix.cy, cy_str("topic/ad/wild/*"), 0U));

    fix.fail_alloc_size  = sizeof(cy_publisher_t);
    fix.fail_alloc_count = 1U;
    TEST_ASSERT_NULL(cy_advertise_client(fix.cy, cy_str("topic/ad/oom"), 0U));
    fix.fail_alloc_count = 0U;
    fix.fail_alloc_size  = 0U;

    const size_t          before = fix.cy->unicast_extent;
    cy_publisher_t* const pub    = cy_advertise_client(fix.cy, cy_str("topic/ad/ok"), before + 1U);
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_TRUE(fix.cy->unicast_extent > before);
    cy_unadvertise(pub);

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

static void test_topic_subscribe_if_matching_oom_topic_new(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe(fix.cy, cy_str("topic/auto/oom/new/>"), 64U);
    TEST_ASSERT_NOT_NULL(sub);

    const cy_str_t name                = cy_str("topic/auto/oom/new/x");
    const uint64_t hash                = rapidhash(name.str, name.len);
    const size_t   async_errors_before = fix.async_error_count;
    fix.fail_alloc_size                = sizeof(cy_topic_t);
    fix.fail_alloc_count               = 1U;

    TEST_ASSERT_NULL(topic_subscribe_if_matching(fix.cy, name, hash, 0U, LAGE_MIN));
    TEST_ASSERT_NULL(cy_topic_find_by_hash(fix.cy, hash));
    TEST_ASSERT_EQUAL_size_t(async_errors_before + 1U, fix.async_error_count);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(fix.cy));
    fixture_deinit(&fix);
}

static void test_topic_subscribe_if_matching_rejects_invalid_and_no_match(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_str_t name = cy_str("topic/auto/no/match");
    const uint64_t hash = rapidhash(name.str, name.len);

    TEST_ASSERT_NULL(topic_subscribe_if_matching(fix.cy, name, hash + 1U, 0U, LAGE_MIN)); // hash mismatch
    TEST_ASSERT_NULL(topic_subscribe_if_matching(fix.cy, str_empty, 0U, 0U, LAGE_MIN));   // empty name
    TEST_ASSERT_NULL(topic_subscribe_if_matching(fix.cy, name, hash, 0U, LAGE_MIN));      // no pattern subscribers
    fixture_deinit(&fix);
}

static void test_topic_subscribe_if_matching_oom_coupling_rolls_back_topic(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe(fix.cy, cy_str("topic/auto/oom/coupling/*"), 64U);
    TEST_ASSERT_NOT_NULL(sub);

    const cy_str_t name                = cy_str("topic/auto/oom/coupling/x");
    const uint64_t hash                = rapidhash(name.str, name.len);
    const size_t   async_errors_before = fix.async_error_count;
    fix.fail_alloc_size                = sizeof(cy_topic_coupling_t) + sizeof(cy_substitution_t);
    fix.fail_alloc_count               = 1U;

    TEST_ASSERT_NULL(topic_subscribe_if_matching(fix.cy, name, hash, 0U, LAGE_MIN));
    TEST_ASSERT_NULL(cy_topic_find_by_hash(fix.cy, hash));
    TEST_ASSERT_EQUAL_size_t(async_errors_before + 1U, fix.async_error_count);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(fix.cy));
    fixture_deinit(&fix);
}

static void test_subscribe_guard_and_allocation_failure_paths(void)
{
    fixture_t fix;
    fixture_init(&fix);

    char overlong[CY_TOPIC_NAME_MAX + 2U];
    memset(overlong, 'a', sizeof(overlong));
    overlong[sizeof(overlong) - 1U] = '\0';
    TEST_ASSERT_NULL(cy_subscribe(fix.cy, (cy_str_t){ .len = CY_TOPIC_NAME_MAX + 1U, .str = overlong }, 16U));

    fix.fail_alloc_size  = sizeof(subscriber_t);
    fix.fail_alloc_count = 1U;
    TEST_ASSERT_NULL(cy_subscribe(fix.cy, cy_str("alloc/sub/future-oom"), 16U));
    fix.fail_alloc_count = 0U;
    fix.fail_alloc_size  = 0U;

    fix.fail_alloc_size  = sizeof(subscriber_root_t);
    fix.fail_alloc_count = 1U;
    TEST_ASSERT_NULL(cy_subscribe(fix.cy, cy_str("alloc/sub/root-oom"), 16U));
    fix.fail_alloc_count = 0U;
    fix.fail_alloc_size  = 0U;

    subscriber_root_t* root = NULL;
    fix.fail_alloc_size     = 0U;
    fix.fail_alloc_count    = 1U;
    TEST_ASSERT_EQUAL_INT(
      CY_ERR_MEMORY,
      ensure_subscriber_root(
        fix.cy, (cy_resolved_t){ .name = cy_str("alloc/sub/node-oom"), .pin = UINT16_MAX, .verbatim = true }, &root));
    TEST_ASSERT_NULL(root);
    TEST_ASSERT_NULL(wkv_get(&fix.cy->subscribers_by_name, cy_str("alloc/sub/node-oom")));

    root                 = NULL;
    fix.fail_alloc_size  = sizeof(cy_topic_t);
    fix.fail_alloc_count = 1U;
    TEST_ASSERT_EQUAL_INT(
      CY_ERR_MEMORY,
      ensure_subscriber_root(
        fix.cy,
        (cy_resolved_t){ .name = cy_str("alloc/sub/topic-ensure-oom"), .pin = UINT16_MAX, .verbatim = true },
        &root));

    fixture_deinit(&fix);
}

static void test_ensure_subscriber_root_pattern_index_oom(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_str_t    pattern = cy_str("alloc/sub/pattern/index/*");
    wkv_node_t* const pre     = wkv_set(&fix.cy->subscribers_by_name, pattern);
    TEST_ASSERT_NOT_NULL(pre);
    TEST_ASSERT_NULL(pre->value);

    fix.fail_alloc_size     = sizeof(wkv_node_t);
    fix.fail_alloc_count    = 1U;
    subscriber_root_t* root = NULL;
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY,
                          ensure_subscriber_root(fix.cy, (cy_resolved_t){ .name = pattern, .pin = UINT16_MAX }, &root));
    TEST_ASSERT_NULL(root);
    TEST_ASSERT_NULL(wkv_get(&fix.cy->subscribers_by_name, pattern));
    TEST_ASSERT_TRUE(wkv_is_empty(&fix.cy->subscribers_by_pattern));
    fixture_deinit(&fix);
}

static void test_subscribe_pattern_coupling_oom_rolls_back(void)
{
    fixture_t fix;
    fixture_init(&fix);

    static const char* const topic_name = "alloc/sub/coupling/fail/topic";
    const cy_str_t           name_str   = cy_str(topic_name);
    const uint64_t           hash       = rapidhash(name_str.str, name_str.len);
    cy_topic_t* const        topic      = fixture_make_explicit_topic(&fix, topic_name, hash);
    TEST_ASSERT_NULL(topic->couplings);

    fix.fail_alloc_size    = sizeof(cy_topic_coupling_t) + sizeof(cy_substitution_t);
    fix.fail_alloc_count   = 1U;
    cy_future_t* const sub = cy_subscribe(fix.cy, cy_str("alloc/sub/coupling/fail/*"), 32U);
    TEST_ASSERT_NULL(sub);
    TEST_ASSERT_NULL(topic->couplings);
    TEST_ASSERT_TRUE(wkv_is_empty(&fix.cy->subscribers_by_name));
    TEST_ASSERT_TRUE(wkv_is_empty(&fix.cy->subscribers_by_pattern));
    topic->pub_count = 0U;
    topic_sync_implicit(topic);
    fixture_deinit(&fix);
}

static void test_subscribe_existing_root_refreshes_reader_extent(void)
{
    fixture_t fix;
    fixture_init(&fix);

    static const char* const topic_name = "alloc/sub/extent/refresh";
    const cy_str_t           name_str   = cy_str(topic_name);
    const uint64_t           hash       = rapidhash(name_str.str, name_str.len);
    cy_topic_t* const        topic      = fixture_make_explicit_topic(&fix, topic_name, hash);

    cy_future_t* const sub_small = cy_subscribe(fix.cy, cy_str("alloc/sub/extent/*"), 8U);
    TEST_ASSERT_NOT_NULL(sub_small);
    TEST_ASSERT_NOT_NULL(topic->sub_reader);
    const size_t reader_destroy_before = fix.subject_reader_destroy_count;

    cy_future_t* const sub_large = cy_subscribe(fix.cy, cy_str("alloc/sub/>"), 1024U);
    TEST_ASSERT_NOT_NULL(sub_large);
    TEST_ASSERT_NOT_NULL(topic->sub_reader);
    TEST_ASSERT_EQUAL_size_t(reader_destroy_before + 1U, fix.subject_reader_destroy_count);

    cy_future_t* const sub_same_root = cy_subscribe(fix.cy, cy_str("alloc/sub/extent/*"), 16U);
    TEST_ASSERT_NOT_NULL(sub_same_root);

    cy_future_destroy(sub_small);
    cy_future_destroy(sub_large);
    cy_future_destroy(sub_same_root);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(fix.cy));
    topic->pub_count = 0U;
    topic_sync_implicit(topic);
    fixture_deinit(&fix);
}

static void test_pattern_root_scout_retry_paths(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_str_t pattern = cy_str("alloc/sub/scout/retry/*");

    fix.fail_subject_send    = true;
    cy_future_t* const first = cy_subscribe(fix.cy, pattern, 32U);
    TEST_ASSERT_NOT_NULL(first);
    const size_t async_after_first = fix.async_error_count;
    TEST_ASSERT_TRUE(async_after_first > 0U);
    const wkv_node_t* const node = wkv_get(&fix.cy->subscribers_by_name, pattern);
    TEST_ASSERT_NOT_NULL(node);
    subscriber_root_t* const root = (subscriber_root_t*)node->value;
    TEST_ASSERT_NOT_NULL(root);
    TEST_ASSERT_TRUE(root->needs_scouting);

    cy_future_t* const second = cy_subscribe(fix.cy, pattern, 48U);
    TEST_ASSERT_NOT_NULL(second);
    TEST_ASSERT_TRUE(fix.async_error_count > async_after_first);
    TEST_ASSERT_TRUE(root->needs_scouting);

    fix.fail_subject_send    = false;
    cy_future_t* const third = cy_subscribe(fix.cy, pattern, 64U);
    TEST_ASSERT_NOT_NULL(third);
    TEST_ASSERT_FALSE(root->needs_scouting);

    cy_future_destroy(first);
    cy_future_destroy(second);
    cy_future_destroy(third);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(fix.cy));
    fixture_deinit(&fix);
}

static void test_topic_new_error_duplicate_name(void)
{
    fixture_t fix;
    fixture_init(&fix);

    static const char* const name     = "topic/new/error/dup-name";
    const cy_str_t           name_str = cy_str(name);
    const uint64_t           hash     = rapidhash(name_str.str, name_str.len);
    cy_topic_t* const        mine     = fixture_make_topic(&fix, name, hash, 0U, LAGE_MIN);
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

static void test_topic_new_pinned_starts_implicit_and_not_gossiped(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const uint64_t    pinned_hash = UINT64_C(0x120);
    cy_topic_t* const topic =
      fixture_make_topic(&fix, "topic/new/pinned/implicit", pinned_hash, EVICTIONS_PINNED_MIN, LAGE_MIN);
    TEST_ASSERT_TRUE(is_pinned(topic->evictions));
    TEST_ASSERT_TRUE(topic_validate_is_implicit(topic));
    TEST_ASSERT_TRUE(is_implicit(topic));
    TEST_ASSERT_TRUE(fix.cy->list_implicit.head == &topic->list_implicit);
    TEST_ASSERT_NULL(topic_find_by_subject_id(fix.cy, (uint32_t)pinned_hash));
    // Pinned topics now participate in gossip; topic_allocate schedules urgent gossip during topic_new.
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));

    schedule_gossip_urgent(topic, 1000);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));
    fixture_deinit(&fix);
}

static void test_pinned_topic_sync_implicit_transitions_without_gossip(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_topic_t* const topic =
      fixture_make_topic(&fix, "topic/pinned/sync", UINT64_C(0x121), EVICTIONS_PINNED_MIN, LAGE_MIN);
    TEST_ASSERT_TRUE(is_pinned(topic->evictions));
    TEST_ASSERT_TRUE(is_implicit(topic));

    topic->pub_count = 1U;
    topic_sync_implicit(topic);
    TEST_ASSERT_FALSE(topic_validate_is_implicit(topic));
    TEST_ASSERT_FALSE(is_implicit(topic));
    // Promotion to explicit schedules gossip; pinned topics now participate in gossip.
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));
    schedule_gossip_urgent(topic, 1000);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));

    topic->pub_count = 0U;
    topic_sync_implicit(topic);
    TEST_ASSERT_TRUE(topic_validate_is_implicit(topic));
    TEST_ASSERT_TRUE(is_implicit(topic));
    TEST_ASSERT_FALSE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));
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

static void test_topic_merge_lage_clamps_out_of_range_values(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t     now  = 200 * MEGA;
    cy_topic_t* const mine = fixture_make_topic(&fix, "alloc/lage/clamp", UINT64_C(0x1000000000000190), 0U, LAGE_MIN);

    mine->ts_origin = now;
    topic_merge_lage(mine, now, LAGE_MAX + 10);
    TEST_ASSERT_EQUAL_INT64((int64_t)(now - (pow2us(LAGE_MAX) * MEGA)), (int64_t)mine->ts_origin);

    mine->ts_origin = now;
    topic_merge_lage(mine, now, LAGE_MIN - 10);
    TEST_ASSERT_EQUAL_INT64((int64_t)now, (int64_t)mine->ts_origin);
    fixture_deinit(&fix);
}

static void test_name_consume_pin_suffix_decimal_parsing(void)
{
    fixture_t fix;
    fixture_init(&fix);

    uint16_t pin = UINT16_MAX;

    // Valid decimal pins.
    TEST_ASSERT_EQUAL_size_t(3U, name_consume_pin_suffix(cy_str("foo#123"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(123U, pin);

    TEST_ASSERT_EQUAL_size_t(3U, name_consume_pin_suffix(cy_str("foo#0"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(0U, pin);

    TEST_ASSERT_EQUAL_size_t(1U, name_consume_pin_suffix(cy_str("x#8191"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(8191U, pin); // CY_SUBJECT_ID_PINNED_MAX

    TEST_ASSERT_EQUAL_size_t(0U, name_consume_pin_suffix(cy_str("#1"), &pin).len); // bare pin: empty prefix
    TEST_ASSERT_EQUAL_UINT16(1U, pin);

    TEST_ASSERT_EQUAL_size_t(3U, name_consume_pin_suffix(cy_str("a/b#7777"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(7777U, pin);

    // Pin = 0 is valid (single digit, no leading zero issue).
    TEST_ASSERT_EQUAL_size_t(0U, name_consume_pin_suffix(cy_str("#0"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(0U, pin);

    // Invalid: out of range.
    TEST_ASSERT_EQUAL_size_t(8U, name_consume_pin_suffix(cy_str("foo#8192"), &pin).len); // > max
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, pin);

    TEST_ASSERT_EQUAL_size_t(9U, name_consume_pin_suffix(cy_str("foo#99999"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, pin);

    // Invalid: leading zeros.
    TEST_ASSERT_EQUAL_size_t(6U, name_consume_pin_suffix(cy_str("foo#01"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, pin);

    TEST_ASSERT_EQUAL_size_t(7U, name_consume_pin_suffix(cy_str("foo#001"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, pin);

    TEST_ASSERT_EQUAL_size_t(6U, name_consume_pin_suffix(cy_str("foo#00"), &pin).len); // "00" has leading zero
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, pin);

    // Invalid: no digits after '#'.
    TEST_ASSERT_EQUAL_size_t(4U, name_consume_pin_suffix(cy_str("foo#"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, pin);

    // Invalid: non-digit characters before '#'.
    TEST_ASSERT_EQUAL_size_t(7U, name_consume_pin_suffix(cy_str("foo#bar"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, pin);

    // No '#' at all.
    TEST_ASSERT_EQUAL_size_t(3U, name_consume_pin_suffix(cy_str("foo"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, pin);

    // Empty string.
    TEST_ASSERT_EQUAL_size_t(0U, name_consume_pin_suffix(cy_str(""), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, pin);

    // Double '#': inner '#' is a literal name character.
    TEST_ASSERT_EQUAL_size_t(4U, name_consume_pin_suffix(cy_str("foo##123"), &pin).len);
    TEST_ASSERT_EQUAL_UINT16(123U, pin);
    // Verify the returned prefix is "foo#".
    {
        const cy_str_t prefix = name_consume_pin_suffix(cy_str("foo##123"), &pin);
        TEST_ASSERT_EQUAL_size_t(4U, prefix.len);
        TEST_ASSERT_EQUAL_CHAR('#', prefix.str[3]);
    }

    fixture_deinit(&fix);
}

static void test_topic_merge_lage_crdt_properties_commutative_associative_idempotent(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t now      = 300 * MEGA;
    const cy_us_t baseline = now - (pow2us(1) * MEGA);

    cy_topic_t* const c1 = fixture_make_topic(&fix, "alloc/crdt/comm/a", UINT64_C(0x1000000000001110), 0U, LAGE_MIN);
    cy_topic_t* const c2 = fixture_make_topic(&fix, "alloc/crdt/comm/b", UINT64_C(0x1000000000001120), 0U, LAGE_MIN);
    c1->ts_origin        = baseline;
    c2->ts_origin        = baseline;
    topic_merge_lage(c1, now, 4);
    topic_merge_lage(c1, now, 7);
    topic_merge_lage(c2, now, 7);
    topic_merge_lage(c2, now, 4);
    TEST_ASSERT_EQUAL_INT64((int64_t)c1->ts_origin, (int64_t)c2->ts_origin);

    cy_topic_t* const a1 = fixture_make_topic(&fix, "alloc/crdt/assoc/a", UINT64_C(0x1000000000001130), 0U, LAGE_MIN);
    cy_topic_t* const a2 = fixture_make_topic(&fix, "alloc/crdt/assoc/b", UINT64_C(0x1000000000001140), 0U, LAGE_MIN);
    a1->ts_origin        = baseline;
    a2->ts_origin        = baseline;
    topic_merge_lage(a1, now, 3);
    topic_merge_lage(a1, now, 6);
    topic_merge_lage(a1, now, 2);
    topic_merge_lage(a2, now, 6);
    topic_merge_lage(a2, now, 2);
    topic_merge_lage(a2, now, 3);
    TEST_ASSERT_EQUAL_INT64((int64_t)a1->ts_origin, (int64_t)a2->ts_origin);

    cy_topic_t* const i1 = fixture_make_topic(&fix, "alloc/crdt/idem/a", UINT64_C(0x1000000000001150), 0U, LAGE_MIN);
    i1->ts_origin        = baseline;
    topic_merge_lage(i1, now, 5);
    const cy_us_t once = i1->ts_origin;
    topic_merge_lage(i1, now, 5);
    TEST_ASSERT_EQUAL_INT64((int64_t)once, (int64_t)i1->ts_origin);
    fixture_deinit(&fix);
}

static void test_on_gossip_known_topic_equal_lage_prefers_higher_evictions(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_us_t now = 120 * MEGA;

    cy_topic_t* const topic_win =
      fixture_make_explicit_topic(&fix, "alloc/divergence/eviction-win", UINT64_C(0x1000000000001160));
    topic_merge_lage(topic_win, now, 5);
    topic_allocate(topic_win, 6U, now);
    TEST_ASSERT_EQUAL_UINT32(6U, topic_win->evictions);
    on_gossip_known_topic(fix.cy, now, topic_win, 5U, topic_lage(topic_win, now), gossip_broadcast);
    TEST_ASSERT_EQUAL_UINT32(6U, topic_win->evictions);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic_win->gossip_event));
    TEST_ASSERT_TRUE(topic_win->gossip_event.handler == gossip_event_urgent);

    cy_topic_t* const topic_lose =
      fixture_make_explicit_topic(&fix, "alloc/divergence/eviction-lose", UINT64_C(0x1000000000001170));
    topic_merge_lage(topic_lose, now, 5);
    topic_allocate(topic_lose, 6U, now);
    on_gossip_known_topic(fix.cy, now, topic_lose, 9U, topic_lage(topic_lose, now), gossip_broadcast);
    TEST_ASSERT_EQUAL_UINT32(9U, topic_lose->evictions);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic_lose->gossip_event));
    TEST_ASSERT_TRUE(topic_lose->gossip_event.handler == gossip_event_periodic);

    topic_win->pub_count  = 0U;
    topic_lose->pub_count = 0U;
    topic_sync_implicit(topic_win);
    topic_sync_implicit(topic_lose);

    assert_subject_index_unique(fix.cy);
    fixture_deinit(&fix);
}

static void test_topic_allocate_reader_recovery_after_subject_reader_oom(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe(fix.cy, cy_str("alloc/reader/oom"), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("alloc/reader/oom"));
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_NOT_NULL(topic->sub_reader);

    const uint32_t sid_before   = topic_subject_id(topic);
    fix.fail_subject_reader_new = true;
    topic_allocate(topic, topic->evictions + 1U, 200 * MEGA);
    TEST_ASSERT_TRUE(topic_subject_id(topic) != sid_before);
    TEST_ASSERT_NULL(topic->sub_reader);
    TEST_ASSERT_TRUE(fix.async_error_count > 0U);
    assert_subject_index_unique(fix.cy);

    fix.fail_subject_reader_new = false;
    topic_sync_subject_reader(topic);
    TEST_ASSERT_NOT_NULL(topic->sub_reader);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(fix.cy));
    fixture_deinit(&fix);
}

static void test_topic_sync_subject_writer_reports_oom(void)
{
    fixture_t fix;
    fixture_init(&fix);
    cy_topic_t* const topic = fixture_make_topic(&fix, "alloc/writer/oom", UINT64_C(0x10000000000011A0), 0U, LAGE_MIN);
    fix.fail_subject_writer_new = true;
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, topic_sync_subject_writer(topic));
    TEST_ASSERT_NULL(topic->pub_writer);
    fixture_deinit(&fix);
}

static void test_topic_allocate_destroys_existing_pub_writer_on_victory(void)
{
    fixture_t fix;
    fixture_init(&fix);
    cy_topic_t* const topic = fixture_make_explicit_topic(&fix, "alloc/writer/destroy", UINT64_C(0x10000000000011B0));
    topic->pub_writer       = writer_acquire(topic->cy, topic_subject_id(topic));
    TEST_ASSERT_NOT_NULL(topic->pub_writer);
    const size_t destroyed_before = fix.subject_writer_destroy_count;
    topic_allocate(topic, topic->evictions + 1U, 220 * MEGA);
    TEST_ASSERT_NULL(topic->pub_writer);
    TEST_ASSERT_TRUE(fix.subject_writer_destroy_count >= destroyed_before);
    topic->pub_count = 0U;
    topic_sync_implicit(topic);
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
    on_gossip_known_topic(fix.cy, 50 * MEGA, t1, ev_before + 1U, 1, gossip_broadcast);
    TEST_ASSERT_EQUAL_UINT32(ev_before, t1->evictions);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &t1->gossip_event));
    TEST_ASSERT_TRUE(t1->gossip_event.handler == gossip_event_urgent);

    topic_merge_lage(t2, 60 * MEGA, 1);
    on_gossip_known_topic(fix.cy, 60 * MEGA, t2, t2->evictions + 3U, 8, gossip_broadcast);
    TEST_ASSERT_EQUAL_UINT32(3U, t2->evictions);
    TEST_ASSERT_TRUE(topic_lage(t2, 60 * MEGA) >= 4);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &t2->gossip_event));
    TEST_ASSERT_TRUE(t2->gossip_event.handler == gossip_event_periodic);

    schedule_gossip_periodic(t1, 70 * MEGA, false);
    const cy_us_t deadline_before = t1->gossip_event.deadline;
    on_gossip_known_topic(fix.cy, 70 * MEGA, t1, t1->evictions, topic_lage(t1, 70 * MEGA), gossip_broadcast);
    TEST_ASSERT_TRUE(t1->gossip_event.handler == gossip_event_periodic);
    TEST_ASSERT_TRUE(t1->gossip_event.deadline > deadline_before);
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
    const uint64_t    base             = UINT64_C(0x1000000000000400);
    const uint64_t    remote           = base + (uint64_t)fix.cy->platform->subject_id_modulus;
    cy_topic_t* const mine             = fixture_make_topic(&fix, "alloc/collision", base, 0U, LAGE_MIN);
    const uint32_t    remote_evictions = 0U;
    topic_merge_lage(mine, 100 * MEGA, 4);

    on_gossip_unknown_topic(fix.cy, 100 * MEGA, remote, remote_evictions, 1);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &mine->gossip_event));
    TEST_ASSERT_TRUE(mine->gossip_event.handler == gossip_event_urgent);

    const uint32_t before = mine->evictions;
    on_gossip_unknown_topic(fix.cy, 110 * MEGA, remote, remote_evictions, 8);
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

    t2->pub_writer = writer_acquire(t2->cy, topic_subject_id(t2));
    TEST_ASSERT_NOT_NULL(t2->pub_writer);
    topic_merge_lage(t1, 200 * MEGA, 8);
    topic_merge_lage(t2, 200 * MEGA, 1);
    topic_allocate(t1, t2->evictions, 200 * MEGA); // force collision with displaced t2
    TEST_ASSERT_NULL(t1->pub_writer);              // writer is acquired lazily on publish, not on allocate
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

    schedule_gossip_urgent(topic, 230 * MEGA);
    topic->pub_writer = writer_acquire(topic->cy, sid);
    topic->sub_reader = reader_acquire(topic->cy, sid, 123U);
    TEST_ASSERT_NOT_NULL(topic->pub_writer);
    TEST_ASSERT_NOT_NULL(topic->sub_reader);

    topic->pub_count = 0U;
    topic_destroy(topic);
    TEST_ASSERT_NULL(cy_topic_find_by_hash(fix.cy, hash));
    TEST_ASSERT_NULL(cy_topic_find_by_name(fix.cy, cy_str(name)));
    TEST_ASSERT_NULL(topic_find_by_subject_id(fix.cy, sid));
    TEST_ASSERT_EQUAL_size_t(2U, fix.subject_writer_destroy_count);
    TEST_ASSERT_EQUAL_size_t(2U, fix.subject_reader_destroy_count);
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

static void test_retire_expired_implicit_topics_retires_tail_topic(void)
{
    fixture_t fix;
    fixture_init(&fix);
    cy_topic_t* const topic =
      fixture_make_topic(&fix, "alloc/implicit/retire", UINT64_C(0x10000000000011C0), 0U, LAGE_MIN);
    const uint64_t hash            = topic->hash;
    fix.cy->implicit_topic_timeout = 10;
    topic->ts_animated             = 0;
    retire_expired_implicit_topics(fix.cy, 11);
    TEST_ASSERT_NULL(cy_topic_find_by_hash(fix.cy, hash));
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
    RUN_TEST(test_cy_destroy_handles_missing_broadcast_handles);
    RUN_TEST(test_cy_advertise_client_validation_oom_and_extent_growth);
    RUN_TEST(test_topic_new_rejects_invalid_name);
    RUN_TEST(test_topic_new_error_oom_topic_object);
    RUN_TEST(test_topic_new_error_oom_topic_name);
    RUN_TEST(test_topic_new_error_oom_name_index_node);
    RUN_TEST(test_topic_subscribe_if_matching_oom_topic_new);
    RUN_TEST(test_topic_subscribe_if_matching_rejects_invalid_and_no_match);
    RUN_TEST(test_topic_subscribe_if_matching_oom_coupling_rolls_back_topic);
    RUN_TEST(test_subscribe_guard_and_allocation_failure_paths);
    RUN_TEST(test_ensure_subscriber_root_pattern_index_oom);
    RUN_TEST(test_subscribe_pattern_coupling_oom_rolls_back);
    RUN_TEST(test_subscribe_existing_root_refreshes_reader_extent);
    RUN_TEST(test_pattern_root_scout_retry_paths);
    RUN_TEST(test_topic_new_error_duplicate_name);
    RUN_TEST(test_topic_new_error_duplicate_hash_rolls_back_name_index);
    RUN_TEST(test_topic_new_pinned_starts_implicit_and_not_gossiped);
    RUN_TEST(test_pinned_topic_sync_implicit_transitions_without_gossip);
    RUN_TEST(test_left_wins_and_topic_merge_lage);
    RUN_TEST(test_topic_merge_lage_clamps_out_of_range_values);
    RUN_TEST(test_name_consume_pin_suffix_decimal_parsing);
    RUN_TEST(test_topic_merge_lage_crdt_properties_commutative_associative_idempotent);
    RUN_TEST(test_on_gossip_known_topic_equal_lage_prefers_higher_evictions);
    RUN_TEST(test_topic_allocate_reader_recovery_after_subject_reader_oom);
    RUN_TEST(test_topic_sync_subject_writer_reports_oom);
    RUN_TEST(test_topic_allocate_destroys_existing_pub_writer_on_victory);
    RUN_TEST(test_on_gossip_known_topic_divergence_paths);
    RUN_TEST(test_on_gossip_unknown_topic_collision_paths);
    RUN_TEST(test_topic_allocate_recursive_chain_converges_and_writer_transfers);
    RUN_TEST(test_topic_destroy_removes_indexes_and_lists_and_handles);
    RUN_TEST(test_topic_destroy_clears_associations_and_dedup);
    RUN_TEST(test_topic_destroy_error_rollback_like_path_on_coupling_oom);
    RUN_TEST(test_topic_destroy_updates_topic_iter_safely);
    RUN_TEST(test_retire_expired_implicit_topics_retires_tail_topic);
    return UNITY_END();
}
