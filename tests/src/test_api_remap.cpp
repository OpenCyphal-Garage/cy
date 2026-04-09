// Integration tests for cy_remap / cy_remap_parse and their interaction with cy_resolve.
// These use a live cy_t (via cy_new) and a guarded heap so that leaks and OOM rollback are observable.
#include <cy_platform.h>
#include <unity.h>
#include "api_mock_platform_utils.hpp"
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>

namespace {

struct test_platform_t final : api_test::test_platform_base_t
{
    std::size_t fail_after{ SIZE_MAX };
    std::size_t new_alloc_count{ 0U };
};

test_platform_t* platform_from(cy_platform_t* const platform)
{
    return api_test::platform_from<test_platform_t>(platform);
}

extern "C" cy_subject_writer_t* platform_subject_writer_new(cy_platform_t* const p, const std::uint32_t sid)
{
    return api_test::subject_writer_new_tracked<test_platform_t>(p, sid);
}

extern "C" void platform_subject_writer_destroy(cy_platform_t* const p, cy_subject_writer_t* const w)
{
    api_test::subject_writer_destroy_tracked<test_platform_t>(p, w);
}

extern "C" cy_err_t platform_subject_writer_send(cy_platform_t* const       platform,
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

extern "C" cy_subject_reader_t* platform_subject_reader_new(cy_platform_t* const p,
                                                            const std::uint32_t  sid,
                                                            const std::size_t    ext)
{
    return api_test::subject_reader_new_tracked<test_platform_t>(p, sid, ext);
}

extern "C" void platform_subject_reader_extent_set(cy_platform_t* const       p,
                                                   cy_subject_reader_t* const r,
                                                   const std::size_t          e)
{
    api_test::subject_reader_extent_set_tracked<test_platform_t>(p, r, e);
}

extern "C" void platform_subject_reader_destroy(cy_platform_t* const p, cy_subject_reader_t* const r)
{
    api_test::subject_reader_destroy_tracked<test_platform_t>(p, r);
}

extern "C" cy_err_t platform_unicast_send(cy_platform_t* const   platform,
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

extern "C" void platform_unicast_extent_set(cy_platform_t* const platform, const std::size_t extent)
{
    (void)platform;
    (void)extent;
}

extern "C" cy_err_t platform_spin(cy_platform_t* const platform, const cy_us_t deadline)
{
    (void)platform;
    (void)deadline;
    return CY_OK;
}

extern "C" cy_us_t platform_now(cy_platform_t* const platform) { return platform_from(platform)->now; }

// Count new allocations (ptr==NULL && size>0) and optionally fail the N-th one. Resizes and frees pass through.
extern "C" void* platform_realloc(cy_platform_t* const platform, void* const ptr, const std::size_t size)
{
    test_platform_t* const self = platform_from(platform);
    if ((ptr == nullptr) && (size > 0U)) {
        if (self->new_alloc_count >= self->fail_after) {
            return nullptr;
        }
        self->new_alloc_count++;
    }
    return api_test::core_heap_realloc<test_platform_t>(platform, ptr, size);
}

extern "C" std::uint64_t platform_random(cy_platform_t* const platform)
{
    return api_test::random_lcg<test_platform_t>(platform);
}

void platform_init(test_platform_t* const self)
{
    *self              = test_platform_t{};
    self->random_state = UINT64_C(0xD1CEB00BCAFEBEEF);
    guarded_heap_init(&self->core_heap, UINT64_C(0xFACEB00C12345678));
    guarded_heap_init(&self->message_heap, UINT64_C(0xDEC0DE1234567890));

    self->vtable.subject_writer_new        = platform_subject_writer_new;
    self->vtable.subject_writer_destroy    = platform_subject_writer_destroy;
    self->vtable.subject_writer_send       = platform_subject_writer_send;
    self->vtable.subject_reader_new        = platform_subject_reader_new;
    self->vtable.subject_reader_extent_set = platform_subject_reader_extent_set;
    self->vtable.subject_reader_destroy    = platform_subject_reader_destroy;
    self->vtable.unicast                   = platform_unicast_send;
    self->vtable.unicast_extent_set        = platform_unicast_extent_set;
    self->vtable.spin                      = platform_spin;
    self->vtable.now                       = platform_now;
    self->vtable.realloc                   = platform_realloc;
    self->vtable.random                    = platform_random;

    api_test::init_platform_base(self->platform, self->vtable);
    self->cy = cy_new(&self->platform, cy_str("test"), cy_str_t{ 0, nullptr });
    TEST_ASSERT_NOT_NULL(self->cy);
}

void platform_deinit(test_platform_t* const self) { api_test::standard_deinit(*self); }

void assert_resolved(const cy_resolved_t r, const char* const expected)
{
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(std::strlen(expected), r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN(expected, r.name.str, r.name.len);
}

// ---------- cy_remap + cy_resolve happy path ----------

void test_remap_insert_and_resolve_exact()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("a/b/c"), cy_str("z")));

    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r = cy_resolve(p.cy, cy_str("a/b/c"), buf.size(), buf.data());
    assert_resolved(r, "z");
    platform_deinit(&p);
}

// Exact-only — a longer query does NOT match.
void test_remap_no_prefix_match()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("a/b/c"), cy_str("z")));
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    assert_resolved(cy_resolve(p.cy, cy_str("a/b/c/d"), buf.size(), buf.data()), "a/b/c/d");
    platform_deinit(&p);
}

// ---------- overwrite semantics ----------

void test_remap_overwrite_replaces_old_value()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("foo"), cy_str("old")));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("foo"), cy_str("new")));

    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    assert_resolved(cy_resolve(p.cy, cy_str("foo"), buf.size(), buf.data()), "new");
    platform_deinit(&p);
}

// ---------- input validation ----------

void test_remap_rejects_empty_from()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_remap(p.cy, cy_str(""), cy_str("z")));
    platform_deinit(&p);
}

// Pins are allowed in `to` — this is the motivating "pin via remap" use case.
void test_remap_accepts_pinned_to()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("a"), cy_str("z#42")));
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r = cy_resolve(p.cy, cy_str("a"), buf.size(), buf.data());
    assert_resolved(r, "z");
    TEST_ASSERT_EQUAL_UINT16(42, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
    platform_deinit(&p);
}

// Pinned patterns are rejected at registration time by cy_remap's pre-check.
void test_remap_rejects_pinned_pattern_to()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_ERR_NAME, cy_remap(p.cy, cy_str("foo"), cy_str("foo/*#42")));
    platform_deinit(&p);
}

// ---------- canonical motivating use cases ----------

// Pin a hardcoded unpinned topic via a remap.
void test_remap_pins_an_unpinned_topic()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("foo"), cy_str("foo#123")));
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r = cy_resolve(p.cy, cy_str("foo"), buf.size(), buf.data());
    assert_resolved(r, "foo");
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
    platform_deinit(&p);
}

// Turn a hardcoded literal into a pattern subscription via a remap.
void test_remap_patterns_an_unpinned_topic()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("foo"), cy_str("foo/*/bar")));
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r = cy_resolve(p.cy, cy_str("foo"), buf.size(), buf.data());
    assert_resolved(r, "foo/*/bar");
    TEST_ASSERT_FALSE(r.verbatim);
    platform_deinit(&p);
}

// ---------- `to` resolution against ns/home ----------

// An absolute `to` (`/...`) ignores the namespace.
void test_remap_to_absolute_ignores_namespace()
{
    test_platform_t p{};
    platform_init(&p); // Fixture home is "test", ns is empty.
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("foo"), cy_str("/zoo")));
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r = cy_resolve(p.cy, cy_str("foo"), buf.size(), buf.data());
    // The leading slash is stripped by name_normalize during the absolute branch of name_resolve_construct;
    // the namespace (empty here) is not prefixed.
    assert_resolved(r, "zoo");
    platform_deinit(&p);
}

// A homeful `to` (`~/...`) expands to the home.
void test_remap_to_homeful_expands_home()
{
    test_platform_t p{};
    platform_init(&p); // Fixture home is "test".
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("foo"), cy_str("~/zoo")));
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r = cy_resolve(p.cy, cy_str("foo"), buf.size(), buf.data());
    assert_resolved(r, "test/zoo");
    platform_deinit(&p);
}

// ---------- pin handling ----------

// Matched rule with pinned `to`: the rule's pin wins (and the user's pin is discarded).
void test_remap_to_pin_overrides_user_pin()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("bar"), cy_str("bar#42")));
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r = cy_resolve(p.cy, cy_str("bar#99"), buf.size(), buf.data());
    assert_resolved(r, "bar");
    TEST_ASSERT_EQUAL_UINT16(42, r.pin);
    platform_deinit(&p);
}

// Per spec: when a rule matches, the user's pin is DISCARDED — even if the rule's `to` is pin-free.
void test_remap_user_pin_discarded_on_match()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("foo"), cy_str("bar")));
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r = cy_resolve(p.cy, cy_str("foo#7"), buf.size(), buf.data());
    assert_resolved(r, "bar");
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    platform_deinit(&p);
}

// No remap match → user pin passes through unchanged.
void test_remap_user_pin_passes_through_on_no_match()
{
    test_platform_t p{};
    platform_init(&p);
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r = cy_resolve(p.cy, cy_str("untouched#5"), buf.size(), buf.data());
    assert_resolved(r, "untouched");
    TEST_ASSERT_EQUAL_UINT16(5, r.pin);
    platform_deinit(&p);
}

// ---------- normalized lookup ----------

// The lookup query is normalized so the integrator's `from` does not need to match exact spelling.
void test_remap_normalized_lookup()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("foo/bar"), cy_str("z")));

    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    assert_resolved(cy_resolve(p.cy, cy_str("foo/bar"), buf.size(), buf.data()), "z");
    assert_resolved(cy_resolve(p.cy, cy_str("/foo/bar"), buf.size(), buf.data()), "z");
    assert_resolved(cy_resolve(p.cy, cy_str("foo/bar/"), buf.size(), buf.data()), "z");
    assert_resolved(cy_resolve(p.cy, cy_str("foo//bar"), buf.size(), buf.data()), "z");
    platform_deinit(&p);
}

// ---------- cy_remap_parse ----------

void test_remap_parse_multiple_pairs()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap_parse(p.cy, cy_str("a=x b/c=y foo/bar=baz/qux")));

    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    assert_resolved(cy_resolve(p.cy, cy_str("a"), buf.size(), buf.data()), "x");
    assert_resolved(cy_resolve(p.cy, cy_str("b/c"), buf.size(), buf.data()), "y");
    assert_resolved(cy_resolve(p.cy, cy_str("foo/bar"), buf.size(), buf.data()), "baz/qux");
    platform_deinit(&p);
}

void test_remap_parse_whitespace_variants()
{
    test_platform_t p{};
    platform_init(&p);
    // Mix of space, tab, newline, carriage return, vertical tab, form feed.
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap_parse(p.cy, cy_str("\t\na=x\r\n  b=y\v\fc=z")));

    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    assert_resolved(cy_resolve(p.cy, cy_str("a"), buf.size(), buf.data()), "x");
    assert_resolved(cy_resolve(p.cy, cy_str("b"), buf.size(), buf.data()), "y");
    assert_resolved(cy_resolve(p.cy, cy_str("c"), buf.size(), buf.data()), "z");
    platform_deinit(&p);
}

void test_remap_parse_malformed_tokens_silently_ignored()
{
    test_platform_t p{};
    platform_init(&p);
    // First token has no '=' (silently ignored). Second has a pinned `from` (invalid). Third is valid.
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap_parse(p.cy, cy_str("nosep x#42=bad good=ok")));

    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    assert_resolved(cy_resolve(p.cy, cy_str("good"), buf.size(), buf.data()), "ok");
    assert_resolved(cy_resolve(p.cy, cy_str("nosep"), buf.size(), buf.data()), "nosep");
    platform_deinit(&p);
}

void test_remap_parse_empty_string_is_ok()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap_parse(p.cy, cy_str("")));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap_parse(p.cy, cy_str("   \t\n")));
    platform_deinit(&p);
}

// ---------- OOM rollback ----------

void test_remap_oom_on_value_alloc_leaves_state_unchanged()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("a"), cy_str("keeper")));

    // Force the next new allocation to fail. The table must remain unchanged and the existing mapping must
    // still work.
    p.fail_after      = 0U;
    p.new_alloc_count = 0U;
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, cy_remap(p.cy, cy_str("b"), cy_str("later")));
    p.fail_after = SIZE_MAX;

    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    assert_resolved(cy_resolve(p.cy, cy_str("a"), buf.size(), buf.data()), "keeper");
    platform_deinit(&p);
}

// ---------- Destroy drains entries ----------

void test_remap_destroy_drains_all_entries()
{
    test_platform_t p{};
    platform_init(&p);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("a"), cy_str("x")));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("b/c"), cy_str("y")));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("d/e/f"), cy_str("z")));
    // Overwrite one entry so that the drain must also free the replaced value.
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_remap(p.cy, cy_str("a"), cy_str("xx")));
    // platform_deinit asserts the heap is clean; if any value leaked, it will fail here.
    platform_deinit(&p);
}

} // namespace

extern "C" void setUp() {}
extern "C" void tearDown() {}

int main()
{
    UNITY_BEGIN();
    RUN_TEST(test_remap_insert_and_resolve_exact);
    RUN_TEST(test_remap_no_prefix_match);
    RUN_TEST(test_remap_overwrite_replaces_old_value);
    RUN_TEST(test_remap_rejects_empty_from);
    RUN_TEST(test_remap_accepts_pinned_to);
    RUN_TEST(test_remap_rejects_pinned_pattern_to);
    RUN_TEST(test_remap_pins_an_unpinned_topic);
    RUN_TEST(test_remap_patterns_an_unpinned_topic);
    RUN_TEST(test_remap_to_absolute_ignores_namespace);
    RUN_TEST(test_remap_to_homeful_expands_home);
    RUN_TEST(test_remap_to_pin_overrides_user_pin);
    RUN_TEST(test_remap_user_pin_discarded_on_match);
    RUN_TEST(test_remap_user_pin_passes_through_on_no_match);
    RUN_TEST(test_remap_normalized_lookup);
    RUN_TEST(test_remap_parse_multiple_pairs);
    RUN_TEST(test_remap_parse_whitespace_variants);
    RUN_TEST(test_remap_parse_malformed_tokens_silently_ignored);
    RUN_TEST(test_remap_parse_empty_string_is_ok);
    RUN_TEST(test_remap_oom_on_value_alloc_leaves_state_unchanged);
    RUN_TEST(test_remap_destroy_drains_all_entries);
    return UNITY_END();
}
