#include <cy.h>
#include <unity.h>
#include <array>
#include <cstddef>
#include <cstring>

namespace {

// ----- cy_name_is_valid -----

void test_name_is_valid_simple()
{
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("a")));
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("foo")));
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("foo/bar")));
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("a/b/c/d")));
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("~")));
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("~/foo")));
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("/absolute")));
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("a/b/c/d/e/f/g")));
}

void test_name_is_valid_printable_ascii()
{
    // All printable ASCII except space (33..126) should be valid as single-char names.
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("!"))); // 33
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("~"))); // 126
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("#"))); // 35
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("Z"))); // 90
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("{"))); // 123
}

void test_name_is_valid_empty()
{
    TEST_ASSERT_FALSE(cy_name_is_valid(wkv_key("")));
    const wkv_str_t null_str = { 0, nullptr };
    TEST_ASSERT_FALSE(cy_name_is_valid(null_str));
}

void test_name_is_valid_null_ptr()
{
    const wkv_str_t null_data = { 5, nullptr };
    TEST_ASSERT_FALSE(cy_name_is_valid(null_data));
}

void test_name_is_valid_too_long()
{
    // CY_TOPIC_NAME_MAX is 200. A name of exactly 200 chars should be valid; 201 should not.
    std::array<char, CY_TOPIC_NAME_MAX + 2> buf{};
    std::memset(buf.data(), 'a', buf.size());
    buf.back() = '\0';

    const wkv_str_t exact = { CY_TOPIC_NAME_MAX, buf.data() };
    TEST_ASSERT_TRUE(cy_name_is_valid(exact));

    const wkv_str_t too_long = { CY_TOPIC_NAME_MAX + 1, buf.data() };
    TEST_ASSERT_FALSE(cy_name_is_valid(too_long));
}

void test_name_is_valid_invalid_chars()
{
    // Space (32) is invalid.
    TEST_ASSERT_FALSE(cy_name_is_valid(wkv_key("foo bar")));
    // Control characters are invalid.
    const char with_tab[] = { 'a', '\t', 'b', '\0' };
    TEST_ASSERT_FALSE(cy_name_is_valid(wkv_key(with_tab)));
    const char      with_nul_inside[] = { 'a', '\0', 'b' };
    const wkv_str_t nul_mid           = { 3, with_nul_inside };
    TEST_ASSERT_FALSE(cy_name_is_valid(nul_mid));
    // DEL (127) is invalid.
    const char with_del[] = { 'a', '\x7f', '\0' };
    TEST_ASSERT_FALSE(cy_name_is_valid(wkv_key(with_del)));
    // High bit (128+) is invalid.
    const char with_high[] = { 'a', '\x80', '\0' };
    TEST_ASSERT_FALSE(cy_name_is_valid(wkv_key(with_high)));
}

// ----- cy_name_is_verbatim -----

void test_name_is_verbatim_simple()
{
    TEST_ASSERT_TRUE(cy_name_is_verbatim(wkv_key("foo")));
    TEST_ASSERT_TRUE(cy_name_is_verbatim(wkv_key("foo/bar/baz")));
    TEST_ASSERT_TRUE(cy_name_is_verbatim(wkv_key("a")));
    TEST_ASSERT_TRUE(cy_name_is_verbatim(wkv_key("~/something")));
    TEST_ASSERT_TRUE(cy_name_is_verbatim(wkv_key("/absolute/path")));
}

void test_name_is_verbatim_patterns()
{
    // '?' matches single segment, '*' matches zero or more segments.
    TEST_ASSERT_FALSE(cy_name_is_verbatim(wkv_key("foo/?/bar")));
    TEST_ASSERT_FALSE(cy_name_is_verbatim(wkv_key("*/bar")));
    TEST_ASSERT_FALSE(cy_name_is_verbatim(wkv_key("foo/*")));
    TEST_ASSERT_FALSE(cy_name_is_verbatim(wkv_key("?")));
    TEST_ASSERT_FALSE(cy_name_is_verbatim(wkv_key("*")));
}

void test_name_is_verbatim_wildcards_inside_segment()
{
    // Per the README: wildcards *within* path segments are treated as literal.
    // "sensor*" is a single segment that contains '*', but it's not a full-segment wildcard.
    TEST_ASSERT_TRUE(cy_name_is_verbatim(wkv_key("sensor*/engine")));
    TEST_ASSERT_TRUE(cy_name_is_verbatim(wkv_key("foo/ba?")));
}

// ----- cy_name_is_homeful -----

void test_name_is_homeful()
{
    TEST_ASSERT_TRUE(cy_name_is_homeful(wkv_key("~")));
    TEST_ASSERT_TRUE(cy_name_is_homeful(wkv_key("~/")));
    TEST_ASSERT_TRUE(cy_name_is_homeful(wkv_key("~/foo")));
    TEST_ASSERT_TRUE(cy_name_is_homeful(wkv_key("~/foo/bar")));
}

void test_name_is_homeful_negative()
{
    TEST_ASSERT_FALSE(cy_name_is_homeful(wkv_key("")));
    TEST_ASSERT_FALSE(cy_name_is_homeful(wkv_key("foo")));
    TEST_ASSERT_FALSE(cy_name_is_homeful(wkv_key("/foo")));
    TEST_ASSERT_FALSE(cy_name_is_homeful(wkv_key("a~b")));
    // "~foo" is not homeful because the second char is not '/'.
    TEST_ASSERT_FALSE(cy_name_is_homeful(wkv_key("~foo")));
}

// ----- cy_name_is_absolute -----

void test_name_is_absolute()
{
    TEST_ASSERT_TRUE(cy_name_is_absolute(wkv_key("/")));
    TEST_ASSERT_TRUE(cy_name_is_absolute(wkv_key("/foo")));
    TEST_ASSERT_TRUE(cy_name_is_absolute(wkv_key("/foo/bar")));
    TEST_ASSERT_TRUE(cy_name_is_absolute(wkv_key("//foo")));
}

void test_name_is_absolute_negative()
{
    TEST_ASSERT_FALSE(cy_name_is_absolute(wkv_key("")));
    TEST_ASSERT_FALSE(cy_name_is_absolute(wkv_key("foo")));
    TEST_ASSERT_FALSE(cy_name_is_absolute(wkv_key("~/")));
    TEST_ASSERT_FALSE(cy_name_is_absolute(wkv_key("foo/bar")));
}

// ----- cy_name_join -----

void test_name_join_both_parts()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_join(wkv_key("foo"), wkv_key("bar"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(7, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", result.str, result.len);
}

void test_name_join_left_empty()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t                         result = cy_name_join(wkv_key(""), wkv_key("bar"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(3, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("bar", result.str, result.len);
}

void test_name_join_right_empty()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t                         result = cy_name_join(wkv_key("foo"), wkv_key(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(3, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", result.str, result.len);
}

void test_name_join_both_empty()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t                         result = cy_name_join(wkv_key(""), wkv_key(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(0, result.len);
}

void test_name_join_normalization()
{
    // Leading/trailing/duplicate separators should be removed.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    wkv_str_t result = cy_name_join(wkv_key("/foo//bar/"), wkv_key("/baz//qux/"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(15, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar/baz/qux", result.str, result.len);

    result = cy_name_join(wkv_key("///a///"), wkv_key("///b///"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(3, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("a/b", result.str, result.len);
}

void test_name_join_null_dest()
{
    const wkv_str_t result = cy_name_join(wkv_key("foo"), wkv_key("bar"), 100, nullptr);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_buffer_too_small()
{
    std::array<char, 3> buf{};
    // "foo/bar" needs 7 bytes, buffer has only 3.
    const wkv_str_t result = cy_name_join(wkv_key("foo"), wkv_key("bar"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_left_fills_buffer_exactly()
{
    // If left normalizes to exactly dest_size, that's >= dest_size, so it fails.
    std::array<char, 3> buf{};
    const wkv_str_t     result = cy_name_join(wkv_key("abc"), wkv_key("d"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_right_only_separators()
{
    // Right part is only separators, normalizes to empty. Left with trailing sep should be stripped.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_join(wkv_key("foo"), wkv_key("///"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(3, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", result.str, result.len);
}

void test_name_join_invalid_char_in_left()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_join(wkv_key("foo bar"), wkv_key("baz"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_invalid_char_in_right()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_join(wkv_key("foo"), wkv_key("ba z"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

// ----- cy_name_expand_home -----

void test_name_expand_home_homeful()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_expand_home(wkv_key("~/foo/bar"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(10, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo/bar", result.str, result.len);
}

void test_name_expand_home_tilde_only()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_expand_home(wkv_key("~"), wkv_key("alice"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(5, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("alice", result.str, result.len);
}

void test_name_expand_home_not_homeful()
{
    // Non-homeful names are simply normalized.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_expand_home(wkv_key("foo//bar/"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(7, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", result.str, result.len);
}

void test_name_expand_home_null_dest()
{
    const wkv_str_t result = cy_name_expand_home(wkv_key("~/foo"), wkv_key("me"), 100, nullptr);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_expand_home_with_slashes()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    // "~//foo//bar/" -> home join "/foo//bar/" -> "me/foo/bar"
    const wkv_str_t result = cy_name_expand_home(wkv_key("~//foo//bar/"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(10, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo/bar", result.str, result.len);
}

// ----- cy_name_resolve -----

void test_name_resolve_relative_with_namespace()
{
    // name="foo/bar" namespace="ns1" home="me" => "ns1/foo/bar"
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_resolve(wkv_key("foo/bar"), wkv_key("ns1"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(11, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1/foo/bar", result.str, result.len);
}

void test_name_resolve_homeful_name()
{
    // name="~//foo/bar" namespace="ns1" home="me" => "me/foo/bar"
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t                         result =
      cy_name_resolve(wkv_key("~//foo/bar"), wkv_key("ns1"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(10, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo/bar", result.str, result.len);
}

void test_name_resolve_absolute_name()
{
    // name="/foo//bar/" namespace="ns1" home="me" => "foo/bar"
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t                         result =
      cy_name_resolve(wkv_key("/foo//bar/"), wkv_key("ns1"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(7, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", result.str, result.len);
}

void test_name_resolve_homeful_namespace()
{
    // name="foo/bar/" namespace="~//ns1" home="me" => "me/ns1/foo/bar"
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t                         result =
      cy_name_resolve(wkv_key("foo/bar/"), wkv_key("~//ns1"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(14, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/ns1/foo/bar", result.str, result.len);
}

void test_name_resolve_null_dest()
{
    const wkv_str_t result = cy_name_resolve(wkv_key("foo"), wkv_key("ns"), wkv_key("me"), 100, nullptr);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_resolve_empty_namespace()
{
    // Relative name with empty namespace should just normalize the name.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_resolve(wkv_key("foo/bar"), wkv_key(""), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(7, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", result.str, result.len);
}

void test_name_resolve_empty_name_with_namespace()
{
    // Empty name with namespace should just give the namespace.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_resolve(wkv_key(""), wkv_key("ns"), wkv_key("me"), buf.size(), buf.data());
    // Empty name is not absolute and not homeful, so namespace is joined with empty name.
    TEST_ASSERT_EQUAL_size_t(2, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns", result.str, result.len);
}

void test_name_resolve_buffer_too_small()
{
    std::array<char, 3> buf{};
    const wkv_str_t result = cy_name_resolve(wkv_key("foo/bar"), wkv_key("ns"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_resolve_homeful_namespace_expand_fails()
{
    // Homeful namespace expansion exceeds buffer; should fail.
    std::array<char, 5> buf{};
    const wkv_str_t     result =
      cy_name_resolve(wkv_key("x"), wkv_key("~/longns"), wkv_key("verylonghome"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

// ----- Boundary and integration tests -----

void test_name_join_separator_only_parts()
{
    // Both parts are just separators, should result in empty.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_join(wkv_key("///"), wkv_key("///"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(0, result.len);
}

void test_name_resolve_docstring_examples()
{
    // Verify all examples from the API docstring.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    wkv_str_t                               result{};

    // name="foo/bar"      namespace="ns1"     home="me"   => "ns1/foo/bar"
    result = cy_name_resolve(wkv_key("foo/bar"), wkv_key("ns1"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(11, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1/foo/bar", result.str, result.len);

    // name="~//foo/bar"   namespace="ns1"     home="me"   => "me/foo/bar"
    result = cy_name_resolve(wkv_key("~//foo/bar"), wkv_key("ns1"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(10, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo/bar", result.str, result.len);

    // name="/foo//bar/"   namespace="ns1"     home="me"   => "foo/bar"
    result = cy_name_resolve(wkv_key("/foo//bar/"), wkv_key("ns1"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(7, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", result.str, result.len);

    // name="foo/bar/"     namespace="~//ns1"  home="me"   => "me/ns1/foo/bar"
    result = cy_name_resolve(wkv_key("foo/bar/"), wkv_key("~//ns1"), wkv_key("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(14, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/ns1/foo/bar", result.str, result.len);
}

void test_name_is_valid_separator_only()
{
    // "/" is valid (printable ASCII, no space), but it's an interesting edge case.
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("/")));
    TEST_ASSERT_TRUE(cy_name_is_valid(wkv_key("///")));
}

void test_name_join_pending_sep_overflow()
{
    // When a pending separator is about to be written but dest is full.
    std::array<char, 4> buf{};
    // "ab" + "cd" => "ab/cd" which needs 5 bytes. Buffer has 4.
    const wkv_str_t result = cy_name_join(wkv_key("ab"), wkv_key("cd"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_expand_home_empty_home()
{
    // Homeful name with empty home string: "~/foo" => join("", "/foo") => "foo"
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t result = cy_name_expand_home(wkv_key("~/foo"), wkv_key(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(3, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", result.str, result.len);
}

void test_name_resolve_absolute_ignores_namespace_and_home()
{
    // Absolute names ignore both namespace and home.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t                         result = cy_name_resolve(
      wkv_key("/absolute/path"), wkv_key("ignored_ns"), wkv_key("ignored_home"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(13, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("absolute/path", result.str, result.len);
}

void test_name_is_homeful_zero_length()
{
    const wkv_str_t empty = { 0, "~" };
    TEST_ASSERT_FALSE(cy_name_is_homeful(empty));
}

void test_name_is_absolute_zero_length()
{
    const wkv_str_t empty = { 0, "/" };
    TEST_ASSERT_FALSE(cy_name_is_absolute(empty));
}

void test_name_join_null_left_str()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t                         null_left = { 3, nullptr };
    const wkv_str_t                         result    = cy_name_join(null_left, wkv_key("bar"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_null_right_str()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const wkv_str_t                         null_right = { 3, nullptr };
    const wkv_str_t                         result = cy_name_join(wkv_key("foo"), null_right, buf.size(), buf.data());
    // Left normalizes to "foo" (len=3), separator is added, then right normalization fails.
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_right_buffer_overflow()
{
    // Left part fits, but right part overflows.
    std::array<char, 6> buf{};
    // "ab" + "cdef" => "ab/cdef" (7 bytes), buffer is 6.
    const wkv_str_t result = cy_name_join(wkv_key("ab"), wkv_key("cdef"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_constants()
{
    TEST_ASSERT_EQUAL_CHAR('/', cy_name_sep);
    TEST_ASSERT_EQUAL_CHAR('~', cy_name_home);
}

void test_name_namespace_max() { TEST_ASSERT_EQUAL_INT(CY_TOPIC_NAME_MAX - 2, CY_NAMESPACE_NAME_MAX); }

} // namespace

extern "C" void setUp() {}

extern "C" void tearDown() {}

int main()
{
    UNITY_BEGIN();

    // cy_name_is_valid
    RUN_TEST(test_name_is_valid_simple);
    RUN_TEST(test_name_is_valid_printable_ascii);
    RUN_TEST(test_name_is_valid_empty);
    RUN_TEST(test_name_is_valid_null_ptr);
    RUN_TEST(test_name_is_valid_too_long);
    RUN_TEST(test_name_is_valid_invalid_chars);
    RUN_TEST(test_name_is_valid_separator_only);

    // cy_name_is_verbatim
    RUN_TEST(test_name_is_verbatim_simple);
    RUN_TEST(test_name_is_verbatim_patterns);
    RUN_TEST(test_name_is_verbatim_wildcards_inside_segment);

    // cy_name_is_homeful
    RUN_TEST(test_name_is_homeful);
    RUN_TEST(test_name_is_homeful_negative);
    RUN_TEST(test_name_is_homeful_zero_length);

    // cy_name_is_absolute
    RUN_TEST(test_name_is_absolute);
    RUN_TEST(test_name_is_absolute_negative);
    RUN_TEST(test_name_is_absolute_zero_length);

    // cy_name_join
    RUN_TEST(test_name_join_both_parts);
    RUN_TEST(test_name_join_left_empty);
    RUN_TEST(test_name_join_right_empty);
    RUN_TEST(test_name_join_both_empty);
    RUN_TEST(test_name_join_normalization);
    RUN_TEST(test_name_join_null_dest);
    RUN_TEST(test_name_join_buffer_too_small);
    RUN_TEST(test_name_join_left_fills_buffer_exactly);
    RUN_TEST(test_name_join_right_only_separators);
    RUN_TEST(test_name_join_invalid_char_in_left);
    RUN_TEST(test_name_join_invalid_char_in_right);
    RUN_TEST(test_name_join_separator_only_parts);
    RUN_TEST(test_name_join_pending_sep_overflow);
    RUN_TEST(test_name_join_null_left_str);
    RUN_TEST(test_name_join_null_right_str);
    RUN_TEST(test_name_join_right_buffer_overflow);

    // cy_name_expand_home
    RUN_TEST(test_name_expand_home_homeful);
    RUN_TEST(test_name_expand_home_tilde_only);
    RUN_TEST(test_name_expand_home_not_homeful);
    RUN_TEST(test_name_expand_home_null_dest);
    RUN_TEST(test_name_expand_home_with_slashes);
    RUN_TEST(test_name_expand_home_empty_home);

    // cy_name_resolve
    RUN_TEST(test_name_resolve_relative_with_namespace);
    RUN_TEST(test_name_resolve_homeful_name);
    RUN_TEST(test_name_resolve_absolute_name);
    RUN_TEST(test_name_resolve_homeful_namespace);
    RUN_TEST(test_name_resolve_null_dest);
    RUN_TEST(test_name_resolve_empty_namespace);
    RUN_TEST(test_name_resolve_empty_name_with_namespace);
    RUN_TEST(test_name_resolve_buffer_too_small);
    RUN_TEST(test_name_resolve_homeful_namespace_expand_fails);
    RUN_TEST(test_name_resolve_docstring_examples);
    RUN_TEST(test_name_resolve_absolute_ignores_namespace_and_home);

    // Constants and limits
    RUN_TEST(test_name_constants);
    RUN_TEST(test_name_namespace_max);

    return UNITY_END();
}
