#include <cy.h>
#include <unity.h>
#include <array>
#include <cstddef>
#include <cstring>

namespace {

// =====================================================================================================================
//                                              cy_name_join
// =====================================================================================================================

void test_name_join_both_parts()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          result = cy_name_join(cy_str("foo"), cy_str("bar"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(7, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", result.str, result.len);
}

void test_name_join_left_empty()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          result = cy_name_join(cy_str(""), cy_str("bar"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(3, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("bar", result.str, result.len);
}

void test_name_join_right_empty()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          result = cy_name_join(cy_str("foo"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(3, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", result.str, result.len);
}

void test_name_join_both_empty()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          result = cy_name_join(cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(0, result.len);
}

void test_name_join_normalization()
{
    // Leading/trailing/duplicate separators should be removed.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_str_t result = cy_name_join(cy_str("/foo//bar/"), cy_str("/baz//qux/"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(15, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar/baz/qux", result.str, result.len);

    result = cy_name_join(cy_str("///a///"), cy_str("///b///"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(3, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("a/b", result.str, result.len);
}

void test_name_join_null_dest()
{
    const cy_str_t result = cy_name_join(cy_str("foo"), cy_str("bar"), 100, nullptr);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_buffer_too_small()
{
    std::array<char, 3> buf{};
    // "foo/bar" needs 7 bytes, buffer has only 3.
    const cy_str_t result = cy_name_join(cy_str("foo"), cy_str("bar"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_left_fills_buffer_exactly()
{
    // If left normalizes to exactly dest_size, that's >= dest_size, so it fails.
    std::array<char, 3> buf{};
    const cy_str_t      result = cy_name_join(cy_str("abc"), cy_str("d"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_right_only_separators()
{
    // Right part is only separators, normalizes to empty. Left with trailing sep should be stripped.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          result = cy_name_join(cy_str("foo"), cy_str("///"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(3, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", result.str, result.len);
}

void test_name_join_invalid_char_in_left()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t result = cy_name_join(cy_str("foo bar"), cy_str("baz"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_invalid_char_in_right()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t result = cy_name_join(cy_str("foo"), cy_str("ba z"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_separator_only_parts()
{
    // Both parts are just separators, should result in empty.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          result = cy_name_join(cy_str("///"), cy_str("///"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(0, result.len);
}

void test_name_join_pending_sep_overflow()
{
    // When a pending separator is about to be written but dest is full.
    std::array<char, 4> buf{};
    // "ab" + "cd" => "ab/cd" which needs 5 bytes. Buffer has 4.
    const cy_str_t result = cy_name_join(cy_str("ab"), cy_str("cd"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_null_left_str()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          null_left = { 3, nullptr };
    const cy_str_t                          result    = cy_name_join(null_left, cy_str("bar"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_null_right_str()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          null_right = { 3, nullptr };
    const cy_str_t                          result = cy_name_join(cy_str("foo"), null_right, buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_right_buffer_overflow()
{
    // Left part fits, but right part overflows.
    std::array<char, 6> buf{};
    // "ab" + "cdef" => "ab/cdef" (7 bytes), buffer is 6.
    const cy_str_t result = cy_name_join(cy_str("ab"), cy_str("cdef"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_join_hash_char_preserved()
{
    // '#' is a valid character (ASCII 35, within [33,126]) and passes through normalization.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t result = cy_name_join(cy_str("ns1#456"), cy_str("foo"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(11, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1#456/foo", result.str, result.len);
}

// =====================================================================================================================
//                                            cy_name_resolve -- docstring examples
// =====================================================================================================================

void test_name_resolve_docstring_examples()
{
    // Verify all examples from the API docstring (cy.h lines 667-676).
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    // foo/bar     ns1         me      ns1/foo/bar     -           yes
    r = cy_name_resolve(cy_str("foo/bar"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(11, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1/foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // ~//foo/bar  ns1         me      me/foo/bar      -           yes
    r = cy_name_resolve(cy_str("~//foo/bar"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(10, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // /foo//bar/  ns1         me      foo/bar         -           yes
    r = cy_name_resolve(cy_str("/foo//bar/"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(7, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // foo/bar/    ~//ns1      me      me/ns1/foo/bar  -           yes
    r = cy_name_resolve(cy_str("foo/bar/"), cy_str("~//ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(14, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/ns1/foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // foo#123     ns1#456     me      ns1#456/foo     123         yes
    r = cy_name_resolve(cy_str("foo#123"), cy_str("ns1#456"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(11, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1#456/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // foo/#123    ns1#456     me      ns1#456/foo     123         yes
    // Pin is consumed from name "foo/#123" -> stripped to "foo/" with pin=123,
    // then join(ns1#456, "foo/") normalizes to "ns1#456/foo".
    r = cy_name_resolve(cy_str("foo/#123"), cy_str("ns1#456"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(11, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1#456/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // */foo       ns1         me      ns1/*/foo       -           no
    r = cy_name_resolve(cy_str("*/foo"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(9, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1/*/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_FALSE(r.verbatim);

    // ~/*/foo/    ns1         me      me/*/foo        -           no
    r = cy_name_resolve(cy_str("~/*/foo/"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(8, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/*/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_FALSE(r.verbatim);

    // /~/*/foo/   ns1         me      ~/*/foo         -           no
    r = cy_name_resolve(cy_str("/~/*/foo/"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(7, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("~/*/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_FALSE(r.verbatim);
}

// =====================================================================================================================
//                                            cy_name_resolve -- basic resolution
// =====================================================================================================================

void test_name_resolve_relative_with_namespace()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo/bar"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(11, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1/foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_homeful_name()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("~//foo/bar"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(10, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_absolute_name()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("/foo//bar/"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(7, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_absolute_ignores_namespace_and_home()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(cy_str("/absolute/path"), cy_str("ignored_ns"), cy_str("ignored_home"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(13, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("absolute/path", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_homeful_namespace()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo/bar/"), cy_str("~//ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(14, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/ns1/foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_empty_namespace()
{
    // Relative name with empty namespace just normalizes the name.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo/bar"), cy_str(""), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(7, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_empty_name_with_namespace()
{
    // Empty name with namespace yields just the namespace.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str(""), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(2, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

// =====================================================================================================================
//                                         cy_name_resolve -- pin parsing
// =====================================================================================================================

void test_name_resolve_pin_simple()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_zero()
{
    // #0 is a valid pin value.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo#0"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(0, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_max()
{
    // CY_SUBJECT_ID_PINNED_MAX = 0x1FFF = 8191.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo#8191"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(8191, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_out_of_range()
{
    // 8192 exceeds CY_SUBJECT_ID_PINNED_MAX, so '#' stays in the name as a literal character.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo#8192"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(8, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#8192", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_leading_zero()
{
    // Leading zeros are not allowed in the pin expression; '#' stays literal.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(cy_str("foo#01"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(6, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#01", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    r = cy_name_resolve(cy_str("foo#00"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(6, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#00", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_pin_bare_hash()
{
    // Bare '#' with no digits is not a pin expression; remains as literal.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo#"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(4, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_pin_non_digit_suffix()
{
    // '#' followed by non-digits: scan right-to-left hits non-digit before '#', so entire name is kept.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo#bar"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(7, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_pin_double_hash()
{
    // "foo##123" -- scan right-to-left: digits "123", then first '#' at pos 4, so hash_pos=4.
    // Prefix = "foo#", pin = 123. This is valid: the pin expression is "##123" consumed as "#123" from pos 4.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo##123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(4, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
}

void test_name_resolve_bare_pin()
{
    // Bare pins: "#N" with empty prefix. The scan finds '#' at pos 0, prefix is empty (len=0).
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    // #0 -> name="" (empty), pin=0
    r = cy_name_resolve(cy_str("#0"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(0, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(0, r.pin);

    // #1 -> name="" (empty), pin=1
    r = cy_name_resolve(cy_str("#1"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(0, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(1, r.pin);

    // #123 -> name="" (empty), pin=123
    r = cy_name_resolve(cy_str("#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(0, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);

    // #8191 -> name="" (empty), pin=8191 (max)
    r = cy_name_resolve(cy_str("#8191"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(0, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(8191, r.pin);
}

void test_name_resolve_bare_pin_with_namespace()
{
    // Bare pin with namespace: name "#123" stripped to "" with pin=123, then join(ns, "") -> "ns".
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("#123"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_with_namespace_pin()
{
    // Both name and namespace have pins; only the name pin is consumed.
    // "foo#123" -> name="foo", pin=123. Namespace "ns1#456" stays as-is.
    // join("ns1#456", "foo") -> "ns1#456/foo"
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo#123"), cy_str("ns1#456"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(11, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1#456/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_in_path_segment()
{
    // "foo/#123" -- scan right-to-left: digits "123", '#' at pos 4. Pin stripped.
    // Remaining name = "foo/" (len=4), which normalizes to "foo".
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo/#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

// =====================================================================================================================
//                                         cy_name_resolve -- verbatim
// =====================================================================================================================

void test_name_resolve_verbatim_simple()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo/bar"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pattern_star()
{
    // '*' as a whole path segment denotes a single-segment wildcard.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(cy_str("*/foo"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1/*/foo", r.name.str, r.name.len);
    TEST_ASSERT_FALSE(r.verbatim);

    r = cy_name_resolve(cy_str("foo/*/bar"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/*/bar", r.name.str, r.name.len);
    TEST_ASSERT_FALSE(r.verbatim);
}

void test_name_resolve_pattern_any()
{
    // '>' as a whole path segment denotes a multi-segment wildcard.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo/>"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/>", r.name.str, r.name.len);
    TEST_ASSERT_FALSE(r.verbatim);
}

void test_name_resolve_wildcard_inside_segment_is_verbatim()
{
    // '*' or '>' embedded within a segment (not occupying the entire segment) is a literal character.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(cy_str("sensor*/engine"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("sensor*/engine", r.name.str, r.name.len);
    TEST_ASSERT_TRUE(r.verbatim);

    r = cy_name_resolve(cy_str("foo/ba?"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/ba?", r.name.str, r.name.len);
    TEST_ASSERT_TRUE(r.verbatim);
}

// =====================================================================================================================
//                                         cy_name_resolve -- error handling
// =====================================================================================================================

void test_name_resolve_null_dest()
{
    const cy_resolved_t r = cy_name_resolve(cy_str("foo"), cy_str("ns"), cy_str("me"), 100, nullptr);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_buffer_too_small()
{
    std::array<char, 3> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo/bar"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_homeful_namespace_expand_fails()
{
    // Homeful namespace expansion exceeds buffer; should fail.
    std::array<char, 5> buf{};
    const cy_resolved_t r =
      cy_name_resolve(cy_str("x"), cy_str("~/longns"), cy_str("verylonghome"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_exceeds_topic_name_max()
{
    // Construct a name that after resolution would exceed CY_TOPIC_NAME_MAX (200).
    // Use a long namespace and a long name that together exceed 200 chars.
    std::array<char, CY_TOPIC_NAME_MAX + 100> buf{};
    std::array<char, CY_TOPIC_NAME_MAX>       ns_buf{};
    std::memset(ns_buf.data(), 'n', ns_buf.size());

    const cy_str_t long_ns = { CY_TOPIC_NAME_MAX - 1, ns_buf.data() };
    // ns (199 chars) + "/" + "x" = 201 chars, exceeds 200.
    const cy_resolved_t r = cy_name_resolve(cy_str("x"), long_ns, cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_exactly_at_topic_name_max()
{
    // Construct a name that after resolution is exactly CY_TOPIC_NAME_MAX (200) -- should succeed.
    std::array<char, CY_TOPIC_NAME_MAX + 100> buf{};
    std::array<char, CY_TOPIC_NAME_MAX>       name_buf{};
    std::memset(name_buf.data(), 'a', CY_TOPIC_NAME_MAX);

    const cy_str_t      exact_name = { CY_TOPIC_NAME_MAX, name_buf.data() };
    const cy_resolved_t r          = cy_name_resolve(exact_name, cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(CY_TOPIC_NAME_MAX, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_invalid_char()
{
    // SPACE (ASCII 32) is invalid.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(cy_str("foo bar"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);

    // DEL (127) is invalid.
    const std::array<char, 3> with_del = { 'a', '\x7f', '\0' };
    r = cy_name_resolve(cy_str(with_del.data()), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);

    // High bit (128+) is invalid.
    const std::array<char, 3> with_high = { 'a', '\x80', '\0' };
    r = cy_name_resolve(cy_str(with_high.data()), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);

    // Control characters are invalid.
    const std::array<char, 4> with_tab = { 'a', '\t', 'b', '\0' };
    r = cy_name_resolve(cy_str(with_tab.data()), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);
}

void test_name_resolve_valid_printable_chars()
{
    // All ASCII 33-126 are valid. Test the boundaries.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(cy_str("!"), cy_str(""), cy_str(""), buf.size(), buf.data()); // 33 -- lowest valid
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(1, r.name.len);

    r = cy_name_resolve(cy_str("~"), cy_str(""), cy_str(""), buf.size(), buf.data()); // 126 -- highest valid
    TEST_ASSERT_NOT_NULL(r.name.str);
    // '~' alone is homeful -> expands with empty home -> empty result
    TEST_ASSERT_EQUAL_size_t(0, r.name.len);

    r = cy_name_resolve(cy_str("Z"), cy_str(""), cy_str(""), buf.size(), buf.data()); // 90
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(1, r.name.len);

    r = cy_name_resolve(cy_str("#"), cy_str(""), cy_str(""), buf.size(), buf.data()); // 35
    TEST_ASSERT_NOT_NULL(r.name.str);
    // Bare '#' with no digits, not a pin expression. '#' is a valid char, stays in the name.
    TEST_ASSERT_EQUAL_size_t(1, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("#", r.name.str, r.name.len);

    r = cy_name_resolve(cy_str("$"), cy_str(""), cy_str(""), buf.size(), buf.data()); // 36
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(1, r.name.len);
}

// =====================================================================================================================
//                                            cy_name_resolve -- edge cases
// =====================================================================================================================

void test_name_resolve_separator_only()
{
    // "/" is absolute, normalizes to empty.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("/"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(0, r.name.len);
}

void test_name_resolve_tilde_only()
{
    // "~" is homeful -> expand with home "me" -> "me"
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("~"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(2, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_tilde_with_empty_home()
{
    // "~" with empty home -> "" (empty)
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("~"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    // '~' -> expand_home("~", "") -> join("", "") -> len 0
    TEST_ASSERT_EQUAL_size_t(0, r.name.len);
}

void test_name_resolve_homeful_with_slashes()
{
    // "~//foo//bar/" with home "me" => "me/foo/bar"
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("~//foo//bar/"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(10, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo/bar", r.name.str, r.name.len);
}

void test_name_resolve_absolute_tilde_literal()
{
    // "/~" is absolute, so '~' is treated as a literal character (not home expansion).
    // Normalizes to "~".
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("/~"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(1, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("~", r.name.str, r.name.len);
}

void test_name_resolve_pin_stripped_before_length_check()
{
    // Ensure that the pin expression is stripped before the CY_TOPIC_NAME_MAX check.
    // A name that would be exactly at the limit after pin stripping should succeed.
    std::array<char, CY_TOPIC_NAME_MAX + 20> buf{};
    std::array<char, CY_TOPIC_NAME_MAX + 10> name_buf{};
    std::memset(name_buf.data(), 'a', CY_TOPIC_NAME_MAX);
    // Append "#0" so the pin is stripped and the remaining name is exactly CY_TOPIC_NAME_MAX.
    name_buf[CY_TOPIC_NAME_MAX]     = '#';
    name_buf[CY_TOPIC_NAME_MAX + 1] = '0';

    const cy_str_t      pinned_name = { CY_TOPIC_NAME_MAX + 2, name_buf.data() };
    const cy_resolved_t r           = cy_name_resolve(pinned_name, cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(CY_TOPIC_NAME_MAX, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(0, r.pin);
}

// =====================================================================================================================
//                                    cy_name_resolve -- pin + normalization interaction
// =====================================================================================================================

void test_name_resolve_pin_trailing_sep_removed()
{
    // "foo/#123" -> pin stripped to "foo/" -> normalization removes trailing sep -> "foo", pin=123
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo/#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_duplicate_seps_collapsed()
{
    // "foo//#123" -> pin stripped to "foo//" -> normalization collapses duplicate seps -> "foo", pin=123
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo//#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_with_path_segment()
{
    // "foo/bar/#123" -> pin stripped to "foo/bar/" -> normalization -> "foo/bar", pin=123
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo/bar/#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(7, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_absolute_leading_sep_removed()
{
    // "/foo#123" -> absolute, pin stripped to "/foo" -> normalization removes leading sep -> "foo", pin=123
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("/foo#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_absolute_all_redundant_seps()
{
    // "//foo//#123" -> absolute, pin stripped to "//foo//" -> normalization -> "foo", pin=123
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("//foo//#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

// =====================================================================================================================
//                                 cy_name_resolve -- docstring negative examples
// =====================================================================================================================

void test_name_resolve_rejects_space_and_nonprintable()
{
    // Docstring: `foo bar\nbaz` -- spaces and non-printable characters are not allowed.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    const std::array<char, 12> with_space = { 'f', 'o', 'o', ' ', 'b', 'a', 'r', '\n', 'b', 'a', 'z', '\0' };
    r = cy_name_resolve(cy_str(with_space.data()), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_rejects_pattern_with_pin()
{
    // Docstring: `foo/*/bar#123` -- patterns cannot be pinned.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(cy_str("foo/*/bar#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);

    // Also with '>' wildcard.
    r = cy_name_resolve(cy_str("foo/>#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);

    // Namespace-derived pattern + pin on the name is also invalid.
    r = cy_name_resolve(cy_str("*#100"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
}

void test_name_resolve_rejects_name_exceeding_max_length()
{
    // Docstring: (long string) -- final name cannot exceed CY_TOPIC_NAME_MAX.
    std::array<char, CY_TOPIC_NAME_MAX + 100> buf{};
    std::array<char, CY_TOPIC_NAME_MAX + 1>   long_name{};
    long_name.fill('a');
    const cy_str_t      name = { .len = long_name.size(), .str = long_name.data() };
    const cy_resolved_t r    = cy_name_resolve(name, cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

// =====================================================================================================================
//                              cy_name_resolve -- additional branch coverage
// =====================================================================================================================

void test_name_resolve_pin_single_digit_one()
{
    // Single-digit pin: no leading zero concern.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo#1"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(1, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_multidigit_no_leading_zero()
{
    // 4-digit pin at exact max.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("x#8191"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("x", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(8191, r.pin);
}

void test_name_resolve_homeful_name_with_pin()
{
    // Home expansion + pin.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("~/foo#123"), cy_str(""), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_absolute_name_with_pin()
{
    // Absolute path + pin.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("/foo/bar#42"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(42, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_leading_zero_two_digits()
{
    // "#00" has leading zero -> not a pin, '#' stays in name.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo#00"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#00", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_empty_name_empty_ns()
{
    // Empty name + empty namespace = empty resolved name → resolution failure (len 0 > CY_TOPIC_NAME_MAX is false,
    // but 0-length result should still be valid if the normalize succeeded).
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str(""), cy_str(""), cy_str(""), buf.size(), buf.data());
    // Empty name after normalization: len=0, str=buf.data() (not NULL).
    TEST_ASSERT_EQUAL_size_t(0, r.name.len);
}

void test_name_resolve_only_pin_no_prefix()
{
    // "#123" -- pin consumed, prefix is empty, namespace is empty → resolved name is empty (len=0).
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(0, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
}

void test_name_resolve_only_pin_with_namespace()
{
    // "#123" with namespace → prefix empty, namespace prepended: "ns".
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("#123"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
}

void test_name_resolve_pin_five_digits_out_of_range()
{
    // 5-digit number exceeding max.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo#99999"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#99999", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_pin_boundary_just_over()
{
    // 8192 = CY_SUBJECT_ID_PINNED_MAX + 1 → out of range.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo#8192"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#8192", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_pin_on_absolute_with_redundant_seps()
{
    // "/foo//bar//#42" → pin 42, normalize "//foo//bar//" → "foo/bar".
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(cy_str("//foo//bar//#42"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(42, r.pin);
}

void test_name_resolve_hash_in_namespace_preserved()
{
    // '#' in the namespace is a literal character (namespaces don't have pins stripped).
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo"), cy_str("ns#456"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns#456/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_verbatim_pin_accepted()
{
    // A verbatim name with a pin is accepted (pin is valid for verbatim).
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(cy_str("foo/bar#0"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(0, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

// =====================================================================================================================
//                                               Constants
// =====================================================================================================================

void test_name_constants()
{
    TEST_ASSERT_EQUAL_CHAR('/', cy_name_sep);
    TEST_ASSERT_EQUAL_CHAR('~', cy_name_home);
    TEST_ASSERT_EQUAL_CHAR('*', cy_name_one);
    TEST_ASSERT_EQUAL_CHAR('>', cy_name_any);
    TEST_ASSERT_EQUAL_CHAR('#', cy_name_pin_prefix);
}

} // namespace

extern "C" void setUp() {}

extern "C" void tearDown() {}

int main()
{
    UNITY_BEGIN();

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
    RUN_TEST(test_name_join_hash_char_preserved);

    // cy_name_resolve -- docstring examples
    RUN_TEST(test_name_resolve_docstring_examples);

    // cy_name_resolve -- basic resolution
    RUN_TEST(test_name_resolve_relative_with_namespace);
    RUN_TEST(test_name_resolve_homeful_name);
    RUN_TEST(test_name_resolve_absolute_name);
    RUN_TEST(test_name_resolve_absolute_ignores_namespace_and_home);
    RUN_TEST(test_name_resolve_homeful_namespace);
    RUN_TEST(test_name_resolve_empty_namespace);
    RUN_TEST(test_name_resolve_empty_name_with_namespace);

    // cy_name_resolve -- pin parsing
    RUN_TEST(test_name_resolve_pin_simple);
    RUN_TEST(test_name_resolve_pin_zero);
    RUN_TEST(test_name_resolve_pin_max);
    RUN_TEST(test_name_resolve_pin_out_of_range);
    RUN_TEST(test_name_resolve_pin_leading_zero);
    RUN_TEST(test_name_resolve_pin_bare_hash);
    RUN_TEST(test_name_resolve_pin_non_digit_suffix);
    RUN_TEST(test_name_resolve_pin_double_hash);
    RUN_TEST(test_name_resolve_bare_pin);
    RUN_TEST(test_name_resolve_bare_pin_with_namespace);
    RUN_TEST(test_name_resolve_pin_with_namespace_pin);
    RUN_TEST(test_name_resolve_pin_in_path_segment);

    // cy_name_resolve -- verbatim
    RUN_TEST(test_name_resolve_verbatim_simple);
    RUN_TEST(test_name_resolve_pattern_star);
    RUN_TEST(test_name_resolve_pattern_any);
    RUN_TEST(test_name_resolve_wildcard_inside_segment_is_verbatim);

    // cy_name_resolve -- error handling
    RUN_TEST(test_name_resolve_null_dest);
    RUN_TEST(test_name_resolve_buffer_too_small);
    RUN_TEST(test_name_resolve_homeful_namespace_expand_fails);
    RUN_TEST(test_name_resolve_exceeds_topic_name_max);
    RUN_TEST(test_name_resolve_exactly_at_topic_name_max);
    RUN_TEST(test_name_resolve_invalid_char);
    RUN_TEST(test_name_resolve_valid_printable_chars);

    // cy_name_resolve -- edge cases
    RUN_TEST(test_name_resolve_separator_only);
    RUN_TEST(test_name_resolve_tilde_only);
    RUN_TEST(test_name_resolve_tilde_with_empty_home);
    RUN_TEST(test_name_resolve_homeful_with_slashes);
    RUN_TEST(test_name_resolve_absolute_tilde_literal);
    RUN_TEST(test_name_resolve_pin_stripped_before_length_check);

    // cy_name_resolve -- pin + normalization interaction
    RUN_TEST(test_name_resolve_pin_trailing_sep_removed);
    RUN_TEST(test_name_resolve_pin_duplicate_seps_collapsed);
    RUN_TEST(test_name_resolve_pin_with_path_segment);
    RUN_TEST(test_name_resolve_pin_absolute_leading_sep_removed);
    RUN_TEST(test_name_resolve_pin_absolute_all_redundant_seps);

    // cy_name_resolve -- docstring negative examples
    RUN_TEST(test_name_resolve_rejects_space_and_nonprintable);
    RUN_TEST(test_name_resolve_rejects_pattern_with_pin);
    RUN_TEST(test_name_resolve_rejects_name_exceeding_max_length);

    // cy_name_resolve -- additional branch coverage
    RUN_TEST(test_name_resolve_pin_single_digit_one);
    RUN_TEST(test_name_resolve_pin_multidigit_no_leading_zero);
    RUN_TEST(test_name_resolve_homeful_name_with_pin);
    RUN_TEST(test_name_resolve_absolute_name_with_pin);
    RUN_TEST(test_name_resolve_pin_leading_zero_two_digits);
    RUN_TEST(test_name_resolve_empty_name_empty_ns);
    RUN_TEST(test_name_resolve_only_pin_no_prefix);
    RUN_TEST(test_name_resolve_only_pin_with_namespace);
    RUN_TEST(test_name_resolve_pin_five_digits_out_of_range);
    RUN_TEST(test_name_resolve_pin_boundary_just_over);
    RUN_TEST(test_name_resolve_pin_on_absolute_with_redundant_seps);
    RUN_TEST(test_name_resolve_hash_in_namespace_preserved);
    RUN_TEST(test_name_resolve_verbatim_pin_accepted);

    // Constants
    RUN_TEST(test_name_constants);

    return UNITY_END();
}
