#include <cy.h>
#include <unity.h>
#include <array>
#include <cstddef>
#include <cstdlib>
#include <cstring>

namespace {

void assert_string(const cy_str_t str, const char* const expected)
{
    TEST_ASSERT_NOT_NULL(str.str);
    TEST_ASSERT_EQUAL_size_t(std::strlen(expected), str.len);
    TEST_ASSERT_EQUAL_STRING_LEN(expected, str.str, str.len);
}

void assert_resolved(const cy_resolved_t r, const char* const expected, const uint16_t pin, const bool verbatim)
{
    assert_string(r.name, expected);
    TEST_ASSERT_EQUAL_UINT16(pin, r.pin);
    TEST_ASSERT_EQUAL(verbatim, r.verbatim);
}

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

void test_name_join_empty_null_inputs()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          empty  = { 0U, nullptr };
    cy_str_t                                result = cy_name_join(empty, cy_str("bar"), buf.size(), buf.data());
    assert_string(result, "bar");

    result = cy_name_join(cy_str("foo"), empty, buf.size(), buf.data());
    assert_string(result, "foo");

    result = cy_name_join(empty, empty, buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(result.str);
    TEST_ASSERT_EQUAL_size_t(0U, result.len);
}

void test_name_join_overlap_left_exact_alias()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    std::memcpy(buf.data(), "foo", 3U);
    const cy_str_t left   = { 3U, buf.data() };
    const cy_str_t result = cy_name_join(left, cy_str("bar"), buf.size(), buf.data());
    assert_string(result, "foo/bar");
}

void test_name_join_overlap_right_exact_alias()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    std::memcpy(buf.data(), "bar", 3U);
    const cy_str_t right  = { 3U, buf.data() };
    const cy_str_t result = cy_name_join(cy_str("foo"), right, buf.size(), buf.data());
    assert_string(result, "foo/bar");
}

void test_name_join_overlap_left_exact_alias_normalized()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    std::memcpy(buf.data(), "foo////", 7U);
    const cy_str_t left   = { 7U, buf.data() };
    const cy_str_t result = cy_name_join(left, cy_str("bar"), buf.size(), buf.data());
    assert_string(result, "foo/bar");
}

void test_name_join_overlap_right_exact_alias_normalized()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    std::memcpy(buf.data(), "/////////a", 10U);
    const cy_str_t right  = { 10U, buf.data() };
    const cy_str_t result = cy_name_join(cy_str("b"), right, buf.size(), buf.data());
    assert_string(result, "b/a");
}

void test_name_join_overlap_left_exact_alias_empty_right()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    std::memcpy(buf.data(), "foo", 3U);
    const cy_str_t left   = { 3U, buf.data() };
    const cy_str_t empty  = { 0U, nullptr };
    const cy_str_t result = cy_name_join(left, empty, buf.size(), buf.data());
    assert_string(result, "foo");
}

void test_name_join_overlap_right_exact_alias_empty_left()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    std::memcpy(buf.data(), "bar", 3U);
    const cy_str_t empty  = { 0U, nullptr };
    const cy_str_t right  = { 3U, buf.data() };
    const cy_str_t result = cy_name_join(empty, right, buf.size(), buf.data());
    assert_string(result, "bar");
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
    r = cy_name_resolve(nullptr, cy_str("foo/bar"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(11, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1/foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // ~//foo/bar  ns1         me      me/foo/bar      -           yes
    r = cy_name_resolve(nullptr, cy_str("~//foo/bar"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(10, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // /foo//bar/  ns1         me      foo/bar         -           yes
    r = cy_name_resolve(nullptr, cy_str("/foo//bar/"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(7, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // foo/bar/    ~//ns1      me      me/ns1/foo/bar  -           yes
    r = cy_name_resolve(nullptr, cy_str("foo/bar/"), cy_str("~//ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(14, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/ns1/foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // foo#123     ns1#456     me      ns1#456/foo     123         yes
    r = cy_name_resolve(nullptr, cy_str("foo#123"), cy_str("ns1#456"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(11, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1#456/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // foo/#123    ns1#456     me      ns1#456/foo     123         yes
    // Pin is consumed from name "foo/#123" -> stripped to "foo/" with pin=123,
    // then join(ns1#456, "foo/") normalizes to "ns1#456/foo".
    r = cy_name_resolve(nullptr, cy_str("foo/#123"), cy_str("ns1#456"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(11, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1#456/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // */foo       ns1         me      ns1/*/foo       -           no
    r = cy_name_resolve(nullptr, cy_str("*/foo"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(9, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1/*/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_FALSE(r.verbatim);

    // ~/*/foo/    ns1         me      me/*/foo        -           no
    r = cy_name_resolve(nullptr, cy_str("~/*/foo/"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(8, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/*/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_FALSE(r.verbatim);

    // /~/*/foo/   ns1         me      ~/*/foo         -           no
    r = cy_name_resolve(nullptr, cy_str("/~/*/foo/"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(7, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("~/*/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_FALSE(r.verbatim);
}

// =====================================================================================================================
//                                         cy_name_resolve -- pin parsing
// =====================================================================================================================

void test_name_resolve_pin_simple()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("foo#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_single_digit()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("foo#1"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(1, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_zero()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("foo#0"), cy_str(""), cy_str(""), buf.size(), buf.data());
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
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo#8191"), cy_str(""), cy_str(""), buf.size(), buf.data());
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
    cy_resolved_t                           r{};

    r = cy_name_resolve(nullptr, cy_str("foo#8192"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(8, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#8192", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    r = cy_name_resolve(nullptr, cy_str("foo#99999"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#99999", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_pin_leading_zero()
{
    // Leading zeros are not allowed in the pin expression; '#' stays literal.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(nullptr, cy_str("foo#01"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(6, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#01", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    r = cy_name_resolve(nullptr, cy_str("foo#00"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(6, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#00", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_pin_bare_hash()
{
    // Bare '#' with no digits is not a pin expression; remains as literal.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("foo#"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(4, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_pin_non_digit_suffix()
{
    // '#' followed by non-digits: scan right-to-left hits non-digit before '#', so entire name is kept.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("foo#bar"), cy_str(""), cy_str(""), buf.size(), buf.data());
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
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo##123"), cy_str(""), cy_str(""), buf.size(), buf.data());
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
    // #0 -> name="" (empty), invalid
    r = cy_name_resolve(nullptr, cy_str("#0"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_bare_pin_with_namespace()
{
    // Bare pin with namespace: name "#123" stripped to "" with pin=123, then join(ns, "") -> "ns".
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("#123"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
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
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo#123"), cy_str("ns1#456"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(11, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1#456/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_homeful_name_with_pin()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("~/foo#123"), cy_str(""), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_absolute_name_with_pin()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("/foo/bar#42"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(42, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_hash_in_namespace_preserved()
{
    // '#' in the namespace is a literal character (namespaces don't have pins stripped).
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo"), cy_str("ns#456"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns#456/foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_all_digit_name_no_hash()
{
    // A name of all digits with no '#' is not a pin expression.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("123", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_trailing_hash_no_digits()
{
    // "foo##" — inner '#' is literal, trailing '#' has no digits: not a pin expression.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("foo##"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(5, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo##", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

// =====================================================================================================================
//                                         cy_name_resolve -- verbatim
// =====================================================================================================================

void test_name_resolve_verbatim_simple()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo/bar"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pattern_star()
{
    // '*' as a whole path segment denotes a single-segment wildcard.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(nullptr, cy_str("*/foo"), cy_str("ns1"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns1/*/foo", r.name.str, r.name.len);
    TEST_ASSERT_FALSE(r.verbatim);

    r = cy_name_resolve(nullptr, cy_str("foo/*/bar"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/*/bar", r.name.str, r.name.len);
    TEST_ASSERT_FALSE(r.verbatim);
}

void test_name_resolve_pattern_any()
{
    // '>' as a whole path segment denotes a multi-segment wildcard.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("foo/>"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/>", r.name.str, r.name.len);
    TEST_ASSERT_FALSE(r.verbatim);
}

void test_name_resolve_wildcard_inside_segment_is_verbatim()
{
    // '*' or '>' embedded within a segment (not occupying the entire segment) is a literal character.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(nullptr, cy_str("sensor*/engine"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("sensor*/engine", r.name.str, r.name.len);
    TEST_ASSERT_TRUE(r.verbatim);

    r = cy_name_resolve(nullptr, cy_str("foo/ba?"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/ba?", r.name.str, r.name.len);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_verbatim_pin_accepted()
{
    // A verbatim name with a pin is accepted.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo/bar#0"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(0, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

// =====================================================================================================================
//                                         cy_name_resolve -- error handling
// =====================================================================================================================

void test_name_resolve_null_dest()
{
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("foo"), cy_str("ns"), cy_str("me"), 100, nullptr);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_accepts_empty_null_namespace_and_home()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          empty = { 0U, nullptr };
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("foo"), empty, empty, buf.size(), buf.data());
    assert_resolved(r, "foo", UINT16_MAX, true);
}

void test_name_resolve_rejects_malformed_name_arguments()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          malformed = { 1U, nullptr };
    cy_resolved_t r = cy_name_resolve(nullptr, malformed, cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);

    r = cy_name_resolve(nullptr, cy_str("foo"), malformed, cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);

    r = cy_name_resolve(nullptr, cy_str("foo"), cy_str("ns"), malformed, buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_empty_null_name_is_empty_and_invalid()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_str_t                          empty = { 0U, nullptr };
    const cy_resolved_t r = cy_name_resolve(nullptr, empty, cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_buffer_too_small()
{
    std::array<char, 3> buf{};
    const cy_resolved_t r =
      cy_name_resolve(nullptr, cy_str("foo/bar"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_homeful_namespace_expand_fails()
{
    // Homeful namespace expansion exceeds buffer; should fail.
    std::array<char, 5> buf{};
    const cy_resolved_t r =
      cy_name_resolve(nullptr, cy_str("x"), cy_str("~/longns"), cy_str("verylonghome"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_absolute_ignores_invalid_namespace_and_home()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("/foo"), cy_str("bad ns"), cy_str("bad home"), buf.size(), buf.data());
    assert_resolved(r, "foo", UINT16_MAX, true);
}

void test_name_resolve_homeful_name_ignores_invalid_namespace()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("~/foo"), cy_str("bad ns"), cy_str("me"), buf.size(), buf.data());
    assert_resolved(r, "me/foo", UINT16_MAX, true);
}

void test_name_resolve_relative_non_homeful_ignores_invalid_home()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo"), cy_str("ns"), cy_str("bad home"), buf.size(), buf.data());
    assert_resolved(r, "ns/foo", UINT16_MAX, true);
}

void test_name_resolve_relative_non_homeful_rejects_invalid_namespace()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo"), cy_str("bad ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_homeful_name_rejects_invalid_home()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("~/foo"), cy_str("ns"), cy_str("bad home"), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_homeful_namespace_rejects_invalid_home()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo"), cy_str("~/ns"), cy_str("bad home"), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_homeful_namespace_rejects_invalid_namespace_tail()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo"), cy_str("~/bad ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
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
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("x"), long_ns, cy_str(""), buf.size(), buf.data());
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
    const cy_resolved_t r = cy_name_resolve(nullptr, exact_name, cy_str(""), cy_str(""), buf.size(), buf.data());
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

    r = cy_name_resolve(nullptr, cy_str("foo bar"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);

    // DEL (127) is invalid.
    const std::array<char, 3> with_del = { 'a', '\x7f', '\0' };
    r = cy_name_resolve(nullptr, cy_str(with_del.data()), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);

    // High bit (128+) is invalid.
    const std::array<char, 3> with_high = { 'a', '\x80', '\0' };
    r = cy_name_resolve(nullptr, cy_str(with_high.data()), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);

    // Control characters are invalid.
    const std::array<char, 4> with_tab = { 'a', '\t', 'b', '\0' };
    r = cy_name_resolve(nullptr, cy_str(with_tab.data()), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);
}

void test_name_resolve_valid_printable_chars()
{
    // All ASCII 33-126 are valid. Test the boundaries.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(nullptr, cy_str("!"), cy_str(""), cy_str(""), buf.size(), buf.data()); // 33 -- lowest valid
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(1, r.name.len);

    r = cy_name_resolve(nullptr, cy_str("/~"), cy_str(""), cy_str(""), buf.size(), buf.data()); // 126 -- highest valid
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(1, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("~", r.name.str, r.name.len);

    r = cy_name_resolve(nullptr, cy_str("Z"), cy_str(""), cy_str(""), buf.size(), buf.data()); // 90
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(1, r.name.len);

    r = cy_name_resolve(nullptr, cy_str("#"), cy_str(""), cy_str(""), buf.size(), buf.data()); // 35
    TEST_ASSERT_NOT_NULL(r.name.str);
    // Bare '#' with no digits, not a pin expression. '#' is a valid char, stays in the name.
    TEST_ASSERT_EQUAL_size_t(1, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("#", r.name.str, r.name.len);

    r = cy_name_resolve(nullptr, cy_str("$"), cy_str(""), cy_str(""), buf.size(), buf.data()); // 36
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(1, r.name.len);
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
    r = cy_name_resolve(nullptr, cy_str(with_space.data()), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_rejects_pattern_with_pin()
{
    // Docstring: `foo/*/bar#123` -- patterns cannot be pinned.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(nullptr, cy_str("foo/*/bar#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);

    // Also with '>' wildcard.
    r = cy_name_resolve(nullptr, cy_str("foo/>#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);

    // Namespace-derived pattern + pin on the name is also invalid.
    r = cy_name_resolve(nullptr, cy_str("*#100"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
}

void test_name_resolve_rejects_empty_name()
{
    std::array<char, CY_TOPIC_NAME_MAX + 100> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str(""), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_rejects_empty_normalized_name()
{
    std::array<char, CY_TOPIC_NAME_MAX + 100> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("/"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_rejects_empty_pinned_name()
{
    std::array<char, CY_TOPIC_NAME_MAX + 100> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("#1234"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_rejects_empty_normalized_pinned_name()
{
    std::array<char, CY_TOPIC_NAME_MAX + 100> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("/#1234"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_rejects_name_exceeding_max_length()
{
    // Docstring: (long string) -- final name cannot exceed CY_TOPIC_NAME_MAX.
    std::array<char, CY_TOPIC_NAME_MAX + 100> buf{};
    std::array<char, CY_TOPIC_NAME_MAX + 1>   long_name{};
    long_name.fill('a');
    const cy_str_t      name = { .len = long_name.size(), .str = long_name.data() };
    const cy_resolved_t r    = cy_name_resolve(nullptr, name, cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

// =====================================================================================================================
//                                            cy_name_resolve -- edge cases
// =====================================================================================================================

void test_name_resolve_separator_only()
{
    // "/" is absolute, normalizes to empty, which is invalid.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("/"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_tilde_only()
{
    // "~" is homeful -> expand with home "me" -> "me"
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("~"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(2, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_tilde_with_empty_home()
{
    // "~" with empty home -> "" (empty), which is invalid.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("~"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_homeful_with_slashes()
{
    // "~//foo//bar/" with home "me" => "me/foo/bar"
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("~//foo//bar/"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(10, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo/bar", r.name.str, r.name.len);
}

void test_name_resolve_absolute_tilde_literal()
{
    // "/~" is absolute, so '~' is treated as a literal character (not home expansion).
    // Normalizes to "~".
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("/~"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(1, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("~", r.name.str, r.name.len);
}

void test_name_resolve_absolute_ignores_namespace_and_home()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r = cy_name_resolve(
      nullptr, cy_str("/absolute/path"), cy_str("ignored_ns"), cy_str("ignored_home"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(13, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("absolute/path", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_tilde_not_followed_by_separator()
{
    // "~x" is NOT homeful (tilde must be alone or followed by separator).
    // It is treated as a relative name and joined with the namespace.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("~x"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns/~x", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_homeful_bare_pin()
{
    // "~#123" — pin stripped first to "~" (pin=123), then "~" is homeful → expand to home.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("~#123"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("me", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_absolute_bare_pin()
{
    // "/#123" — pin stripped to "/" (pin=123), absolute path normalizes to "" (empty), which is invalid.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("/#123"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_homeful_trailing_sep()
{
    // "~/" with home "me" → same as "~": home is expanded, trailing separator stripped.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("~/"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(2, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me", r.name.str, r.name.len);
}

void test_name_resolve_empty_namespace()
{
    // Relative name with empty namespace just normalizes the name.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo/bar"), cy_str(""), cy_str("me"), buf.size(), buf.data());
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
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str(""), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(2, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_empty_name_empty_ns()
{
    // Empty name + empty namespace = empty resolved name, which is invalid.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str(""), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
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
    const cy_resolved_t r = cy_name_resolve(nullptr, pinned_name, cy_str(""), cy_str(""), buf.size(), buf.data());
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
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo/#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
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
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo//#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
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
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo/bar/#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
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
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("/foo#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
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
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("//foo//#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(3, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_pin_on_absolute_with_redundant_seps()
{
    // "/foo//bar//#42" -> pin 42, normalize "//foo//bar//" -> "foo/bar".
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("//foo//bar//#42"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(42, r.pin);
}

// =====================================================================================================================
//                                    cy_name_resolve -- pin edge cases with pinning
// =====================================================================================================================

void test_name_resolve_pin_at_name_max_boundary()
{
    // Name that is exactly CY_TOPIC_NAME_MAX after pin stripping should succeed.
    std::array<char, CY_TOPIC_NAME_MAX + 20> buf{};
    std::array<char, CY_TOPIC_NAME_MAX + 10> name_buf{};
    std::memset(name_buf.data(), 'a', CY_TOPIC_NAME_MAX);
    name_buf[CY_TOPIC_NAME_MAX]     = '#';
    name_buf[CY_TOPIC_NAME_MAX + 1] = '0';
    const cy_str_t      at_max      = { CY_TOPIC_NAME_MAX + 2, name_buf.data() };
    const cy_resolved_t r           = cy_name_resolve(nullptr, at_max, cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(CY_TOPIC_NAME_MAX, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(0, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // Name that is CY_TOPIC_NAME_MAX+1 after pin stripping should fail.
    std::array<char, CY_TOPIC_NAME_MAX + 20> buf2{};
    std::array<char, CY_TOPIC_NAME_MAX + 10> name_buf2{};
    std::memset(name_buf2.data(), 'a', CY_TOPIC_NAME_MAX + 1);
    name_buf2[CY_TOPIC_NAME_MAX + 1] = '#';
    name_buf2[CY_TOPIC_NAME_MAX + 2] = '0';
    const cy_str_t      over_max     = { CY_TOPIC_NAME_MAX + 3, name_buf2.data() };
    const cy_resolved_t r2 = cy_name_resolve(nullptr, over_max, cy_str(""), cy_str(""), buf2.size(), buf2.data());
    TEST_ASSERT_NULL(r2.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r2.name.len);
}

void test_name_resolve_pin_exceeding_max_is_literal()
{
    // Values above CY_SUBJECT_ID_PINNED_MAX (8191) are not valid pins; '#' stays literal.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    // 8192 -- just above max.
    r = cy_name_resolve(nullptr, cy_str("foo#8192"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns/foo#8192", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    // 65535 -- UINT16_MAX as text, still not a valid pin.
    r = cy_name_resolve(nullptr, cy_str("foo#65535"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns/foo#65535", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    // 10000 -- well above max.
    r = cy_name_resolve(nullptr, cy_str("foo#10000"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns/foo#10000", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_pin_uint16_overflow_regression()
{
    // Values that would wrap uint16_t into the valid pin range [0, 8191] before the fix.
    // After the fix, they must all be rejected: '#' stays literal in the name, pin = UINT16_MAX.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    // 65536 wraps uint16 to 0.
    r = cy_name_resolve(nullptr, cy_str("foo#65536"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns/foo#65536", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    // 65537 wraps uint16 to 1.
    r = cy_name_resolve(nullptr, cy_str("foo#65537"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns/foo#65537", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    // 73727 wraps uint16 to 8191 = CY_SUBJECT_ID_PINNED_MAX.
    r = cy_name_resolve(nullptr, cy_str("foo#73727"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns/foo#73727", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    // 70000 wraps uint16 to 4464.
    r = cy_name_resolve(nullptr, cy_str("foo#70000"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns/foo#70000", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    // 131072 = 2*65536, double wrap to 0.
    r = cy_name_resolve(nullptr, cy_str("foo#131072"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns/foo#131072", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    // Without namespace: overflow value stays literal.
    r = cy_name_resolve(nullptr, cy_str("foo#65536"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#65536", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    // Absolute name with overflow: "/foo#65536" -> normalize -> "foo#65536", no pin.
    r = cy_name_resolve(nullptr, cy_str("/foo#65536"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo#65536", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);

    // Homeful name with overflow: "~/foo#65536" -> expand home -> "me/foo#65536", no pin.
    r = cy_name_resolve(nullptr, cy_str("~/foo#65536"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("me/foo#65536", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
}

void test_name_resolve_pin_mid_name_not_stripped()
{
    // '#' not at the end of the name (followed by '/bar') is not a pin expression.
    // The right-to-left scan hits '/' before '#' and bails out.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo#123/bar"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("ns/foo#123/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

void test_name_resolve_empty_after_pin_strip_fails()
{
    // "#N" with no namespace: name is empty after pin stripping -> rejected.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    r = cy_name_resolve(nullptr, cy_str("#1234"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);

    r = cy_name_resolve(nullptr, cy_str("#0"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
}

void test_name_resolve_pin_on_absolute_and_homeful()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    // Absolute name with pin: "/foo#100" -> strip pin -> "/foo" -> normalize -> "foo", pin=100.
    r = cy_name_resolve(nullptr, cy_str("/foo#100"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(100, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // Homeful name with pin: "~/bar#0" -> strip pin -> "~/bar" -> expand home -> "me/bar", pin=0.
    r = cy_name_resolve(nullptr, cy_str("~/bar#0"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("me/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(0, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // Relative name with empty namespace and home: "foo#123" -> strip pin -> "foo", pin=123.
    r = cy_name_resolve(nullptr, cy_str("foo#123"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("foo", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(123, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

// =====================================================================================================================
//                                               Constants
// =====================================================================================================================

void test_name_join_sep_overflow_after_left()
{
    // Buffer too small to fit left + separator + right.
    // "a" + "b" needs 3 bytes ("a/b"). Buffer of size 2 triggers the overflow check.
    std::array<char, 2> buf{};
    const cy_str_t      result = cy_name_join(cy_str("a"), cy_str("b"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_resolve_non_homeful_passthrough()
{
    // Exercise the relative non-homeful namespace branch and the absolute branch end-to-end.
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("foo/bar"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(10, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ns/foo/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);

    // Also test with an absolute name that is NOT homeful -- goes through name_normalize directly.
    const cy_resolved_t r2 =
      cy_name_resolve(nullptr, cy_str("/abs/path"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r2.name.str);
    TEST_ASSERT_EQUAL_STRING_LEN("abs/path", r2.name.str, r2.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r2.pin);
    TEST_ASSERT_TRUE(r2.verbatim);
}

void test_name_constants()
{
    TEST_ASSERT_EQUAL_CHAR('/', cy_name_sep);
    TEST_ASSERT_EQUAL_CHAR('~', cy_name_home);
    TEST_ASSERT_EQUAL_CHAR('*', cy_name_one);
    TEST_ASSERT_EQUAL_CHAR('>', cy_name_any);
    TEST_ASSERT_EQUAL_CHAR('#', cy_name_pin_prefix);
}

/// cy_name_join where left fills to exactly (dest_size - 1) characters.
/// The separator needs one more byte; with right non-empty, the result should fit if there is room.
/// This targets the separator overflow check in cy_name_join (line 5014).
void test_name_join_left_one_short_of_buffer()
{
    // Buffer of 3, left = "ab" (normalizes to 2 = dest_size-1), right = empty.
    // Left + empty right = "ab" (2 chars). Should succeed since right is empty, separator stripped.
    std::array<char, 3> buf{};
    cy_str_t            result = cy_name_join(cy_str("ab"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(2, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("ab", result.str, result.len);

    // Buffer of 3, left = "ab" (2), right = "c" (1). Total = "ab/c" = 4 > 3. Should fail.
    result = cy_name_join(cy_str("ab"), cy_str("c"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

/// cy_name_resolve with NULL dest pointer -- covers the public API argument validation.
void test_name_resolve_null_dest_ptr()
{
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("foo"), cy_str("ns"), cy_str("me"), 100, nullptr);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, r.name.len);
    TEST_ASSERT_NULL(r.name.str);
}

/// cy_name_resolve with a homeful namespace.
/// The namespace is "~", which expands to home "me". Then the name "bar" is joined: "me/bar".
void test_name_resolve_homeful_namespace_expanded()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("bar"), cy_str("~"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(6, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/bar", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

/// cy_name_resolve with a homeful namespace and an empty relative name.
/// This exercises the second cy_name_join() in the homeful-namespace branch with an empty right part.
void test_name_resolve_homeful_namespace_empty_name()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str(""), cy_str("~/ns"), cy_str("me"), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(5U, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("me/ns", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

/// cy_name_join with zero dest_size -- left is non-empty but buffer is zero-sized.
/// name_normalize would return SIZE_MAX (invalid) because there is no room even for a single char.
void test_name_join_zero_dest_size()
{
    char     dummy  = 'x';
    cy_str_t result = cy_name_join(cy_str("a"), cy_str("b"), 0, &dummy);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);

    // Also try with empty inputs -- should produce empty result even with zero-size buffer.
    result = cy_name_join(cy_str(""), cy_str(""), 0, &dummy);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
}

/// cy_name_join with buffer of size 1 -- just enough for one character.
/// name_normalize("a", dest_size=1) produces len=1, which is >= dest_size=1 in the left check, so left "a" fails.
/// But empty left + "a" right works since the right part has dest_size=1 which can hold "a" (len=1, and 1 > 1 = false).
void test_name_join_buffer_size_one()
{
    std::array<char, 1> buf{};
    // Left="a" normalizes to len=1, 1 >= 1 = true => str_invalid.
    cy_str_t result = cy_name_join(cy_str("a"), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);

    // Empty left + "a" right: left normalizes to 0, right normalizes to 1. 1 > (1-0) = false => ok, len=1.
    result = cy_name_join(cy_str(""), cy_str("a"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(1, result.len);
    TEST_ASSERT_EQUAL_STRING_LEN("a", result.str, result.len);

    // Empty left + empty right: size is 0, which should succeed.
    result = cy_name_join(cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(0, result.len);

    // Left="a" right="b": "a" fills buffer, no room for separator. Fails.
    result = cy_name_join(cy_str("a"), cy_str("b"), buf.size(), buf.data());
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, result.len);
    TEST_ASSERT_NULL(result.str);
}

void test_name_resolve_can_compat_1234_hash_1234()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(nullptr, cy_str("1234#1234"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NOT_NULL(r.name.str);
    TEST_ASSERT_EQUAL_size_t(4, r.name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("1234", r.name.str, r.name.len);
    TEST_ASSERT_EQUAL_UINT16(1234, r.pin);
    TEST_ASSERT_TRUE(r.verbatim);
}

// =====================================================================================================================
//                                              cy_name_resolve -- remap
// =====================================================================================================================

// A wkv-compatible allocator backed by libc for the name-resolve remap tests; no live cy_t is involved.
void* test_wkv_realloc(wkv_t* /*self*/, void* const ptr, const size_t new_size)
{
    if (new_size == 0U) {
        std::free(ptr); // NOLINT(hicpp-no-malloc,cppcoreguidelines-no-malloc)
        return nullptr;
    }
    return std::realloc(ptr, new_size); // NOLINT(hicpp-no-malloc,cppcoreguidelines-no-malloc)
}

// RAII helper that owns a wkv_t remap built from a list of literal {from, to} pairs.
// The `to` strings point at static string literals supplied by the caller, so no value ownership is needed;
// the destructor only needs to prune the trie via wkv_del.
struct RemapFixture
{
    wkv_t kv{};
    RemapFixture(const std::initializer_list<std::pair<const char*, const char*>> entries)
    {
        wkv_init(&kv, &test_wkv_realloc);
        for (const auto& e : entries) {
            wkv_node_t* const node = wkv_set(&kv, cy_str(e.first));
            TEST_ASSERT_NOT_NULL(node);
            // NOLINTNEXTLINE(cppcoreguidelines-pro-type-const-cast)
            node->value = const_cast<char*>(e.second);
        }
    }
    ~RemapFixture()
    {
        while (!wkv_is_empty(&kv)) {
            wkv_del(&kv, wkv_at(&kv, 0));
        }
    }
    RemapFixture(const RemapFixture&)            = delete;
    RemapFixture(RemapFixture&&)                 = delete;
    RemapFixture& operator=(const RemapFixture&) = delete;
    RemapFixture& operator=(RemapFixture&&)      = delete;
    wkv_t*        get() { return &kv; }
};

// Mirrors test_name_resolve_docstring_examples, but for the "with a remap" table in the cy_name_resolve
// docstring (cy.h). Every row of that table is exercised here in docstring order.
void test_name_resolve_docstring_remap_examples()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    cy_resolved_t                           r{};

    // foo/bar foo/bar zoo     ns me ns/zoo  -   relative remap
    {
        RemapFixture remap{ { "foo/bar", "zoo" } };
        r = cy_name_resolve(remap.get(), cy_str("foo/bar"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
        assert_resolved(r, "ns/zoo", UINT16_MAX, true);
    }

    // foo/bar foo/bar zoo#123 ns me ns/zoo  123 pinned relative remap
    {
        RemapFixture remap{ { "foo/bar", "zoo#123" } };
        r = cy_name_resolve(remap.get(), cy_str("foo/bar"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
        assert_resolved(r, "ns/zoo", 123, true);
    }

    // foo/bar#456 foo/bar zoo  ns me ns/zoo  -   matched rule discards user pin
    {
        RemapFixture remap{ { "foo/bar", "zoo" } };
        r = cy_name_resolve(remap.get(), cy_str("foo/bar#456"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
        assert_resolved(r, "ns/zoo", UINT16_MAX, true);
    }

    // foo/bar foo/bar /zoo    ns me zoo     -   absolute remap (ns ignored)
    {
        RemapFixture remap{ { "foo/bar", "/zoo" } };
        r = cy_name_resolve(remap.get(), cy_str("foo/bar"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
        assert_resolved(r, "zoo", UINT16_MAX, true);
    }

    // foo/bar foo/bar ~/zoo   ns me me/zoo  -   homeful remap (home expanded)
    {
        RemapFixture remap{ { "foo/bar", "~/zoo" } };
        r = cy_name_resolve(remap.get(), cy_str("foo/bar"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
        assert_resolved(r, "me/zoo", UINT16_MAX, true);
    }
}

// ----- Basic sanity / no-op cases -----

void test_name_resolve_remap_null_is_noop()
{
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(nullptr, cy_str("a/b/c"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "a/b/c", UINT16_MAX, true);
}

void test_name_resolve_remap_empty_wkv_is_noop()
{
    RemapFixture                            remap{};
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(remap.get(), cy_str("a/b/c"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "a/b/c", UINT16_MAX, true);
}

void test_name_resolve_remap_non_matching_query_unchanged()
{
    RemapFixture                            remap{ { "a/b/c", "z" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(remap.get(), cy_str("x/y/z"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "x/y/z", UINT16_MAX, true);
}

// `foo` must NOT match a query like `foobar/baz` — separator-aware lookup, not substring.
void test_name_resolve_remap_partial_segment_false_match()
{
    RemapFixture                            remap{ { "foo", "z" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(remap.get(), cy_str("foobar/baz"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "foobar/baz", UINT16_MAX, true);
}

// ----- Exact match -----

void test_name_resolve_remap_exact_match()
{
    RemapFixture                            remap{ { "a/b/c", "z" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(remap.get(), cy_str("a/b/c"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "z", UINT16_MAX, true);
}

// An exact rule does NOT match a longer query.
void test_name_resolve_remap_no_prefix_match()
{
    RemapFixture                            remap{ { "a/b/c", "z" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(remap.get(), cy_str("a/b/c/d"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "a/b/c/d", UINT16_MAX, true);
}

// ----- Normalized lookup: integrator's `from` and the user's input both go through name_normalize. -----

void test_name_resolve_remap_normalized_lookup_collapses_dup_seps()
{
    RemapFixture                            remap{ { "foo/bar", "z" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    // The query has duplicate separators, but normalization collapses them to match the stored key.
    const cy_resolved_t r =
      cy_name_resolve(remap.get(), cy_str("foo//bar"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "z", UINT16_MAX, true);
}

void test_name_resolve_remap_normalized_lookup_strips_leading_slash()
{
    RemapFixture                            remap{ { "foo/bar", "z" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    // The query is absolute; both forms normalize to `foo/bar` and match the same rule.
    const cy_resolved_t r =
      cy_name_resolve(remap.get(), cy_str("/foo/bar"), cy_str("ns"), cy_str(""), buf.size(), buf.data());
    // The matched `to` "z" is then resolved as relative (no leading slash) → ns/z.
    assert_resolved(r, "ns/z", UINT16_MAX, true);
}

// ----- `to` resolution: absolute, homeful, relative -----

void test_name_resolve_remap_absolute_to_ignores_namespace()
{
    RemapFixture                            remap{ { "foo", "/zoo" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(remap.get(), cy_str("foo"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    assert_resolved(r, "zoo", UINT16_MAX, true);
}

void test_name_resolve_remap_homeful_to_expands_home()
{
    RemapFixture                            remap{ { "foo", "~/zoo" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(remap.get(), cy_str("foo"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    assert_resolved(r, "me/zoo", UINT16_MAX, true);
}

void test_name_resolve_remap_relative_to_uses_namespace()
{
    RemapFixture                            remap{ { "foo", "zoo" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(remap.get(), cy_str("foo"), cy_str("ns"), cy_str("me"), buf.size(), buf.data());
    assert_resolved(r, "ns/zoo", UINT16_MAX, true);
}

// ----- Pin handling -----

// Canonical use case: the integrator pins a hardcoded unpinned topic via a remap.
void test_name_resolve_remap_pins_via_exact_rule()
{
    RemapFixture                            remap{ { "foo", "foo#123" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(remap.get(), cy_str("foo"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "foo", 123, true);
}

// A remap can rename and pin in one rule.
void test_name_resolve_remap_rename_with_pin()
{
    RemapFixture                            remap{ { "foo", "bar#456" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(remap.get(), cy_str("foo"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "bar", 456, true);
}

// No remap match → user's pin passes through unchanged.
void test_name_resolve_remap_query_pin_passes_through_on_no_match()
{
    RemapFixture                            remap{};
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(remap.get(), cy_str("foo#99"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "foo", 99, true);
}

// Matched rule with pin-free `to` discards the user's pin (per spec: pin honoured only if no rule matched).
void test_name_resolve_remap_pinned_query_pin_discarded_on_match()
{
    RemapFixture                            remap{ { "foo", "bar" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(remap.get(), cy_str("foo#99"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "bar", UINT16_MAX, true);
}

// Matched rule with pinned `to`: the rule's pin wins (and the user's pin is discarded).
void test_name_resolve_remap_to_pin_overrides_user_pin()
{
    RemapFixture                            remap{ { "foo", "bar#42" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t                     r =
      cy_name_resolve(remap.get(), cy_str("foo#99"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "bar", 42, true);
}

// ----- Pattern `to` -----

// A `to` containing wildcards turns a literal subscription into a pattern subscription (verbatim=false).
void test_name_resolve_remap_to_has_wildcard()
{
    RemapFixture                            remap{ { "foo", "foo/*/bar" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(remap.get(), cy_str("foo"), cy_str(""), cy_str(""), buf.size(), buf.data());
    assert_resolved(r, "foo/*/bar", UINT16_MAX, false);
}

// If the post-remap result contains wildcards AND a pin, the pinned-pattern rule rejects it. This case
// bypasses cy_remap's usual validation (which rejects pinned patterns at the `to` side) by populating the
// wkv directly via the RemapFixture, so that we can exercise the final guard inside cy_name_resolve.
void test_name_resolve_remap_post_remap_pattern_with_pin_rejected()
{
    RemapFixture                            remap{ { "foo", "bar/*#42" } };
    std::array<char, CY_TOPIC_NAME_MAX + 1> buf{};
    const cy_resolved_t r = cy_name_resolve(remap.get(), cy_str("foo"), cy_str(""), cy_str(""), buf.size(), buf.data());
    TEST_ASSERT_NULL(r.name.str);
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
    RUN_TEST(test_name_join_empty_null_inputs);
    RUN_TEST(test_name_join_overlap_left_exact_alias);
    RUN_TEST(test_name_join_overlap_right_exact_alias);
    RUN_TEST(test_name_join_overlap_left_exact_alias_normalized);
    RUN_TEST(test_name_join_overlap_right_exact_alias_normalized);
    RUN_TEST(test_name_join_overlap_left_exact_alias_empty_right);
    RUN_TEST(test_name_join_overlap_right_exact_alias_empty_left);
    RUN_TEST(test_name_join_left_one_short_of_buffer);
    RUN_TEST(test_name_join_zero_dest_size);
    RUN_TEST(test_name_join_buffer_size_one);

    // cy_name_resolve -- docstring examples
    RUN_TEST(test_name_resolve_docstring_examples);

    // cy_name_resolve -- pin parsing
    RUN_TEST(test_name_resolve_pin_simple);
    RUN_TEST(test_name_resolve_pin_single_digit);
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
    RUN_TEST(test_name_resolve_homeful_name_with_pin);
    RUN_TEST(test_name_resolve_absolute_name_with_pin);
    RUN_TEST(test_name_resolve_hash_in_namespace_preserved);
    RUN_TEST(test_name_resolve_all_digit_name_no_hash);
    RUN_TEST(test_name_resolve_trailing_hash_no_digits);
    RUN_TEST(test_name_resolve_can_compat_1234_hash_1234);

    // cy_name_resolve -- verbatim
    RUN_TEST(test_name_resolve_verbatim_simple);
    RUN_TEST(test_name_resolve_pattern_star);
    RUN_TEST(test_name_resolve_pattern_any);
    RUN_TEST(test_name_resolve_wildcard_inside_segment_is_verbatim);
    RUN_TEST(test_name_resolve_verbatim_pin_accepted);

    // cy_name_resolve -- error handling
    RUN_TEST(test_name_resolve_null_dest);
    RUN_TEST(test_name_resolve_accepts_empty_null_namespace_and_home);
    RUN_TEST(test_name_resolve_rejects_malformed_name_arguments);
    RUN_TEST(test_name_resolve_empty_null_name_is_empty_and_invalid);
    RUN_TEST(test_name_resolve_buffer_too_small);
    RUN_TEST(test_name_resolve_homeful_namespace_expand_fails);
    RUN_TEST(test_name_resolve_absolute_ignores_invalid_namespace_and_home);
    RUN_TEST(test_name_resolve_homeful_name_ignores_invalid_namespace);
    RUN_TEST(test_name_resolve_relative_non_homeful_ignores_invalid_home);
    RUN_TEST(test_name_resolve_relative_non_homeful_rejects_invalid_namespace);
    RUN_TEST(test_name_resolve_homeful_name_rejects_invalid_home);
    RUN_TEST(test_name_resolve_homeful_namespace_rejects_invalid_home);
    RUN_TEST(test_name_resolve_homeful_namespace_rejects_invalid_namespace_tail);
    RUN_TEST(test_name_resolve_exceeds_topic_name_max);
    RUN_TEST(test_name_resolve_exactly_at_topic_name_max);
    RUN_TEST(test_name_resolve_invalid_char);
    RUN_TEST(test_name_resolve_valid_printable_chars);

    // cy_name_resolve -- docstring negative examples
    RUN_TEST(test_name_resolve_rejects_space_and_nonprintable);
    RUN_TEST(test_name_resolve_rejects_pattern_with_pin);
    RUN_TEST(test_name_resolve_rejects_empty_name);
    RUN_TEST(test_name_resolve_rejects_empty_normalized_name);
    RUN_TEST(test_name_resolve_rejects_empty_pinned_name);
    RUN_TEST(test_name_resolve_rejects_empty_normalized_pinned_name);
    RUN_TEST(test_name_resolve_rejects_name_exceeding_max_length);

    // cy_name_resolve -- edge cases
    RUN_TEST(test_name_resolve_separator_only);
    RUN_TEST(test_name_resolve_tilde_only);
    RUN_TEST(test_name_resolve_tilde_with_empty_home);
    RUN_TEST(test_name_resolve_homeful_with_slashes);
    RUN_TEST(test_name_resolve_absolute_tilde_literal);
    RUN_TEST(test_name_resolve_absolute_ignores_namespace_and_home);
    RUN_TEST(test_name_resolve_tilde_not_followed_by_separator);
    RUN_TEST(test_name_resolve_homeful_bare_pin);
    RUN_TEST(test_name_resolve_absolute_bare_pin);
    RUN_TEST(test_name_resolve_homeful_trailing_sep);
    RUN_TEST(test_name_resolve_empty_namespace);
    RUN_TEST(test_name_resolve_empty_name_with_namespace);
    RUN_TEST(test_name_resolve_empty_name_empty_ns);
    RUN_TEST(test_name_resolve_pin_stripped_before_length_check);

    // cy_name_resolve -- pin + normalization interaction
    RUN_TEST(test_name_resolve_pin_trailing_sep_removed);
    RUN_TEST(test_name_resolve_pin_duplicate_seps_collapsed);
    RUN_TEST(test_name_resolve_pin_with_path_segment);
    RUN_TEST(test_name_resolve_pin_absolute_leading_sep_removed);
    RUN_TEST(test_name_resolve_pin_absolute_all_redundant_seps);
    RUN_TEST(test_name_resolve_pin_on_absolute_with_redundant_seps);

    // cy_name_resolve -- pin edge cases with pinning
    RUN_TEST(test_name_resolve_pin_at_name_max_boundary);
    RUN_TEST(test_name_resolve_pin_exceeding_max_is_literal);
    RUN_TEST(test_name_resolve_pin_uint16_overflow_regression);
    RUN_TEST(test_name_resolve_pin_mid_name_not_stripped);
    RUN_TEST(test_name_resolve_empty_after_pin_strip_fails);
    RUN_TEST(test_name_resolve_pin_on_absolute_and_homeful);

    // Buffer edge cases
    RUN_TEST(test_name_join_sep_overflow_after_left);
    RUN_TEST(test_name_resolve_non_homeful_passthrough);

    // Additional resolve tests
    RUN_TEST(test_name_resolve_null_dest_ptr);
    RUN_TEST(test_name_resolve_homeful_namespace_expanded);
    RUN_TEST(test_name_resolve_homeful_namespace_empty_name);

    // cy_name_resolve -- remap
    RUN_TEST(test_name_resolve_docstring_remap_examples);
    RUN_TEST(test_name_resolve_remap_null_is_noop);
    RUN_TEST(test_name_resolve_remap_empty_wkv_is_noop);
    RUN_TEST(test_name_resolve_remap_non_matching_query_unchanged);
    RUN_TEST(test_name_resolve_remap_partial_segment_false_match);
    RUN_TEST(test_name_resolve_remap_exact_match);
    RUN_TEST(test_name_resolve_remap_no_prefix_match);
    RUN_TEST(test_name_resolve_remap_normalized_lookup_collapses_dup_seps);
    RUN_TEST(test_name_resolve_remap_normalized_lookup_strips_leading_slash);
    RUN_TEST(test_name_resolve_remap_absolute_to_ignores_namespace);
    RUN_TEST(test_name_resolve_remap_homeful_to_expands_home);
    RUN_TEST(test_name_resolve_remap_relative_to_uses_namespace);
    RUN_TEST(test_name_resolve_remap_pins_via_exact_rule);
    RUN_TEST(test_name_resolve_remap_rename_with_pin);
    RUN_TEST(test_name_resolve_remap_query_pin_passes_through_on_no_match);
    RUN_TEST(test_name_resolve_remap_pinned_query_pin_discarded_on_match);
    RUN_TEST(test_name_resolve_remap_to_pin_overrides_user_pin);
    RUN_TEST(test_name_resolve_remap_to_has_wildcard);
    RUN_TEST(test_name_resolve_remap_post_remap_pattern_with_pin_rejected);

    // Constants
    RUN_TEST(test_name_constants);

    return UNITY_END();
}
