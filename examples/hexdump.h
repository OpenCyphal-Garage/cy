#pragma once

#include <stddef.h>
#include <stdlib.h>
#include <assert.h>
#include <stdint.h>

static inline char hexdump_hex_digit(const unsigned v) { return (v < 10U) ? (char)('0' + v) : (char)('a' + (v - 10U)); }

static inline char* hexdump_hex_size_8(char* const out, size_t v)
{
    for (int i = 7; i >= 0; --i) {
        out[i] = hexdump_hex_digit((unsigned)(v & 0xFU));
        v >>= 4U;
    }
    return out + 8;
}

/// Generates a standard two-pane hexdump of the provided data buffer, with the hex bytes next to the ASCII contents.
/// Returns a malloc()-ed null-terminated string which must be freed by the caller, or NULL on failure.
/// The data may be NULL if size==0.
static inline char* hexdump(const size_t size, const void* const data, const size_t bytes_per_row)
{
    if (((size > 0U) && (data == NULL)) || (bytes_per_row == 0U) || (bytes_per_row > 1024)) {
        return NULL;
    }
    const unsigned char* const bytes = (const unsigned char*)data;
    const size_t               rows  = (size == 0U) ? 1U : ((size + bytes_per_row - 1U) / bytes_per_row);
    const size_t split_extra = (bytes_per_row - 1U) / 8U; // Insert an extra space every 8 bytes for readability.
    // Row length (excluding '\n' and excluding final '\0'):
    // "00000000"(8) + " | "(3) + hex area (3*bpr+split_extra) + "| "(2) + ascii area (bpr) = 13 + 4*bpr + split_extra
    const size_t row_len = 13U + split_extra + (4U * bytes_per_row);
    // Total size including '\n' between rows and final '\0':
    // total = rows*row_len + (rows-1) + 1 = rows*(row_len + 1)
    if (rows > (SIZE_MAX / (row_len + 1U))) {
        return NULL;
    }

    const size_t total_size = rows * (row_len + 1U);
    char* const  out        = (char*)malloc(total_size);
    if (NULL == out) {
        return NULL;
    }

    char*  p      = out;
    size_t offset = 0U;
    for (size_t r = 0U; r < rows; ++r) {
        // Offset
        p    = hexdump_hex_size_8(p, offset);
        *p++ = ' ';
        *p++ = ' ';
        *p++ = ' ';
        offset += bytes_per_row;
        const size_t row_base = r * bytes_per_row;

        // Hex bytes
        for (size_t i = 0U; i < bytes_per_row; ++i) {
            if (((i % 8U) == 0) && (i != 0U)) {
                *p++ = ' ';
            }
            const size_t idx = row_base + i;
            if (idx < size) {
                assert(bytes != NULL);
                const unsigned char b = bytes[idx];
                *p++                  = hexdump_hex_digit(b >> 4U);
                *p++                  = hexdump_hex_digit(b & 0x0FU);
                *p++                  = ' ';
            } else {
                *p++ = ' ';
                *p++ = ' ';
                *p++ = ' ';
            }
        }
        *p++ = ' ';
        *p++ = ' ';

        // ASCII
        for (size_t i = 0U; i < bytes_per_row; ++i) {
            const size_t idx = row_base + i;
            if (idx < size) {
                assert(bytes != NULL);
                const unsigned char b = bytes[idx];
                *p++                  = ((b >= 32U) && (b <= 126U)) ? (char)b : '.';
            } else {
                *p++ = ' ';
            }
        }
        if ((r + 1U) < rows) {
            *p++ = '\n';
        }
        assert((size_t)(p - out) <= total_size);
    }
    assert((size_t)(p - out) == (total_size - 1U));
    *p = '\0';
    return out;
}
