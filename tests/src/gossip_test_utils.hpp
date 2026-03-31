#pragma once

#include <cy_platform.h>
#include <cstddef>
#include <cstring>

namespace gossip_test {

inline std::size_t flatten_fragments(const cy_bytes_t message, unsigned char* const out, const std::size_t out_size)
{
    std::size_t       copied = 0U;
    const cy_bytes_t* frag   = &message;
    while ((frag != nullptr) && (copied < out_size)) {
        if ((frag->size > 0U) && (frag->data != nullptr)) {
            const std::size_t n = ((out_size - copied) < frag->size) ? (out_size - copied) : frag->size;
            std::memcpy(out + copied, frag->data, n);
            copied += n;
        }
        frag = frag->next;
    }
    return copied;
}

} // namespace gossip_test
