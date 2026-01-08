#pragma once

#include "rapidhash.h"
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>

#define KILO 1000L
#define MEGA (KILO * 1LL * KILO)

/// Generates a new random locally administered unicast EUI-64 identifier suitable for use as a 64-bit Cyphal node-ID.
/// Returns zero on failure, which is not a valid EUI-64.
///
/// For node identification convenience, a few of the most significant bits are the same for nodes running on the same
/// host, while the least significant bits are random. The random part is much wider to avoid collisions among nodes
/// running on the same host. Collisions of the host part are harmless because the protocol doesn't really care
/// about the UID structure -- the only issue is that diagnostics may become slightly ambiguous.
static inline uint64_t volatile_eui64(void)
{
    uint32_t host_20 = 0; // 2 of these bits are used for EUI-64 flags, 18 bits remain. These are first 5 hex digits.
    uint64_t rand_44 = 0; // The remaining 44 random bits, which are the last 11 hex digits.
#ifdef __linux__
    {
        const int fd = open("/etc/machine-id", O_RDONLY);
        if (fd < 0) {
            return 0;
        }
        char          buf[64];
        const ssize_t n = read(fd, buf, sizeof(buf));
        close(fd);
        if (n < 32) { // min required size
            return 0;
        }
        host_20 = (uint32_t)(rapidhash(buf, (size_t)n) & 0xFFFFFU);
    }
    {
        const int fd = open("/dev/urandom", O_RDONLY);
        if (fd < 0) {
            return 0;
        }
        if (read(fd, &rand_44, sizeof(rand_44)) != sizeof(rand_44)) {
            close(fd);
            return 0;
        }
        close(fd);
    }
#else
#error "volatile_eui64() is not implemented for this platform yet."
#endif
    uint64_t out = (((uint64_t)host_20) << 44U) | (rand_44 & ((1ULL << 44U) - 1U));
    out &= ~(1ULL << 56U); // clear bit I/G (unicast)
    out |= (1ULL << 57U);  // set bit U/L (locally administered)
    return out;
}
