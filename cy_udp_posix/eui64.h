#pragma once

#include "rapidhash.h"
#include <fcntl.h>
#include <unistd.h>
#include <stdint.h>
#if defined(__APPLE__) || defined(__FreeBSD__) || defined(__NetBSD__) || defined(__OpenBSD__)
#include <sys/sysctl.h>
#endif

/// Generates a new random locally administered unicast EUI-64 identifier suitable for use as a 64-bit Cyphal node-ID.
/// Returns zero on failure, which is not a valid EUI-64.
///
/// For node identification convenience, a few of the most significant bits are the same for nodes running on the same
/// host, while the least significant bits are random. The random part is much wider to avoid collisions among nodes
/// running on the same host. Collisions of the host part are more likely but are harmless because the protocol doesn't
/// really care about the UID structure -- the only downside is that diagnostics/logs may become somewhat ambiguous.
static inline uint64_t eui64_semirandom(void)
{
    uint32_t host_20 = 0; // 2 of these bits are used for EUI-64 flags, 18 bits remain. These are first 5 hex digits.
    uint64_t rand_44 = 0; // The remaining 44 random bits, which are the last 11 hex digits.
#ifdef __linux__
    {
        const int fd = open("/etc/machine-id", O_RDONLY);
        if (fd < 0) {
            return 0;
        }
        char          buf[32];
        const ssize_t n = read(fd, buf, sizeof(buf));
        close(fd);
        if (n < 32) {
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
#elif defined(__APPLE__) || defined(__FreeBSD__) || defined(__NetBSD__) || defined(__OpenBSD__)
    {
        // Use sysctl kern.hostid for host identifier
        int      mib[2] = { CTL_KERN, KERN_HOSTID };
        uint32_t hostid = 0;
        size_t   len    = sizeof(hostid);
        if (sysctl(mib, 2, &hostid, &len, NULL, 0) != 0) {
            return 0;
        }
        host_20 = hostid & 0xFFFFFU;
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
#error "eui64_semirandom() is not implemented for this platform yet."
#endif
    uint64_t out = (((uint64_t)host_20) << 44U) | (rand_44 & ((1ULL << 44U) - 1U));
    out &= ~(1ULL << 56U); // clear bit I/G (unicast)
    out |= (1ULL << 57U);  // set bit U/L (locally administered)
    return out;
}
