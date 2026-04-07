/// A simple helper that constructs a cy_platform_t instance based on the command-line arguments.

#pragma once

#include <cy.h>
#include <cy_can_socketcan.h>
#include <cy_udp_posix.h>
#include <eui64.h>

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/// Stores the platform instance constructed through parsing the argv and the corresponding destructor.
typedef struct example_platform_t
{
    cy_platform_t* platform;
    void (*destroy)(cy_platform_t*); ///< Invoke this to dispose the platform instance.
} example_platform_t;

/// The returned string reference is valid until the next invocation.
static inline cy_str_t example_platform_home(void)
{
#if defined(__cplusplus) || (defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 202311L))
    thread_local
#elif defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 201112L)
    _Thread_local
#endif
      static char  home_storage[CY_TOPIC_NAME_MAX + 1U];
    const uint64_t uid     = eui64_semirandom();
    const int      written = snprintf(home_storage, sizeof(home_storage), "%016llx", (unsigned long long)uid);
    if ((uid == 0U) || (written <= 0) || ((size_t)written >= sizeof(home_storage))) {
        return (cy_str_t){ .len = 0, .str = NULL };
    }
    return (cy_str_t){ .len = (size_t)written, .str = home_storage };
}

/// The returned string reference is valid until the environment is modified, otherwise static.
static inline cy_str_t example_platform_namespace(void) { return cy_str(getenv("CYPHAL_NAMESPACE")); }

/// Consumes the argv elements starting with `iface=` and constructs the appropriate platform instance.
/// The argc/argv will be modified in-place to remove the consumed arguments.
/// Returns platform=NULL if the arguments are invalid.
static inline example_platform_t example_platform_make(int* const argc, char** argv)
{
    example_platform_t out = { 0 };
    if ((argc == NULL) || (*argc <= 0) || (argv == NULL)) {
        (void)fprintf(stderr, "Invalid argv\n");
        return out;
    }

    uint32_t    udp_iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX] = { 0 };
    const char* can_iface_name[CANARD_IFACE_COUNT]              = { 0 };
    size_t      iface_count                                     = 0U;
    bool        use_udp                                         = false;
    bool        use_can                                         = false;
    int         dst                                             = 1;
    for (int src = 1; src < *argc; src++) {
        char* const arg = argv[src];
        if ((arg != NULL) && (strncmp(arg, "iface=", 6) == 0)) {
            const char* const spec = arg + 6;
            if (spec[0] == '\0') {
                (void)fprintf(stderr, "iface= requires a value\n");
                return out;
            }
            if (strncmp(spec, "socketcan:", 10) == 0) {
                const char* const name = spec + 10;
                if (name[0] == '\0') {
                    (void)fprintf(stderr, "SocketCAN iface name is empty: %s\n", arg);
                    return out;
                }
                if (use_udp) {
                    (void)fprintf(stderr, "Mixed UDP and SocketCAN iface specs are not supported\n");
                    return out;
                }
                if (iface_count >= CANARD_IFACE_COUNT) {
                    (void)fprintf(stderr, "Too many SocketCAN ifaces, limit is %u\n", CANARD_IFACE_COUNT);
                    return out;
                }
                for (size_t i = 0; i < iface_count; i++) {
                    if ((can_iface_name[i] != NULL) && (strcmp(can_iface_name[i], name) == 0)) {
                        (void)fprintf(stderr, "Duplicate SocketCAN iface: %s\n", name);
                        return out;
                    }
                }
                can_iface_name[iface_count++] = name;
                use_can                       = true;
            } else {
                const uint32_t addr = cy_udp_parse_iface_address(spec);
                if (addr == 0U) {
                    (void)fprintf(stderr, "Invalid iface spec: %s\n", arg);
                    return out;
                }
                if (use_can) {
                    (void)fprintf(stderr, "Mixed UDP and SocketCAN iface specs are not supported\n");
                    return out;
                }
                if (iface_count >= CY_UDP_POSIX_IFACE_COUNT_MAX) {
                    (void)fprintf(stderr, "Too many UDP ifaces, limit is %u\n", (unsigned)CY_UDP_POSIX_IFACE_COUNT_MAX);
                    return out;
                }
                for (size_t i = 0; i < iface_count; i++) {
                    if (udp_iface_address[i] == addr) {
                        (void)fprintf(stderr, "Duplicate UDP iface: %s\n", spec);
                        return out;
                    }
                }
                udp_iface_address[iface_count++] = addr;
                use_udp                          = true;
            }
        } else {
            argv[dst++] = argv[src];
        }
    }
    argv[dst] = NULL;
    *argc     = dst;

    if (use_can) {
        out.platform = cy_can_socketcan_new((uint_least8_t)iface_count, can_iface_name, 1000U);
        out.destroy  = cy_can_socketcan_destroy;
    } else if (use_udp) {
        const uint64_t uid = eui64_semirandom();
        if (uid == 0U) {
            (void)fprintf(stderr, "eui64_semirandom\n");
            return out;
        }
        out.platform = cy_udp_posix_new_manual(uid, udp_iface_address, 50000U);
        out.destroy  = cy_udp_posix_destroy;
    } else {
        out.platform = cy_udp_posix_new();
        out.destroy  = cy_udp_posix_destroy;
    }
    if (out.platform == NULL) {
        (void)fprintf(stderr, "platform factory failure\n");
        return out;
    }
    return out;
}
