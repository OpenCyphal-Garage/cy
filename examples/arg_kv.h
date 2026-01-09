#pragma once

#include "rapidhash.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

/// The pointed strings have a static lifetime.
typedef struct arg_kv_t
{
    size_t      index;    ///< Argument index, where 0 is the program name.
    const char* key;      ///< NULL key indicates that no more arguments are available.
    uint64_t    key_hash; ///< arg_kv_hash(key); 0 if no key.
    const char* value;    ///< NULL unless the argument matches "key=value". May be empty if "key=".
} arg_kv_t;

static inline uint64_t arg_kv_hash(const char* const s) { return rapidhash(s, strlen(s)); }

/// Returns the next argument key/value pair at every invocation. Returns NULL key when there are no more arguments.
/// Invokes exit(1) with a message if the arguments are malformed. The argv array past the zeroth index may be mutated.
static inline arg_kv_t arg_kv_next(const int argc, char* const argv[])
{
    if (argc <= 1) {
        (void)fprintf(stderr,
                      "Usage:\n\t%s key1[=value1] [key2[=value2] ...]\n"
                      "No spaces around '=' are allowed.",
                      argv[0]);
        exit(1);
    }
    static size_t index = 1;
    arg_kv_t      out   = { .index = index++, .key = NULL, .key_hash = 0, .value = NULL };
    if (((int)out.index) < argc) {
        out.key       = argv[out.index];
        char* const q = strchr(out.key, '=');
        if (q != NULL) {
            *q        = '\0';
            out.value = q + 1;
        }
        out.key_hash = arg_kv_hash(out.key);
    }
    return out;
}
