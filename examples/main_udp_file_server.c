#include "cy_udp_posix.h"
#include <time.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <errno.h>
#include <err.h>

static uint64_t random_uid(void)
{
    const uint16_t vid = UINT16_MAX; // This is the reserved public VID.
    const uint16_t pid = (uint16_t)rand();
    const uint32_t iid = (uint32_t)rand();
    return (((uint64_t)vid) << 48U) | (((uint64_t)pid) << 32U) | iid;
}

/// Request schema:
///     uint64      read_offset
///     utf8[<=256] file_path
/// Response schema:
///     uint32      errno
///     byte[<=256] data
void on_file_read_msg(struct cy_subscription_t* const sub)
{
    assert(sub != NULL);
    struct cy_transfer_owned_t* const transfer = &sub->topic->sub_last_transfer;
    CY_BUFFER_GATHER_ON_STACK(payload, transfer->payload.base)
    if ((payload.size < 10) || (payload.size > (256 + 2 + 8))) {
        CY_TRACE(sub->topic->cy, "Malformed request: Payload size %zu is invalid", payload.size);
        return;
    }
    assert(payload.data != NULL);

    // Deserialize the payload.
    uint64_t read_offset = 0;
    memcpy(&read_offset, payload.data, 8);
    uint16_t path_len = 0;
    memcpy(&path_len, ((const char*)payload.data) + 8, 2);
    char file_name[257];
    if (path_len > 256) {
        CY_TRACE(sub->topic->cy, "Malformed request: File path length %u is too long", path_len);
        return;
    }
    memcpy(file_name, ((const char*)payload.data) + 10, path_len);
    file_name[path_len] = '\0';

    // Prepare response buffer.
    struct response_t
    {
        uint32_t error;
        uint16_t data_len;
        uint8_t  data[256];
    } response;
    response.data_len = 0;

    // Read the file, 256 bytes max, at the specified offset.
    errno            = 0;
    FILE* const file = fopen(file_name, "rb");
    if ((file != NULL) && (fseek(file, (long)read_offset, SEEK_SET) == 0)) {
        response.data_len = (uint16_t)fread(response.data, 1, 256, file);
    }
    response.error = (uint32_t)errno;
    (void)fclose(file);

    // Send the response.
    CY_TRACE(sub->topic->cy,
             "Responding to file read request: %s, offset %llu, size %u, error %u",
             file_name,
             (unsigned long long)read_offset,
             response.data_len,
             response.error);
    (void)cy_respond(sub->topic, //
                     transfer->timestamp + 1000000,
                     transfer->metadata,
                     (struct cy_buffer_borrowed_t){ .view = { .data = &response, .size = response.data_len + 6 } });
}

/// The only command line argument is the node namespace.
int main(const int argc, char* argv[])
{
    srand((unsigned)time(NULL));

    // SET UP THE NODE. This is the only platform-specific part; the rest is platform- and transport-agnostic.
    struct cy_udp_posix_t cy_udp;
    cy_err_t              res = cy_udp_posix_new(&cy_udp,
                                    random_uid(),
                                    (argc > 1) ? argv[1] : "~",
                                    (uint32_t[3]){ udp_wrapper_parse_iface_address("127.0.0.1") },
                                    1000);
    if (res < 0) {
        errx(res, "cy_udp_posix_new");
    }
    struct cy_t* const cy = &cy_udp.base;

    // SET UP THE FILE READ TOPIC.
    struct cy_topic_t* const topic_file_read = cy_topic_new(cy, "file/read");
    if (topic_file_read == NULL) {
        errx(0, "cy_udp_topic_new");
    }
    struct cy_subscription_t sub_file_read;
    res = cy_subscribe(topic_file_read, &sub_file_read, 1024, on_file_read_msg);
    if (res < 0) {
        errx(res, "cy_subscribe");
    }

    // SPIN THE EVENT LOOP.
    while (1) {
        res = cy_udp_posix_spin_once(&cy_udp);
        if (res < 0) {
            errx(res, "cy_udp_posix_spin_once");
        }
    }

    return 0;
}
