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

/// Constructs a random locally-administered EUI-64. The collision probability given 1 million of identifiers is ≈10^-7.
static uint64_t random_eui64(void)
{
    uint64_t x = (((uint64_t)rand()) << 32U) | (uint32_t)rand(); // first octet is bits 63..56
    x &= ~(1ULL << 56U);                                         // clear bit I/G (unicast)
    x |= (1ULL << 57U);                                          // set bit U/L (locally administered)
    return x;
}

/// Request schema:
///     uint64      read_offset
///     utf8[<=256] file_path
/// Response schema:
///     uint32      errno
///     byte[<=256] data
static void on_file_read_msg(cy_t* const cy, const cy_arrival_t* const arv)
{
    CY_BUFFER_GATHER_ON_STACK(payload, arv->transfer->payload.base)
    if ((payload.size < 10) || (payload.size > (256 + 2 + 8))) {
        CY_TRACE(cy, "Malformed request: Payload size %zu is invalid", payload.size);
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
        CY_TRACE(cy, "Malformed request: File path length %u is too long", path_len);
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
    CY_TRACE(cy,
             "Responding to file read request [tid=%016llx]: %s, offset %llu, size %u, error %u",
             (unsigned long long)arv->transfer->metadata.transfer_id,
             file_name,
             (unsigned long long)read_offset,
             response.data_len,
             response.error);
    (void)cy_respond(cy,
                     arv->topic, //
                     arv->transfer->timestamp + 1000000,
                     arv->transfer->metadata,
                     (cy_buffer_borrowed_t){ .view = { .data = &response, .size = response.data_len + 6 } });
}

/// The only command line argument is the node namespace.
int main(const int argc, char* argv[])
{
    srand((unsigned)time(NULL));

    // SET UP THE NODE. This is the only platform-specific part; the rest is platform- and transport-agnostic.
    cy_udp_posix_t cy_udp;
    cy_err_t       res = cy_udp_posix_new_c(&cy_udp,
                                      random_eui64(),
                                      (argc > 1) ? argv[1] : "~",
                                      (uint32_t[3]){ udp_wrapper_parse_iface_address("127.0.0.1") },
                                      1000);
    if (res != CY_OK) {
        errx(res, "cy_udp_posix_new");
    }
    cy_t* const cy = &cy_udp.base;

    // SET UP THE FILE READ SUBSCRIBER.
    cy_subscriber_t sub_file_read;
    res = cy_subscribe_c(cy, &sub_file_read, "file/read", 1024, on_file_read_msg);
    if (res != CY_OK) {
        errx(res, "cy_subscribe_c");
    }

    // SPIN THE EVENT LOOP.
    while (1) {
        res = cy_udp_posix_spin_once(&cy_udp);
        if (res != CY_OK) {
            errx(res, "cy_udp_posix_spin_once");
        }
    }

    return 0;
}
