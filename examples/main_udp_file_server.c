#include "cy_udp_posix.h"
#include "util.h"
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <errno.h>
#include <err.h>

/// Request schema:
///     uint64      read_offset
///     utf8[<=256] file_path
/// Response schema:
///     uint32      errno
///     byte[<=256] data
static void on_file_read_msg(const cy_user_context_t user, cy_arrival_t* const arv)
{
    (void)user;
    cy_t* const cy = arv->topic->cy;

    // Deserialize the payload, assuming the local machine is little-endian, for simplicity.
    uint64_t read_offset = 0;
    uint16_t path_len    = 0;
    char     file_name[257];
    if ((8 != cy_message_read(&arv->message.content, 0, 8, &read_offset)) ||
        (2 != cy_message_read(&arv->message.content, 8, 2, &path_len)) || (path_len == 0) || (path_len > 256) ||
        (path_len != cy_message_read(&arv->message.content, 10, path_len, file_name))) {
        CY_TRACE(cy, "Malformed request of size %zu", cy_message_size(arv->message.content));
        return;
    }
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
    if (file != NULL) {
        (void)fclose(file);
    }

    // Send the response.
    CY_TRACE(cy,
             "Responding: file='%s' offset=%llu size=%u error=%u",
             file_name,
             (unsigned long long)read_offset,
             response.data_len,
             response.error);
    (void)cy_respond(arv->responder,
                     arv->message.timestamp + 1000000,
                     (cy_bytes_t){ .size = 4 + 2 + response.data_len, .data = &response },
                     CY_USER_CONTEXT_EMPTY,
                     NULL);
}

int main(void)
{
    cy_udp_posix_t cy_udp;
    cy_err_t       res = cy_udp_posix_new(&cy_udp,
                                    volatile_eui64(),
                                    wkv_key(""),
                                    wkv_key(""),
                                    (uint32_t[3]){ udp_wrapper_parse_iface_address("127.0.0.1") },
                                    1000);
    if (res != CY_OK) {
        errx(res, "cy_udp_posix_new");
    }
    cy_t* const cy = &cy_udp.base;

    cy_subscriber_t* const sub_file_read =
      cy_subscribe(cy, wkv_key("file/read"), 1024, CY_USER_CONTEXT_EMPTY, on_file_read_msg);
    if (sub_file_read == NULL) {
        errx(res, "cy_subscribe");
    }

    while (true) {
        res = cy_udp_posix_spin_once(&cy_udp);
        if (res != CY_OK) {
            errx(res, "cy_udp_posix_spin_once");
        }
    }
    // ReSharper disable once CppDFAUnreachableCode
    return 0;
}
