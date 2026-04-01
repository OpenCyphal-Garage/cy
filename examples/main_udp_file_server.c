#include <cy.h>
#include <cy_udp_posix.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <errno.h>

#define MEGA 1000000LL

#define PATH_MAX_LEN 2048
#define DATA_MAX     4096

// Request schema:
//     uint64           read_offset
//     utf8[<=PATH_MAX] file_path
// Response schema:
//     uint32           errno
//     byte[<=DATA_MAX] data
static void on_file_read_msg(cy_future_t* const subscriber)
{
    if (!cy_future_done(subscriber)) {
        (void)fprintf(stderr, "subscriber error: %d\n", cy_future_error(subscriber));
        return;
    }
    cy_arrival_t arv = cy_arrival_move(subscriber);
    if (arv.message.content == NULL) {
        return;
    }

    // Deserialize the payload, assuming the local machine is little-endian, for simplicity.
    uint64_t read_offset = 0;
    uint16_t path_len    = 0;
    char     file_name[PATH_MAX_LEN + 1];
    if ((8 != cy_message_read(arv.message.content, 0, 8, &read_offset)) ||
        (2 != cy_message_read(arv.message.content, 8, 2, &path_len)) || (path_len == 0) || (path_len > PATH_MAX_LEN) ||
        (path_len != cy_message_read(arv.message.content, 10, path_len, file_name))) {
        (void)fprintf(stderr, "Malformed request of size %zu\n", cy_message_size(arv.message.content));
        cy_message_refcount_dec(arv.message.content);
        return;
    }
    file_name[path_len] = '\0';

    // Prepare response buffer.
    struct response_t
    {
        uint32_t error;
        uint16_t data_len;
        uint8_t  data[DATA_MAX];
    } response;
    response.data_len = 0;

    // Read the file at the specified offset.
    errno            = 0;
    FILE* const file = fopen(file_name, "rb");
    if ((file != NULL) && (fseek(file, (long)read_offset, SEEK_SET) == 0)) {
        response.data_len = (uint16_t)fread(response.data, 1, DATA_MAX, file);
    }
    response.error = (uint32_t)errno;
    if (file != NULL) {
        (void)fclose(file);
    }

    // Send the response back to the client using reliable delivery.
    (void)fprintf(stderr,
                  "Responding: file='%s' offset=%lu size=%lu error=%u\n",
                  file_name,
                  (unsigned long)read_offset,
                  (unsigned long)response.data_len,
                  response.error);
    cy_future_t* const future =
      cy_respond_reliable(&arv.breadcrumb,
                          arv.message.timestamp + (10 * MEGA),
                          (cy_bytes_t){ .size = 4 + 2 + response.data_len, .data = &response });
    // We want the stack to retransmit until the client acknowledges reception, but we don't care about the result.
    // If we simply destroy the future, the transmission will be cancelled, so instead we set up auto-destruction.
    if (future != NULL) {
        cy_future_callback_set(future, &cy_future_destroy); // Will auto-destroy when done.
    } else {
        (void)fprintf(stderr, "FAILED TO RESPOND\n");
    }
    cy_message_refcount_dec(arv.message.content);
}

int main(void)
{
    cy_platform_t* const platform = cy_udp_posix_new();
    if (platform == NULL) {
        (void)fprintf(stderr, "cy_udp_posix_new\n");
        return 1;
    }
    cy_t* const cy = cy_new(platform, cy_udp_posix_home(platform, "udp_file_server"), cy_udp_posix_namespace());
    if (cy == NULL) {
        (void)fprintf(stderr, "cy_new\n");
        return 1;
    }

    cy_future_t* const sub_file_read = cy_subscribe(cy, cy_str("file/read"), 1024);
    if (sub_file_read == NULL) {
        (void)fprintf(stderr, "cy_subscribe\n");
        return 1;
    }
    cy_future_callback_set(sub_file_read, &on_file_read_msg);

    while (true) {
        const cy_err_t res = cy_spin_once(cy);
        if (res != CY_OK) {
            (void)fprintf(stderr, "cy_spin_once: %d\n", res);
            return 1;
        }
    }
    return 0;
}
