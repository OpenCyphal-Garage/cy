#include <cy.h>

#include "example_platform.h"

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MEGA 1000000LL

#define PATH_MAX_LEN 1024U
#define DATA_MAX     2036U
#define SEEK_MASK    UINT64_C(0x0000FFFFFFFFFFFF)

// zubax.file.Read.0.1, manually serialized for little-endian hosts.
typedef struct file_read_request_t
{
    uint64_t seek_size;
    uint16_t reserved; // cppcheck-suppress unusedStructMember
    uint16_t path_len;
    char     path[PATH_MAX_LEN];
} file_read_request_t;

typedef struct file_read_response_t
{
    uint64_t seek_error_end;
    uint16_t reserved; // cppcheck-suppress unusedStructMember
    uint16_t data_len;
    uint8_t  data[DATA_MAX];
} file_read_response_t;

_Static_assert(offsetof(file_read_request_t, path) == 12U, "");
_Static_assert(offsetof(file_read_response_t, data) == 12U, "");
_Static_assert(sizeof(file_read_response_t) == 2048U, "");

static void future_destroy_when_done(cy_future_t* const future)
{
    if (cy_future_done(future)) {
        cy_future_destroy(future);
    }
}

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

    file_read_request_t req = { 0 };
    char                file_name[PATH_MAX_LEN + 1];
    if ((12U != cy_message_read(arv.message.content, 0, 12U, &req)) || (req.path_len > PATH_MAX_LEN) ||
        (req.path_len != cy_message_read(arv.message.content, 12U, req.path_len, req.path))) {
        (void)fprintf(stderr, "Malformed request of size %zu\n", cy_message_size(arv.message.content));
        cy_message_refcount_dec(arv.message.content);
        return;
    }
    memcpy(file_name, req.path, req.path_len);
    file_name[req.path_len] = '\0';

    const uint64_t       read_offset = req.seek_size & SEEK_MASK;
    file_read_response_t response    = { 0 };

    // Read the file at the specified offset.
    FILE* file = NULL;
    if ((req.seek_size & (UINT64_C(1) << 47U)) != 0U) {
        response.seek_error_end |= UINT64_C(1) << 48U; // error=1 in bits 48..51
    } else {
        response.seek_error_end = read_offset;
        file                    = fopen(file_name, "rb");
        if (file == NULL) {
            response.seek_error_end |= UINT64_C(7) << 48U; // error=7 in bits 48..51
        } else if (fseek(file, (long)read_offset, SEEK_SET) != 0) {
            response.seek_error_end = read_offset | (UINT64_C(1) << 48U); // seek | error=1 << 48
        } else {
            response.seek_error_end = read_offset;
            const size_t read_size  = (size_t)(uint16_t)(req.seek_size >> 48U);
            response.data_len = (uint16_t)fread(response.data, 1, (read_size < DATA_MAX) ? read_size : DATA_MAX, file);
            if (ferror(file)) {
                response.seek_error_end |= UINT64_C(7) << 48U; // error=7 in bits 48..51
            } else if (feof(file)) {
                response.seek_error_end |= UINT64_C(1) << 56U; // end in bit 56
            } else {
                const int next = fgetc(file);
                if (ferror(file)) {
                    response.seek_error_end |= UINT64_C(7) << 48U; // error=7 in bits 48..51
                } else if (next == EOF) {
                    response.seek_error_end |= UINT64_C(1) << 56U; // end in bit 56
                }
            }
        }
    }
    if (file != NULL) {
        (void)fclose(file);
    }

    // Send the response back to the client using reliable delivery.
    (void)fprintf(stderr,
                  "Responding: file='%s' offset=%lu size=%lu error=%u\n",
                  file_name,
                  response.seek_error_end & SEEK_MASK,
                  (unsigned long)response.data_len,
                  (unsigned)((response.seek_error_end >> 48U) & 0xFU));
    cy_future_t* const future = cy_respond_reliable(&arv.breadcrumb,
                                                    arv.message.timestamp + (10 * MEGA),
                                                    (cy_bytes_t){ .size = 12U + response.data_len, .data = &response });
    // We want the stack to retransmit until the client acknowledges reception, but we don't care about the result.
    // If we simply destroy the future, the transmission will be cancelled, so instead we set up auto-destruction.
    if (future != NULL) {
        cy_future_callback_set(future, &future_destroy_when_done);
    } else {
        (void)fprintf(stderr, "FAILED TO RESPOND\n");
    }
    cy_message_refcount_dec(arv.message.content);
}

int main(int argc, char* argv[])
{
    const example_platform_t platform = example_platform_make(&argc, argv);
    if (platform.platform == NULL) {
        return 1;
    }
    cy_t* const cy =
      cy_new(platform.platform, example_platform_home(), example_platform_namespace(), example_platform_remap());
    if (cy == NULL) {
        (void)fprintf(stderr, "cy_new\n");
        return 1;
    }

    cy_future_t* const sub_file_read = cy_subscribe(cy, cy_str("file/read"), 2048U);
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
