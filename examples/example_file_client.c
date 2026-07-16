#include <cy.h>

#include "example_platform.h"

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MEGA 1000000LL

#define RESPONSE_TIMEOUT (30 * MEGA)
#define PATH_MAX_LEN     1024U
#define DATA_MAX         2036U
#define SEEK_MASK        UINT64_C(0x0000FFFFFFFFFFFF)

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

// Command line arguments: file name.
// The read file will be written into stdout as-is.
int main(int argc, char* argv[])
{
    const example_platform_t platform = example_platform_make(&argc, argv);
    if (platform.platform == NULL) {
        return 1;
    }
    if (argc < 2) {
        (void)fprintf(stderr, "Usage: %s [iface=...] <file>\n", argv[0]);
        return 1;
    }

    // PREPARE THE FILE REQUEST OBJECT.
    const size_t path_len = strlen(argv[1]);
    if (path_len > PATH_MAX_LEN) {
        (void)fprintf(stderr, "File path length %zu is too long\n", path_len);
        return 1;
    }
    file_read_request_t req = { .path_len = (uint16_t)path_len };
    memcpy(req.path, argv[1], req.path_len);

    // SET UP THE NODE.
    cy_t* const cy =
      cy_new(platform.platform, example_platform_home(), example_platform_namespace(), example_platform_remap());
    if (cy == NULL) {
        (void)fprintf(stderr, "cy_new\n");
        return 1;
    }

    // SET UP THE FILE READ PUBLISHER.
    cy_publisher_t* const pub_file_read = cy_advertise_client(cy, cy_str("file/read"), sizeof(file_read_response_t));
    if (pub_file_read == NULL) {
        (void)fprintf(stderr, "cy_advertise_client\n");
        return 1;
    }

    // READ THE FILE SEQUENTIALLY.
    // Cyphal also supports streaming, so we could let the server stream responses, but this is an RPC demo.
    // There may be multiple subscribers on a topic (either intentionally or due to a network config error),
    // in which case we may get conflicting responses, so it is a good practice here to check which remote we're
    // processing each response from.
    uint64_t discovered_server_uid = UINT64_MAX;
    uint64_t read_offset           = 0;
    while (true) {
        const cy_us_t now = cy_now(cy);
        req.seek_size     = read_offset | ((uint64_t)DATA_MAX << 48U); // int48 seek | uint16 size << 48

        // Send the request.
        (void)fprintf(stderr, "\nRequesting offset %lu...\n", (unsigned long)read_offset);
        cy_future_t* const future = cy_request(pub_file_read,
                                               now + (RESPONSE_TIMEOUT / 2),
                                               RESPONSE_TIMEOUT,
                                               (cy_bytes_t){ .size = 12U + req.path_len, .data = &req });
        if (future == NULL) {
            (void)fprintf(stderr, "cy_request\n");
            return 1;
        }

        // Wait for the response while spinning the event loop.
        while (!cy_future_done(future)) {
            const cy_err_t res = cy_spin_once(cy);
            if (res != CY_OK) {
                (void)fprintf(stderr, "cy_spin_once: %d\n", res);
                return 1;
            }
        }

        // Process the response outcome.
        if (cy_future_error(future) != CY_OK) {
            (void)fprintf(stderr, "Request failed: %d\n", cy_future_error(future));
            cy_future_destroy(future);
            return 1;
        }
        cy_response_t response = cy_response_move(future);
        cy_future_destroy(future);

        // Make sure we're receiving responses from the correct server, in case the network has multiple.
        // Here we just remember the first server to respond and drop responses from others.
        if ((discovered_server_uid != UINT64_MAX) && (response.remote_id != discovered_server_uid)) {
            (void)fprintf(stderr,
                          "Ignoring response from redundant server %016llx, expected %016llx\n",
                          (unsigned long long)response.remote_id,
                          (unsigned long long)discovered_server_uid);
            cy_message_refcount_dec(response.message.content);
            continue;
        }
        if (discovered_server_uid == UINT64_MAX) {
            discovered_server_uid = response.remote_id;
            (void)fprintf(stderr, "Discovered server UID: %016llx\n", (unsigned long long)discovered_server_uid);
        }

        // Process the next chunk.
        (void)fprintf(stderr, "Received response: offset %lu\n", (unsigned long)read_offset);
        file_read_response_t resp      = { 0 };
        const size_t         resp_size = cy_message_read(response.message.content, 0, sizeof(resp), &resp);
        cy_message_refcount_dec(response.message.content);
        if ((resp_size < 12U) || (resp_size != (12U + resp.data_len)) ||
            ((resp.seek_error_end & SEEK_MASK) != read_offset)) {
            (void)fprintf(stderr, "Invalid response size %zu\n", resp_size);
            return 1;
        }
        const unsigned error = (unsigned)((resp.seek_error_end >> 48U) & 0xFU);
        if (error != 0U) {
            (void)fprintf(stderr, "Remote error: %u\n", error);
            return 1;
        }
        if (resp.data_len > 0) {
            (void)fwrite(resp.data, 1, resp.data_len, stdout);
            (void)fflush(stdout);
            read_offset += resp.data_len;
        }
        if ((resp.seek_error_end & (UINT64_C(1) << 56U)) != 0U) {
            (void)fprintf(stderr, "\nFinished transferring %llu bytes\n", (unsigned long long)read_offset);
            break;
        }
    }
    return 0;
}
