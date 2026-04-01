#include <cy.h>
#include <cy_udp_posix.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>

#define MEGA 1000000LL

#define RESPONSE_TIMEOUT (30 * MEGA)
#define PATH_MAX_LEN     2048
#define DATA_MAX         4096

typedef struct file_read_request_t
{
    uint64_t read_offset;
    uint16_t path_len;
    char     path[PATH_MAX_LEN];
} file_read_request_t;

typedef struct file_read_response_t
{
    uint32_t error;
    uint16_t data_len;
    uint8_t  data[DATA_MAX];
} file_read_response_t;

// Command line arguments: file name.
// The read file will be written into stdout as-is.
int main(const int argc, const char* const argv[])
{
    if (argc < 2) {
        (void)fprintf(stderr, "Usage: %s <file>\n", argv[0]);
        return 1;
    }

    // PREPARE THE FILE REQUEST OBJECT.
    file_read_request_t req;
    req.read_offset = 0;
    req.path_len    = (uint16_t)strlen(argv[1]);
    if (req.path_len > PATH_MAX_LEN) {
        (void)fprintf(stderr, "File path length %u is too long\n", req.path_len);
        return 1;
    }
    memcpy(req.path, argv[1], req.path_len);

    // SET UP THE NODE.
    cy_platform_t* const platform = cy_udp_posix_new();
    if (platform == NULL) {
        (void)fprintf(stderr, "cy_udp_posix_new\n");
        return 1;
    }
    cy_t* const cy = cy_new(platform, cy_udp_posix_home(platform, "udp_file_client"), cy_udp_posix_namespace());
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
    while (true) {
        const cy_us_t now = cy_now(cy);

        // Send the request.
        (void)fprintf(stderr, "\nRequesting offset %lu...\n", (unsigned long)req.read_offset);
        cy_future_t* const future = cy_request(pub_file_read,
                                               now + (RESPONSE_TIMEOUT / 2),
                                               RESPONSE_TIMEOUT,
                                               (cy_bytes_t){ .size = 8 + 2 + req.path_len, .data = &req });
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
        (void)fprintf(stderr, "Received response: offset %lu\n", (unsigned long)req.read_offset);
        file_read_response_t resp;
        const size_t         resp_size = cy_message_read(response.message.content, 0, sizeof(resp), &resp);
        cy_message_refcount_dec(response.message.content);
        if (resp_size < 6) {
            (void)fprintf(stderr, "Invalid response size %zu\n", resp_size);
            return 1;
        }
        if (resp.error != 0) {
            (void)fprintf(stderr, "Remote error: %u\n", resp.error);
            return 1;
        }
        if (resp.data_len > 0) {
            (void)fwrite(resp.data, 1, resp.data_len, stdout);
            (void)fflush(stdout);
            req.read_offset += resp.data_len;
        } else {
            (void)fprintf(stderr, "\nFinished transferring %llu bytes\n", (unsigned long long)req.read_offset);
            break;
        }
    }
    return 0;
}
