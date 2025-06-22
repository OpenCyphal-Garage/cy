#include "cy_udp_posix.h"
#include <time.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <err.h>

#define MEGA 1000000LL

#define RESPONSE_TIMEOUT (3 * MEGA)

struct file_read_request_t
{
    uint64_t read_offset;
    uint16_t path_len;
    char     path[256];
};
struct file_read_response_t
{
    uint32_t error;
    uint16_t data_len;
    uint8_t  data[256];
};

static uint64_t random_uid(void)
{
    const uint16_t vid = UINT16_MAX; // This is the reserved public VID.
    const uint16_t pid = (uint16_t)rand();
    const uint32_t iid = (uint32_t)rand();
    return (((uint64_t)vid) << 48U) | (((uint64_t)pid) << 32U) | iid;
}

/// Command line arguments: namespace, file name.
/// The read file will be written into stdout as-is.
int main(const int argc, char* argv[])
{
    if (argc < 3) {
        fprintf(stderr, "Usage: %s <namespace> <file>\n", argv[0]);
        return 1;
    }
    srand((unsigned)time(NULL));

    // PREPARE THE FILE REQUEST OBJECT.
    struct file_read_request_t req;
    req.read_offset = 0;
    req.path_len    = (uint16_t)strlen(argv[2]);
    if (req.path_len > 256) {
        fprintf(stderr, "File path length %u is too long\n", req.path_len);
        return 1;
    }
    memcpy(req.path, argv[2], req.path_len);

    // SET UP THE NODE. This is the only platform-specific part; the rest is platform- and transport-agnostic.
    cy_udp_posix_t cy_udp;
    cy_err_t       res = cy_udp_posix_new_c(
      &cy_udp, random_uid(), argv[1], (uint32_t[3]){ udp_wrapper_parse_iface_address("127.0.0.1") }, 1000);
    if (res != CY_OK) {
        errx(res, "cy_udp_posix_new");
    }
    cy_t* const cy = &cy_udp.base;

    // SET UP THE FILE READ PUBLISHER.
    cy_publisher_t pub_file_read;
    res = cy_advertise_c(cy, &pub_file_read, "file/read", 1024);
    if (res != CY_OK) {
        errx(res, "cy_advertise_c");
    }

    // WAIT FOR THE NODE TO JOIN THE NETWORK.
    // We consider the node joined when it has a node-ID and there have been no topic conflicts/divergences
    // for some time. This stage can be skipped if we have a configuration hint recovered from nonvolatile storage.
    fprintf(stderr, "Waiting for the node to join the network...\n");
    while (!cy_ready(&cy_udp.base)) {
        res = cy_udp_posix_spin_once(&cy_udp);
        if (res != CY_OK) {
            errx(res, "cy_udp_posix_spin_once");
        }
    }

    // READ THE FILE SEQUENTIALLY.
    while (true) {
        const cy_us_t now = cy_udp_posix_now();

        // Send the request.
        cy_future_t future;
        cy_future_new(&future, NULL, NULL);
        fprintf(stderr, "\nRequesting offset %llu...\n", (unsigned long long)req.read_offset);
        res = cy_publish(cy,
                         &pub_file_read,
                         now + MEGA,
                         (cy_buffer_borrowed_t){ .view = { .size = req.path_len + 10, .data = &req } },
                         now + RESPONSE_TIMEOUT,
                         &future);
        if (res != CY_OK) {
            errx(res, "cy_publish");
        }

        // Wait for the response while spinning the event loop.
        // We could do it asynchronously as well, but in this simple application it is easier to do it synchronously.
        // We could also spin the loop in a background thread and use a condition variable to wake up the main thread.
        assert(future.state == cy_future_pending);
        while (future.state == cy_future_pending) {
            res = cy_udp_posix_spin_once(&cy_udp);
            if (res != CY_OK) {
                errx(res, "cy_udp_posix_spin_once");
            }
        }
        if (future.state == cy_future_response_timeout) {
            errx(0, "Request timed out");
        }
        assert(future.state == cy_future_success);

        // Process the next chunk.
        CY_TRACE(cy,
                 "Received response [rnid=%04x tid=%016llx]: offset %llu",
                 future.last_response.metadata.remote_node_id,
                 (unsigned long long)future.last_response.metadata.transfer_id,
                 (unsigned long long)req.read_offset);
        struct file_read_response_t resp;
        const size_t                resp_size =
          cy_buffer_owned_gather(future.last_response.payload, (cy_bytes_mut_t){ .size = sizeof(resp), .data = &resp });
        if (resp_size < 6) {
            errx(0, "Invalid response size %zu", resp_size);
        }
        if (resp.error != 0) {
            errx((int)resp.error, "Remote error");
        }
        if (resp.data_len > 0) {
            fwrite(resp.data, 1, resp.data_len, stdout);
            fflush(stdout);
            req.read_offset += resp.data_len;
        } else {
            fprintf(stderr, "\nFinished transferring %llu bytes\n", (unsigned long long)req.read_offset);
            break;
        }
    }

    return 0;
}
