#include "cy_udp_posix.h"
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <err.h>

#define MEGA 1000000LL

#define RESPONSE_TIMEOUT (30 * MEGA)
#define PATH_MAX         2048
#define DATA_MAX         4096

typedef struct file_read_request_t
{
    uint64_t read_offset;
    uint16_t path_len;
    char     path[PATH_MAX];
} file_read_request_t;

typedef struct file_read_response_t
{
    uint32_t error;
    uint16_t data_len;
    uint8_t  data[DATA_MAX];
} file_read_response_t;

/// Command line arguments: namespace, file name.
/// The read file will be written into stdout as-is.
int main(const int argc, char* argv[])
{
    if (argc < 2) {
        (void)fprintf(stderr, "Usage: %s <file>\n", argv[0]);
        return 1;
    }

    // PREPARE THE FILE REQUEST OBJECT.
    file_read_request_t req;
    req.read_offset = 0;
    req.path_len    = (uint16_t)strlen(argv[1]);
    if (req.path_len > PATH_MAX) {
        (void)fprintf(stderr, "File path length %ju is too long\n", (uintmax_t)req.path_len);
        return 1;
    }
    memcpy(req.path, argv[1], req.path_len);

    // SET UP THE NODE.
    cy_udp_posix_t cy_udp;
    {
        const cy_err_t res = cy_udp_posix_new_simple(&cy_udp);
        if (res != CY_OK) {
            errx(res, "cy_udp_posix_new_simple");
        }
    }
    cy_t* const cy = &cy_udp.base;

    // SET UP THE FILE READ PUBLISHER.
    cy_publisher_t* const pub_file_read = cy_advertise_client(cy, cy_str("file/read"), sizeof(file_read_response_t));
    if (pub_file_read == NULL) {
        errx(0, "cy_advertise_client");
    }

    // READ THE FILE SEQUENTIALLY.
    while (true) {
        const cy_us_t now = cy_udp_posix_now();

        // Send the request.
        (void)fprintf(stderr, "\nRequesting offset %ju...\n", (uintmax_t)req.read_offset);
        cy_future_t* const future = cy_request(pub_file_read,
                                               now + (RESPONSE_TIMEOUT / 2),
                                               now + RESPONSE_TIMEOUT,
                                               (cy_bytes_t){ .size = 8 + 2 + req.path_len, .data = &req });
        if (future == NULL) {
            errx(0, "cy_request");
        }

        // Wait for the response while spinning the event loop.
        // We could also spin the loop in a background thread and use a condition variable to wake up the main thread.
        while (cy_future_status(future) == cy_future_pending) {
            const cy_err_t res = cy_udp_posix_spin_once(&cy_udp);
            if (res != CY_OK) {
                errx(res, "cy_udp_posix_spin_once");
            }
        }

        // Process the response outcome.
        if (cy_future_status(future) == cy_future_failure) {
            errx(0, "Request timed out");
        }
        assert(cy_future_status(future) == cy_future_success);
        cy_request_result_t* const result = cy_future_result(future);
        // We could use the response message directly from the future, but moving it out allows us to release
        // the future memory earlier. Sometimes it may be useful; this is an example of how it can be done.
        cy_message_t message = cy_message_move(&result->response.message.content);
        cy_future_destroy(future); // This must be eventually done for every future.

        // Process the next chunk.
        (void)fprintf(stderr, "Received response: offset %ju\n", (uintmax_t)req.read_offset);
        file_read_response_t resp;
        const size_t         resp_size = cy_message_read(&message, 0, sizeof(resp), &resp);
        cy_message_destroy(&message); // release the memory asap
        if (resp_size < 6) {
            errx(0, "Invalid response size %zu", resp_size);
        }
        if (resp.error != 0) {
            errx((int)resp.error, "Remote error");
        }
        if (resp.data_len > 0) {
            (void)fwrite(resp.data, 1, resp.data_len, stdout);
            (void)fflush(stdout);
            req.read_offset += resp.data_len;
        } else {
            (void)fprintf(stderr, "\nFinished transferring %ju bytes\n", (uintmax_t)req.read_offset);
            break;
        }
    }
    return 0;
}
