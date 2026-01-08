#include "cy_udp_posix.h"
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <stdint.h>
#include <unistd.h>
#include <err.h>

#define MEGA 1000000LL

#define RESPONSE_TIMEOUT (30 * MEGA)
#define PATH_CAPACITY    256

typedef struct file_read_request_t
{
    uint64_t read_offset;
    uint16_t path_len;
    char     path[PATH_CAPACITY];
} file_read_request_t;

typedef struct file_read_response_t
{
    uint32_t error;
    uint16_t data_len;
    uint8_t  data[PATH_CAPACITY];
} file_read_response_t;

typedef struct future_t
{
    bool         done;
    bool         success;
    cy_message_t message;
} future_t;

static void on_response(const cy_user_context_t ctx, cy_message_ts_t* const msg)
{
    future_t* const fut = (future_t* const)ctx.ptr[0];
    assert(!fut->done);
    fut->done    = true;
    fut->success = msg != NULL;
    if (fut->success) {
        fut->message = cy_message_move(&msg->content);
    }
}

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
    if (req.path_len > PATH_CAPACITY) {
        (void)fprintf(stderr, "File path length %u is too long\n", req.path_len);
        return 1;
    }
    memcpy(req.path, argv[1], req.path_len);

    // SET UP THE NODE.
    cy_udp_posix_t cy_udp;
    cy_err_t       res = cy_udp_posix_new_simple(&cy_udp);
    if (res != CY_OK) {
        errx(res, "cy_udp_posix_new_simple");
    }
    cy_t* const cy = &cy_udp.base;

    // SET UP THE FILE READ PUBLISHER.
    cy_publisher_t* const pub_file_read = cy_advertise_client(cy, wkv_key("file/read"), 16 + PATH_CAPACITY);
    if (res != CY_OK) {
        errx(res, "cy_advertise_client");
    }

    // READ THE FILE SEQUENTIALLY.
    while (true) {
        const cy_us_t now = cy_udp_posix_now();

        // Send the request.
        (void)fprintf(stderr, "\nRequesting offset %llu...\n", (unsigned long long)req.read_offset);
        future_t future = { .done = false };
        res             = cy_request(pub_file_read,
                         now + (RESPONSE_TIMEOUT / 2),
                         now + RESPONSE_TIMEOUT,
                         (cy_bytes_t){ .size = 8 + 2 + req.path_len, .data = &req },
                         CY_USER_CONTEXT_EMPTY,
                         cy_delivery_callback_stub,
                         (cy_user_context_t){ .ptr = { &future, NULL, NULL, NULL } },
                         on_response);
        if (res != CY_OK) {
            errx(res, "cy_request");
        }

        // Wait for the response while spinning the event loop.
        // We could do it asynchronously as well, but in this simple application it is easier to do it synchronously.
        // We could also spin the loop in a background thread and use a condition variable to wake up the main thread.
        while (!future.done) {
            res = cy_udp_posix_spin_once(&cy_udp);
            if (res != CY_OK) {
                errx(res, "cy_udp_posix_spin_once");
            }
        }
        if (!future.success) {
            errx(0, "Request timed out");
        }

        // Process the next chunk.
        CY_TRACE(cy, "Received response: offset %llu", (unsigned long long)req.read_offset);
        file_read_response_t resp;
        const size_t         resp_size = cy_message_read(&future.message, 0, sizeof(resp), &resp);
        cy_message_destroy(&future.message); // release the memory asap
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
            (void)fprintf(stderr, "\nFinished transferring %llu bytes\n", (unsigned long long)req.read_offset);
            break;
        }
    }
    return 0;
}
