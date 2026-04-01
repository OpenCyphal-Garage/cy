// Publishes the current time every second.

#include <cy.h>
#include <cy_udp_posix.h>

#include <stdio.h>
#include <string.h>
#include <time.h>

#define MEGA 1000000LL

static const char* const topic_name = "demo/time";

static void on_publish(cy_future_t* const future)
{
    const cy_err_t err = cy_future_error(future);
    if (cy_future_done(future)) {
        if (err != CY_OK) {
            (void)fprintf(stderr, "❌ delivery failed: %d\n", err);
        } else {
            (void)fprintf(stderr, "✅ delivered\n");
        }
        cy_future_destroy(future);
    } else {
        (void)fprintf(stderr, "💥 transient error: %d\n", err);
    }
}

int main(void)
{
    cy_platform_t* const platform = cy_udp_posix_new();
    if (platform == NULL) {
        (void)fprintf(stderr, "cy_udp_posix_new\n");
        return 1;
    }
    cy_t* const cy = cy_new(platform, cy_udp_posix_home(platform, "udp_time_pub"), cy_udp_posix_namespace());
    if (cy == NULL) {
        (void)fprintf(stderr, "cy_new\n");
        return 1;
    }

    cy_publisher_t* const pub = cy_advertise(cy, cy_str(topic_name));
    if (pub == NULL) {
        (void)fprintf(stderr, "cy_advertise\n");
        return 1;
    }

    cy_us_t next_publish_at = cy_now(cy);
    while (true) {
        const cy_us_t now = cy_now(cy);
        if (now >= next_publish_at) {
            // Compose the message.
            char                   text[32];
            const time_t           wall_time = time(NULL);
            const struct tm* const tm        = localtime(&wall_time);
            if ((tm == NULL) || (strftime(text, sizeof(text), "%Y-%m-%d %H:%M:%S", tm) == 0U)) {
                strcpy(text, "<time error>");
            }
            const cy_bytes_t message = { .size = strlen(text), .data = text };

            // Publish the message.
            cy_future_t* const future = cy_publish_reliable(pub, now + (3 * MEGA), message);
            if (future == NULL) {
                (void)fprintf(stderr, "cy_publish_reliable\n");
                return 1;
            }
            cy_future_callback_set(future, on_publish);
            next_publish_at += MEGA;
        }

        const cy_err_t err = cy_spin_until(cy, next_publish_at);
        if (err != CY_OK) {
            (void)fprintf(stderr, "cy_spin_until: %d\n", err);
            return 1;
        }
    }
}
