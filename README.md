<div align="center">

<img src="https://opencyphal.org/favicon-192.png" width="60px">

<h1>Cyphal v1.1 in C</h1>

_pub/sub without steroids_

[![CI](https://github.com/OpenCyphal-Garage/cy/actions/workflows/main.yml/badge.svg)](https://github.com/OpenCyphal-Garage/cy/actions/workflows/main.yml)
[![Coverage](https://coveralls.io/repos/github/OpenCyphal-Garage/cy/badge.svg)](https://coveralls.io/github/OpenCyphal-Garage/cy)
[![Distributed consensus demo](https://img.shields.io/badge/visualization-gerasim.opencyphal.org-black?color=ff00aa)](https://gerasim.opencyphal.org/)
[![Website](https://img.shields.io/badge/website-opencyphal.org-black?color=1700b3)](https://opencyphal.org/)
[![Forum](https://img.shields.io/discourse/https/forum.opencyphal.org/users.svg?logo=discourse&color=1700b3)](https://forum.opencyphal.org)

</div>

-----

A C implementation of Cyphal v1.1: robust decentralized zero-configuration pub/sub with tunable reliability
and service discovery in only a few thousand lines of straightforward C.
Runs anywhere, including small baremetal MCUs.
The key design goals are simplicity and robustness.

To use the library in your project, simply copy `cy.c`, `cy.h`, and `cy_platform.h` into your source tree,
or add this repository as a submodule.
The following external dependencies are required, all single-header-only:

- [`cavl2.h`](https://github.com/pavel-kirienko/cavl) --- An AVL tree (Pavel Kirienko, MIT license).
- [`wild_key_value.h`](https://github.com/pavel-kirienko/wild_key_value) --- A key-value container with fast pattern
  matching & key routing (Pavel Kirienko, MIT license).
- [`olga_scheduler.h`](https://github.com/Zubax/olga_scheduler) --- A simple event loop (Zubax Robotics, MIT license).
- [`rapidhash.h`](https://github.com/Nicoshev/rapidhash) --- A good 64-bit hash (Nicolas De Carli, BSD 2-clause
  license).

On an embedded system, one may also prefer to use [`o1heap`](https://github.com/pavel-kirienko/o1heap) for memory
management, but this is not a hard dependency -- any allocator will work. O1Heap is the recommended choice for embedded
platforms due to its hard determinism and low fragmentation.

Pick one of the transport/platform glue layers suitable for your application: `cy_can`, `cy_udp_posix`, etc.
The integration instructions are identical: simply copy the C files and add them to your build system.
These components may be moved into dedicated repositories in the future.

🌐 A live demo of the distributed consensus algorithm can be found at <https://gerasim.opencyphal.org>.

For a detailed design overview, refer to `model/`.

## 📚 API crash course

The library offers a very compact API.
It is fully asynchronous/non-blocking; if necessary, synchronous wrappers can be implemented on top of it.

The specifics of setting up a local node depend on the platform and transport used,
unlike the rest of the API, which is entirely platform- and transport-agnostic.

```c++
#include <cy.h>               // platform- and transport-agnostic Cyphal API
#include <cy_udp_posix.h>     // thin low-level glue specific to Cyphal/UDP on POSIX systems; choose one for your setup
#include <cy_can_socketcan.h> // thin low-level glue specific to Cyphal/CAN on SocketCAN; choose one for your setup

int main(void)
{
    // Set up the platform layer that connects Cy to the underlying transport and OS.
    // Here we're using Cyphal/UDP on POSIX as an example.
    cy_platform_t* platform = cy_udp_posix_new();
    if (platform == NULL) { ... }

    // If you need Cyphal/CAN on SocketCAN instead, just replace the above with:
    cy_platform_t* platform = cy_can_socketcan_new(1, (const char*[]){"can0"}, 1000); // 1 iface, 1000 frames TX queue
    if (platform == NULL) { ... }

    // Set up the local Cyphal node instance.
    // Every node needs a home, which should be unique across the network.
    // The namespace is optional. The POSIX glue provides convenience functions for this.
    cy_t* cy = cy_new(platform, cy_str("my_node_name"), cy_str(""));  // platform, home, and namespace.
    if (cy == NULL) { ... }

    // ... to be continued ...
}
```

The library uses Pascal strings represented as `cy_str_t` throughout;
these strings are normally not nul-terminated, unless specifically noted otherwise.
Use `cy_str(const char*)` to create such strings from ordinary C strings.

### 📢 Publish messages on a topic

```c++
cy_publisher_t* my_pub = cy_advertise(cy, cy_str("my/topic"));
if (my_pub == NULL) { ... }  // handle error
```

Publish a message asynchronously (non-blocking) using best-effort delivery:

```c++
cy_us_t deadline = cy_now(cy) + 100'000; // the message must be sent within 0.1 seconds from now
cy_err_t err = cy_publish(my_pub, deadline, (cy_bytes_t){.size = 13, .data = "Hello Cyphal!"}); // nonblocking
if (err != CY_OK) { ... }
```

Publish a message asynchronously using reliable delivery; the progress and outcome can be checked via the future:

```c++
cy_us_t    deadline = cy_now(cy) + 2'000'000; // keep trying to deliver the message for up to 2 seconds
cy_bytes_t message = {.size = 34, .data = "Would you like to hear a TCP joke?"};
cy_future_t* future = cy_publish_reliable(my_pub, deadline, message);
if (future == NULL) { ... }  // handle error
```

There may be an arbitrary number of pending reliable messages per publisher, each with a dedicated future.
The future can be polled to check the delivery outcome:

```c++
if (cy_future_done(future)) {
    switch (cy_future_error(future)) {
        case CY_OK:             // message was delivered successfully
            break;
        case CY_ERR_DELIVERY:   // message could not be delivered before the deadline
            break;
        default:                // some other error, e.g., failed to send
            break;
    }
} else {
    // wait some more
}
```

Instead of polling, one can also attach a callback to be invoked once the future has materialized or an error has
occurred; to pass arbitrary context data to the callback, use `cy_user_context_t`:

```c++
cy_future_context_set(future, (cy_user_context_t){ { "🐈", this } });
cy_future_callback_set(future, on_future_update);
```

```c++
void on_future_update(cy_future_t* future)
{
    cy_user_context_t ctx = cy_future_context(future);
    cy_err_t error = cy_future_error(future);
    if (cy_future_done(future)) {
        // The future has materialized; check the error to see if it has succeeded or something went wrong.
    } else {
        // Check the error and optionally log it or update perfcounters. No action is necessary.
    }
}
```

When done with the future, be sure to destroy it. Destroying a pending future cancels the associated action.
A future may be destroyed from within its own callback.

```c++
cy_future_destroy(future);
```

If you don't care about the future outcome, you can set it up for auto-destruction upon materialization as shown below.
Do not destroy unwanted futures right away because that cancels the associated operation.

```c++
cy_future_callback_set(future, cy_future_destroy);  // Will destroy itself when done, no need to keep the reference.
```

The examples folder contains a simple publisher example `example_time_pub.c`.

### 📩 Subscribe to topics and receive messages

`cy_subscribe()` covers most use cases:

```c++
size_t extent = 1024 * 100;         // max message size in bytes; excess truncated
cy_future_t* subscription = cy_subscribe(cy, cy_str("my/topic"), extent);
if (subscription == NULL) { ... }   // handle error
```

Future again! Everything that can produce results after some time (like delivery confirmation or message arrival)
is represented as a future in Cy. Futures have a shared interface for common tasks like checking if done, callbacks,
error handling, etc. Actions that are specific to a particular future type (e.g., retrieving received message)
are accessed via type-specific functions that check the polymorphic future type safely at runtime.

Aside from `cy_subscribe()` there is also `cy_subscribe_ordered()` if the application requires the messages to
arrive strictly in the publication order per remote -- some transports may deliver messages out of order and Cy will
reconstruct the original order. This can be vital for certain applications that deal with streamed data, real-time
state estimation, etc.

One powerful feature is pattern subscriptions -- a kind of automatic service discovery.
When a pattern subscription is created, the local node will scout the network for topics matching the specified
pattern and will automatically subscribe to them as they appear, and unsubscribe when they disappear.

Cy *intentionally uses the same API* for both verbatim and pattern subscriptions,
as this enables flexible configuration at the time of integration/runtime as opposed to compile time only.
To create a pattern subscription, simply use a topic name that contains substitution wildcards:

* `*` -- matches a single name segment; e.g., `sensors/*/temperature` matches `sensors/engine/temperature` and
  `sensors/cabin/temperature` and so on.
* `>` -- matches zero or more name segments at the end; e.g., `sensors/>` matches `sensors`,
  `sensors/engine/temperature`, etc.

Cyphal is designed to be lightweight and efficient, which is why we don't support substitution characters *within*
name segments; e.g., `sensor*/eng>` will be treated as a verbatim topic name rather than a pattern.

When a message is received, the subscriber future becomes done:

```c++
if (cy_future_done(subscription)) {
    // Retrieve the last received message. The queue depth is 1, newer messages overwrite older ones.
    cy_arrival_t arrival = cy_arrival_borrow(subscription);

    // Read the payload from the message.
    size_t  size = cy_message_size(arrival.message.content);
    unsigned char data[size];
    cy_message_read(arrival.message.content, 0, size, data); // feel free to read only the parts of interest

    // This is how you can access the message metadata if needed.
    cy_us_t timestamp = arrival.message.timestamp;
    cy_topic_t* topic = cy_topic_find_by_hash(arrival.breadcrumb.cy, arrival.breadcrumb.topic_hash);
    cy_str_t topic_name = cy_topic_name(topic);

    // Print the message; hexdump() is just a helper, not part of the library.
    char* dump = hexdump(size, data, 32);
    printf("Received message on topic %s at %.3f:\n%s\n", topic_name.str, 1e-6 * timestamp, dump);

    // One can optionally send a response back to the publisher using cy_respond() or cy_respond_reliable();
    // see more about RPC & streaming in the next section.
} else {
    // No message has arrived yet, check back later.
}
```

Polling like above is useful when one needs a sampling subscriber that just stores the most recently received message,
but often one would want to set up a callback to be invoked when a message arrives, which has been shown earlier --
it uses the same future callback API. The callback will be also triggered on transient errors, so one will have
to check if the future is done in the handler:

```c++
void on_message(cy_future_t* subscription)
{
    if (cy_future_done(subscription)) {
        // A message has arrived, process it as shown above.
    } else {
        cy_err_t error = cy_future_error(subscription);
        // A transient error has occurred; report it or increment perfcounters, but no action is necessary.
    }
}
```

If a pattern subscription is used, then it is often needed to know which pattern substitutions were made to match the
topic name, like when `system/primary/sensor/0/data` matches `system/*/sensor/*/data`,
we want to know that `primary` and `0` were the substitutions for the two `*` tokens.
The pattern matching information is available with each `cy_arrival_t`:

```c++
// Already shown above:
cy_arrival_t arrival = cy_arrival_borrow(subscription);
cy_topic_t* topic = cy_topic_find_by_hash(arrival.breadcrumb.cy, arrival.breadcrumb.topic_hash);

// Retrieve the substitutions -- very efficient, no string matching is done (everything is precomputed):
cy_substitution_set_t subs = cy_subscriber_substitutions(subscription, topic);
printf("Topic name %s matched with %zu substitutions:\n", cy_topic_name(topic), subs.count);
for (size_t i = 0; i < subs.count; i++) {
    cy_substitution_t s = subs.substitutions[i];
    printf("Substitution #%zu matched token #%zu with %.*s\n", i, s.ordinal, (int)s.str.len, s.str.str);
}
```

It is also possible to monitor subscriber liveness and alert the application via its callback when messages cease to
arrive; see the API docs for details.

The examples folder contains a simple subscriber example `example_echo.c`.

### 🔄 RPC & streaming

Cyphal v1.1 implements RPC with optional streaming directly on top of pub/sub by allowing subscribers to optionally
respond to any received message. Such responses are unicast directly back to the publisher, and are invisible to
other nodes on the network.

Streaming is simply a special case of RPC where the server (i.e., subscriber) sends multiple responses
to the same request. Each request carries a non-wrapping seqno that starts from zero and is incremented by one
for each subsequent response.

If there are multiple subscribers on a topic, then each may respond, in which case the client (i.e., publisher)
will receive multiple responses separately from each server (subscriber).
This can be used to implement anycast-like redundant topologies.

Protocol-wise, there is no difference between a regular published message and a request, but in the Cy API the
distinction is important because the library needs to know where to dispatch responses received for a given message.
Hence there is a separate function for sending messages for which responses are expected: `cy_request()`:

```c++
cy_us_t delivery_deadline = cy_now(cy) + 3'000'000; // request must be acknowledged by the remote within 3 seconds
cy_us_t response_timeout  = 1'000'000;              // first response must arrive within 1 second after that
cy_future_t* future = cy_request(my_pub, delivery_deadline, response_timeout, message);
if (future == NULL) { ... }  // handle error
```

As usual, the future can be polled, or we can set up a callback to be invoked when the response arrives:

```c++
void on_response(cy_future_t* future)
{
    cy_err_t error = cy_future_error(future);
    if (cy_future_done(future)) {
        // Response is either received or has timed out.
        switch (error) {

            case CY_OK:                                             // Response received successfully.
                cy_response_t response = cy_response_move(future);  // The future will become pending again.
                uint64_t subscriber_node_id = response.remote_id;   // Identity of the responding node.
                uint64_t stream_seqno = response.seqno;             // 0 = first response, 1 = second, etc.
                cy_us_t timestamp = response.message.timestamp;     // Response arrival time.
                cy_message_t* message = response.message.content;
                // Read the response payload as shown above for messages, using cy_message_read() etc.
                break;
            
            case CY_ERR_LIVENESS:   // Response did not arrive.
                break;
            
            default:                // Some other error, e.g., from the transport layer.
                break;
        }
        // We can destroy the future if no further responses are needed/expected.
        // If we keep it alive, future responses will be reported; the future will become done again.
        if (no_more_responses_needed) {
            cy_future_destroy(future); // Invalidates the future.
        }
    } else {
        // A transient error has occurred; report it or increment perfcounters, but no action is necessary.
    }
}
```

The request future will trigger a liveness error if response messages cease to arrive for longer than the timeout
configured at the original `cy_request()` call; i.e., timeout monitoring does not stop after the first response.

Subscribers respond to messages using `cy_respond()` or `cy_respond_reliable()`,
which are very similar to `cy_publish()` and `cy_publish_reliable()`.

If streaming is used, then normally it will be done using reliable delivery via `cy_respond_reliable()`,
as reliable messages inform the server whether the remote side is accepting the response messages:
- If the remote client accepts a response, the `cy_respond_reliable()` future will materialize with `CY_OK`,
  indicating that streaming may proceed.
- If the remote client application is no longer interested in the responses, it will destroy the future, causing all
  subsequent responses to be NACK-ed by the client, and the server's future will materialize with `CY_ERR_NACK`.
- If the remote client node is not reachable due to being down or disconnected, the server's future will
  materialize with `CY_ERR_DELIVERY` after the delivery deadline expires.

### ⚙ Event loop

Finally, spin the event loop to keep the stack making progress and processing incoming/outgoing messages.
The event loop API is transport-agnostic and delegates to the platform layer internally:

```c++
while (true)
{
    err = cy_spin_until(cy, cy_now(cy) + 10000);  // spin for 0.01 seconds
    if (err != CY_OK) { ... }
    // do some other stuff here periodically
}
```

That's it! See the `examples/` folder for more complete examples, and read the API docs in [`cy.h`](cy/cy.h).

## 🥽 Advanced usage

### 📍 Topic pinning to a specific subject-ID

By default, the CRDT allocation protocol will ensure that each topic gets a dedicated subject-ID.
Some deployments, in particular hard real-time/safety-critical ones,
may want to avoid dependency on automatic allocation and instead assign (some of) the topics to subjects manually.
Such topics are called *pinned topics*.

A pinned topic has the desired subject-ID encoded as a decimal number at the end of its name following a `#` character;
e.g., `foo/bar#1234` is a pinned topic with subject-ID 1234.
Leading zeros are not allowed. The pinned subject-ID must be in the range \[0, 8191\].
This range is never used for automatically allocated topics, so there is no risk of collision with non-pinned topics.

Pinning does not affect the topic identity; as such, for topic identification purposes, only the part of the name
before the `#` of the pinning expression is significant.

A pinned topic is still an ordinary CRDT state. If the same topic is pinned inconsistently across the network, the
conflict is resolved by the usual CRDT arbitration rules: older topic wins by log-age, and ties are broken by the
larger eviction counter. A pinned topic does not bypass consensus or get special priority; it keeps its requested
subject-ID only if its state wins that ordinary arbitration. The same rule is applied locally as repeated verbatim
advertisements/subscriptions are added on a node: once a topic instance exists, later local pinning requests attach to
it without rewriting its current allocation.

For example, if the application joins (i.e., advertises or subscribes to) `foo/bar` followed by `foo/bar#1234`,
the latter pin is effectively ignored. Same holds if one node joins `foo/bar`, and then some time later another
node joins `foo/bar#1234` -- the pinning loses arbitration because there is a pre-existing topic that should not be
disturbed by newcomers.

Unlike the default automatic allocation mode, pinning allows multiple topics to share the same subject-ID ---
each participant of such multi-tenant subjects will filter out messages of interest upon arrival;
usually this is only a good idea for relatively low-rate topics.
For example, having `foo#1234` and `bar#1234` simultaneously is valid;
a node that subscribes to either will receive messages from both and filter out the relevant traffic locally in software
(Cy does the necessary routing/filtering internally so the application doesn't have to).

A topic name may not be empty, therefore `#1234` is invalid because the part before `#` is empty.

## 🚌 Compatibility with Cyphal/CAN v1.0

Cyphal v1.1 is wire-compatible with Cyphal/CAN v1.0.
To join a Cyphal/CAN v1.0 subject, use pinned topics like `1234#1234`, where 1234 is the desired subject-ID.

Cyphal v1.1 has no RPC in the same way as Cyphal/CAN v1.0 does.
To use RPC in a legacy CAN network, a low-level CAN transport access is required at the moment;
first-class v1.0 RPC support may be added in the future if there is demand (please discuss on the forum).

## 🚁 Compatibility with UAVCAN v0 / DroneCAN

The `cy_can` transport layer exposes a small sidecar API for legacy UAVCAN v0 / DroneCAN interoperability:
`cy_can_v0_subscribe()` and `cy_can_v0_publish()`.

This API is transport-local: it uses v0 data type IDs and CRC seeds directly, and it does not create Cy topics or
participate in the Cy consensus protocol. Event processing is still driven by the usual `cy_spin...()` calls.

See [`examples/example_dronecan_echo.c`](examples/example_dronecan_echo.c) for a minimal SocketCAN subscriber.
