<img src="https://opencyphal.org/favicon-192.png" width="50px" align="right" style="text-align:right">
<div align="center">

# Cyphal v1.1 in C

_pub/sub without steroids_

</div>

-----

A C implementation of Cyphal v1.1: robust decentralized zero-configuration pub/sub with tunable reliability
and service discovery in only a couple thousand lines of straightforward C.
Runs anywhere, including small baremetal MCUs.
The key design goals are simplicity and robustness.

🚧 **WORK IN PROGRESS** 🏗️ The library is under active development; the API and functionality may change. Bugs afoot.

To use the library in your project, simply copy `cy.c`, `cy.h`, and `cy_platform.h` into your source tree,
or add this repository as a submodule.
The following external dependencies are required, all single-header-only:

- [`cavl2.h`](https://github.com/pavel-kirienko/cavl) --- An AVL tree (Pavel Kirienko, MIT license).
- [`wkv.h`](https://github.com/pavel-kirienko/wild_key_value) --- A key-value container with fast pattern matching & key routing (Pavel Kirienko, MIT license).
- [`rapidhash.h`](https://github.com/Nicoshev/rapidhash) --- A good 64-bit hash (Nicolas De Carli, BSD 2-clause license).

## 📚 API crash course

The library is extremely simple and easy to use on any platform.
The entire API header is just a few hundred lines of code, mostly comments.
The API is fully asynchronous/non-blocking; if necessary, synchronous wrappers can be implemented on top of it.

The specifics of setting up a local node depend on the platform and transport used,
unlike the rest of the API, which is entirely platform- and transport-agnostic.
Here is an example for Cyphal/UDP on POSIX systems:

```c++
#include <cy.h>             // platform- and transport-agnostic Cyphal API
#include <cy_udp_posix.h>   // thin low-level glue specific to Cyphal/UDP on POSIX systems; choose one for your setup

int main(void)
{
    // Set up the local Cyphal node. This is done using the platform- and transport-specific glue layer.
    // The rest of the application uses the generic Cyphal API only, except for the event loop spinning part.
    cy_udp_posix_t cy_udp;
    cy_err_t       err = cy_udp_posix_new_simple(&cy_udp);
    if (err != CY_OK) { ... }
    cy_t* cy = &cy_udp.base;  // Get a pointer to the Cy instance for convenience.

    // ... to be continued ...
}
```

The library uses Pascal strings represented as `wkv_str_t` throughout;
these strings are normally not nul-terminated, unless specifically noted otherwise.
Use `wkv_key(const char*)` to create such strings from ordinary C strings.

### 📢 Publish messages

```c++
cy_publisher_t* my_pub = cy_advertise(cy, wkv_key("my/topic"));
if (my_pub == NULL) { ... }  // handle error
```

Publish a message asynchronously (non-blocking) using best-effort delivery:

```c++
cy_us_t deadline = cy_now(cy) + 100_000; // the message must be sent within 0.1 seconds from now
err = cy_publish(my_pub, deadline, (cy_bytes_t){.size = 13, .data = "Hello Cyphal!"});
if (err != CY_OK) { ... }
```

Publish a message asynchronously using reliable delivery; the outcome can be checked via the returned future:

```c++
cy_us_t    deadline = cy_now(cy) + 2_000_000; // keep trying to deliver the message for up to 2 seconds
cy_bytes_t message = {.size = 34, .data = "Would you like to hear a TCP joke?"}
cy_future_t* future = cy_publish_reliable(my_pub, deadline, message);
if (future == NULL) { ... }  // handle error
```

There may be an arbitrary number of pending reliable messages per publisher, each with a dedicated future.
The future can be polled to check the delivery outcome:

```c++
cy_future_status_t status = cy_future_status(future);
if (status == cy_future_pending) {
    // wait some more
} else if (status == cy_future_success) {
    // message was delivered successfully
} else {
    // message could not be delivered within the specified deadline
    assert(status == cy_future_failure);
}
```

Instead of polling, one can also attach a callback to be invoked once the future has materialized;
to pass arbitrary context data to the callback, use `cy_user_context_t`:

```c++
cy_future_context_set(future, (cy_user_context_t){ { "🐈", NULL, (void*)123456 } });
cy_future_callback_set(future, on_future_done);
```
```c++
void on_future_done(cy_future_t* future)
{
    cy_user_context_t ctx = cy_future_context(future);
    // Query the future as you normally would.
}
```

When done with the future, be sure to destroy it. Destroying a pending future cancels the associated action.
A future may be destroyed from within its own callback.

```c++
cy_future_destroy(future);
```

### 📩 Subscribe to messages

```c++
cy_subscriber_t* my_sub = cy_subscribe(cy,
                                       wkv_key("my/topic"),
                                       1024 * 100,            // max message size in bytes; excess truncated
                                       CY_USER_CONTEXT_EMPTY, // context data passed to the callback
                                       on_message);           // callback invoked upon message arrival
if (my_sub == NULL) { ... }
```

The message arrival callback looks like this:

```c++
void on_message(cy_user_context_t user_context, cy_arrival_t* arrival) 
{
    size_t  size = cy_message_size(arrival->message.content);
    unsigned char data[size];
    cy_message_read(&arrival->message.content, 0, size, data);  // feel free to read only the parts of interest
    char* dump = hexdump(size, data, 32);
    printf("Received message on topic %s:\n%s\n", cy_topic_name(arrival->topic).str, dump);
    // If relevant, one can optionally send a response back to the publisher here using cy_respond():
    err = cy_respond(arrival->responder, deadline, response_data);
    // It is also possible to store the responder instance to send the response at any time later after the callback.
}
```

### ↩️ Respond to messages (RPC)

Observe that the message callback provides an option to send a response back to the publisher directly using
a direct P2P channel.
This is how one can implement request/response (RPC-like) interactions.
If the application expects a response, then the correct publishing function to use is `cy_request()`:

```c++
cy_us_t request_deadline  = cy_now(cy) + 3_000_000; // request must be acknowledged by the remote within 3 seconds
cy_us_t response_deadline = cy_now(cy) + 6_000_000; // give up waiting for the response after 6 seconds
cy_future_t* future = cy_request(my_pub, request_deadline, response_deadline, message);
if (future == NULL) { ... }  // handle error
```

As usual, the future can be polled, or we can set up a callback to be invoked when the response arrives:

```c++
void on_response(cy_future_t* future)
{
    cy_future_status_t status = cy_future_status(future);
    if (status == cy_future_pending) {
        // Intermediate progress update: request delivery has been confirmed, waiting for the response now.
    } else if (status == cy_future_success) {
        cy_request_result_t* const result = cy_future_result(future);
        cy_us_t response_arrival_timestamp = result->response.timestamp;
        const size_t  size = cy_message_size(result->response.content);
        unsigned char data[size];
        cy_message_read(&result->response.content, 0, size, data);
        // Process the response data!
        cy_future_destroy(future);
    } else {
        assert(status == cy_future_failure);
        cy_request_result_t* const result = cy_future_result(future);
        if (result->request.acknowledgements == 0) {
            // The request could not be delivered.
        } else {
            // The request was delivered, but no response was received.
        }
        cy_future_destroy(future);
    }
}
```

### ⚙ Event loop

Finally, spin the event loop to keep the stack making progress and processing incoming/outgoing messages.
Depending on the platform- and transport-specific glue layer used, the event loop spinning part may look like this:

```c++
while (true)
{
    err = cy_udp_posix_spin_until(cy, cy_now(cy) + 10000);  // spin for 0.01 seconds
    if (err != CY_OK) { ... }
    // do some other stuff here periodically
}
```

That's it! See the `examples/` folder for more complete examples.

## 🎨 Prior art

### [Group Address Allocation Protocol (GAAP)](https://datatracker.ietf.org/doc/html/draft-ietf-pim-gaap-03)

This is a form of a distributed consensus protocol that assigns unique numeric identifiers (multicast group addresses)
to string keys. Cyphal v1.1 solves essentially the same problem where it finds a unique subject-ID per topic name.
The difference of GAAP is that instead of CRDT, it relies on the conventional claim/deny approach.

### [Zeroconf Multicast Address Allocation Protocol (ZMAAP)](https://datatracker.ietf.org/doc/html/draft-ietf-zeroconf-zmaap-02)

Similar to GAAP.

### Well-known decentralized pub/sub systems

These include DDS, Zenoh, etc. Cyphal does not attempt to directly compete with these, but instead offers an alternative for applications where the complexity of the competitors is undesirable.

## 🚌 Compatibility with Cyphal/CAN v1.0

Cyphal v1.1 is wire-compatible with Cyphal/CAN v1.0.

To publish or subscribe to v1.0 subjects, use pinned topics of the form `whatever/#abcd`,
where `abcd` is the subject-ID of the topic as a hexadecimal number,
and the part before `#` is arbitrary and does not influence the topic hash (it is only meaningful for pattern matching).
For example, to subscribe to subject-ID 1234, use the topic name `#04d2`.

Cyphal v1.1 has no RPC in the same way as Cyphal/CAN v1.0 does; instead, it uses pub/sub for everything, including request/response interactions. Thus, to use RPC in a legacy CAN network, a low-level CAN transport access is required.

## 📝 Design notes

```mermaid
classDiagram
direction LR
    class cy {
        +advertise()
        +subscribe()
    }
    class publisher {
        +publish()
    }
    class subscriber {
        +callback
    }
    class pending_response {
        +callback
    }
    cy "1" o-- "*" _topic
    cy "1" o-- "*" _subscriber_root
    cy "1" --> "*" pending_response
    _topic "1" o-- "*" _coupling
    _topic "1" <-- "*" publisher
    publisher "1" <-- "*" pending_response
    _coupling "*" --> "1" _subscriber_root
    _subscriber_root "1" o-- "*" subscriber
    note "Automatically managed private entities are prefixed with '_'"
```
