# H4 — Zero-length datagram double-frees and crashes every node on the broadcast group

- **Severity:** 🔴 HIGH (borderline critical) (report H-4 / U-F1)
- **Confidence:** reproduced end-to-end by the UDP review agent; glibc `realloc(ptr,0)→NULL` confirmed on host
- **Subsystem:** `cy_udp_posix/cy_udp_posix.c`, `cy_udp_posix/udp_wrapper.c`
- **Status:** RESOLVED

## Summary
A single valid zero-length UDP datagram to the broadcast-subject multicast group (which every Cy/UDP node joins)
causes a double-free / heap corruption on every receiving node. Remote, unauthenticated, one packet, all nodes down.

## Location
- `cy_udp_posix/cy_udp_posix.c:623-627` — `realloc(dgram.data, 0)` then `if (dgram_realloc != NULL) { dgram.data = ... }`.
- `cy_udp_posix/udp_wrapper.c:236-259` — `udp_wrapper_receive` returns 1 with `*inout_payload_size = 0` for a valid 0-byte datagram.
- `cy_udp_posix/cy_udp_posix.c:631` — dangling `dgram.data` handed to `udpard_rx_port_push`.

## Mechanism
`recvmsg` on an empty datagram returns 0; with `IP_PKTINFO` present and the iface matching, `udp_wrapper_receive`
sets size 0 and returns 1 (a "valid datagram" result, not the `rx_result==0` drop path). `read_socket` then calls
`realloc(dgram.data, 0)`, which on glibc frees the buffer and returns NULL. The guard `if (dgram_realloc != NULL)`
is false, so `dgram.data` is left pointing at freed memory. That dangling pointer is passed to
`udpard_rx_port_push`, whose `header_deserialize` fails on the 0-byte frame and calls the deleter
(`mem_free_payload` → free) on the already-freed pointer → double free.

## Trigger / repro
`sendto(fd, "", 0, 0, &group_239_x_9382)` from any host → every node receiving it crashes. Also reachable from a
port scanner or unrelated 239.x multicast app.

## Fix direction
Guard the empty case before the realloc, and free through the memory vtable (not raw libc), e.g.:
```c
if (dgram.size == 0) {                 // nothing to deliver; drop cleanly
    self->mem.vtable->base.free(self->mem.context, CY_UDP_SOCKET_READ_BUFFER_SIZE, dgram.data);
    self->stats.sock_rx.error_count[iface_index]++;   // or a dedicated dropped counter
    return;
}
```
Additionally (same neighbourhood): the shrink at line 623 uses raw libc `realloc`/`free` and hand-patches
`stats.mem.allocated_bytes` (line 626); route the shrink through `self->mem` too so it stays correct under a
non-malloc block-pool allocator. If the shrink stays raw, at minimum handle `realloc(ptr,0)` returning NULL without
losing the pointer.

## Regression test (required)
- Add a test (in `cy_udp_posix/tests/`, or a focused unit test around `read_socket`/the message path) that injects a
  received **0-byte** datagram and a **sub-header (1-byte and <24-byte)** datagram, asserting: no crash, exactly one
  free of the RX buffer, balanced allocation accounting, and normal nonzero datagrams still delivered.
- Must be wired into `ctest` and pass under AddressSanitizer. It must double-free / ASan-abort on the pre-fix code.
- If a full socket loopback is impractical in the unit harness, drive the internal receive/parse path directly so the
  `realloc(ptr,0)` → `udpard_rx_port_push` sequence is exercised.

## Acceptance criteria
- [ ] A received 0-byte datagram is dropped without any free of an already-freed pointer (no double free).
- [ ] The RX buffer allocated via `self->mem` is always freed through `self->mem` (allocator consistency), and
      `stats.mem.allocated_bytes` accounting stays correct on the drop path.
- [ ] A regression test injects a 0-byte datagram and asserts no crash and no leak (fragment/byte counts balanced).
- [ ] Verified under AddressSanitizer (no double-free / heap-corruption report).
- [ ] `udp_wrapper` still delivers genuine nonzero datagrams unchanged; broadcast/gossip traffic unaffected.

## Verification notes (adversarial cross-check)
- I will drive a 0-byte datagram through the real `read_socket`/`udpard_rx_port_push` path under ASan and confirm no
  double free; also a 1-byte and a sub-header (< 24-byte) datagram, since those also fail `header_deserialize` and
  exercise the deleter — the fix must not merely special-case size 0 while leaving a dangling pointer for the
  short-but-nonzero shrink path.
- I will confirm the fix does not introduce a leak on the drop path (the buffer must be freed exactly once).
- I will check that the fix routes frees through the vtable so a hypothetical non-malloc allocator wouldn't corrupt.
- I will re-run the example smoke test (real UDP multicast) to confirm normal traffic still flows.
