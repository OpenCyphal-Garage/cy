#include <cy_platform.h>
#include <unity.h>
#include "e2e_faults.hpp"
#include "e2e_sim_net.hpp"
#include "e2e_test_utils.hpp"
#include "message.h"
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <ranges>
#include <vector>

namespace {

constexpr std::uint8_t header_msg_rel  = 1U;
constexpr std::uint8_t header_msg_ack  = 2U;
constexpr std::uint8_t header_rsp_be   = 3U;
constexpr std::uint8_t header_rsp_rel  = 4U;
constexpr std::uint8_t header_rsp_ack  = 5U;
constexpr std::uint8_t header_rsp_nack = 6U;

constexpr std::size_t header_size      = 24U;
constexpr cy_us_t     step_us          = 5'000;
constexpr cy_us_t     ack_timeout_us   = 20'000;
constexpr cy_us_t     wait_timeout_us  = 800'000;
constexpr cy_us_t     response_extent  = 256;
constexpr cy_us_t     respond_deadline = 200'000;

struct request_wire_info_t final
{
    std::uint64_t tag{ 0U };
    std::uint64_t topic_hash{ 0U };
};

struct response_control_t final
{
    std::uint8_t  header_type{ 0U };
    std::uint8_t  tag{ 0U };
    std::uint64_t seqno{ 0U };
    std::uint64_t topic_hash{ 0U };
    std::uint64_t message_tag{ 0U };
};

struct server_context_t final
{
    std::size_t   request_count{ 0U };
    std::size_t   responses_per_request{ 1U };
    std::uint64_t response_seq{ 0U };
    std::uint32_t response_publisher_id{ 700U };
    cy_err_t      first_respond_error{ CY_OK };
    std::uint64_t first_message_tag{ 0U };
    std::uint64_t first_topic_hash{ 0U };
};

struct reliable_server_context_t final
{
    std::size_t               request_count{ 0U };
    std::size_t               responses_per_request{ 1U };
    std::uint64_t             response_seq{ 0U };
    std::uint32_t             response_publisher_id{ 750U };
    std::size_t               submit_failures{ 0U };
    std::vector<cy_future_t*> futures{};
};

struct deferred_reliable_server_context_t final
{
    bool            captured{ false };
    std::size_t     request_count{ 0U };
    cy_breadcrumb_t breadcrumb{};
    cy_us_t         request_timestamp{ 0 };
};

struct callback_capture_t final
{
    std::size_t total{ 0U };
    std::size_t pending{ 0U };
    std::size_t done_ok{ 0U };
    std::size_t done_error{ 0U };
    bool        last_done{ false };
    cy_err_t    last_error{ CY_OK };
};

struct future_event_capture_t final
{
    std::size_t total{ 0U };
    std::size_t pending{ 0U };
    std::size_t done{ 0U };

    bool saw_pending_media{ false };
    bool saw_pending_lag{ false };
    bool saw_done_delivery{ false };

    bool     last_done{ false };
    cy_err_t last_error{ CY_OK };
};

struct realloc_fail_state_t final
{
    cy_platform_vtable_t* vtable{ nullptr };
    void* (*original)(cy_platform_t*, void*, std::size_t){ nullptr };
    std::size_t skip_new_remaining{ 0U };
    std::size_t fail_new_remaining{ 0U };
    bool        installed{ false };
};

realloc_fail_state_t& realloc_fail_state()
{
    static realloc_fail_state_t state{}; // NOLINT(*-non-const-global-variables)
    return state;
}

extern "C" void* realloc_fail_wrapper(cy_platform_t* const platform, void* const ptr, const std::size_t size)
{
    realloc_fail_state_t& state = realloc_fail_state();
    if (state.installed && (ptr == nullptr) && (size > 0U)) {
        if (state.skip_new_remaining > 0U) {
            state.skip_new_remaining--;
        } else if (state.fail_new_remaining > 0U) {
            state.fail_new_remaining--;
            return nullptr;
        }
    }
    return state.original(platform, ptr, size);
}

void write_u48(unsigned char* const out, const std::uint64_t value)
{
    for (std::size_t i = 0U; i < 6U; i++) {
        out[i] = static_cast<unsigned char>((value >> (i * 8U)) & 0xFFU);
    }
}

void write_u64(unsigned char* const out, const std::uint64_t value)
{
    for (std::size_t i = 0U; i < 8U; i++) {
        out[i] = static_cast<unsigned char>((value >> (i * 8U)) & 0xFFU);
    }
}

std::uint64_t read_u48(const unsigned char* const in)
{
    std::uint64_t out = 0U;
    for (std::size_t i = 0U; i < 6U; i++) {
        out |= static_cast<std::uint64_t>(in[i]) << (i * 8U);
    }
    return out;
}

std::uint64_t read_u64(const unsigned char* const in)
{
    std::uint64_t out = 0U;
    for (std::size_t i = 0U; i < 8U; i++) {
        out |= static_cast<std::uint64_t>(in[i]) << (i * 8U);
    }
    return out;
}

void install_fail_new_alloc_after(e2e::sim_net_t& net,
                                  std::size_t     node_index,
                                  std::size_t     skip_count,
                                  std::size_t     fail_count);

void install_fail_next_new_alloc(e2e::sim_net_t& net, const std::size_t node_index, const std::size_t fail_count)
{
    install_fail_new_alloc_after(net, node_index, 0U, fail_count);
}

void install_fail_new_alloc_after(e2e::sim_net_t&   net,
                                  const std::size_t node_index,
                                  const std::size_t skip_count,
                                  const std::size_t fail_count)
{
    realloc_fail_state_t& state = realloc_fail_state();
    TEST_ASSERT_FALSE(state.installed);
    cy_platform_t* const platform = e2e::sim_net_platform(net, node_index);
    TEST_ASSERT_NOT_NULL(platform);
    TEST_ASSERT_NOT_NULL(platform->vtable);
    cy_platform_vtable_t* const vtbl = &net.nodes.at(node_index).vtable;
    state                            = realloc_fail_state_t{};
    state.vtable                     = vtbl;
    state.original                   = vtbl->realloc;
    state.skip_new_remaining         = skip_count;
    state.fail_new_remaining         = fail_count;
    state.installed                  = true;
    TEST_ASSERT_NOT_NULL(state.original);
    vtbl->realloc = realloc_fail_wrapper;
}

void restore_realloc_wrapper()
{
    realloc_fail_state_t& state = realloc_fail_state();
    if (state.installed) {
        TEST_ASSERT_NOT_NULL(state.vtable);
        state.vtable->realloc = state.original;
        state                 = realloc_fail_state_t{};
    }
}

void set_now(e2e::sim_net_t& net, const cy_us_t now)
{
    e2e::sim_net_node_now_set(net, e2e::sim_node_a, now);
    e2e::sim_net_node_now_set(net, e2e::sim_node_b, now);
}

void drive_for(e2e::sim_net_t& net, cy_us_t& now, const cy_us_t duration)
{
    const cy_us_t end = now + duration;
    while (now < end) {
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
    }
}

void drain_queue(e2e::sim_net_t& net, cy_us_t& now)
{
    std::size_t guard = 0U;
    while (e2e::sim_net_pending_frames(net) > 0U) {
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
        guard++;
        TEST_ASSERT_TRUE(guard < 30'000U);
    }
}

bool wait_until_done(e2e::sim_net_t& net, cy_us_t& now, const cy_future_t* const future, const cy_us_t timeout)
{
    const cy_us_t end = now + timeout;
    while (now <= end) {
        if (cy_future_done(future)) {
            return true;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
    }
    return false;
}

void assert_request_state(const cy_future_t* const future, const bool done, const cy_err_t error)
{
    TEST_ASSERT_EQUAL_INT(done ? 1 : 0, cy_future_done(future) ? 1 : 0);
    TEST_ASSERT_EQUAL_INT(error, cy_future_error(future));
}

cy_publisher_t* make_client(e2e::sim_net_t& net, const char* const topic_name)
{
    cy_publisher_t* const out =
      cy_advertise_client(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str(topic_name), response_extent);
    TEST_ASSERT_NOT_NULL(out);
    cy_ack_timeout_set(out, ack_timeout_us);
    return out;
}

cy_future_t* make_server_subscriber(e2e::sim_net_t& net, const char* const topic_name, server_context_t& context);
cy_future_t* make_server_subscriber_reliable(e2e::sim_net_t&            net,
                                             const char* const          topic_name,
                                             reliable_server_context_t& context);
cy_future_t* make_server_subscriber_capture_only(e2e::sim_net_t&                     net,
                                                 const char* const                   topic_name,
                                                 deferred_reliable_server_context_t& context);

extern "C" void on_server_request(cy_future_t* const sub)
{
    const cy_arrival_t arrival = cy_arrival_move(sub);
    if (arrival.message.content == nullptr) {
        return;
    }

    auto* const ctx = static_cast<server_context_t*>(cy_future_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(ctx);
    ctx->request_count++;
    if (ctx->request_count == 1U) {
        ctx->first_message_tag = arrival.breadcrumb.message_tag;
        ctx->first_topic_hash  = arrival.breadcrumb.topic_hash;
    }

    cy_breadcrumb_t breadcrumb = arrival.breadcrumb;
    for (std::size_t i = 0U; i < ctx->responses_per_request; i++) {
        const auto       payload = e2e::app_payload_pack(ctx->response_publisher_id, ++ctx->response_seq);
        const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
        const cy_err_t   err     = cy_respond(&breadcrumb, arrival.message.timestamp + respond_deadline, msg);
        if ((ctx->first_respond_error == CY_OK) && (err != CY_OK)) {
            ctx->first_respond_error = err;
        }
    }
    cy_message_refcount_dec(arrival.message.content);
}

cy_future_t* make_server_subscriber(e2e::sim_net_t& net, const char* const topic_name, server_context_t& context)
{
    cy_future_t* const out = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(topic_name), 512U);
    TEST_ASSERT_NOT_NULL(out);
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &context;
    cy_future_context_set(out, ctx);
    cy_future_callback_set(out, on_server_request);
    return out;
}

extern "C" void on_server_request_reliable(cy_future_t* const sub)
{
    const cy_arrival_t arrival = cy_arrival_move(sub);
    if (arrival.message.content == nullptr) {
        return;
    }

    auto* const ctx = static_cast<reliable_server_context_t*>(cy_future_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(ctx);
    ctx->request_count++;

    cy_breadcrumb_t breadcrumb = arrival.breadcrumb;
    for (std::size_t i = 0U; i < ctx->responses_per_request; i++) {
        const auto         payload = e2e::app_payload_pack(ctx->response_publisher_id, ++ctx->response_seq);
        const cy_bytes_t   msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
        cy_future_t* const fut = cy_respond_reliable(&breadcrumb, arrival.message.timestamp + respond_deadline, msg);
        if (fut != nullptr) {
            ctx->futures.push_back(fut);
        } else {
            ctx->submit_failures++;
        }
    }
    cy_message_refcount_dec(arrival.message.content);
}

cy_future_t* make_server_subscriber_reliable(e2e::sim_net_t&            net,
                                             const char* const          topic_name,
                                             reliable_server_context_t& context)
{
    cy_future_t* const out = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(topic_name), 512U);
    TEST_ASSERT_NOT_NULL(out);
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &context;
    cy_future_context_set(out, ctx);
    cy_future_callback_set(out, on_server_request_reliable);
    return out;
}

extern "C" void on_server_request_capture_only(cy_future_t* const sub)
{
    const cy_arrival_t arrival = cy_arrival_move(sub);
    if (arrival.message.content == nullptr) {
        return;
    }

    auto* const ctx = static_cast<deferred_reliable_server_context_t*>(cy_future_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(ctx);
    ctx->request_count++;
    if (!ctx->captured) {
        ctx->captured          = true;
        ctx->breadcrumb        = arrival.breadcrumb;
        ctx->request_timestamp = arrival.message.timestamp;
    }
    cy_message_refcount_dec(arrival.message.content);
}

cy_future_t* make_server_subscriber_capture_only(e2e::sim_net_t&                     net,
                                                 const char* const                   topic_name,
                                                 deferred_reliable_server_context_t& context)
{
    cy_future_t* const out = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(topic_name), 512U);
    TEST_ASSERT_NOT_NULL(out);
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &context;
    cy_future_context_set(out, ctx);
    cy_future_callback_set(out, on_server_request_capture_only);
    return out;
}

cy_future_t* request_once(cy_publisher_t* const      client,
                          const cy_us_t              now,
                          const std::uint32_t        publisher_id,
                          const std::uint64_t        sequence,
                          const cy_us_t              delivery_deadline_offset,
                          const cy_us_t              response_timeout,
                          const cy_future_callback_t callback         = nullptr,
                          void* const                callback_context = nullptr)
{
    const auto         payload = e2e::app_payload_pack(publisher_id, sequence);
    const cy_bytes_t   msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    cy_future_t* const fut     = cy_request(client, now + delivery_deadline_offset, response_timeout, msg);
    if ((fut != nullptr) && (callback != nullptr)) {
        cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
        ctx.ptr[0]            = callback_context;
        cy_future_context_set(fut, ctx);
        cy_future_callback_set(fut, callback);
    }
    return fut;
}

request_wire_info_t last_request_wire(const e2e::sim_net_t& net)
{
    request_wire_info_t out{};
    const auto&         captures = e2e::sim_net_captures(net);
    bool                found    = false;
    for (const e2e::frame_capture_t& cap : std::ranges::reverse_view(captures)) {
        if (cap.dropped) {
            continue;
        }
        if ((cap.frame.source == e2e::sim_node_a) && (cap.frame.destination == e2e::sim_node_b) && !cap.frame.unicast &&
            (cap.frame.header_type == header_msg_rel) && cap.frame.has_tag && cap.frame.has_topic_hash) {
            out.tag        = cap.frame.tag;
            out.topic_hash = cap.frame.topic_hash;
            found          = true;
            break;
        }
    }
    TEST_ASSERT_TRUE(found);
    return out;
}

void inject_response_wire(e2e::sim_net_t&                   net,
                          const std::uint8_t                type,
                          const std::uint8_t                tag,
                          const std::uint64_t               seqno,
                          const std::uint64_t               topic_hash,
                          const std::uint64_t               message_tag,
                          const std::vector<unsigned char>& payload,
                          const cy_us_t                     timestamp,
                          const bool                        as_multicast       = false,
                          const std::uint64_t               remote_id_override = 0U)
{
    std::vector<unsigned char> wire(header_size + payload.size(), 0U);
    wire.at(0) = type;
    wire.at(1) = tag;
    write_u48(&wire.at(2), seqno);
    write_u64(&wire.at(8), topic_hash);
    write_u64(&wire.at(16), message_tag);
    if (!payload.empty()) {
        (void)std::ranges::copy(payload, wire.begin() + static_cast<std::ptrdiff_t>(header_size));
    }

    cy_message_t* const msg =
      cy_test_message_make(&e2e::sim_net_message_heap(net, e2e::sim_node_a), wire.data(), wire.size());
    TEST_ASSERT_NOT_NULL(msg);

    cy_lane_t lane{};
    lane.id   = (remote_id_override == 0U) ? e2e::sim_net_node_id(net, e2e::sim_node_b) : remote_id_override;
    lane.prio = cy_prio_nominal;
    std::memset(lane.ctx.state, 0, sizeof(lane.ctx.state));
    std::memcpy(lane.ctx.state, &lane.id, std::min(sizeof(lane.ctx.state), sizeof(lane.id)));

    cy_message_ts_t mts{};
    mts.timestamp = timestamp;
    mts.content   = msg;

    if (as_multicast) {
        cy_subject_reader_t fake_reader{};
        fake_reader.subject_id = 1U;
        cy_on_message(e2e::sim_net_platform(net, e2e::sim_node_a), lane, &fake_reader, mts);
    } else {
        cy_on_message(e2e::sim_net_platform(net, e2e::sim_node_a), lane, nullptr, mts);
    }
}

std::vector<response_control_t> response_controls_since(const e2e::sim_net_t& net, const std::size_t start_index)
{
    std::vector<response_control_t> out{};
    const auto&                     captures = e2e::sim_net_captures(net);
    for (std::size_t i = start_index; i < captures.size(); i++) {
        const e2e::frame_capture_t& cap = captures.at(i);
        if (cap.dropped || !cap.frame.unicast || (cap.frame.source != e2e::sim_node_a) ||
            (cap.frame.destination != e2e::sim_node_b)) {
            continue;
        }
        if ((cap.frame.header_type != header_rsp_ack) && (cap.frame.header_type != header_rsp_nack)) {
            continue;
        }
        TEST_ASSERT_TRUE(cap.frame.wire.size() >= header_size);
        response_control_t item{};
        item.header_type = cap.frame.header_type;
        item.tag         = cap.frame.wire.at(1U);
        item.seqno       = read_u48(&cap.frame.wire.at(2U));
        item.topic_hash  = read_u64(&cap.frame.wire.at(8U));
        item.message_tag = read_u64(&cap.frame.wire.at(16U));
        out.push_back(item);
    }
    return out;
}

bool unpack_response_payload(const cy_response_t& response, e2e::app_payload_t& out)
{
    if (response.message.content == nullptr) {
        return false;
    }
    std::array<unsigned char, 32> bytes{};
    const std::size_t             size = cy_message_read(response.message.content, 0U, bytes.size(), bytes.data());
    return e2e::app_payload_unpack(bytes.data(), size, out);
}

template <typename Predicate>
bool wait_until(e2e::sim_net_t& net, cy_us_t& now, const cy_us_t timeout, Predicate predicate)
{
    const cy_us_t end = now + timeout;
    while (now <= end) {
        if (predicate()) {
            return true;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
    }
    return false;
}

bool wait_all_done(e2e::sim_net_t& net, cy_us_t& now, const std::vector<cy_future_t*>& futures, const cy_us_t timeout)
{
    return wait_until(net, now, timeout, [&futures]() {
        return std::ranges::all_of(
          futures, [](const cy_future_t* const fut) { return (fut != nullptr) && cy_future_done(fut); });
    });
}

void cleanup_case(e2e::sim_net_t&                     net,
                  cy_us_t&                            now,
                  const std::vector<cy_future_t*>&    futures,
                  const std::vector<cy_future_t*>&    subscribers,
                  const std::vector<cy_publisher_t*>& publishers)
{
    for (cy_future_t* const fut : futures) {
        if (fut != nullptr) {
            cy_future_destroy(fut);
        }
    }

    for (cy_future_t* const sub : subscribers) {
        if (sub != nullptr) {
            cy_future_destroy(sub);
        }
    }
    drive_for(net, now, 40'000);

    for (cy_publisher_t* const pub : publishers) {
        if (pub != nullptr) {
            cy_unadvertise(pub);
        }
    }
    drive_for(net, now, 40'000);

    drain_queue(net, now);
    e2e::assert_quiescent(net);

    e2e::sim_net_deinit(net);
    e2e::assert_all_heaps_clean(net);
    e2e::assert_no_live_messages();
}

extern "C" void on_request_future(cy_future_t* const future)
{
    auto* const cap = static_cast<callback_capture_t*>(cy_future_context(future).ptr[0]);
    TEST_ASSERT_NOT_NULL(cap);
    cap->total++;
    cap->last_done  = cy_future_done(future);
    cap->last_error = cy_future_error(future);
    if (!cap->last_done) {
        cap->pending++;
    } else if (cap->last_error == CY_OK) {
        cap->done_ok++;
    } else {
        cap->done_error++;
    }
}

extern "C" void on_future_event(cy_future_t* const future)
{
    auto* const cap = static_cast<future_event_capture_t*>(cy_future_context(future).ptr[0]);
    TEST_ASSERT_NOT_NULL(cap);
    cap->total++;
    cap->last_done  = cy_future_done(future);
    cap->last_error = cy_future_error(future);
    if (cap->last_done) {
        cap->done++;
        cap->saw_done_delivery = cap->saw_done_delivery || (cap->last_error == CY_ERR_DELIVERY);
    } else {
        cap->pending++;
        cap->saw_pending_media = cap->saw_pending_media || (cap->last_error == CY_ERR_MEDIA);
        cap->saw_pending_lag   = cap->saw_pending_lag || (cap->last_error == CY_ERR_LAG);
    }
}

void test_api_rpc_e2e_r01_argument_validation()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    cy_publisher_t* const client = make_client(net, "rpc/r01/topic");
    const cy_bytes_t      empty  = { .size = 0U, .data = nullptr, .next = nullptr };
    const cy_bytes_t      bad    = { .size = 1U, .data = nullptr, .next = nullptr };

    TEST_ASSERT_NULL(cy_request(nullptr, now + 100'000, 50'000, empty));
    TEST_ASSERT_NULL(cy_request(client, -1, 50'000, empty));
    TEST_ASSERT_NULL(cy_request(client, now + 100'000, -1, empty));
    TEST_ASSERT_NULL(cy_request(client, now + 100'000, 50'000, bad));
    cy_future_t* const valid_empty = cy_request(client, now + 100'000, 50'000, empty);
    TEST_ASSERT_NOT_NULL(valid_empty);
    cy_future_destroy(valid_empty);

    const cy_response_t none_from_null = cy_response_move(nullptr);
    TEST_ASSERT_NULL(none_from_null.message.content);

    const auto         payload = e2e::app_payload_pack(42U, 1U);
    const cy_bytes_t   msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    cy_future_t* const pub_fut = cy_publish_reliable(client, now + 100'000, msg);
    TEST_ASSERT_NOT_NULL(pub_fut);
    const cy_response_t none_from_wrong_type = cy_response_move(pub_fut);
    TEST_ASSERT_NULL(none_from_wrong_type.message.content);
    cy_future_destroy(pub_fut);

    cleanup_case(net, now, {}, {}, { client });
}

void test_api_rpc_e2e_r02_single_response_success_and_move_semantics()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r02/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    cy_future_t* const           server_sub = make_server_subscriber(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 1U, 1U, 200'000, 200'000);
    TEST_ASSERT_NOT_NULL(request);

    TEST_ASSERT_TRUE(wait_until_done(net, now, request, wait_timeout_us));
    assert_request_state(request, true, CY_OK);
    TEST_ASSERT_EQUAL_size_t(1U, server.request_count);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, server.first_respond_error);

    const cy_response_t response = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(response.message.content);
    TEST_ASSERT_EQUAL_UINT64(e2e::sim_net_node_id(net, e2e::sim_node_b), response.remote_id);
    TEST_ASSERT_EQUAL_UINT64(0U, response.seqno);
    e2e::app_payload_t payload{};
    TEST_ASSERT_TRUE(unpack_response_payload(response, payload));
    TEST_ASSERT_EQUAL_UINT32(server.response_publisher_id, payload.publisher_id);
    TEST_ASSERT_EQUAL_UINT64(1U, payload.sequence);
    cy_message_refcount_dec(response.message.content);

    TEST_ASSERT_FALSE(cy_future_done(request));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(request));
    const cy_response_t none = cy_response_move(request);
    TEST_ASSERT_NULL(none.message.content);

    drive_for(net, now, 220'000);
    assert_request_state(request, true, CY_ERR_LIVENESS);

    cleanup_case(net, now, { request }, { server_sub }, { client });
}

void test_api_rpc_e2e_r03_stream_overwrite_latest_wins()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r03/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    server.responses_per_request  = 3U;
    cy_future_t* const server_sub = make_server_subscriber(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 2U, 1U, 200'000, 200'000);
    TEST_ASSERT_NOT_NULL(request);

    TEST_ASSERT_TRUE(wait_until_done(net, now, request, wait_timeout_us));
    assert_request_state(request, true, CY_OK);
    TEST_ASSERT_EQUAL_size_t(1U, server.request_count);
    TEST_ASSERT_EQUAL_UINT64(3U, server.response_seq);

    const cy_response_t response = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(response.message.content);
    TEST_ASSERT_EQUAL_UINT64(2U, response.seqno);
    e2e::app_payload_t payload{};
    TEST_ASSERT_TRUE(unpack_response_payload(response, payload));
    TEST_ASSERT_EQUAL_UINT64(3U, payload.sequence);
    cy_message_refcount_dec(response.message.content);

    cleanup_case(net, now, { request }, { server_sub }, { client });
}

void test_api_rpc_e2e_r04_failure_then_late_success_transition()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r04/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    server.responses_per_request  = 0U;
    cy_future_t* const server_sub = make_server_subscriber(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 3U, 1U, 80'000, 40'000);
    TEST_ASSERT_NOT_NULL(request);

    const request_wire_info_t req_wire = last_request_wire(net);
    TEST_ASSERT_TRUE(wait_until_done(net, now, request, wait_timeout_us));
    assert_request_state(request, true, CY_ERR_LIVENESS);

    const auto payload = e2e::app_payload_pack(900U, 1U);
    inject_response_wire(net,
                         header_rsp_be,
                         0U,
                         0U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 1);
    assert_request_state(request, true, CY_OK);

    const cy_response_t response = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(response.message.content);
    e2e::app_payload_t got{};
    TEST_ASSERT_TRUE(unpack_response_payload(response, got));
    TEST_ASSERT_EQUAL_UINT32(900U, got.publisher_id);
    TEST_ASSERT_EQUAL_UINT64(1U, got.sequence);
    cy_message_refcount_dec(response.message.content);

    cleanup_case(net, now, { request }, { server_sub }, { client });
}

void test_api_rpc_e2e_r05_reliable_response_ack_and_duplicate_ack()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r05/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    server.responses_per_request  = 0U;
    cy_future_t* const server_sub = make_server_subscriber(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 4U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);

    const request_wire_info_t req_wire = last_request_wire(net);
    const std::size_t         before   = e2e::sim_net_captures(net).size();

    const auto payload = e2e::app_payload_pack(901U, 1U);
    inject_response_wire(net,
                         header_rsp_rel,
                         0x42U,
                         0U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 1);
    assert_request_state(request, true, CY_OK);
    std::vector<response_control_t> controls = response_controls_since(net, before);
    TEST_ASSERT_EQUAL_size_t(1U, controls.size());
    TEST_ASSERT_EQUAL_UINT8(header_rsp_ack, controls.at(0).header_type);
    TEST_ASSERT_EQUAL_UINT8(0x42U, controls.at(0).tag);
    TEST_ASSERT_EQUAL_UINT64(0U, controls.at(0).seqno);
    TEST_ASSERT_EQUAL_UINT64(req_wire.topic_hash, controls.at(0).topic_hash);
    TEST_ASSERT_EQUAL_UINT64(req_wire.tag, controls.at(0).message_tag);

    const cy_response_t first = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(first.message.content);
    cy_message_refcount_dec(first.message.content);
    TEST_ASSERT_FALSE(cy_future_done(request));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(request));

    const std::size_t before_dup = e2e::sim_net_captures(net).size();
    inject_response_wire(net,
                         header_rsp_rel,
                         0x42U,
                         0U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 2);
    controls = response_controls_since(net, before_dup);
    TEST_ASSERT_EQUAL_size_t(1U, controls.size());
    TEST_ASSERT_EQUAL_UINT8(header_rsp_ack, controls.at(0).header_type);
    assert_request_state(request, false, CY_OK);
    const cy_response_t none = cy_response_move(request);
    TEST_ASSERT_NULL(none.message.content);

    cleanup_case(net, now, { request }, { server_sub }, { client });
}

void test_api_rpc_e2e_r06_reliable_response_history_nack_and_unknown_nack()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r06/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    server.responses_per_request  = 0U;
    cy_future_t* const server_sub = make_server_subscriber(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 5U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);
    const request_wire_info_t req_wire = last_request_wire(net);

    const auto        payload  = e2e::app_payload_pack(902U, 1U);
    const std::size_t before_a = e2e::sim_net_captures(net).size();
    inject_response_wire(net,
                         header_rsp_rel,
                         0x33U,
                         300U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 1);
    std::vector<response_control_t> controls = response_controls_since(net, before_a);
    TEST_ASSERT_EQUAL_size_t(1U, controls.size());
    TEST_ASSERT_EQUAL_UINT8(header_rsp_ack, controls.at(0).header_type);

    const cy_response_t first = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(first.message.content);
    cy_message_refcount_dec(first.message.content);

    const std::size_t before_b = e2e::sim_net_captures(net).size();
    inject_response_wire(net,
                         header_rsp_rel,
                         0x34U,
                         0U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 2);
    controls = response_controls_since(net, before_b);
    TEST_ASSERT_EQUAL_size_t(1U, controls.size());
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, controls.at(0).header_type);

    const std::size_t before_c = e2e::sim_net_captures(net).size();
    inject_response_wire(net,
                         header_rsp_rel,
                         0x35U,
                         0U,
                         req_wire.topic_hash + 123U,
                         req_wire.tag + 100U,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 3);
    controls = response_controls_since(net, before_c);
    TEST_ASSERT_EQUAL_size_t(1U, controls.size());
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, controls.at(0).header_type);

    cleanup_case(net, now, { request }, { server_sub }, { client });
}

void test_api_rpc_e2e_r07_zombie_ack_seen_nack_unseen()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r07/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    server.responses_per_request  = 0U;
    cy_future_t* const server_sub = make_server_subscriber(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 6U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);
    const request_wire_info_t req_wire = last_request_wire(net);

    const auto payload = e2e::app_payload_pack(903U, 1U);
    inject_response_wire(net,
                         header_rsp_rel,
                         0x55U,
                         5U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 1);
    const cy_response_t first = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(first.message.content);
    cy_message_refcount_dec(first.message.content);

    cy_future_destroy(request);

    const std::size_t before_dup = e2e::sim_net_captures(net).size();
    inject_response_wire(net,
                         header_rsp_rel,
                         0x55U,
                         5U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 2);
    std::vector<response_control_t> controls = response_controls_since(net, before_dup);
    TEST_ASSERT_EQUAL_size_t(1U, controls.size());
    TEST_ASSERT_EQUAL_UINT8(header_rsp_ack, controls.at(0).header_type);

    const std::size_t before_new = e2e::sim_net_captures(net).size();
    inject_response_wire(net,
                         header_rsp_rel,
                         0x56U,
                         6U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 3);
    controls = response_controls_since(net, before_new);
    TEST_ASSERT_EQUAL_size_t(1U, controls.size());
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, controls.at(0).header_type);

    cleanup_case(net, now, {}, { server_sub }, { client });
}

void test_api_rpc_e2e_r08_multicast_response_is_rejected()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r08/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    server.responses_per_request  = 0U;
    cy_future_t* const server_sub = make_server_subscriber(net, topic_name, server);
    cy_future_t* const sink_sub   = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("rpc/r08/sink"), 64U);
    TEST_ASSERT_NOT_NULL(sink_sub);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 7U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);
    const request_wire_info_t req_wire = last_request_wire(net);

    const auto        payload = e2e::app_payload_pack(904U, 1U);
    const std::size_t before  = e2e::sim_net_captures(net).size();
    inject_response_wire(net,
                         header_rsp_rel,
                         0x21U,
                         0U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 1,
                         true);
    const std::vector<response_control_t> controls = response_controls_since(net, before);
    TEST_ASSERT_TRUE(controls.empty());
    assert_request_state(request, false, CY_OK);

    const std::size_t before_msg_ack = e2e::sim_net_captures(net).size();
    inject_response_wire(net, header_msg_ack, 0U, 0U, req_wire.topic_hash, req_wire.tag, {}, now + 2, true);
    const std::vector<response_control_t> controls_msg_ack = response_controls_since(net, before_msg_ack);
    TEST_ASSERT_TRUE(controls_msg_ack.empty());
    assert_request_state(request, false, CY_OK);

    cleanup_case(net, now, { request }, { sink_sub, server_sub }, { client });
}

void test_api_rpc_e2e_r09_request_callback_status_transitions()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r09/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    server.responses_per_request  = 0U;
    cy_future_t* const server_sub = make_server_subscriber(net, topic_name, server);
    callback_capture_t cb{};

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 8U, 1U, 80'000, 40'000, on_request_future, &cb);
    TEST_ASSERT_NOT_NULL(request);
    const request_wire_info_t req_wire = last_request_wire(net);

    TEST_ASSERT_TRUE(wait_until_done(net, now, request, wait_timeout_us));
    assert_request_state(request, true, CY_ERR_LIVENESS);
    TEST_ASSERT_TRUE(cb.done_error >= 1U);

    const auto payload = e2e::app_payload_pack(905U, 1U);
    inject_response_wire(net,
                         header_rsp_be,
                         0U,
                         0U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 1);
    assert_request_state(request, true, CY_OK);
    TEST_ASSERT_TRUE(cb.done_ok >= 1U);

    const cy_response_t response = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(response.message.content);
    cy_message_refcount_dec(response.message.content);
    assert_request_state(request, false, CY_OK);

    drive_for(net, now, 80'000);
    assert_request_state(request, true, CY_ERR_LIVENESS);
    TEST_ASSERT_TRUE(cb.done_error >= 2U);
    TEST_ASSERT_TRUE(cb.total >= 3U);

    cleanup_case(net, now, { request }, { server_sub }, { client });
}

void test_api_rpc_e2e_r10_initial_publish_failure_returns_null()
{
    e2e::op_fault_plan_t op_faults{};
    e2e::op_fault_plan_add_fail(op_faults, CY_ERR_MEDIA, e2e::op_fault_predicate_all());

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_op_faults_set(net, &op_faults);
    cy_us_t now = 0;

    cy_publisher_t* const client = make_client(net, "rpc/r10/topic");
    set_now(net, now);
    TEST_ASSERT_NULL(request_once(client, now, 9U, 1U, 80'000, 40'000));

    e2e::sim_net_op_faults_set(net, nullptr);
    cleanup_case(net, now, {}, {}, { client });
}

void test_api_rpc_e2e_r11_request_publish_fails_without_response()
{
    e2e::fault_plan_t frame_faults{};
    e2e::fault_plan_add_drop(
      frame_faults,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_direction(e2e::sim_node_a, e2e::sim_node_b),
                                    e2e::fault_predicate_header_type(header_msg_rel) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_faults_set(net, &frame_faults);
    cy_us_t now = 0;

    cy_publisher_t* const client = make_client(net, "rpc/r11/topic");
    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 10U, 1U, 80'000, 60'000);
    TEST_ASSERT_NOT_NULL(request);

    TEST_ASSERT_TRUE(wait_until_done(net, now, request, wait_timeout_us));
    TEST_ASSERT_TRUE(cy_future_done(request));
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cy_future_error(request));

    cleanup_case(net, now, { request }, {}, { client });
}

void test_api_rpc_e2e_r12_concurrent_requests_are_correlated()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r12/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    cy_future_t* const           server_sub = make_server_subscriber(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const req_a = request_once(client, now, 11U, 1U, 250'000, 200'000);
    cy_future_t* const req_b = request_once(client, now, 11U, 2U, 250'000, 200'000);
    TEST_ASSERT_NOT_NULL(req_a);
    TEST_ASSERT_NOT_NULL(req_b);

    TEST_ASSERT_TRUE(wait_until_done(net, now, req_a, wait_timeout_us));
    TEST_ASSERT_TRUE(wait_until_done(net, now, req_b, wait_timeout_us));
    assert_request_state(req_a, true, CY_OK);
    assert_request_state(req_b, true, CY_OK);
    TEST_ASSERT_EQUAL_size_t(2U, server.request_count);

    const cy_response_t a = cy_response_move(req_a);
    const cy_response_t b = cy_response_move(req_b);
    TEST_ASSERT_NOT_NULL(a.message.content);
    TEST_ASSERT_NOT_NULL(b.message.content);
    e2e::app_payload_t pa{};
    e2e::app_payload_t pb{};
    TEST_ASSERT_TRUE(unpack_response_payload(a, pa));
    TEST_ASSERT_TRUE(unpack_response_payload(b, pb));
    cy_message_refcount_dec(a.message.content);
    cy_message_refcount_dec(b.message.content);
    TEST_ASSERT_TRUE(pa.sequence != pb.sequence);

    cleanup_case(net, now, { req_a, req_b }, { server_sub }, { client });
}

void test_api_rpc_e2e_r13_reliable_response_unknown_request_tag_nack()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r13/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    server.responses_per_request  = 0U;
    cy_future_t* const server_sub = make_server_subscriber(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 12U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);
    const request_wire_info_t req_wire = last_request_wire(net);

    const auto        payload = e2e::app_payload_pack(910U, 1U);
    const std::size_t before  = e2e::sim_net_captures(net).size();
    inject_response_wire(net,
                         header_rsp_rel,
                         0x61U,
                         0U,
                         req_wire.topic_hash,
                         req_wire.tag + 1U,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 1);

    const std::vector<response_control_t> controls = response_controls_since(net, before);
    TEST_ASSERT_EQUAL_size_t(1U, controls.size());
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, controls.at(0).header_type);
    TEST_ASSERT_EQUAL_UINT64(req_wire.topic_hash, controls.at(0).topic_hash);
    TEST_ASSERT_EQUAL_UINT64(req_wire.tag + 1U, controls.at(0).message_tag);
    assert_request_state(request, false, CY_OK);

    cleanup_case(net, now, { request }, { server_sub }, { client });
}

void test_api_rpc_e2e_r14_zombie_unseen_remote_reliable_response_nack()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r14/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    server.responses_per_request  = 0U;
    cy_future_t* const server_sub = make_server_subscriber(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 13U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);
    const request_wire_info_t req_wire = last_request_wire(net);

    const auto          payload     = e2e::app_payload_pack(911U, 1U);
    const std::uint64_t remote_seed = e2e::sim_net_node_id(net, e2e::sim_node_a);
    inject_response_wire(net,
                         header_rsp_rel,
                         0x62U,
                         5U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 1,
                         false,
                         remote_seed);
    const cy_response_t accepted = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(accepted.message.content);
    cy_message_refcount_dec(accepted.message.content);

    cy_future_destroy(request);

    const std::size_t before = e2e::sim_net_captures(net).size();
    inject_response_wire(net,
                         header_rsp_rel,
                         0x63U,
                         6U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 2);

    const std::vector<response_control_t> controls = response_controls_since(net, before);
    TEST_ASSERT_EQUAL_size_t(1U, controls.size());
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, controls.at(0).header_type);
    TEST_ASSERT_EQUAL_UINT64(6U, controls.at(0).seqno);

    cleanup_case(net, now, {}, { server_sub }, { client });
}

void test_api_rpc_e2e_r15_publish_failure_after_response_keeps_future_alive_until_liveness()
{
    e2e::fault_plan_t frame_faults{};
    e2e::fault_plan_add_drop(
      frame_faults,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_direction(e2e::sim_node_b, e2e::sim_node_a),
                                    e2e::fault_predicate_header_type(header_msg_ack) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_faults_set(net, &frame_faults);
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r15/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    server.responses_per_request  = 0U;
    cy_future_t* const server_sub = make_server_subscriber(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 14U, 1U, 80'000, 140'000);
    TEST_ASSERT_NOT_NULL(request);
    const request_wire_info_t req_wire = last_request_wire(net);

    const auto payload = e2e::app_payload_pack(912U, 1U);
    inject_response_wire(net,
                         header_rsp_be,
                         0U,
                         0U,
                         req_wire.topic_hash,
                         req_wire.tag,
                         std::vector<unsigned char>(payload.begin(), payload.end()),
                         now + 1);
    assert_request_state(request, true, CY_OK);
    const cy_response_t response = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(response.message.content);
    cy_message_refcount_dec(response.message.content);
    assert_request_state(request, false, CY_OK);

    drive_for(net, now, 120'000);
    assert_request_state(request, false, CY_ERR_DELIVERY);

    drive_for(net, now, 80'000);
    assert_request_state(request, true, CY_ERR_LIVENESS);

    e2e::sim_net_faults_set(net, nullptr);
    cleanup_case(net, now, { request }, { server_sub }, { client });
}

void test_api_rpc_e2e_r16_request_future_allocation_failure_returns_null()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    cy_publisher_t* const client = make_client(net, "rpc/r16/topic");
    install_fail_next_new_alloc(net, e2e::sim_node_a, 1U);
    set_now(net, now);
    TEST_ASSERT_NULL(request_once(client, now, 15U, 1U, 120'000, 120'000));
    restore_realloc_wrapper();

    cleanup_case(net, now, {}, {}, { client });
}

void test_api_rpc_e2e_r17_server_reliable_response_ack_success()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r17/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    reliable_server_context_t    server{};
    cy_future_t* const           server_sub = make_server_subscriber_reliable(net, topic_name, server);

    set_now(net, now);
    const std::size_t  before_controls = e2e::sim_net_captures(net).size();
    cy_future_t* const request         = request_once(client, now, 17U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);

    TEST_ASSERT_TRUE(wait_until(net, now, wait_timeout_us, [&server, request]() {
        return (server.futures.size() == 1U) && cy_future_done(request) && cy_future_done(server.futures.front());
    }));
    TEST_ASSERT_EQUAL_size_t(0U, server.submit_failures);
    TEST_ASSERT_EQUAL_size_t(1U, server.request_count);
    assert_request_state(request, true, CY_OK);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(server.futures.front()));

    const std::vector<response_control_t> controls = response_controls_since(net, before_controls);
    const bool                            seen_ack =
      std::ranges::any_of(controls, [](const response_control_t& ctl) { return ctl.header_type == header_rsp_ack; });
    TEST_ASSERT_TRUE(seen_ack);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_response_count(request));

    const cy_response_t response = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(response.message.content);
    e2e::app_payload_t payload{};
    TEST_ASSERT_TRUE(unpack_response_payload(response, payload));
    TEST_ASSERT_EQUAL_UINT32(server.response_publisher_id, payload.publisher_id);
    TEST_ASSERT_EQUAL_UINT64(1U, payload.sequence);
    cy_message_refcount_dec(response.message.content);

    cleanup_case(net, now, { request, server.futures.front() }, { server_sub }, { client });
}

void test_api_rpc_e2e_r18_server_reliable_response_nack_after_request_destroy()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char*       topic_name = "rpc/r18/topic";
    cy_publisher_t* const              client     = make_client(net, topic_name);
    deferred_reliable_server_context_t server{};
    cy_future_t* const                 server_sub = make_server_subscriber_capture_only(net, topic_name, server);

    set_now(net, now);
    cy_future_t* request = request_once(client, now, 18U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);

    TEST_ASSERT_TRUE(wait_until(net, now, wait_timeout_us, [&server]() { return server.captured; }));
    TEST_ASSERT_EQUAL_size_t(1U, server.request_count);
    cy_future_destroy(request);
    request = nullptr;

    set_now(net, now);
    const auto         payload         = e2e::app_payload_pack(980U, 1U);
    const cy_bytes_t   msg             = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    const std::size_t  before_controls = e2e::sim_net_captures(net).size();
    cy_future_t* const respond_future  = cy_respond_reliable(&server.breadcrumb, now + respond_deadline, msg);
    TEST_ASSERT_NOT_NULL(respond_future);

    TEST_ASSERT_TRUE(wait_until_done(net, now, respond_future, wait_timeout_us));
    TEST_ASSERT_TRUE(cy_future_done(respond_future));
    TEST_ASSERT_EQUAL_INT(CY_ERR_NACK, cy_future_error(respond_future));

    const std::vector<response_control_t> controls = response_controls_since(net, before_controls);
    const bool                            seen_nack =
      std::ranges::any_of(controls, [](const response_control_t& ctl) { return ctl.header_type == header_rsp_nack; });
    TEST_ASSERT_TRUE(seen_nack);

    cleanup_case(net, now, { respond_future }, { server_sub }, { client });
}

void test_api_rpc_e2e_r19_server_reliable_response_ack_blackout_times_out()
{
    e2e::fault_plan_t frame_faults{};
    e2e::fault_plan_add_drop(
      frame_faults,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_direction(e2e::sim_node_a, e2e::sim_node_b),
                                    e2e::fault_predicate_header_type(header_rsp_ack) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_faults_set(net, &frame_faults);
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r19/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    cy_priority_set(client, cy_prio_exceptional); // Ensure retry window fits inside respond deadline.
    reliable_server_context_t server{};
    cy_future_t* const        server_sub = make_server_subscriber_reliable(net, topic_name, server);

    set_now(net, now);
    const std::size_t  before  = e2e::sim_net_captures(net).size();
    cy_future_t* const request = request_once(client, now, 19U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);

    TEST_ASSERT_TRUE(wait_until(net, now, wait_timeout_us, [&server]() {
        return (server.futures.size() == 1U) && cy_future_done(server.futures.front());
    }));
    TEST_ASSERT_TRUE(wait_until_done(net, now, request, wait_timeout_us));
    TEST_ASSERT_EQUAL_size_t(0U, server.submit_failures);
    assert_request_state(request, true, CY_OK);
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cy_future_error(server.futures.front()));
    TEST_ASSERT_EQUAL_UINT64(1U, cy_response_count(request));

    std::size_t rsp_rel_count = 0U;
    for (const e2e::frame_capture_t& cap : e2e::sim_net_captures(net)) {
        if (cap.dropped) {
            continue;
        }
        if ((cap.frame.source == e2e::sim_node_b) && (cap.frame.destination == e2e::sim_node_a) &&
            (cap.frame.header_type == header_rsp_rel)) {
            rsp_rel_count++;
        }
    }
    TEST_ASSERT_TRUE(rsp_rel_count > 1U);
    std::size_t dropped_ack_count = 0U;
    for (const e2e::frame_capture_t& cap : e2e::sim_net_captures(net)) {
        if (!cap.dropped) {
            continue;
        }
        if ((cap.frame.source == e2e::sim_node_a) && (cap.frame.destination == e2e::sim_node_b) &&
            (cap.frame.header_type == header_rsp_ack)) {
            dropped_ack_count++;
        }
    }
    TEST_ASSERT_TRUE(dropped_ack_count > 0U);
    TEST_ASSERT_TRUE(response_controls_since(net, before).empty());

    e2e::sim_net_faults_set(net, nullptr);
    cleanup_case(net, now, { request, server.futures.front() }, { server_sub }, { client });
}

void test_api_rpc_e2e_r20_server_reliable_response_late_ack_does_not_resurrect()
{
    constexpr cy_us_t ack_delay = 260'000;

    e2e::fault_plan_t frame_faults{};
    e2e::fault_plan_add_delay(
      frame_faults,
      ack_delay,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_direction(e2e::sim_node_a, e2e::sim_node_b),
                                    e2e::fault_predicate_header_type(header_rsp_ack) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_faults_set(net, &frame_faults);
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r20/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    cy_priority_set(client, cy_prio_exceptional); // Prevent one-shot mode so delayed ACK arrives after retries fail.
    reliable_server_context_t server{};
    cy_future_t* const        server_sub = make_server_subscriber_reliable(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 20U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);

    TEST_ASSERT_TRUE(wait_until(net, now, wait_timeout_us, [&server]() {
        return (server.futures.size() == 1U) && cy_future_done(server.futures.front());
    }));
    TEST_ASSERT_TRUE(wait_until_done(net, now, request, wait_timeout_us));
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cy_future_error(server.futures.front()));

    drive_for(net, now, ack_delay + 80'000);
    TEST_ASSERT_TRUE(cy_future_done(server.futures.front()));
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cy_future_error(server.futures.front()));

    e2e::sim_net_faults_set(net, nullptr);
    cleanup_case(net, now, { request, server.futures.front() }, { server_sub }, { client });
}

void test_api_rpc_e2e_r21_server_reliable_response_stream_two_messages()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r21/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    reliable_server_context_t    server{};
    server.responses_per_request  = 2U;
    cy_future_t* const server_sub = make_server_subscriber_reliable(net, topic_name, server);

    set_now(net, now);
    const std::size_t  before_controls = e2e::sim_net_captures(net).size();
    cy_future_t* const request         = request_once(client, now, 21U, 1U, 250'000, 250'000);
    TEST_ASSERT_NOT_NULL(request);

    TEST_ASSERT_TRUE(wait_until(net, now, wait_timeout_us, [&server, request]() {
        return (server.futures.size() == 2U) && cy_future_done(server.futures.at(0)) &&
               cy_future_done(server.futures.at(1)) && cy_future_done(request);
    }));
    TEST_ASSERT_EQUAL_size_t(0U, server.submit_failures);
    assert_request_state(request, true, CY_OK);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(server.futures.at(0)));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(server.futures.at(1)));
    TEST_ASSERT_EQUAL_UINT64(2U, cy_response_count(request));

    const std::vector<response_control_t> controls  = response_controls_since(net, before_controls);
    bool                                  seen_seq0 = false;
    bool                                  seen_seq1 = false;
    for (const response_control_t& ctl : controls) {
        if (ctl.header_type != header_rsp_ack) {
            continue;
        }
        seen_seq0 = seen_seq0 || (ctl.seqno == 0U);
        seen_seq1 = seen_seq1 || (ctl.seqno == 1U);
    }
    TEST_ASSERT_TRUE(seen_seq0);
    TEST_ASSERT_TRUE(seen_seq1);

    const cy_response_t response = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(response.message.content);
    cy_message_refcount_dec(response.message.content);

    cleanup_case(net, now, { request, server.futures.at(0), server.futures.at(1) }, { server_sub }, { client });
}

void test_api_rpc_e2e_r22_response_count_invalid_future_returns_zero()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    cy_publisher_t* const client  = make_client(net, "rpc/r22/topic");
    const auto            payload = e2e::app_payload_pack(22U, 1U);
    const cy_bytes_t      msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };

    TEST_ASSERT_EQUAL_UINT64(0U, cy_response_count(nullptr));

    set_now(net, now);
    cy_future_t* const publish = cy_publish_reliable(client, now + 100'000, msg);
    TEST_ASSERT_NOT_NULL(publish);
    TEST_ASSERT_EQUAL_UINT64(0U, cy_response_count(publish));
    cy_future_destroy(publish);

    cleanup_case(net, now, {}, {}, { client });
}

void test_api_rpc_e2e_r23_respond_reliable_argument_validation()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char*       topic_name = "rpc/r23/topic";
    cy_publisher_t* const              client     = make_client(net, topic_name);
    deferred_reliable_server_context_t server{};
    cy_future_t* const                 server_sub = make_server_subscriber_capture_only(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 23U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);
    TEST_ASSERT_TRUE(wait_until(net, now, wait_timeout_us, [&server]() { return server.captured; }));

    const auto       payload = e2e::app_payload_pack(923U, 1U);
    const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    const cy_bytes_t bad     = { .size = 1U, .data = nullptr, .next = nullptr };
    const cy_bytes_t empty   = { .size = 0U, .data = nullptr, .next = nullptr };

    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_respond(nullptr, now + respond_deadline, msg));
    cy_breadcrumb_t invalid = server.breadcrumb;
    invalid.cy              = nullptr;
    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_respond(&invalid, now + respond_deadline, msg));
    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_respond(&server.breadcrumb, -1, msg));
    cy_breadcrumb_t empty_best_effort = server.breadcrumb;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_respond(&empty_best_effort, now + respond_deadline, empty));

    TEST_ASSERT_NULL(cy_respond_reliable(nullptr, now + respond_deadline, msg));

    invalid    = server.breadcrumb;
    invalid.cy = nullptr;
    TEST_ASSERT_NULL(cy_respond_reliable(&invalid, now + respond_deadline, msg));

    invalid                 = server.breadcrumb;
    const auto bad_priority = static_cast<std::uint8_t>(CY_PRIO_COUNT);
    std::memcpy(&invalid.priority, &bad_priority, sizeof(bad_priority));
    TEST_ASSERT_NULL(cy_respond_reliable(&invalid, now + respond_deadline, msg));

    TEST_ASSERT_NULL(cy_respond_reliable(&server.breadcrumb, -1, msg));
    TEST_ASSERT_NULL(cy_respond_reliable(&server.breadcrumb, now + respond_deadline, bad));
    cy_breadcrumb_t    empty_reliable_breadcrumb = server.breadcrumb;
    cy_future_t* const empty_reliable = cy_respond_reliable(&empty_reliable_breadcrumb, now + respond_deadline, empty);
    TEST_ASSERT_NOT_NULL(empty_reliable);
    cy_future_destroy(empty_reliable);

    cleanup_case(net, now, { request }, { server_sub }, { client });
}

void test_api_rpc_e2e_r24_respond_reliable_allocation_failures()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char*       topic_name = "rpc/r24/topic";
    cy_publisher_t* const              client     = make_client(net, topic_name);
    deferred_reliable_server_context_t server{};
    cy_future_t* const                 server_sub = make_server_subscriber_capture_only(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 24U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);
    TEST_ASSERT_TRUE(wait_until(net, now, wait_timeout_us, [&server]() { return server.captured; }));

    const auto       payload = e2e::app_payload_pack(924U, 1U);
    const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };

    cy_breadcrumb_t breadcrumb = server.breadcrumb;
    breadcrumb.priority        = cy_prio_exceptional; // Ensure non-one-shot path exists for bytes_dup().

    install_fail_next_new_alloc(net, e2e::sim_node_b, 1U); // Fail future_new().
    TEST_ASSERT_NULL(cy_respond_reliable(&breadcrumb, now + 220'000, msg));
    restore_realloc_wrapper();

    install_fail_new_alloc_after(net, e2e::sim_node_b, 1U, 1U); // Skip future_new(), fail bytes_dup().
    TEST_ASSERT_NULL(cy_respond_reliable(&breadcrumb, now + 220'000, msg));
    restore_realloc_wrapper();

    cleanup_case(net, now, { request }, { server_sub }, { client });
}

void test_api_rpc_e2e_r25_respond_reliable_tag_exhaustion_returns_null()
{
    e2e::fault_plan_t frame_faults{};
    e2e::fault_plan_add_drop(
      frame_faults,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_direction(e2e::sim_node_a, e2e::sim_node_b),
                                    e2e::fault_predicate_header_type(header_rsp_ack) }));
    e2e::fault_plan_add_drop(
      frame_faults,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_direction(e2e::sim_node_a, e2e::sim_node_b),
                                    e2e::fault_predicate_header_type(header_rsp_nack) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_faults_set(net, &frame_faults);
    cy_us_t now = 0;

    static constexpr const char*       topic_name = "rpc/r25/topic";
    cy_publisher_t* const              client     = make_client(net, topic_name);
    deferred_reliable_server_context_t server{};
    cy_future_t* const                 server_sub = make_server_subscriber_capture_only(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 25U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);
    TEST_ASSERT_TRUE(wait_until(net, now, wait_timeout_us, [&server]() { return server.captured; }));

    const auto       payload  = e2e::app_payload_pack(925U, 1U);
    const cy_bytes_t msg      = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    const cy_us_t    deadline = now + 120'000;

    std::vector<cy_future_t*> respond_futures{};
    respond_futures.reserve(256U);
    for (std::size_t i = 0U; i < 256U; i++) {
        cy_breadcrumb_t    breadcrumb = server.breadcrumb;
        cy_future_t* const fut        = cy_respond_reliable(&breadcrumb, deadline, msg);
        TEST_ASSERT_NOT_NULL(fut);
        respond_futures.push_back(fut);
    }

    cy_breadcrumb_t overflow = server.breadcrumb;
    TEST_ASSERT_NULL(cy_respond_reliable(&overflow, deadline, msg));

    e2e::sim_net_faults_set(net, nullptr);
    std::vector<cy_future_t*> cleanup_futures{ request };
    cleanup_futures.insert(cleanup_futures.end(), respond_futures.begin(), respond_futures.end());
    cleanup_case(net, now, cleanup_futures, { server_sub }, { client });
}

void test_api_rpc_e2e_r26_respond_reliable_retransmit_media_error_notifies_then_times_out()
{
    e2e::fault_plan_t frame_faults{};
    e2e::fault_plan_add_drop(
      frame_faults,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_direction(e2e::sim_node_a, e2e::sim_node_b),
                                    e2e::fault_predicate_header_type(header_rsp_ack) }));

    e2e::op_fault_plan_t op_faults{};
    e2e::op_fault_plan_add_fail(op_faults,
                                CY_ERR_MEDIA,
                                e2e::op_fault_predicate_all_of(
                                  { e2e::op_fault_predicate_node(e2e::sim_node_b),
                                    e2e::op_fault_predicate_kind(e2e::op_kind_t::unicast_send),
                                    e2e::op_fault_predicate_deadline(30'000, std::numeric_limits<cy_us_t>::max()) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_faults_set(net, &frame_faults);
    cy_us_t now = 0;

    static constexpr const char*       topic_name = "rpc/r26/topic";
    cy_publisher_t* const              client     = make_client(net, topic_name);
    deferred_reliable_server_context_t server{};
    cy_future_t* const                 server_sub = make_server_subscriber_capture_only(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 26U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);
    TEST_ASSERT_TRUE(wait_until(net, now, wait_timeout_us, [&server]() { return server.captured; }));

    cy_breadcrumb_t breadcrumb = server.breadcrumb;
    breadcrumb.priority        = cy_prio_exceptional;
    const auto       payload   = e2e::app_payload_pack(926U, 1U);
    const cy_bytes_t msg       = { .size = payload.size(), .data = payload.data(), .next = nullptr };

    cy_future_t* const respond = cy_respond_reliable(&breadcrumb, now + 220'000, msg);
    TEST_ASSERT_NOT_NULL(respond);
    future_event_capture_t cap{};
    cy_user_context_t      ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]                 = &cap;
    cy_future_context_set(respond, ctx);
    cy_future_callback_set(respond, on_future_event);

    e2e::sim_net_op_faults_set(net, &op_faults);

    TEST_ASSERT_TRUE(wait_until_done(net, now, respond, wait_timeout_us));
    TEST_ASSERT_TRUE(cy_future_done(respond));
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cy_future_error(respond));
    TEST_ASSERT_TRUE(cap.saw_pending_media);
    TEST_ASSERT_TRUE(cap.saw_done_delivery);

    const auto& async_errors = e2e::sim_net_async_errors(net);
    TEST_ASSERT_TRUE(!async_errors.empty());
    const bool saw_media_async = std::ranges::any_of(async_errors, [](const e2e::async_error_capture_t& err) {
        return (err.node_index == e2e::sim_node_b) && (err.error == CY_ERR_MEDIA);
    });
    TEST_ASSERT_TRUE(saw_media_async);

    e2e::sim_net_op_faults_set(net, nullptr);
    e2e::sim_net_faults_set(net, nullptr);
    e2e::sim_net_clear_captures(net); // Ignore expected async media-error diagnostics from this scenario.
    cleanup_case(net, now, { request, respond }, { server_sub }, { client });
}

void test_api_rpc_e2e_r27_respond_reliable_lag_paths()
{
    const auto run_case = [](const cy_us_t lag_offset_from_deadline, const bool expect_pending_lag) {
        e2e::fault_plan_t frame_faults{};
        e2e::fault_plan_add_drop(
          frame_faults,
          e2e::fault_predicate_all_of({ e2e::fault_predicate_direction(e2e::sim_node_a, e2e::sim_node_b),
                                        e2e::fault_predicate_header_type(header_rsp_ack) }));

        e2e::sim_net_t net{};
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
        e2e::sim_net_faults_set(net, &frame_faults);
        cy_us_t now = 0;

        static constexpr const char*       topic_name = "rpc/r27/topic";
        cy_publisher_t* const              client     = make_client(net, topic_name);
        deferred_reliable_server_context_t server{};
        cy_future_t* const                 server_sub = make_server_subscriber_capture_only(net, topic_name, server);

        set_now(net, now);
        cy_future_t* const request = request_once(client, now, 27U, 1U, 220'000, 220'000);
        TEST_ASSERT_NOT_NULL(request);
        TEST_ASSERT_TRUE(wait_until(net, now, wait_timeout_us, [&server]() { return server.captured; }));

        cy_breadcrumb_t breadcrumb = server.breadcrumb;
        breadcrumb.priority        = cy_prio_exceptional;
        const auto       payload   = e2e::app_payload_pack(927U, 1U);
        const cy_bytes_t msg       = { .size = payload.size(), .data = payload.data(), .next = nullptr };

        const cy_us_t      respond_deadline_local = now + 600'000;
        cy_future_t* const respond                = cy_respond_reliable(&breadcrumb, respond_deadline_local, msg);
        TEST_ASSERT_NOT_NULL(respond);
        future_event_capture_t cap{};
        cy_user_context_t      ctx = CY_USER_CONTEXT_EMPTY;
        ctx.ptr[0]                 = &cap;
        cy_future_context_set(respond, ctx);
        cy_future_callback_set(respond, on_future_event);

        // Force scheduler lag deterministically by jumping the simulated clock forward.
        now = respond_deadline_local + lag_offset_from_deadline;
        set_now(net, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;

        TEST_ASSERT_TRUE(wait_until_done(net, now, respond, wait_timeout_us));
        TEST_ASSERT_TRUE(cy_future_done(respond));
        TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cy_future_error(respond));
        TEST_ASSERT_EQUAL_INT(expect_pending_lag ? 1 : 0, cap.saw_pending_lag ? 1 : 0);
        TEST_ASSERT_TRUE(cap.saw_done_delivery);

        e2e::sim_net_faults_set(net, nullptr);
        cleanup_case(net, now, { request, respond }, { server_sub }, { client });
    };

    run_case(-10'000, true);  // Timeout fires late but still before deadline.
    run_case(+10'000, false); // Timeout fires after deadline: immediate completion branch.
}

void test_api_rpc_e2e_r28_request_introspection_and_borrow_contract()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "rpc/r28/topic";
    cy_publisher_t* const        client     = make_client(net, topic_name);
    server_context_t             server{};
    cy_future_t* const           server_sub = make_server_subscriber(net, topic_name, server);

    set_now(net, now);
    cy_future_t* const request = request_once(client, now, 28U, 1U, 220'000, 220'000);
    TEST_ASSERT_NOT_NULL(request);
    TEST_ASSERT_TRUE(cy_is_request(request));
    TEST_ASSERT_FALSE(cy_is_request(nullptr));

    const auto         payload = e2e::app_payload_pack(28U, 2U);
    const cy_bytes_t   msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    cy_future_t* const publish = cy_publish_reliable(client, now + 220'000, msg);
    TEST_ASSERT_NOT_NULL(publish);
    TEST_ASSERT_FALSE(cy_is_request(publish));

    cy_future_t* const subscriber = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("rpc/r28/sub"), 64U);
    TEST_ASSERT_NOT_NULL(subscriber);
    TEST_ASSERT_FALSE(cy_is_request(subscriber));

    TEST_ASSERT_TRUE(wait_until_done(net, now, request, wait_timeout_us));
    assert_request_state(request, true, CY_OK);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_response_count(request));

    const cy_response_t borrow_1 = cy_response_borrow(request);
    const cy_response_t borrow_2 = cy_response_borrow(request);
    TEST_ASSERT_NOT_NULL(borrow_1.message.content);
    TEST_ASSERT_NOT_NULL(borrow_2.message.content);
    TEST_ASSERT_TRUE(borrow_1.message.content == borrow_2.message.content);
    TEST_ASSERT_TRUE(cy_future_done(request));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(request));

    e2e::app_payload_t unpacked{};
    TEST_ASSERT_TRUE(unpack_response_payload(borrow_1, unpacked));
    TEST_ASSERT_EQUAL_UINT32(server.response_publisher_id, unpacked.publisher_id);
    TEST_ASSERT_EQUAL_UINT64(1U, unpacked.sequence);

    const cy_response_t moved = cy_response_move(request);
    TEST_ASSERT_NOT_NULL(moved.message.content);
    TEST_ASSERT_TRUE(moved.message.content == borrow_1.message.content);
    cy_message_refcount_dec(moved.message.content);

    TEST_ASSERT_FALSE(cy_future_done(request));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(request));
    TEST_ASSERT_NULL(cy_response_borrow(request).message.content);
    TEST_ASSERT_NULL(cy_response_borrow(publish).message.content);

    cleanup_case(net, now, { request, publish }, { server_sub, subscriber }, { client });
}

} // namespace

extern "C" void setUp()
{
    restore_realloc_wrapper();
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
    cy_test_message_reset_counters();
}

extern "C" void tearDown()
{
    restore_realloc_wrapper();
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
}

int main()
{
    UNITY_BEGIN();
    RUN_TEST(test_api_rpc_e2e_r01_argument_validation);
    RUN_TEST(test_api_rpc_e2e_r02_single_response_success_and_move_semantics);
    RUN_TEST(test_api_rpc_e2e_r03_stream_overwrite_latest_wins);
    RUN_TEST(test_api_rpc_e2e_r04_failure_then_late_success_transition);
    RUN_TEST(test_api_rpc_e2e_r05_reliable_response_ack_and_duplicate_ack);
    RUN_TEST(test_api_rpc_e2e_r06_reliable_response_history_nack_and_unknown_nack);
    RUN_TEST(test_api_rpc_e2e_r07_zombie_ack_seen_nack_unseen);
    RUN_TEST(test_api_rpc_e2e_r08_multicast_response_is_rejected);
    RUN_TEST(test_api_rpc_e2e_r09_request_callback_status_transitions);
    RUN_TEST(test_api_rpc_e2e_r10_initial_publish_failure_returns_null);
    RUN_TEST(test_api_rpc_e2e_r11_request_publish_fails_without_response);
    RUN_TEST(test_api_rpc_e2e_r12_concurrent_requests_are_correlated);
    RUN_TEST(test_api_rpc_e2e_r13_reliable_response_unknown_request_tag_nack);
    RUN_TEST(test_api_rpc_e2e_r14_zombie_unseen_remote_reliable_response_nack);
    RUN_TEST(test_api_rpc_e2e_r15_publish_failure_after_response_keeps_future_alive_until_liveness);
    RUN_TEST(test_api_rpc_e2e_r16_request_future_allocation_failure_returns_null);
    RUN_TEST(test_api_rpc_e2e_r17_server_reliable_response_ack_success);
    RUN_TEST(test_api_rpc_e2e_r18_server_reliable_response_nack_after_request_destroy);
    RUN_TEST(test_api_rpc_e2e_r19_server_reliable_response_ack_blackout_times_out);
    RUN_TEST(test_api_rpc_e2e_r20_server_reliable_response_late_ack_does_not_resurrect);
    RUN_TEST(test_api_rpc_e2e_r21_server_reliable_response_stream_two_messages);
    RUN_TEST(test_api_rpc_e2e_r22_response_count_invalid_future_returns_zero);
    RUN_TEST(test_api_rpc_e2e_r23_respond_reliable_argument_validation);
    RUN_TEST(test_api_rpc_e2e_r24_respond_reliable_allocation_failures);
    RUN_TEST(test_api_rpc_e2e_r25_respond_reliable_tag_exhaustion_returns_null);
    RUN_TEST(test_api_rpc_e2e_r26_respond_reliable_retransmit_media_error_notifies_then_times_out);
    RUN_TEST(test_api_rpc_e2e_r27_respond_reliable_lag_paths);
    RUN_TEST(test_api_rpc_e2e_r28_request_introspection_and_borrow_contract);
    return UNITY_END();
}
