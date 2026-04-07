#include <cy_can.h>
#include <unity.h>
#include "guarded_heap.h"
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>

namespace {

constexpr cy_us_t     spin_slice_us  = 10'000;
constexpr std::size_t queue_capacity = 512U;

struct queued_frame_t
{
    std::uint32_t                      can_id{ 0U };
    std::uint_least8_t                 len{ 0U };
    bool                               fd{ false };
    std::array<std::uint_least8_t, 64> data{};
};

struct test_platform_t
{
    guarded_heap_t                             heap{};
    std::uint64_t                              random_state{ UINT64_C(0x123456789ABCDEF0) };
    cy_us_t                                    now{ 1000 };
    std::size_t                                tx_classic_count{ 0U };
    std::size_t                                rx_call_count{ 0U };
    std::size_t                                queue_head{ 0U };
    std::size_t                                queue_tail{ 0U };
    std::size_t                                queued_count{ 0U };
    std::array<queued_frame_t, queue_capacity> queue{};
};

struct fixture_t
{
    test_platform_t io{};
    cy_can_vtable_t vtable{};
    cy_platform_t*  platform{ nullptr };
    cy_t*           cy{ nullptr };
};

template <std::size_t Size>
std::array<unsigned char, Size> make_payload(const unsigned char seed)
{
    std::array<unsigned char, Size> out{};
    for (std::size_t i = 0U; i < out.size(); i++) {
        out.at(i) = static_cast<unsigned char>(seed + static_cast<unsigned char>(i));
    }
    return out;
}

void enqueue_frame(test_platform_t* const   self,
                   const std::uint32_t      can_id,
                   const bool               fd,
                   const void* const        data,
                   const std::uint_least8_t len)
{
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_TRUE(self->queued_count < self->queue.size());
    queued_frame_t& out = self->queue.at(self->queue_tail);
    out.can_id          = can_id;
    out.len             = len;
    out.fd              = fd;
    if (len > 0U) {
        (void)std::memcpy(out.data.data(), data, len);
    }
    self->queue_tail = (self->queue_tail + 1U) % self->queue.size();
    self->queued_count++;
}

bool dequeue_frame(test_platform_t* const self, cy_can_rx_t* const out_frame)
{
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_NOT_NULL(out_frame);
    if (self->queued_count == 0U) {
        return false;
    }
    const queued_frame_t& in = self->queue.at(self->queue_head);
    out_frame->timestamp     = self->now++;
    out_frame->can_id        = in.can_id;
    out_frame->iface_index   = 0U;
    out_frame->len           = in.len;
    out_frame->fd            = in.fd;
    if (in.len > 0U) {
        (void)std::memcpy(out_frame->data, in.data.data(), in.len);
    }
    self->queue_head = (self->queue_head + 1U) % self->queue.size();
    self->queued_count--;
    return true;
}

extern "C" bool platform_tx_classic(void* const              user,
                                    const std::uint_least8_t iface_index,
                                    const std::uint32_t      can_id,
                                    const void* const        data,
                                    const std::uint_least8_t len)
{
    auto* const self = static_cast<test_platform_t*>(user);
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_EQUAL_UINT8(0U, iface_index);
    TEST_ASSERT_TRUE(len <= 8U);
    self->tx_classic_count++;
    enqueue_frame(self, can_id, false, data, len);
    return true;
}

extern "C" bool platform_rx(void* const              user,
                            cy_can_rx_t* const       out_frame,
                            const cy_us_t            deadline,
                            const std::uint_least8_t tx_pending_iface_bitmap)
{
    (void)tx_pending_iface_bitmap;
    auto* const self = static_cast<test_platform_t*>(user);
    TEST_ASSERT_NOT_NULL(self);
    self->rx_call_count++;
    if (dequeue_frame(self, out_frame)) {
        return true;
    }
    if (self->now <= deadline) {
        self->now = deadline + 1;
    }
    return false;
}

extern "C" cy_us_t platform_now(void* const user)
{
    const auto* const self = static_cast<const test_platform_t*>(user);
    TEST_ASSERT_NOT_NULL(self);
    return self->now;
}

extern "C" void* platform_realloc(void* const user, void* const ptr, const std::size_t size)
{
    return guarded_heap_realloc(user, ptr, size);
}

extern "C" std::uint64_t platform_random(void* const user)
{
    auto* const self = static_cast<test_platform_t*>(user);
    TEST_ASSERT_NOT_NULL(self);
    self->random_state = (self->random_state * UINT64_C(6364136223846793005)) + UINT64_C(1);
    return self->random_state;
}

void fixture_init(fixture_t* const self)
{
    TEST_ASSERT_NOT_NULL(self);
    *self = fixture_t{};
    guarded_heap_init(&self->io.heap, UINT64_C(0xA5A55A5ADEADBEEF));
    self->io.now = 1000;

    self->vtable.tx_classic = platform_tx_classic;
    self->vtable.tx_fd      = nullptr;
    self->vtable.rx         = platform_rx;
    self->vtable.now        = platform_now;
    self->vtable.realloc    = platform_realloc;
    self->vtable.random     = platform_random;

    self->platform = cy_can_new(1U, 128U, 0U, &self->vtable, &self->io);
    TEST_ASSERT_NOT_NULL(self->platform);

    self->cy = cy_new(self->platform, cy_str("test_can"), cy_str_t{ 0U, nullptr });
    TEST_ASSERT_NOT_NULL(self->cy);
}

void fixture_deinit(fixture_t* const self)
{
    TEST_ASSERT_NOT_NULL(self);
    if (self->cy != nullptr) {
        cy_destroy(self->cy);
        self->cy = nullptr;
    }
    if (self->platform != nullptr) {
        cy_can_destroy(self->platform);
        self->platform = nullptr;
    }
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&self->io.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&self->io.heap));
}

void spin_until_done(fixture_t* const self, cy_future_t* const future)
{
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_NOT_NULL(future);
    for (std::size_t i = 0U; (i < 16U) && !cy_future_done(future); i++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(self->cy, cy_now(self->cy) + spin_slice_us));
    }
    TEST_ASSERT_TRUE(cy_future_done(future));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(future));
}

void spin_once(fixture_t* const self)
{
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(self->cy, cy_now(self->cy)));
}

template <std::size_t Size>
void publish_and_expect_payload(fixture_t* const                       self,
                                cy_publisher_t* const                  pub,
                                cy_future_t* const                     sub,
                                const std::array<unsigned char, Size>& payload)
{
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_NOT_NULL(sub);
    self->io.tx_classic_count = 0U;

    const cy_bytes_t msg = { payload.size(), payload.data(), nullptr };
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, cy_now(self->cy) + (10U * spin_slice_us), msg));
    spin_until_done(self, sub);
    TEST_ASSERT_TRUE(self->io.tx_classic_count > 0U);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub));

    const cy_arrival_t arrival = cy_arrival_borrow(sub);
    TEST_ASSERT_NOT_NULL(arrival.message.content);
    TEST_ASSERT_EQUAL_size_t(payload.size(), cy_message_size(arrival.message.content));

    std::array<unsigned char, Size> restored{};
    TEST_ASSERT_EQUAL_size_t(payload.size(),
                             cy_message_read(arrival.message.content, 0U, restored.size(), restored.data()));
    TEST_ASSERT_EQUAL_UINT8_ARRAY(payload.data(), restored.data(), payload.size());
}

void test_api_can_revives_verbatim_reader_and_preserves_extent()
{
    fixture_t fix{};
    fixture_init(&fix);

    static const char* const topic_name = "test/can/revive/verbatim";
    constexpr std::size_t    extent_old = 128U;
    constexpr std::size_t    extent_new = 64U;
    const auto               payload    = make_payload<96U>(0x10U);

    const std::size_t base_readers = cy_can_stats(fix.platform).subject_reader_count;
    TEST_ASSERT_EQUAL_size_t(1U, base_readers);

    cy_future_t* const first = cy_subscribe(fix.cy, cy_str(topic_name), extent_old);
    TEST_ASSERT_NOT_NULL(first);
    const std::size_t readers_after_first = cy_can_stats(fix.platform).subject_reader_count;
    TEST_ASSERT_TRUE(readers_after_first > base_readers);

    cy_future_destroy(first);
    spin_once(&fix);
    TEST_ASSERT_EQUAL_size_t(readers_after_first, cy_can_stats(fix.platform).subject_reader_count);

    cy_future_t* const second = cy_subscribe(fix.cy, cy_str(topic_name), extent_new);
    TEST_ASSERT_NOT_NULL(second);
    TEST_ASSERT_EQUAL_size_t(readers_after_first, cy_can_stats(fix.platform).subject_reader_count);

    cy_publisher_t* const pub = cy_advertise(fix.cy, cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(pub);
    publish_and_expect_payload(&fix, pub, second, payload);

    cy_unadvertise(pub);
    cy_future_destroy(second);
    spin_once(&fix);

    fixture_deinit(&fix);
}

void test_api_can_revives_pinned_reader_and_preserves_extent()
{
    fixture_t fix{};
    fixture_init(&fix);

    static const char* const topic_name = "123#123";
    constexpr std::size_t    extent_old = 128U;
    constexpr std::size_t    extent_new = 64U;
    const auto               payload    = make_payload<96U>(0x40U);

    const std::size_t base_readers = cy_can_stats(fix.platform).subject_reader_count;
    TEST_ASSERT_EQUAL_size_t(1U, base_readers);

    cy_future_t* const first = cy_subscribe(fix.cy, cy_str(topic_name), extent_old);
    TEST_ASSERT_NOT_NULL(first);
    const std::size_t readers_after_first = cy_can_stats(fix.platform).subject_reader_count;
    TEST_ASSERT_TRUE(readers_after_first > base_readers);

    cy_future_destroy(first);
    spin_once(&fix);
    TEST_ASSERT_EQUAL_size_t(readers_after_first, cy_can_stats(fix.platform).subject_reader_count);

    cy_future_t* const second = cy_subscribe(fix.cy, cy_str(topic_name), extent_new);
    TEST_ASSERT_NOT_NULL(second);
    TEST_ASSERT_EQUAL_size_t(readers_after_first, cy_can_stats(fix.platform).subject_reader_count);

    cy_publisher_t* const pub = cy_advertise(fix.cy, cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(pub);
    publish_and_expect_payload(&fix, pub, second, payload);

    cy_unadvertise(pub);
    cy_future_destroy(second);
    spin_once(&fix);

    fixture_deinit(&fix);
}

void test_api_can_reuses_tombstoned_broadcast_reader_after_cy_destroy()
{
    fixture_t fix{};
    fixture_init(&fix);

    const std::size_t base_readers = cy_can_stats(fix.platform).subject_reader_count;
    TEST_ASSERT_EQUAL_size_t(1U, base_readers);

    cy_destroy(fix.cy);
    fix.cy = nullptr;
    TEST_ASSERT_EQUAL_size_t(base_readers, cy_can_stats(fix.platform).subject_reader_count);

    fix.cy = cy_new(fix.platform, cy_str("test_can"), cy_str_t{ 0U, nullptr });
    TEST_ASSERT_NOT_NULL(fix.cy);
    TEST_ASSERT_EQUAL_size_t(base_readers, cy_can_stats(fix.platform).subject_reader_count);

    fixture_deinit(&fix);
}

} // namespace

extern "C" void setUp() {}

extern "C" void tearDown() {}

int main()
{
    UNITY_BEGIN();
    RUN_TEST(test_api_can_revives_verbatim_reader_and_preserves_extent);
    RUN_TEST(test_api_can_revives_pinned_reader_and_preserves_extent);
    RUN_TEST(test_api_can_reuses_tombstoned_broadcast_reader_after_cy_destroy);
    return UNITY_END();
}
