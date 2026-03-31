#pragma once

#include <cy_platform.h>
#include <unity.h>
#include "guarded_heap.h"
#include <cstddef>
#include <cstdint>
#include <set>

namespace api_test {

/// Common base for all API test platform structs. Each test file inherits from this and adds test-specific fields.
/// The first member must remain cy_platform_t so that platform_from<T> reinterpret_cast works correctly.
struct test_platform_base_t
{
    cy_platform_t        platform{};
    cy_platform_vtable_t vtable{};
    guarded_heap_t       core_heap{};
    guarded_heap_t       message_heap{};
    cy_t*                cy{ nullptr };
    cy_us_t              now{ 0 };
    std::uint64_t        random_state{ UINT64_C(0x123456789ABCDEF0) };
    std::set<std::uint32_t> active_reader_subjects;
    std::set<std::uint32_t> active_writer_subjects;
};

struct subject_writer_t
{
    cy_subject_writer_t base{};
};

struct subject_reader_t
{
    cy_subject_reader_t base{};
    std::size_t         extent{ 0U };
};

template <typename Platform>
Platform* platform_from(cy_platform_t* const platform)
{
    return reinterpret_cast<Platform*>(platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
}

template <typename Platform>
const Platform* platform_from_const(const cy_platform_t* const platform)
{
    return reinterpret_cast<const Platform*>(platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
}

template <typename Platform>
cy_subject_writer_t* subject_writer_new(cy_platform_t* const platform, const std::uint32_t subject_id)
{
    Platform* const self = platform_from<Platform>(platform);
    auto* const writer = static_cast<subject_writer_t*>(guarded_heap_alloc(&self->core_heap, sizeof(subject_writer_t)));
    if (writer != nullptr) {
        writer->base.subject_id = subject_id;
    }
    return (writer != nullptr) ? &writer->base : nullptr;
}

template <typename Platform>
void subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    Platform* const self = platform_from<Platform>(platform);
    guarded_heap_free(&self->core_heap, writer);
}

template <typename Platform>
cy_subject_reader_t* subject_reader_new(cy_platform_t* const platform,
                                        const std::uint32_t  subject_id,
                                        const std::size_t    extent)
{
    Platform* const self = platform_from<Platform>(platform);
    auto* const reader = static_cast<subject_reader_t*>(guarded_heap_alloc(&self->core_heap, sizeof(subject_reader_t)));
    if (reader != nullptr) {
        reader->base.subject_id = subject_id;
        reader->extent          = extent;
    }
    return (reader != nullptr) ? &reader->base : nullptr;
}

template <typename Platform>
void subject_reader_extent_set(cy_platform_t* const       platform,
                               cy_subject_reader_t* const reader,
                               const std::size_t          extent)
{
    (void)platform;
    auto* const r = reinterpret_cast<subject_reader_t*>(reader); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
    r->extent     = extent;
}

template <typename Platform>
void subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    Platform* const self = platform_from<Platform>(platform);
    guarded_heap_free(&self->core_heap, reader);
}

template <typename Platform>
void* core_heap_realloc(cy_platform_t* const platform, void* const ptr, const std::size_t size)
{
    Platform* const self = platform_from<Platform>(platform);
    return guarded_heap_realloc(&self->core_heap, ptr, size);
}

template <typename Platform>
std::uint64_t random_lcg(cy_platform_t* const platform)
{
    Platform* const self = platform_from<Platform>(platform);
    self->random_state   = (self->random_state * UINT64_C(6364136223846793005)) + UINT64_C(1);
    return self->random_state;
}

inline void init_platform_base(cy_platform_t& platform, cy_platform_vtable_t& vtable)
{
    platform.cy                 = nullptr;
    platform.subject_id_modulus = static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit);
    platform.vtable             = &vtable;
}

inline void assert_heaps_clean(const guarded_heap_t& core_heap, const guarded_heap_t& message_heap)
{
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&core_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&core_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&message_heap));
}

// ----- Tracked subject management: allocation + active_*_subjects bookkeeping -----

template <typename Platform>
cy_subject_writer_t* subject_writer_new_tracked(cy_platform_t* const platform, const std::uint32_t subject_id)
{
    cy_subject_writer_t* const out = subject_writer_new<Platform>(platform, subject_id);
    if (out != nullptr) {
        Platform* const self = platform_from<Platform>(platform);
        TEST_ASSERT_EQUAL_INT(0, self->active_writer_subjects.count(subject_id));
        self->active_writer_subjects.insert(subject_id);
    }
    return out;
}

template <typename Platform>
void subject_writer_destroy_tracked(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    Platform* const self = platform_from<Platform>(platform);
    TEST_ASSERT_EQUAL_INT(1, self->active_writer_subjects.erase(writer->subject_id));
    subject_writer_destroy<Platform>(platform, writer);
}

template <typename Platform>
cy_subject_reader_t* subject_reader_new_tracked(cy_platform_t* const platform,
                                                const std::uint32_t  subject_id,
                                                const std::size_t    extent)
{
    cy_subject_reader_t* const out = subject_reader_new<Platform>(platform, subject_id, extent);
    if (out != nullptr) {
        Platform* const self = platform_from<Platform>(platform);
        TEST_ASSERT_EQUAL_INT(0, self->active_reader_subjects.count(subject_id));
        self->active_reader_subjects.insert(subject_id);
    }
    return out;
}

template <typename Platform>
void subject_reader_extent_set_tracked(cy_platform_t* const       platform,
                                       cy_subject_reader_t* const reader,
                                       const std::size_t          extent)
{
    Platform* const self = platform_from<Platform>(platform);
    TEST_ASSERT_EQUAL_INT(1, self->active_reader_subjects.count(reader->subject_id));
    subject_reader_extent_set<Platform>(platform, reader, extent);
}

template <typename Platform>
void subject_reader_destroy_tracked(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    Platform* const self = platform_from<Platform>(platform);
    TEST_ASSERT_EQUAL_INT(1, self->active_reader_subjects.erase(reader->subject_id));
    subject_reader_destroy<Platform>(platform, reader);
}

// ----- Standard teardown -----

template <typename Platform>
void standard_deinit(Platform& self)
{
    if (self.cy != nullptr) {
        cy_destroy(self.cy);
        self.cy = nullptr;
    }
    assert_heaps_clean(self.core_heap, self.message_heap);
}

} // namespace api_test
