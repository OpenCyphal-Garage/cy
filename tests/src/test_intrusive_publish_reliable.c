#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
#include <stddef.h>
#include <string.h>

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    cy_t                 cy;
    guarded_heap_t       heap;

    size_t fail_after;      ///< Fail N-th new allocation if new_alloc_count >= fail_after.
    size_t new_alloc_count; ///< Counts new allocations only, excludes realloc/free.
} fixture_t;

static void* fixture_realloc(cy_platform_t* const platform, void* const ptr, const size_t size)
{
    fixture_t* const self = (fixture_t*)platform;
    if ((ptr == NULL) && (size > 0U)) {
        if (self->new_alloc_count >= self->fail_after) {
            return NULL;
        }
        self->new_alloc_count++;
    }
    return guarded_heap_realloc(&self->heap, ptr, size);
}

static void fixture_init(fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->heap, UINT64_C(0xB17E5D0C1234ABCD));
    self->platform.vtable             = &self->vtable;
    self->platform.subject_id_modulus = (uint32_t)CY_SUBJECT_ID_MODULUS_17bit;
    self->platform.cy                 = &self->cy;
    self->vtable.realloc              = fixture_realloc;
    self->cy.platform                 = &self->platform;
    self->fail_after                  = SIZE_MAX;
    self->new_alloc_count             = 0;
}

static void fixture_set_fail_after(fixture_t* const self, const size_t fail_after)
{
    self->fail_after      = fail_after;
    self->new_alloc_count = 0;
}

static void test_publish_future_is_last_attempt_basic(void)
{
    // (100 + 50*2) = 200 > 200 is FALSE
    TEST_ASSERT_FALSE(publish_future_is_last_attempt(100, 50, 200));
    // (100 + 50*2) = 200 > 199 is TRUE
    TEST_ASSERT_TRUE(publish_future_is_last_attempt(100, 50, 199));
    // (0 + 0*2) = 0 > 0 is FALSE
    TEST_ASSERT_FALSE(publish_future_is_last_attempt(0, 0, 0));
    // (0 + 1*2) = 2 > 1 is TRUE
    TEST_ASSERT_TRUE(publish_future_is_last_attempt(0, 1, 1));
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_publish_future_is_last_attempt_basic);
    return UNITY_END();
}
