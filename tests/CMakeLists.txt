# Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

cmake_minimum_required(VERSION 3.24)
project(cy_tests C CXX)

set(CTEST_OUTPUT_ON_FAILURE ON)

include_directories(SYSTEM "${CMAKE_SOURCE_DIR}/lib")

set(unity_root "${CMAKE_SOURCE_DIR}/lib/unity")

function(cy_gen_test name compile_flags link_flags c_standard definitions)
    # Build Unity per-target to avoid mixing object architectures between -m32/-m64 variants etc.
    add_library("${name}_unity" STATIC "${unity_root}/src/unity.c")
    target_include_directories("${name}_unity" SYSTEM PUBLIC "${unity_root}/src")
    target_compile_definitions("${name}_unity" PUBLIC UNITY_INCLUDE_DOUBLE=1 UNITY_OUTPUT_COLOR=1 UNITY_SUPPORT_64=1)
    target_compile_options(
            "${name}_unity"
            PRIVATE
            ${compile_flags}
            -Wno-sign-conversion
            -Wno-conversion
            -Wno-switch-enum
            -Wno-float-equal
            -Wno-double-promotion
            -Wno-missing-declarations
    )
    target_link_options("${name}_unity" PRIVATE ${link_flags})
    set_target_properties(
            "${name}_unity"
            PROPERTIES
            C_STANDARD ${c_standard}
            C_STANDARD_REQUIRED ON
            C_EXTENSIONS OFF
            COMPILE_WARNING_AS_ERROR OFF
            C_CLANG_TIDY ""
            CXX_CLANG_TIDY ""
            C_CPPCHECK ""
            CXX_CPPCHECK ""
    )

    # Build the test executable.
    # Clang-Tidy and Cppcheck are mandatory in the test suite.
    add_executable(${name} ${ARGN})
    target_include_directories(
            ${name}
            PRIVATE
            ${CMAKE_SOURCE_DIR}/cy
            ${CMAKE_CURRENT_SOURCE_DIR}/src
            ${CMAKE_CURRENT_SOURCE_DIR}/platform_stubs
    )
    target_link_libraries(${name} PRIVATE "${name}_unity")
    target_compile_options(${name} PRIVATE ${compile_flags} -Wno-unused-function)
    target_link_options(${name} PRIVATE ${link_flags})
    if (definitions)
        target_compile_definitions(${name} PRIVATE ${definitions})
    endif ()
    set_target_properties(
            ${name}
            PROPERTIES
            C_STANDARD ${c_standard}
            C_STANDARD_REQUIRED ON
            C_EXTENSIONS OFF
            CXX_STANDARD 20
            CXX_STANDARD_REQUIRED ON
            CXX_EXTENSIONS OFF
            COMPILE_WARNING_AS_ERROR ON
    )

    # Register the test with CTest.
    add_test(NAME "run_${name}" COMMAND ${name})
endfunction()

function(cy_gen_test_arch_matrix name c_standard definitions)
    cy_gen_test("${name}_x64_c${c_standard}" "-m64" "-m64" "${c_standard}" "${definitions}" ${ARGN})
    cy_gen_test("${name}_x32_c${c_standard}" "-m32" "-m32" "${c_standard}" "${definitions}" ${ARGN})
endfunction()

function(cy_gen_test_intrusive_matrix name)
    cy_gen_test_arch_matrix("${name}" 99 "" ${ARGN})
    cy_gen_test_arch_matrix("${name}" 11 "" ${ARGN})
endfunction()

# INTRUSIVE TESTS.
# These tests have access to the library internals and are written in C.
# They should only be used for behaviors that cannot be efficiently tested through the public API,
# and should be kept to a minimum.
cy_gen_test_intrusive_matrix(test_intrusive_dedup
        src/test_intrusive_dedup.c
        src/helpers.c
        platform_stubs/guarded_heap.c
)
cy_gen_test_intrusive_matrix(test_intrusive_reordering
        src/test_intrusive_reordering.c
        src/helpers.c
        platform_stubs/guarded_heap.c
        platform_stubs/message.c
)

# API TESTS.
# These tests only have access to the public API and are written in modern C++.
# They should be preferred over intrusive tests whenever possible.
cy_gen_test_arch_matrix(test_api_rx 11 "CY_CONFIG_TRACE=1"
        src/test_api_rx.cpp
        ${CMAKE_SOURCE_DIR}/cy/cy.c
        src/helpers.c
        src/cy_trace.c
        platform_stubs/guarded_heap.c
        platform_stubs/message.c
)
cy_gen_test_arch_matrix(test_api_name 11 "CY_CONFIG_TRACE=1"
        src/test_api_name.cpp
        ${CMAKE_SOURCE_DIR}/cy/cy.c
        src/cy_trace.c
)
