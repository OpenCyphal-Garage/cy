# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy_tests C CXX)

set(CTEST_OUTPUT_ON_FAILURE ON)

set(unity_root "${CMAKE_SOURCE_DIR}/lib/unity")

add_compile_definitions(CY_CONFIG_TRACE=1)

function(cy_gen_test name compile_flags link_flags c_standard)
    # Build Unity per-target to avoid mixing object architectures between -m32/-m64 variants.
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
    )

    add_executable(${name} ${ARGN} src/helpers.c src/cy_trace.c platform_stubs/guarded_heap.c platform_stubs/message.c)
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
    # Clang-Tidy is mandatory in the test suite.
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
    set_property(GLOBAL APPEND PROPERTY CY_TEST_EXECUTABLE_TARGETS ${name})
    add_test(NAME "run_${name}" COMMAND ${name})
    set_property(GLOBAL APPEND PROPERTY CY_TEST_CTEST_NAMES "run_${name}")
endfunction()

function(cy_gen_test_arch_matrix name c_standard)
    cy_gen_test("${name}_x64_c${c_standard}" "-m64" "-m64" "${c_standard}" ${ARGN})
    cy_gen_test("${name}_x32_c${c_standard}" "-m32" "-m32" "${c_standard}" ${ARGN})
endfunction()

function(cy_gen_test_intrusive_matrix name)
    cy_gen_test_arch_matrix("${name}" 99 ${ARGN})
    cy_gen_test_arch_matrix("${name}" 11 ${ARGN})
endfunction()

cy_gen_test_intrusive_matrix(test_intrusive_dedup src/test_intrusive_dedup.c)
cy_gen_test_intrusive_matrix(test_intrusive_reordering src/test_intrusive_reordering.c)
cy_gen_test_arch_matrix(test_api_rx 11 src/test_api_rx.cpp ${CMAKE_SOURCE_DIR}/cy/cy.c)

get_property(cy_test_executable_targets GLOBAL PROPERTY CY_TEST_EXECUTABLE_TARGETS)
if (cy_test_executable_targets)
    add_test(
            NAME build_test_binaries
            COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --parallel --target ${cy_test_executable_targets}
    )
    set_tests_properties(build_test_binaries PROPERTIES FIXTURES_SETUP cy_test_binaries_built)

    get_property(cy_test_ctest_names GLOBAL PROPERTY CY_TEST_CTEST_NAMES)
    if (cy_test_ctest_names)
        set_tests_properties(${cy_test_ctest_names} PROPERTIES FIXTURES_REQUIRED cy_test_binaries_built)
    endif ()
endif ()
