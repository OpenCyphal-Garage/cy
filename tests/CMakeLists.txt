# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy_tests C CXX)

set(CTEST_OUTPUT_ON_FAILURE ON)

set(unity_root "${CMAKE_SOURCE_DIR}/lib/unity")

add_library(cy_test_unity STATIC "${unity_root}/src/unity.c")
target_include_directories(cy_test_unity SYSTEM PUBLIC "${unity_root}/src")
target_compile_definitions(cy_test_unity PUBLIC UNITY_INCLUDE_DOUBLE=1 UNITY_OUTPUT_COLOR=1 UNITY_SUPPORT_64=1)
target_compile_options(
        cy_test_unity
        PRIVATE
        -Wno-sign-conversion
        -Wno-conversion
        -Wno-switch-enum
        -Wno-float-equal
        -Wno-double-promotion
        -Wno-missing-declarations
)

add_library(cy_test_support STATIC src/helpers.c platform_stubs/message.c)
target_include_directories(
        cy_test_support
        PUBLIC
        ${CMAKE_SOURCE_DIR}/cy
        ${CMAKE_CURRENT_SOURCE_DIR}/src
        ${CMAKE_CURRENT_SOURCE_DIR}/platform_stubs
)
target_link_libraries(cy_test_support PUBLIC cy_test_unity)
set_target_properties(
        cy_test_support
        PROPERTIES
        C_STANDARD 11
        C_STANDARD_REQUIRED ON
        C_EXTENSIONS OFF
)

function(cy_gen_test name)
    add_executable(${name} ${ARGN})
    target_include_directories(
            ${name}
            PRIVATE
            ${CMAKE_SOURCE_DIR}/cy
            ${CMAKE_CURRENT_SOURCE_DIR}/src
            ${CMAKE_CURRENT_SOURCE_DIR}/platform_stubs
    )
    target_link_libraries(${name} PRIVATE cy_test_support)
    target_compile_options(${name} PRIVATE -Wno-unused-function)
    set_target_properties(
            ${name}
            PROPERTIES
            C_STANDARD 11
            C_STANDARD_REQUIRED ON
            C_EXTENSIONS OFF
            CXX_STANDARD 20
            CXX_STANDARD_REQUIRED ON
            CXX_EXTENSIONS OFF
    )
    add_test(NAME "run_${name}" COMMAND ${name})
endfunction()

cy_gen_test(test_intrusive_dedup src/test_intrusive_dedup.c)
cy_gen_test(test_intrusive_reordering src/test_intrusive_reordering.c)
cy_gen_test(test_api_rx src/test_api_rx.cpp ${CMAKE_SOURCE_DIR}/cy/cy.c)
