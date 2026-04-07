# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)

set(cy_can_tests_root ${CMAKE_CURRENT_SOURCE_DIR})
set(unity_root "${CMAKE_SOURCE_DIR}/lib/unity")
set(canard_root "${CMAKE_SOURCE_DIR}/lib/libcanard/libcanard")

add_library(cy_can_tests_unity STATIC "${unity_root}/src/unity.c")
target_include_directories(cy_can_tests_unity SYSTEM PUBLIC "${unity_root}/src")
target_compile_definitions(cy_can_tests_unity PUBLIC UNITY_INCLUDE_DOUBLE=1 UNITY_OUTPUT_COLOR=1 UNITY_SUPPORT_64=1)
target_compile_options(
        cy_can_tests_unity
        PRIVATE
        -m32
        -Wno-sign-conversion
        -Wno-conversion
        -Wno-switch-enum
        -Wno-float-equal
        -Wno-double-promotion
        -Wno-missing-declarations
)
set_target_properties(
        cy_can_tests_unity
        PROPERTIES
        C_STANDARD 99
        C_STANDARD_REQUIRED ON
        C_EXTENSIONS OFF
        COMPILE_WARNING_AS_ERROR OFF
        C_CLANG_TIDY ""
        CXX_CLANG_TIDY ""
        C_CPPCHECK ""
        CXX_CPPCHECK ""
)

add_library(cy_can_tests_canard STATIC "${canard_root}/canard.c")
target_include_directories(cy_can_tests_canard SYSTEM PUBLIC "${canard_root}")
target_compile_options(cy_can_tests_canard PRIVATE -m32 -Wno-cast-align)
set_target_properties(
        cy_can_tests_canard
        PROPERTIES
        C_STANDARD 99
        C_STANDARD_REQUIRED ON
        C_EXTENSIONS OFF
        COMPILE_WARNING_AS_ERROR OFF
        C_CLANG_TIDY ""
        CXX_CLANG_TIDY ""
        C_CPPCHECK ""
        CXX_CPPCHECK ""
)

function(cy_can_add_test name)
    add_executable(
            ${name}
            ${ARGN}
            ${CMAKE_SOURCE_DIR}/cy/cy.c
            ${CMAKE_SOURCE_DIR}/cy_can/cy_can.c
            ${cy_can_tests_root}/test_support.c
    )
    target_include_directories(
            ${name}
            PRIVATE
            ${CMAKE_SOURCE_DIR}/cy
            ${CMAKE_SOURCE_DIR}/cy_can
            ${canard_root}
            ${cy_can_tests_root}
    )
    target_link_libraries(${name} PRIVATE cy_can_tests_unity cy_can_tests_canard)
    target_compile_options(${name} PRIVATE -m32)
    target_link_options(${name} PRIVATE -m32)
    set_target_properties(
            ${name}
            PROPERTIES
            C_STANDARD 99
            C_STANDARD_REQUIRED ON
            C_EXTENSIONS OFF
            COMPILE_WARNING_AS_ERROR ON
    )
    add_test(NAME run_${name} COMMAND ${name})
endfunction()

cy_can_add_test(test_api_can_constructor test_api_can_constructor.c)
cy_can_add_test(test_api_can_pubsub test_api_can_pubsub.c)
cy_can_add_test(test_api_can_reliable_rpc test_api_can_reliable_rpc.c)
cy_can_add_test(test_api_can_redundancy_lifecycle test_api_can_redundancy_lifecycle.c)
cy_can_add_test(test_api_can_failures test_api_can_failures.c)

if (CMAKE_SYSTEM_NAME STREQUAL "Linux")
    add_executable(
            test_api_can_socketcan_e2e
            test_api_can_socketcan_e2e.c
            ${CMAKE_SOURCE_DIR}/cy/cy.c
            ${CMAKE_SOURCE_DIR}/cy_can/cy_can.c
            ${CMAKE_SOURCE_DIR}/cy_can/cy_can_socketcan.c
    )
    target_include_directories(
            test_api_can_socketcan_e2e
            PRIVATE
            ${CMAKE_SOURCE_DIR}/cy
            ${CMAKE_SOURCE_DIR}/cy_can
            ${canard_root}
            ${cy_can_tests_root}
    )
    target_link_libraries(test_api_can_socketcan_e2e PRIVATE cy_can_tests_unity cy_can_tests_canard)
    target_compile_definitions(test_api_can_socketcan_e2e PRIVATE _POSIX_C_SOURCE=200809L)
    target_compile_options(test_api_can_socketcan_e2e PRIVATE -m32)
    target_link_options(test_api_can_socketcan_e2e PRIVATE -m32)
    set_target_properties(
            test_api_can_socketcan_e2e
            PROPERTIES
            C_STANDARD 99
            C_STANDARD_REQUIRED ON
            C_EXTENSIONS OFF
            COMPILE_WARNING_AS_ERROR ON
    )
    add_test(NAME run_test_api_can_socketcan_e2e COMMAND test_api_can_socketcan_e2e)
    set_tests_properties(run_test_api_can_socketcan_e2e PROPERTIES SKIP_RETURN_CODE 77)
endif ()
