# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)

set(cy_udp_posix_tests_root ${CMAKE_CURRENT_SOURCE_DIR})
set(unity_root "${CMAKE_SOURCE_DIR}/lib/unity")
set(udpard_root "${CMAKE_SOURCE_DIR}/lib/libudpard/libudpard")

add_library(cy_udp_posix_tests_unity STATIC "${unity_root}/src/unity.c")
target_include_directories(cy_udp_posix_tests_unity SYSTEM PUBLIC "${unity_root}/src")
target_compile_definitions(
        cy_udp_posix_tests_unity
        PUBLIC
        UNITY_INCLUDE_DOUBLE=1
        UNITY_OUTPUT_COLOR=1
        UNITY_SUPPORT_64=1
)
target_compile_options(
        cy_udp_posix_tests_unity
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
        cy_udp_posix_tests_unity
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

add_library(cy_udp_posix_tests_udpard STATIC "${udpard_root}/udpard.c")
target_include_directories(cy_udp_posix_tests_udpard SYSTEM PUBLIC "${udpard_root}")
target_compile_options(cy_udp_posix_tests_udpard PRIVATE -m32 -Wno-cast-align)
set_target_properties(
        cy_udp_posix_tests_udpard
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

function(cy_udp_posix_add_test name)
    add_executable(
            ${name}
            ${ARGN}
            ${CMAKE_SOURCE_DIR}/cy/cy.c
            ${CMAKE_SOURCE_DIR}/cy_udp_posix/cy_udp_posix.c
            ${CMAKE_SOURCE_DIR}/cy_udp_posix/udp_wrapper.c
            ${cy_udp_posix_tests_root}/test_support.c
    )
    target_include_directories(
            ${name}
            PRIVATE
            ${CMAKE_SOURCE_DIR}/cy
            ${CMAKE_SOURCE_DIR}/cy_udp_posix
            ${udpard_root}
            ${cy_udp_posix_tests_root}
    )
    target_link_libraries(${name} PRIVATE cy_udp_posix_tests_unity cy_udp_posix_tests_udpard)
    target_compile_definitions(${name} PRIVATE _POSIX_C_SOURCE=200809L)
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

cy_udp_posix_add_test(test_api_udp_posix_basic test_api_udp_posix_basic.c)
cy_udp_posix_add_test(test_api_udp_posix_pubsub test_api_udp_posix_pubsub.c)
cy_udp_posix_add_test(test_api_udp_posix_rpc_lifecycle test_api_udp_posix_rpc_lifecycle.c)
cy_udp_posix_add_test(test_api_udp_posix_default_ctor test_api_udp_posix_default_ctor.c)
set_tests_properties(run_test_api_udp_posix_default_ctor PROPERTIES SKIP_RETURN_CODE 77)
