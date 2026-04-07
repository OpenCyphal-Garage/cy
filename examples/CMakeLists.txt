# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy_examples CXX)
enable_testing()

include_directories(SYSTEM "${CMAKE_SOURCE_DIR}/lib")

option(CY_EXAMPLES_TRACE "Enable cy_trace() logging in the example executables" ON)

add_library(cy_examples_support STATIC ../cy/cy.c)
target_include_directories(cy_examples_support PUBLIC ${CMAKE_SOURCE_DIR}/cy)
set_target_properties(
        cy_examples_support
        PROPERTIES
        COMPILE_WARNING_AS_ERROR ON
        C_STANDARD_REQUIRED ON
        C_EXTENSIONS OFF
)
if (CY_EXAMPLES_TRACE)
    target_sources(cy_examples_support PRIVATE cy_trace_stderr.c)
    target_compile_definitions(cy_examples_support PUBLIC CY_CONFIG_TRACE=1)
endif ()

function(cy_add_example target platform_target)
    add_executable(${target} ${ARGN})
    target_link_libraries(${target} PRIVATE cy_examples_support ${platform_target})
    if (TARGET cy_can_socketcan)
        target_link_libraries(${target} PRIVATE cy_can_socketcan)
    endif ()
endfunction()

# Node examples.
cy_add_example(example_pub cy_udp_posix example_pub.c)
cy_add_example(example_sub cy_udp_posix example_sub.c)
cy_add_example(example_time_pub cy_udp_posix example_time_pub.c)
cy_add_example(example_echo cy_udp_posix example_echo.c)

# File transfer examples.
cy_add_example(example_file_server cy_udp_posix example_file_server.c)
cy_add_example(example_file_client cy_udp_posix example_file_client.c)

# Streaming examples.
cy_add_example(example_streaming_server cy_udp_posix example_streaming_server.c)
cy_add_example(example_streaming_client cy_udp_posix example_streaming_client.c)
