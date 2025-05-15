# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy_examples CXX)
enable_testing()

set(lib_dir ${CMAKE_SOURCE_DIR}/lib)

# These are just temporary options for debugging and testing.
# Overriding the preferred subject-ID creates a very challenging environment for the consensus algorithm,
# increasing the random pick collision probability to 100%.
add_compile_definitions(
        CY_CONFIG_TRACE=1
        CY_CONFIG_HEARTBEAT_TOPIC_NAME="/8191"
        CY_CONFIG_PREFERRED_TOPIC_OVERRIDE=0
)

include_directories(${CMAKE_SOURCE_DIR}/lib)

# Cy static library.
add_library(cy STATIC ${CMAKE_SOURCE_DIR}/cy/cy.c)
target_include_directories(cy INTERFACE ${CMAKE_SOURCE_DIR}/cy)

# LibUDPard static library.
add_library(udpard STATIC ${lib_dir}/libudpard/libudpard/udpard.c)
target_compile_options(udpard PRIVATE -Wno-cast-align)
target_include_directories(udpard SYSTEM INTERFACE ${lib_dir}/libudpard/libudpard)

# Cy trace logging helper.
add_library(cy_trace_stderr STATIC cy_trace_stderr.c)
target_link_libraries(cy_trace_stderr PUBLIC cy)

# Cy UDP static library.
add_library(cy_udp STATIC cy_udp.c udp.c)
target_link_libraries(cy_udp PUBLIC cy udpard)

# UDP node example.
add_executable(udp_node main_udp_node.c)
target_link_libraries(udp_node cy_udp cy_trace_stderr)

# UDP file transfer examples.
add_executable(udp_file_server main_udp_file_server.c)
add_executable(udp_file_client main_udp_file_client.c)
target_link_libraries(udp_file_server cy_udp cy_trace_stderr)
target_link_libraries(udp_file_client cy_udp cy_trace_stderr)
