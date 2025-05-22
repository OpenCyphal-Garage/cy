# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy_examples CXX)
enable_testing()

# Cy trace logging helper.
add_library(cy_trace_stderr STATIC cy_trace_stderr.c)
target_link_libraries(cy_trace_stderr PUBLIC cy)

# UDP node example.
add_executable(udp_node main_udp_node.c)
target_link_libraries(udp_node cy_udp_posix cy_trace_stderr)

# UDP file transfer examples.
add_executable(udp_file_server main_udp_file_server.c)
add_executable(udp_file_client main_udp_file_client.c)
target_link_libraries(udp_file_server cy_udp_posix cy_trace_stderr)
target_link_libraries(udp_file_client cy_udp_posix cy_trace_stderr)
