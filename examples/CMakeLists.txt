# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy_examples CXX)
enable_testing()

# Overriding the preferred subject-ID creates a very challenging environment for the consensus algorithm,
# increasing the collision probability to 100%.
add_compile_definitions(
        CY_CONFIG_TRACE=1
        CY_CONFIG_PREFERRED_TOPIC_OVERRIDE=0
)

# Cy trace logging helper.
add_library(cy_trace_stderr STATIC cy_trace_stderr.c)
target_link_libraries(cy_trace_stderr PUBLIC cy)

# UDP node examples.
add_executable(udp_pub main_udp_pub.c)
add_executable(udp_sub main_udp_sub.c)
target_link_libraries(udp_pub cy_udp_posix cy_trace_stderr)
target_link_libraries(udp_sub cy_udp_posix cy_trace_stderr)

# UDP file transfer examples.
add_executable(udp_file_server main_udp_file_server.c)
add_executable(udp_file_client main_udp_file_client.c)
target_link_libraries(udp_file_server cy_udp_posix cy_trace_stderr)
target_link_libraries(udp_file_client cy_udp_posix cy_trace_stderr)

# UDP streaming examples.
add_executable(udp_streaming_server main_udp_streaming_server.c)
add_executable(udp_streaming_client main_udp_streaming_client.c)
target_link_libraries(udp_streaming_server cy_udp_posix cy_trace_stderr)
target_link_libraries(udp_streaming_client cy_udp_posix cy_trace_stderr)
