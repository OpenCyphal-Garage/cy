# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy_udp_posix C)

# LibUDPard static library.
add_library(udpard STATIC ${CMAKE_SOURCE_DIR}/lib/libudpard/libudpard/udpard.c)
target_compile_options(udpard PRIVATE -Wno-cast-align -Wno-error)
target_include_directories(udpard SYSTEM INTERFACE ${CMAKE_SOURCE_DIR}/lib/libudpard/libudpard)

# Cy UDP POSIX static library.
add_library(cy_udp_posix STATIC ${CMAKE_CURRENT_SOURCE_DIR}/cy_udp_posix.c ${CMAKE_CURRENT_SOURCE_DIR}/udp_wrapper.c)
target_link_libraries(cy_udp_posix PUBLIC cy udpard)
target_include_directories(cy_udp_posix SYSTEM INTERFACE ${CMAKE_CURRENT_SOURCE_DIR})
