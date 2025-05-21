# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy_udp_posix C)

set(lib_dir ${CMAKE_SOURCE_DIR}/lib)

# LibUDPard static library.
add_library(udpard STATIC ${lib_dir}/libudpard/libudpard/udpard.c)
target_compile_options(udpard PRIVATE -Wno-cast-align)
target_include_directories(udpard SYSTEM INTERFACE ${lib_dir}/libudpard/libudpard)

# Cy UDP POSIX static library.
add_library(cy_udp_posix STATIC cy_udp_posix.c udp_wrapper.c)
target_link_libraries(cy_udp_posix PUBLIC cy udpard)
