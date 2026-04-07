# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy_udp_posix C)

include_directories(SYSTEM "${CMAKE_SOURCE_DIR}/lib")

# LibUDPard static library.
add_library(udpard STATIC "${CMAKE_SOURCE_DIR}/lib/libudpard/libudpard/udpard.c")
target_compile_options(udpard PRIVATE -Wno-cast-align)
target_include_directories(udpard SYSTEM INTERFACE ${CMAKE_SOURCE_DIR}/lib/libudpard/libudpard)
set_target_properties(
        udpard
        PROPERTIES
        COMPILE_WARNING_AS_ERROR OFF
        C_STANDARD_REQUIRED ON
        C_EXTENSIONS OFF
        C_CLANG_TIDY ""
        CXX_CLANG_TIDY ""
        C_CPPCHECK ""
        CXX_CPPCHECK ""
)

# Cy UDP POSIX transport glue static library.
# Consumers link cy/cy.c themselves; this target only contains the transport/platform layer.
add_library(cy_udp_posix STATIC cy_udp_posix.c udp_wrapper.c)
target_link_libraries(cy_udp_posix PUBLIC udpard)
target_include_directories(cy_udp_posix SYSTEM INTERFACE ${CMAKE_CURRENT_SOURCE_DIR})
target_include_directories(cy_udp_posix PUBLIC ${CMAKE_SOURCE_DIR}/cy)
set_target_properties(cy_udp_posix PROPERTIES COMPILE_WARNING_AS_ERROR ON C_STANDARD_REQUIRED ON C_EXTENSIONS OFF)
