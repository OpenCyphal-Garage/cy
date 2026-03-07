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

# Cy UDP POSIX static library. Cy is included as well.
function(configure_cy_udp_posix_target target)
    target_link_libraries(${target} PUBLIC udpard)
    target_include_directories(${target} SYSTEM INTERFACE ${CMAKE_CURRENT_SOURCE_DIR})
    target_include_directories(${target} PUBLIC ${CMAKE_SOURCE_DIR}/cy)
    set_target_properties(
            ${target}
            PROPERTIES
            COMPILE_WARNING_AS_ERROR ON
            C_STANDARD_REQUIRED ON
            C_EXTENSIONS OFF
    )
endfunction()

set(cy_udp_posix_sources cy_udp_posix.c udp_wrapper.c ../cy/cy.c)

# The normal production build.
add_library(cy_udp_posix STATIC ${cy_udp_posix_sources})
configure_cy_udp_posix_target(cy_udp_posix)

# Same but with CY_CONFIG_TRACE=1 for examples and tests.
add_library(cy_udp_posix_trace STATIC ${cy_udp_posix_sources} cy_trace_stderr.c)
target_compile_definitions(cy_udp_posix_trace PUBLIC CY_CONFIG_TRACE=1)
configure_cy_udp_posix_target(cy_udp_posix_trace)
