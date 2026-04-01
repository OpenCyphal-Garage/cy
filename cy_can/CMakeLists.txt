# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy_can C)

include_directories(SYSTEM "${CMAKE_SOURCE_DIR}/lib")

# Libcanard static library.
add_library(canard STATIC "${CMAKE_SOURCE_DIR}/lib/libcanard/libcanard/canard.c")
target_compile_options(canard PRIVATE -Wno-cast-align)
target_include_directories(canard SYSTEM INTERFACE ${CMAKE_SOURCE_DIR}/lib/libcanard/libcanard)
set_target_properties(
        canard
        PROPERTIES
        COMPILE_WARNING_AS_ERROR OFF
        C_STANDARD_REQUIRED ON
        C_EXTENSIONS OFF
        C_CLANG_TIDY ""
        CXX_CLANG_TIDY ""
        C_CPPCHECK ""
        CXX_CPPCHECK ""
)

# Shared configuration for cy_can targets.
function(configure_cy_can_target target)
    target_link_libraries(${target} PUBLIC canard)
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

# Platform-agnostic CAN transport (cy_can.c + cy.c).
set(cy_can_sources cy_can.c ../cy/cy.c)

add_library(cy_can STATIC ${cy_can_sources})
configure_cy_can_target(cy_can)

# With Linux SocketCAN support.
add_library(cy_can_socketcan STATIC ${cy_can_sources} cy_can_socketcan.c)
configure_cy_can_target(cy_can_socketcan)

# Same but with CY_CONFIG_TRACE=1 for examples and tests.
add_library(cy_can_socketcan_trace STATIC ${cy_can_sources} cy_can_socketcan.c)
target_compile_definitions(cy_can_socketcan_trace PUBLIC CY_CONFIG_TRACE=1)
configure_cy_can_target(cy_can_socketcan_trace)
