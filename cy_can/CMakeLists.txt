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

# Platform-agnostic CAN transport glue static library.
# Consumers link cy/cy.c themselves; this target only contains the transport/platform layer.
add_library(cy_can STATIC cy_can.c)
target_link_libraries(cy_can PUBLIC canard)
target_include_directories(cy_can PUBLIC ${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_SOURCE_DIR}/cy)
set_target_properties(cy_can PROPERTIES COMPILE_WARNING_AS_ERROR ON C_STANDARD_REQUIRED ON C_EXTENSIONS OFF)

# Linux SocketCAN backend for cy_can. Includes cy_can and canard, making it self-contained except for cy.c.
if (CMAKE_SYSTEM_NAME STREQUAL "Linux")
    add_library(cy_can_socketcan STATIC cy_can_socketcan.c)
    target_link_libraries(cy_can_socketcan PUBLIC cy_can)
    set_target_properties(cy_can_socketcan PROPERTIES COMPILE_WARNING_AS_ERROR ON C_STANDARD_REQUIRED ON C_EXTENSIONS OFF)
endif ()

add_subdirectory(tests)
