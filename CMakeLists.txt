# Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

cmake_minimum_required(VERSION 3.24)
project(cy C CXX)
enable_testing()
set(CMAKE_CTEST_ARGUMENTS "-V")  # Enable test outputs when running `make test`
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_VERBOSE_MAKEFILE ON)

# Static analysis.
set(NO_STATIC_ANALYSIS OFF CACHE BOOL "Disable static analysis to speed up the build")
if (NOT NO_STATIC_ANALYSIS)
    find_program(clang_tidy NAMES clang-tidy)
    if (NOT clang_tidy)
        message(FATAL_ERROR "Could not locate clang-tidy")
    endif ()
    message(STATUS "Using clang-tidy: ${clang_tidy}")
    set(CMAKE_CXX_CLANG_TIDY ${clang_tidy})
    set(CMAKE_C_CLANG_TIDY ${clang_tidy})
endif ()

# Code formatting.
find_program(clang_format NAMES clang-format)
if (NOT clang_format)
    message(STATUS "Could not locate clang-format")
else ()
    file(GLOB format_files
            ${CMAKE_SOURCE_DIR}/cy/*.[ch]
            ${CMAKE_SOURCE_DIR}/tests/*/*.[ch]
            ${CMAKE_SOURCE_DIR}/tests/*/*.[ch]pp
            ${CMAKE_SOURCE_DIR}/examples/*.[ch]
            ${CMAKE_SOURCE_DIR}/cy_udp_posix/*.[ch]
    )
    message(STATUS "Using clang-format: ${clang_format}; files: ${format_files}")
    add_custom_target(format COMMAND ${clang_format} -i -fallback-style=none -style=file --verbose ${format_files})
endif ()

# Build options.
# C
set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Wextra -pedantic -fstrict-aliasing -Wundef -Wconversion")
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wmissing-declarations")
# C++
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -pedantic -fstrict-aliasing -Wundef -Wconversion")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wsign-conversion -Wmissing-declarations -Wold-style-cast")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wsign-promo -Wzero-as-null-pointer-constant")

include_directories(SYSTEM ${CMAKE_SOURCE_DIR}/lib)

add_subdirectory(cy)
#add_subdirectory(cy_udp_posix) # TODO: temporarily disabled until the refactoring is complete
#add_subdirectory(examples)     # TODO: temporarily disabled until the refactoring is complete
add_subdirectory(tests)
