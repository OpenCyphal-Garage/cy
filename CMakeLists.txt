# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy C CXX)
enable_testing()

# Use -DNO_STATIC_ANALYSIS=1 to suppress static analysis.
# If not suppressed, the tools used here shall be available, otherwise the build will fail.
if (NOT NO_STATIC_ANALYSIS)
    # clang-tidy (separate config files per directory)
    find_program(clang_tidy NAMES clang-tidy)
    if (NOT clang_tidy)
        message(FATAL_ERROR "Could not locate clang-tidy")
    endif ()
    message(STATUS "Using clang-tidy: ${clang_tidy}")
    set(CMAKE_CXX_CLANG_TIDY ${clang_tidy})
endif ()

# clang-format
find_program(clang_format NAMES clang-format)
if (NOT clang_format)
    message(STATUS "Could not locate clang-format")
else ()
    file(GLOB format_files
            ${CMAKE_SOURCE_DIR}/cy/*.[ch]
            ${CMAKE_SOURCE_DIR}/examples/*.[ch]
            ${CMAKE_SOURCE_DIR}/tests/*.[ch]pp
    )
    message(STATUS "Using clang-format: ${clang_format}; files: ${format_files}")
    add_custom_target(format COMMAND ${clang_format} -i -fallback-style=none -style=file --verbose ${format_files})
endif ()

# Build options
set(CMAKE_COMPILE_WARNING_AS_ERROR ON)
set(c_cxx_flags "\
-Wall -Wextra -pedantic -fstrict-aliasing -Wundef -Wconversion -Wsign-promo -Wsign-conversion \
-Wmissing-declarations -Wtype-limits \
")
# C
set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${c_cxx_flags}")
# C++
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${c_cxx_flags} -Wzero-as-null-pointer-constant")

include_directories(${CMAKE_SOURCE_DIR}/lib ${CMAKE_SOURCE_DIR}/lib/wild_key_value)

# These are just temporary options for debugging and testing.
# Overriding the preferred subject-ID creates a very challenging environment for the consensus algorithm,
# increasing the random pick collision probability to 100%.
add_compile_definitions(
        CY_CONFIG_TRACE=1
        CY_CONFIG_HEARTBEAT_TOPIC_NAME="/@/8191"
        CY_CONFIG_PREFERRED_TOPIC_OVERRIDE=0
)

add_subdirectory(cy)
add_subdirectory(cy_udp_posix)
add_subdirectory(examples)
