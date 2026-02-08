# Copyright (c) Pavel Kirienko <pavel@opencyphal.org>
#
# This recipe is intended only for library development.
# Do not use it in production; add cy/cy.c to your build directly instead, along with the cy/ directory for includes.

cmake_minimum_required(VERSION 3.24)
project(cy C CXX)
enable_testing()
set(CMAKE_CTEST_ARGUMENTS "-V")  # Enable test outputs when running `make test`
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
#set(CMAKE_VERBOSE_MAKEFILE ON)

# STATIC ANALYSIS
option(NO_STATIC_ANALYSIS "Disable static analysis to speed up the build" OFF)
if (NOT NO_STATIC_ANALYSIS)
    # Clang-Tidy
    find_program(clang_tidy NAMES clang-tidy REQUIRED)
    message(STATUS "Using clang-tidy: ${clang_tidy}")
    set(CMAKE_CXX_CLANG_TIDY ${clang_tidy})
    set(CMAKE_C_CLANG_TIDY ${clang_tidy})

    # Cppcheck
    find_program(cppcheck NAMES cppcheck)
    if (NOT cppcheck)
        message(FATAL_ERROR "Could not locate cppcheck")
    endif ()
    message(STATUS "Using cppcheck: ${cppcheck}")
    set(cppcheck_options
            --enable=warning,style,performance,portability
            --error-exitcode=2
            --suppress=missingIncludeSystem
            --suppress=badBitmaskCheck
            --suppress=constParameterCallback
            --suppress=duplInheritedMember
            --inline-suppr
    )
    set(CMAKE_C_CPPCHECK ${cppcheck};--language=c;--std=c11;${cppcheck_options})
    set(CMAKE_CXX_CPPCHECK ${cppcheck};--language=c++;--std=c++20;${cppcheck_options})

    # Clang-Format
    find_program(clang_format NAMES clang-format REQUIRED)
    file(GLOB format_files
            ${CMAKE_SOURCE_DIR}/cy/*.[ch]
            ${CMAKE_SOURCE_DIR}/tests/*/*.[ch]
            ${CMAKE_SOURCE_DIR}/tests/*/*.[ch]pp
            ${CMAKE_SOURCE_DIR}/examples/*.[ch]
            ${CMAKE_SOURCE_DIR}/cy_udp_posix/*.[ch]
    )
    message(STATUS "Using clang-format: ${clang_format}; files to format: ${format_files}")
    add_custom_target(format COMMAND ${clang_format} -i -fallback-style=none -style=file --verbose ${format_files})
    add_custom_target(
            format_check
            ALL
            COMMAND ${clang_format} --dry-run --Werror -fallback-style=none -style=file --verbose ${format_files}
            COMMENT "Checking clang-format conformance"
    )
endif ()

# BUILD OPTIONS
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

# COVERAGE
option(COVERAGE "Enable branch coverage measurement" OFF)
if (COVERAGE)
    message(STATUS "Enabling branch coverage measurement")
    add_compile_options(--coverage -Wno-unused-variable -Wno-unused-parameter -Wno-unused-but-set-variable)
    add_link_options(--coverage)
    add_compile_definitions(NDEBUG=1)  # Disable assertions to remove uncovered fault branches from the report.
    find_program(gcovr NAMES gcovr REQUIRED)
    set(coverage_report_html "${CMAKE_BINARY_DIR}/coverage/index.html")
    add_custom_target(coverage
            COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/coverage
            COMMAND ${gcovr}
            --root ${CMAKE_SOURCE_DIR}
            --filter ${CMAKE_SOURCE_DIR}/cy/
            --html-details ${coverage_report_html}
            --print-summary
            COMMAND ${CMAKE_COMMAND} -E echo "📜 📜 📜 COVERAGE REPORT: file://${coverage_report_html} 📜 📜 📜"
            WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
            COMMENT "Generating branch coverage HTML report"
    )
endif ()

# SUBDIRECTORIES
#add_subdirectory(cy_udp_posix) # TODO: temporarily disabled until the refactoring is complete
#add_subdirectory(examples)     # TODO: temporarily disabled until the refactoring is complete
add_subdirectory(tests)
