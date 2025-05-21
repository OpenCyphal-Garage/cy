# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy C)

# These are just temporary options for debugging and testing.
# Overriding the preferred subject-ID creates a very challenging environment for the consensus algorithm,
# increasing the random pick collision probability to 100%.
add_compile_definitions(
        CY_CONFIG_TRACE=1
        CY_CONFIG_HEARTBEAT_TOPIC_NAME="/8191"
        CY_CONFIG_PREFERRED_TOPIC_OVERRIDE=0
)

include_directories(${CMAKE_SOURCE_DIR}/lib)

# Cy static library.
add_library(cy STATIC ${CMAKE_SOURCE_DIR}/cy/cy.c)
target_include_directories(cy INTERFACE ${CMAKE_SOURCE_DIR}/cy)
