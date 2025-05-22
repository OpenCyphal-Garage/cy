# Copyright (c) Pavel Kirienko

cmake_minimum_required(VERSION 3.24)
project(cy C)
add_library(cy STATIC ${CMAKE_CURRENT_SOURCE_DIR}/cy.c)
target_include_directories(cy SYSTEM INTERFACE ${CMAKE_CURRENT_SOURCE_DIR})
