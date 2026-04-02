# Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

cmake_minimum_required(VERSION 3.24)
project(cy_tests C CXX)

set(CTEST_OUTPUT_ON_FAILURE ON)

include_directories(SYSTEM "${CMAKE_SOURCE_DIR}/lib")

set(unity_root "${CMAKE_SOURCE_DIR}/lib/unity")

# --------------------------------------------------------------------------------------------------
# OBJECT LIBRARIES FOR SHARED SOURCES
# Static analysis (clang-tidy, cppcheck) runs once per unique (source, flags) combination
# instead of once per test target that includes the source. This avoids redundant re-analysis
# of files like helpers.c (76x -> 6x) and cy.c (40x -> 2x).
# --------------------------------------------------------------------------------------------------

# Get or create an object library for a set of shared sources with specific build settings.
# The library name is deterministic: the same (tag, compile_flags, c_standard, definitions, sources)
# combination yields the same target.
function(cy_get_objlib out_var tag compile_flags c_standard definitions sources)
    string(MD5 src_hash "${compile_flags}|${c_standard}|${definitions}|${sources}")
    string(SUBSTRING "${src_hash}" 0 6 src_hash_short)
    set(lib_name "_cy_shared_${tag}_${src_hash_short}")
    if (NOT TARGET ${lib_name})
        add_library(${lib_name} OBJECT ${sources})
        target_include_directories(${lib_name} PRIVATE
                ${CMAKE_SOURCE_DIR}/cy
                ${CMAKE_CURRENT_SOURCE_DIR}/src
                ${CMAKE_CURRENT_SOURCE_DIR}/platform_stubs
        )
        target_include_directories(${lib_name} SYSTEM PRIVATE "${unity_root}/src")
        target_compile_options(${lib_name} PRIVATE ${compile_flags})
        target_compile_definitions(${lib_name} PRIVATE UNITY_INCLUDE_DOUBLE=1 UNITY_OUTPUT_COLOR=1 UNITY_SUPPORT_64=1)
        if (definitions)
            target_compile_definitions(${lib_name} PRIVATE ${definitions})
        endif ()
        set_target_properties(${lib_name} PROPERTIES
                C_STANDARD ${c_standard}
                C_STANDARD_REQUIRED ON
                C_EXTENSIONS OFF
                CXX_STANDARD 20
                CXX_STANDARD_REQUIRED ON
                CXX_EXTENSIONS OFF
                COMPILE_WARNING_AS_ERROR ON
        )
    endif ()
    set(${out_var} ${lib_name} PARENT_SCOPE)
endfunction()

# --------------------------------------------------------------------------------------------------
# TEST TARGET GENERATION
# --------------------------------------------------------------------------------------------------

function(cy_gen_test name compile_flags link_flags c_standard definitions unique_sources)
    # Build Unity per-target to avoid mixing object architectures between -m32/-m64 variants etc.
    add_library("${name}_unity" STATIC "${unity_root}/src/unity.c")
    target_include_directories("${name}_unity" SYSTEM PUBLIC "${unity_root}/src")
    target_compile_definitions("${name}_unity" PUBLIC UNITY_INCLUDE_DOUBLE=1 UNITY_OUTPUT_COLOR=1 UNITY_SUPPORT_64=1)
    target_compile_options(
            "${name}_unity"
            PRIVATE
            ${compile_flags}
            -Wno-sign-conversion
            -Wno-conversion
            -Wno-switch-enum
            -Wno-float-equal
            -Wno-double-promotion
            -Wno-missing-declarations
    )
    target_link_options("${name}_unity" PRIVATE ${link_flags})
    set_target_properties(
            "${name}_unity"
            PROPERTIES
            C_STANDARD ${c_standard}
            C_STANDARD_REQUIRED ON
            C_EXTENSIONS OFF
            COMPILE_WARNING_AS_ERROR OFF
            C_CLANG_TIDY ""
            CXX_CLANG_TIDY ""
            C_CPPCHECK ""
            CXX_CPPCHECK ""
    )

    # Build the test executable from its unique sources only.
    # Shared sources are linked via object libraries passed as extra ARGN arguments.
    # Clang-Tidy and Cppcheck are mandatory in the test suite.
    add_executable(${name} ${unique_sources})
    target_include_directories(
            ${name}
            PRIVATE
            ${CMAKE_SOURCE_DIR}/cy
            ${CMAKE_CURRENT_SOURCE_DIR}/src
            ${CMAKE_CURRENT_SOURCE_DIR}/platform_stubs
    )
    target_link_libraries(${name} PRIVATE "${name}_unity" ${ARGN})
    target_compile_options(${name} PRIVATE ${compile_flags})
    target_link_options(${name} PRIVATE ${link_flags})
    if (definitions)
        target_compile_definitions(${name} PRIVATE ${definitions})
    endif ()
    set_target_properties(
            ${name}
            PROPERTIES
            C_STANDARD ${c_standard}
            C_STANDARD_REQUIRED ON
            C_EXTENSIONS OFF
            CXX_STANDARD 20
            CXX_STANDARD_REQUIRED ON
            CXX_EXTENSIONS OFF
            COMPILE_WARNING_AS_ERROR ON
    )

    # Register the test with CTest.
    add_test(NAME "run_${name}" COMMAND ${name})
endfunction()

# Intrusive test matrix: 4 variants (x64/x32 × C99/C11).
# shared_sources are built as object libraries; unique_sources are built per-target.
function(cy_gen_test_intrusive_matrix name unique_sources shared_sources)
    foreach (arch IN ITEMS x64 x32)
        if (arch STREQUAL "x64")
            set(arch_flags "-m64")
        else ()
            set(arch_flags "-m32")
        endif ()
        foreach (std IN ITEMS 99 11)
            set(target_name "${name}_${arch}_c${std}")
            cy_get_objlib(objlib "intrusive_${arch}_c${std}" "${arch_flags}" "${std}" "" "${shared_sources}")
            cy_gen_test("${target_name}" "${arch_flags}" "${arch_flags}" "${std}" "" "${unique_sources}" ${objlib})
        endforeach ()
    endforeach ()
endfunction()

# API test matrix: 2 variants (x64/x32), C11 + C++20.
function(cy_gen_test_api_matrix name definitions unique_sources shared_c_sources shared_cxx_sources)
    foreach (arch IN ITEMS x64 x32)
        if (arch STREQUAL "x64")
            set(arch_flags "-m64")
        else ()
            set(arch_flags "-m32")
        endif ()
        set(target_name "${name}_${arch}_c11")
        set(objlibs "")
        if (shared_c_sources)
            cy_get_objlib(c_objlib "api_c_${arch}" "${arch_flags}" "11" "${definitions}" "${shared_c_sources}")
            list(APPEND objlibs ${c_objlib})
        endif ()
        if (shared_cxx_sources)
            cy_get_objlib(cxx_objlib "api_cxx_${arch}" "${arch_flags}" "11" "${definitions}" "${shared_cxx_sources}")
            list(APPEND objlibs ${cxx_objlib})
        endif ()
        cy_gen_test("${target_name}" "${arch_flags}" "${arch_flags}" "11" "${definitions}" "${unique_sources}" ${objlibs})
    endforeach ()
endfunction()

# API test matrix with cy_can + libcanard sources built per-arch so the transport integration can be exercised
# under the same x64/x32 settings without reusing the host-arch convenience library targets.
function(cy_gen_test_api_can_matrix name definitions unique_sources)
    foreach (arch IN ITEMS x64 x32)
        if (arch STREQUAL "x64")
            set(arch_flags "-m64")
        else ()
            set(arch_flags "-m32")
        endif ()
        set(target_name "${name}_${arch}_c11")

        add_library("${target_name}_canard" STATIC "${CMAKE_SOURCE_DIR}/lib/libcanard/libcanard/canard.c")
        target_compile_options("${target_name}_canard" PRIVATE ${arch_flags} -Wno-cast-align)
        target_link_options("${target_name}_canard" PRIVATE ${arch_flags})
        target_include_directories("${target_name}_canard" SYSTEM INTERFACE ${CMAKE_SOURCE_DIR}/lib/libcanard/libcanard)
        set_target_properties(
                "${target_name}_canard"
                PROPERTIES
                C_STANDARD 11
                C_STANDARD_REQUIRED ON
                C_EXTENSIONS OFF
                COMPILE_WARNING_AS_ERROR OFF
                C_CLANG_TIDY ""
                CXX_CLANG_TIDY ""
                C_CPPCHECK ""
                CXX_CPPCHECK ""
        )

        cy_gen_test("${target_name}" "${arch_flags}" "${arch_flags}" "11" "${definitions}"
                "${unique_sources};${CMAKE_SOURCE_DIR}/cy_can/cy_can.c;${CMAKE_SOURCE_DIR}/cy/cy.c;src/cy_trace.c;platform_stubs/guarded_heap.c"
        )
        target_include_directories(${target_name} PRIVATE ${CMAKE_SOURCE_DIR}/cy_can)
        target_link_libraries(${target_name} PRIVATE "${target_name}_canard")
    endforeach ()
endfunction()

# --------------------------------------------------------------------------------------------------
# INTRUSIVE TESTS.
# These tests have access to the library internals and are written in C.
# They should only be used for behaviors that cannot be efficiently tested through the public API,
# and should be kept to a minimum.
# --------------------------------------------------------------------------------------------------
cy_gen_test_intrusive_matrix(test_intrusive_dedup
        "src/test_intrusive_dedup.c"
        "src/helpers.c;platform_stubs/guarded_heap.c"
)
cy_gen_test_intrusive_matrix(test_intrusive_reordering
        "src/test_intrusive_reordering.c"
        "src/helpers.c;platform_stubs/guarded_heap.c;platform_stubs/message.c"
)
cy_gen_test_intrusive_matrix(test_intrusive_subject_id
        "src/test_intrusive_subject_id.c"
        "src/helpers.c"
)
cy_gen_test_intrusive_matrix(test_intrusive_misc
        "src/test_intrusive_misc.c"
        "src/helpers.c;platform_stubs/guarded_heap.c"
)
cy_gen_test_intrusive_matrix(test_intrusive_publish_reliable
        "src/test_intrusive_publish_reliable.c"
        "src/helpers.c;platform_stubs/guarded_heap.c"
)
cy_gen_test_intrusive_matrix(test_intrusive_rpc
        "src/test_intrusive_rpc.c"
        "src/helpers.c;platform_stubs/guarded_heap.c;platform_stubs/message.c"
)
cy_gen_test_intrusive_matrix(test_intrusive_future_notify_destroy
        "src/test_intrusive_future_notify_destroy.c"
        "src/helpers.c;platform_stubs/guarded_heap.c;platform_stubs/message.c"
)
cy_gen_test_intrusive_matrix(test_intrusive_gossip
        "src/test_intrusive_gossip.c"
        "src/helpers.c;platform_stubs/guarded_heap.c"
)
cy_gen_test_intrusive_matrix(test_intrusive_topic_allocation
        "src/test_intrusive_topic_allocation.c"
        "src/helpers.c;platform_stubs/guarded_heap.c"
)
cy_gen_test_intrusive_matrix(test_intrusive_topic_allocate_exhaustive
        "src/test_intrusive_topic_allocate_exhaustive.c"
        "src/helpers.c;platform_stubs/guarded_heap.c"
)

# --------------------------------------------------------------------------------------------------
# API TESTS.
# These tests only have access to the public API and are written in modern C++.
# They should be preferred over intrusive tests whenever possible.
# --------------------------------------------------------------------------------------------------
set(cy_api_shared_c_sources
        ${CMAKE_SOURCE_DIR}/cy/cy.c
        src/helpers.c
        src/cy_trace.c
        platform_stubs/guarded_heap.c
        platform_stubs/message.c
)
cy_gen_test_api_matrix(test_api_rx "CY_CONFIG_TRACE=1"
        "src/test_api_rx.cpp"
        "${cy_api_shared_c_sources}" ""
)
cy_gen_test_api_matrix(test_api_name "CY_CONFIG_TRACE=1"
        "src/test_api_name.cpp"
        "${CMAKE_SOURCE_DIR}/cy/cy.c;src/cy_trace.c" ""
)
cy_gen_test_api_matrix(test_api_publish_reliable "CY_CONFIG_TRACE=1"
        "src/test_api_publish_reliable.cpp"
        "${cy_api_shared_c_sources}" ""
)
cy_gen_test_api_matrix(test_api_core_contracts "CY_CONFIG_TRACE=1"
        "src/test_api_core_contracts.cpp"
        "${cy_api_shared_c_sources}" ""
)
cy_gen_test_api_matrix(test_api_gossip "CY_CONFIG_TRACE=1"
        "src/test_api_gossip.cpp"
        "${cy_api_shared_c_sources}" ""
)
cy_gen_test_api_matrix(test_api_parser_adversarial "CY_CONFIG_TRACE=1"
        "src/test_api_parser_adversarial.cpp"
        "${cy_api_shared_c_sources}" ""
)
cy_gen_test_api_matrix(test_api_state_machine_fuzz "CY_CONFIG_TRACE=1"
        "src/test_api_state_machine_fuzz.cpp"
        "${cy_api_shared_c_sources}" ""
)
cy_gen_test_api_matrix(test_api_gossip_sim "CY_CONFIG_TRACE=1"
        "src/test_api_gossip_sim.cpp"
        "${cy_api_shared_c_sources}" ""
)
cy_gen_test_api_can_matrix(test_api_can_subscription_revival "CY_CONFIG_TRACE=1"
        "src/test_api_can_subscription_revival.cpp"
)

# --------------------------------------------------------------------------------------------------
# END-TO-END API TESTS.
# Shared simulation/fault/utils infrastructure is linked via object library.
# All tests listed here are mandatory and always executed by default.
# --------------------------------------------------------------------------------------------------
set(cy_api_e2e_shared_cxx_sources
        src/e2e_sim_net.cpp
        src/e2e_faults.cpp
        src/e2e_test_utils.cpp
)
cy_gen_test_api_matrix(test_api_consensus_edge_matrix "CY_CONFIG_TRACE=1"
        "src/test_api_consensus_edge_matrix.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_consensus_model_based "CY_CONFIG_TRACE=1"
        "src/test_api_consensus_model_based.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_pubsub_e2e_baseline "CY_CONFIG_TRACE=1"
        "src/test_api_pubsub_e2e_baseline.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_rpc_e2e "CY_CONFIG_TRACE=1"
        "src/test_api_rpc_e2e.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_pubsub_e2e_reliable_loss "CY_CONFIG_TRACE=1"
        "src/test_api_pubsub_e2e_reliable_loss.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_pubsub_e2e_reordering "CY_CONFIG_TRACE=1"
        "src/test_api_pubsub_e2e_reordering.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_pubsub_e2e_migration "CY_CONFIG_TRACE=1"
        "src/test_api_pubsub_e2e_migration.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_pubsub_e2e_lifecycle "CY_CONFIG_TRACE=1"
        "src/test_api_pubsub_e2e_lifecycle.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_pubsub_e2e_platform_failures "CY_CONFIG_TRACE=1"
        "src/test_api_pubsub_e2e_platform_failures.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_consensus_e2e_multinode "CY_CONFIG_TRACE=1"
        "src/test_api_consensus_e2e_multinode.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_pinning_e2e_pattern_match "CY_CONFIG_TRACE=1"
        "src/test_api_pinning_e2e_pattern_match.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_pinning_e2e_subject_id "CY_CONFIG_TRACE=1"
        "src/test_api_pinning_e2e_subject_id.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
cy_gen_test_api_matrix(test_api_pinning_e2e_cohabitation "CY_CONFIG_TRACE=1"
        "src/test_api_pinning_e2e_cohabitation.cpp"
        "${cy_api_shared_c_sources}" "${cy_api_e2e_shared_cxx_sources}"
)
