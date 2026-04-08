#pragma once

#include "e2e_faults.hpp"
#include "guarded_heap.h"
#include <array>
#include <cstddef>
#include <cstdint>
#include <set>
#include <vector>

namespace e2e {

constexpr std::size_t sim_node_count = 2U;
constexpr std::size_t sim_node_a     = 0U;
constexpr std::size_t sim_node_b     = 1U;

struct async_error_capture_t final
{
    std::size_t   node_index{ 0U };
    cy_err_t      error{ CY_OK };
    std::uint16_t line_number{ 0U };
    bool          has_topic{ false };
    std::uint64_t topic_hash{ 0U };
};

enum class diag_kind_t
{
    topic_reallocated,
    topic_created,
    topic_destroyed,
    gossip_processed,
};

struct diag_capture_t final
{
    std::size_t                              node_index{ 0U };
    diag_kind_t                              kind{ diag_kind_t::topic_created };
    bool                                     has_topic{ false };
    std::uint64_t                            topic_hash{ 0U };
    std::uint32_t                            subject_id{ 0U };
    std::uint32_t                            evictions{ 0U };
    std::uint64_t                            gossip_hash{ 0U };
    std::size_t                              name_len{ 0U };
    std::array<char, CY_TOPIC_NAME_MAX + 1U> name{};
};

struct frame_capture_t final
{
    frame_info_t frame{};
    bool         dropped{ false };
    std::size_t  copy_index{ 0U };
};

struct op_fault_capture_t final
{
    op_info_t op{};

    bool     failed{ false };
    cy_err_t error{ CY_OK };
};

struct queued_frame_t final
{
    frame_info_t frame{};
};

struct sim_subject_writer_t final
{
    cy_subject_writer_t base{};
};

struct sim_subject_reader_t final
{
    cy_subject_reader_t   base{};
    std::size_t           extent{ 0U };
    sim_subject_reader_t* next{ nullptr };
};

struct sim_net_t;

struct sim_node_t final
{
    cy_platform_t        platform{};
    cy_platform_vtable_t vtable{};
    guarded_heap_t       core_heap{};
    guarded_heap_t       message_heap{};

    sim_net_t*    network{ nullptr };
    std::size_t   index{ 0U };
    std::uint64_t node_id{ 0U };
    cy_t*         cy{ nullptr };

    cy_us_t       now{ 0 };
    std::uint64_t random_state{ UINT64_C(0x1020304050607080) };

    sim_subject_reader_t* readers{ nullptr };
    cy_diag_t             diag_listener{};

    std::set<std::uint32_t> active_reader_subjects;
    std::set<std::uint32_t> active_writer_subjects;
};

struct sim_net_config_t final
{
    std::size_t   node_count{ sim_node_count };
    std::uint32_t subject_id_modulus{ static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit) };
    std::uint64_t random_seed_base{ UINT64_C(0x1020304050607080) };
};

struct sim_net_t final
{
    std::vector<sim_node_t>            nodes{};
    std::vector<queued_frame_t>        queue{};
    std::vector<frame_capture_t>       captures{};
    std::vector<async_error_capture_t> async_errors{};
    std::vector<diag_capture_t>        diag_captures{};
    std::vector<op_fault_capture_t>    op_fault_captures{};
    std::uint64_t                      next_sequence{ 0U };
    std::uint64_t                      next_operation_sequence{ 0U };
    std::uint32_t                      subject_id_modulus{ static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit) };
    const fault_plan_t*                frame_faults{ nullptr };
    const op_fault_plan_t*             op_faults{ nullptr };
};

cy_err_t sim_net_init(sim_net_t&    self,
                      std::uint32_t subject_id_modulus = static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit),
                      std::uint64_t random_seed_base   = UINT64_C(0x1020304050607080));
cy_err_t sim_net_init_ex(sim_net_t& self, const sim_net_config_t& config);
void     sim_net_deinit(sim_net_t& self);

void sim_net_faults_set(sim_net_t& self, const fault_plan_t* frame_faults);
void sim_net_faults_set(sim_net_t& self, const fault_plan_t* frame_faults, const op_fault_plan_t* op_faults);
void sim_net_op_faults_set(sim_net_t& self, const op_fault_plan_t* op_faults);

cy_t*       sim_net_cy(sim_net_t& self, std::size_t node_index);
const cy_t* sim_net_cy(const sim_net_t& self, std::size_t node_index);

cy_platform_t*       sim_net_platform(sim_net_t& self, std::size_t node_index);
const cy_platform_t* sim_net_platform(const sim_net_t& self, std::size_t node_index);

void          sim_net_node_now_set(sim_net_t& self, std::size_t node_index, cy_us_t now);
std::uint64_t sim_net_node_id(const sim_net_t& self, std::size_t node_index);
std::size_t   sim_net_node_count(const sim_net_t& self);

cy_err_t sim_net_spin_node(sim_net_t& self, std::size_t node_index);

void sim_net_deliver_due(sim_net_t& self, cy_us_t now_limit);

std::size_t                               sim_net_pending_frames(const sim_net_t& self);
const std::vector<frame_capture_t>&       sim_net_captures(const sim_net_t& self);
const std::vector<async_error_capture_t>& sim_net_async_errors(const sim_net_t& self);
const std::vector<diag_capture_t>&        sim_net_diag_captures(const sim_net_t& self);
const std::vector<op_fault_capture_t>&    sim_net_op_fault_captures(const sim_net_t& self);
void                                      sim_net_clear_captures(sim_net_t& self);
guarded_heap_t&                           sim_net_core_heap(sim_net_t& self, std::size_t node_index);
const guarded_heap_t&                     sim_net_core_heap(const sim_net_t& self, std::size_t node_index);
guarded_heap_t&                           sim_net_message_heap(sim_net_t& self, std::size_t node_index);
const guarded_heap_t&                     sim_net_message_heap(const sim_net_t& self, std::size_t node_index);

} // namespace e2e
