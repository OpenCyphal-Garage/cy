--                            ____                   ______            __          __
--                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
--                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
--                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
--                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
--                             /_/                     /____/_/
--
-- Wireshark Lua dissector for Cyphal heartbeats.
-- Use as described in https://github.com/OpenCyphal/wireshark_plugins/
-- Use the following capture filter expression to filter Cyphal traffic only:
--
--      udp and dst net 239.0.0.0 mask 255.0.0.0 and dst port 9382
--
-- Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

local heartbeat_dst_ip = "239.0.29.85"
local heartbeat_proto = Proto("cyphal_heartbeat", "Cyphal Heartbeat")

local f_uptime          = ProtoField.uint32("heartbeat.uptime", "Uptime [s]", base.DEC, nil, nil, "[second]")
local f_user_word       = ProtoField.uint24("heartbeat.user_word", "User word", base.HEX)
local f_version         = ProtoField.uint8 ("heartbeat.version", "Version", base.DEC)
local f_uid             = ProtoField.uint64("heartbeat.uid", "UID", base.HEX)
local f_uid_vid         = ProtoField.uint16("heartbeat.uid.vid", "Vendor-ID (VID)",  base.HEX)
local f_uid_pid         = ProtoField.uint16("heartbeat.uid.pid", "Product-ID (PID)", base.HEX)
local f_uid_iid         = ProtoField.uint32("heartbeat.uid.iid", "Instance-ID (IID)", base.HEX)
local f_topic_hash      = ProtoField.uint64("heartbeat.topic_hash", "Topic hash", base.HEX)
local f_topic_evictions = ProtoField.uint64("heartbeat.topic_evictions", "Topic evictions", base.DEC)
local f_topic_lage      = ProtoField.int8  ("heartbeat.topic_lage", "Topic age floor∘log", base.DEC)
local f_topic_name_len  = ProtoField.uint8 ("heartbeat.topic_name_len", "Topic name length", base.DEC)
local f_topic_name      = ProtoField.string("heartbeat.topic_name", "Topic name", base.ASCII)

heartbeat_proto.fields = {
    f_uptime,
    f_user_word,
    f_version,
    f_uid,
    f_uid_vid,
    f_uid_pid,
    f_uid_iid,
    f_topic_hash,
    f_topic_evictions,
    f_topic_lage,
    f_topic_name_len,
    f_topic_name
}

function heartbeat_proto.dissector(tvb, pinfo, tree)
    if tostring(pinfo.dst) ~= heartbeat_dst_ip then
        return
    end
    if tvb:len() < 1 then
        return
    end

    -- Handle the Cyphal/UDP header.
    local header_version = tvb(0, 1):le_uint()
    local header_size = 0
    if header_version == 1 then
        header_size = 24
    elseif header_version == 2 then
        header_size = 32
    else
        return
    end
    if tvb:len() < header_size + 8 then
        return
    end

    -- Process the Heartbeat payload.
    pinfo.cols.protocol = "CYPHAL❤"
    local subtree = tree:add(heartbeat_proto, tvb(), "Cyphal Heartbeat")
    local offset = header_size

    -- uptime
    subtree:add_le(f_uptime, tvb(offset, 4))
    local uptime = tvb(offset, 4):le_uint()
    offset = offset + 4

    -- user word
    subtree:add_le(f_user_word, tvb(offset, 3))
    local user_word_val = tvb(offset, 3):le_uint()
    offset = offset + 3

    -- version
    local version = tvb(offset, 1):uint()
    subtree:add(f_version, tvb(offset, 1))
    offset = offset + 1

    -- Default Info column
    local info = string.format("⏳% 6us %06x", uptime, user_word_val)
    pinfo.cols.info = info

    -- Version-specific parts
    if version ~= 1 then
        return
    end
    if tvb:len() < offset + 24 then
        return
    end

    -- UID
    local uid_range = tvb(offset, 8)
    local uid = uid_range:le_uint64():tonumber()
    local uid_tree = subtree:add_le(f_uid, uid_range)
    uid_tree:add_le(f_uid_iid, tvb(offset, 4))
    uid_tree:add_le(f_uid_pid, tvb(offset + 4, 2))
    uid_tree:add_le(f_uid_vid, tvb(offset + 6, 2))
    offset = offset + 8

    -- topic hash
    subtree:add_le(f_topic_hash, tvb(offset, 8))
    offset = offset + 8

    -- topic evictions
    subtree:add_le(f_topic_evictions, tvb(offset, 5))
    local topic_evictions = tvb(offset, 5):le_uint64():tonumber()
    offset = offset + 5

    -- floor(log(topic_age))
    local lage_range = tvb(offset, 1)
    local topic_lage = lage_range:int()
    subtree:add(f_topic_lage, lage_range)
    offset = offset + 1

    -- reserved
    offset = offset + 1

    -- topic name
    local name_len_range = tvb(offset, 1)
    local name_len = name_len_range:uint()
    subtree:add(f_topic_name_len, name_len_range)
    offset = offset + 1
    local remaining = tvb:len() - offset
    local actual_len = name_len
    if actual_len > remaining then
        actual_len = remaining
    end
    local topic_name = ""
    if actual_len > 0 then
        local name_range = tvb(offset, actual_len)
        topic_name = name_range:string()
        subtree:add(f_topic_name, name_range, topic_name)
    end

    -- Update Info column
    pinfo.cols.info = info..string.format(" 🆔%016x 🗣 %u %+d \"%s\"", uid, topic_evictions, topic_lage, topic_name)
end

-- Register dissector for UDP port 9382
local udp_port = DissectorTable.get("udp.port")
udp_port:add(9382, heartbeat_proto)
