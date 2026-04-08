#!/usr/bin/env bash
# Manage SocketCAN vcan interfaces. Usage:
#   vcan.sh {fd|classic|down} <iface>
# Example:
#   vcan.sh fd vcan0
#   vcan.sh down vcan0

set -euo pipefail

usage() {
    echo "Usage: ${0##*/} {fd|classic|down} <iface>" >&2
    exit 1
}

[ $# -eq 2 ] || usage

mode="$1"
iface="$2"

run() {
    if [ "$(id -u)" -eq 0 ]; then
        "$@"
    else
        sudo "$@"
    fi
}

case "$mode" in
    fd)      mtu=72 ;;
    classic) mtu=16 ;;
    down)
        run ip link delete dev "$iface"
        exit 0
        ;;
    *) usage ;;
esac

run modprobe vcan 2>/dev/null || true
run ip link add dev "$iface" type vcan
run ip link set dev "$iface" mtu "$mtu"
run ip link set dev "$iface" up
