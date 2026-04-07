#!/usr/bin/env python3
"""
Smoke-test a pair of examples in unattended CI:
1) example_echo subscribes to a topic.
2) example_time_pub publishes wall-clock timestamps onto that topic.
The test passes once echo output contains both topic name and timestamp text.
"""

from __future__ import annotations

import argparse
import os
import pathlib
import re
import shutil
import signal
import subprocess
import sys
import time
from dataclasses import dataclass


TOPIC = "demo/time"
TOPIC_RE = re.compile(r"\bdemo/time\b")
TIMESTAMP_RE = re.compile(r"\b\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}\b")


@dataclass
class ProcessFiles:
    stdout: pathlib.Path
    stderr: pathlib.Path


@dataclass
class SmokeResult:
    passed: bool
    failure_reason: str
    echo_files: ProcessFiles
    pub_files: ProcessFiles


@dataclass
class VcanSetup:
    iface_name: str
    ip_cmd: str
    privilege_prefix: list[str]
    created: bool


def terminate_process(proc: subprocess.Popen[str] | None) -> None:
    if proc is None:
        return
    if proc.poll() is not None:
        return
    proc.terminate()
    try:
        proc.wait(timeout=2.0)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait(timeout=2.0)


def read_text(path: pathlib.Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf8", errors="replace")


def short(text: str, limit: int = 1200) -> str:
    if len(text) <= limit:
        return text
    return text[-limit:]


def run_quiet(cmd: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, text=True, capture_output=True, check=False)


def privileged_command_prefix() -> list[str] | None:
    if not sys.platform.startswith("linux"):
        return None
    if getattr(os, "geteuid", lambda: 1)() == 0:
        return []
    sudo = shutil.which("sudo")
    if sudo is None:
        return None
    return [sudo, "-n"] if run_quiet([sudo, "-n", "true"]).returncode == 0 else None


def setup_vcan() -> tuple[VcanSetup | None, str]:
    if not sys.platform.startswith("linux"):
        return None, "non-Linux platform"
    ip_cmd = shutil.which("ip")
    if ip_cmd is None:
        return None, "`ip` command is unavailable"
    privilege_prefix = privileged_command_prefix()
    if privilege_prefix is None:
        return None, "passwordless sudo is unavailable"

    iface_name = "vcan0"
    created = False
    if run_quiet([ip_cmd, "link", "show", "dev", iface_name]).returncode != 0:
        modprobe = shutil.which("modprobe")
        if modprobe is not None:
            _ = run_quiet(privilege_prefix + [modprobe, "vcan"])
        add_result = run_quiet(privilege_prefix + [ip_cmd, "link", "add", "dev", iface_name, "type", "vcan"])
        if add_result.returncode != 0:
            return None, f"unable to create {iface_name}: {short(add_result.stderr.strip())}"
        created = True

    up_result = run_quiet(privilege_prefix + [ip_cmd, "link", "set", "dev", iface_name, "up"])
    if up_result.returncode != 0:
        if created:
            _ = run_quiet(privilege_prefix + [ip_cmd, "link", "delete", "dev", iface_name])
        return None, f"unable to activate {iface_name}: {short(up_result.stderr.strip())}"
    return VcanSetup(iface_name=iface_name, ip_cmd=ip_cmd, privilege_prefix=privilege_prefix, created=created), ""


def cleanup_vcan(setup: VcanSetup | None) -> None:
    if (setup is None) or (not setup.created):
        return
    _ = run_quiet(setup.privilege_prefix + [setup.ip_cmd, "link", "delete", "dev", setup.iface_name])


def run_smoke_case(
    build_dir: pathlib.Path,
    echo_bin: pathlib.Path,
    pub_bin: pathlib.Path,
    timeout_sec: float,
    publisher_delay_sec: float,
    label: str,
    echo_args: list[str],
    pub_args: list[str],
) -> SmokeResult:
    suffix = label.replace("/", "_")
    echo_files = ProcessFiles(stdout=build_dir / f"example_smoke_{suffix}_echo.out",
                              stderr=build_dir / f"example_smoke_{suffix}_echo.err")
    pub_files = ProcessFiles(stdout=build_dir / f"example_smoke_{suffix}_pub.out",
                             stderr=build_dir / f"example_smoke_{suffix}_pub.err")
    for f in (echo_files.stdout, echo_files.stderr, pub_files.stdout, pub_files.stderr):
        f.write_text("", encoding="utf8")

    echo_proc: subprocess.Popen[str] | None = None
    pub_proc: subprocess.Popen[str] | None = None
    passed = False
    failure_reason = ""

    try:
        with echo_files.stdout.open("w", encoding="utf8") as echo_out, echo_files.stderr.open(
            "w", encoding="utf8"
        ) as echo_err:
            echo_proc = subprocess.Popen([str(echo_bin), *echo_args], stdout=echo_out, stderr=echo_err)

        time.sleep(publisher_delay_sec)

        with pub_files.stdout.open("w", encoding="utf8") as pub_out, pub_files.stderr.open("w", encoding="utf8") as pub_err:
            pub_proc = subprocess.Popen([str(pub_bin), *pub_args], stdout=pub_out, stderr=pub_err)

        deadline = time.monotonic() + timeout_sec
        while time.monotonic() < deadline:
            if (echo_proc.poll() is not None) and (echo_proc.returncode != 0):
                failure_reason = f"example_echo exited early with code {echo_proc.returncode}"
                break
            if (pub_proc.poll() is not None) and (pub_proc.returncode != 0):
                failure_reason = f"example_time_pub exited early with code {pub_proc.returncode}"
                break

            echo_stdout = read_text(echo_files.stdout)
            if TOPIC_RE.search(echo_stdout) and TIMESTAMP_RE.search(echo_stdout):
                passed = True
                break
            time.sleep(0.1)
        if not passed and not failure_reason:
            failure_reason = "timeout waiting for expected echoed message"
    finally:
        terminate_process(pub_proc)
        terminate_process(echo_proc)

    return SmokeResult(passed=passed, failure_reason=failure_reason, echo_files=echo_files, pub_files=pub_files)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--build-dir", default="build", help="CMake build directory path")
    parser.add_argument("--timeout-sec", type=float, default=12.0, help="Overall smoke-test timeout")
    parser.add_argument("--publisher-delay-sec", type=float, default=1.0, help="Delay before starting publisher")
    args = parser.parse_args()

    build_dir = pathlib.Path(args.build_dir).resolve()
    echo_bin = build_dir / "examples" / "example_echo"
    pub_bin = build_dir / "examples" / "example_time_pub"
    for bin_path in (echo_bin, pub_bin):
        if not (bin_path.is_file() and os.access(bin_path, os.X_OK)):
            print(f"Missing executable: {bin_path}", file=sys.stderr)
            return 2

    build_dir.mkdir(parents=True, exist_ok=True)

    udp_result = run_smoke_case(build_dir,
                                echo_bin,
                                pub_bin,
                                args.timeout_sec,
                                args.publisher_delay_sec,
                                "udp",
                                [TOPIC],
                                [])
    if not udp_result.passed:
        print(f"Example smoke test failed: {udp_result.failure_reason}", file=sys.stderr)
        print("--- UDP example_echo stdout (tail) ---", file=sys.stderr)
        print(short(read_text(udp_result.echo_files.stdout)), file=sys.stderr)
        print("--- UDP example_echo stderr (tail) ---", file=sys.stderr)
        print(short(read_text(udp_result.echo_files.stderr)), file=sys.stderr)
        print("--- UDP example_time_pub stderr (tail) ---", file=sys.stderr)
        print(short(read_text(udp_result.pub_files.stderr)), file=sys.stderr)
        return 1

    vcan_setup, vcan_skip_reason = setup_vcan()
    if vcan_setup is None:
        print(f"Example smoke test passed: observed echoed demo/time timestamp; vcan skipped ({vcan_skip_reason}).")
        return 0

    try:
        iface_arg = f"iface=socketcan:{vcan_setup.iface_name}"
        vcan_result = run_smoke_case(build_dir,
                                     echo_bin,
                                     pub_bin,
                                     args.timeout_sec,
                                     args.publisher_delay_sec,
                                     "vcan",
                                     [iface_arg, TOPIC],
                                     [iface_arg])
    finally:
        cleanup_vcan(vcan_setup)

    if vcan_result.passed:
        print("Example smoke test passed: observed echoed demo/time timestamp over UDP and vcan.")
        return 0

    print(f"Example smoke test failed: {vcan_result.failure_reason}", file=sys.stderr)
    print("--- vcan example_echo stdout (tail) ---", file=sys.stderr)
    print(short(read_text(vcan_result.echo_files.stdout)), file=sys.stderr)
    print("--- vcan example_echo stderr (tail) ---", file=sys.stderr)
    print(short(read_text(vcan_result.echo_files.stderr)), file=sys.stderr)
    print("--- vcan example_time_pub stderr (tail) ---", file=sys.stderr)
    print(short(read_text(vcan_result.pub_files.stderr)), file=sys.stderr)
    return 1


if __name__ == "__main__":
    signal.signal(signal.SIGINT, signal.SIG_DFL)
    signal.signal(signal.SIGTERM, signal.SIG_DFL)
    raise SystemExit(main())
