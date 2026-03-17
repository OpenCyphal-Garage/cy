#!/usr/bin/env python3
"""
Smoke-test a pair of UDP examples in unattended CI:
1) udp_echo subscribes to a topic.
2) udp_time_pub publishes wall-clock timestamps onto that topic.
The test passes once echo output contains both topic name and timestamp text.
"""

from __future__ import annotations

import argparse
import os
import pathlib
import re
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--build-dir", default="build", help="CMake build directory path")
    parser.add_argument("--timeout-sec", type=float, default=12.0, help="Overall smoke-test timeout")
    parser.add_argument("--publisher-delay-sec", type=float, default=1.0, help="Delay before starting publisher")
    args = parser.parse_args()

    build_dir = pathlib.Path(args.build_dir).resolve()
    echo_bin = build_dir / "examples" / "udp_echo"
    pub_bin = build_dir / "examples" / "udp_time_pub"
    for bin_path in (echo_bin, pub_bin):
        if not (bin_path.is_file() and os.access(bin_path, os.X_OK)):
            print(f"Missing executable: {bin_path}", file=sys.stderr)
            return 2

    tmp = build_dir
    tmp.mkdir(parents=True, exist_ok=True)
    echo_files = ProcessFiles(stdout=tmp / "example_smoke_echo.out", stderr=tmp / "example_smoke_echo.err")
    pub_files = ProcessFiles(stdout=tmp / "example_smoke_pub.out", stderr=tmp / "example_smoke_pub.err")
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
            echo_proc = subprocess.Popen([str(echo_bin), TOPIC], stdout=echo_out, stderr=echo_err)

        time.sleep(args.publisher_delay_sec)

        with pub_files.stdout.open("w", encoding="utf8") as pub_out, pub_files.stderr.open("w", encoding="utf8") as pub_err:
            pub_proc = subprocess.Popen([str(pub_bin)], stdout=pub_out, stderr=pub_err)

        deadline = time.monotonic() + args.timeout_sec
        while time.monotonic() < deadline:
            if (echo_proc.poll() is not None) and (echo_proc.returncode != 0):
                failure_reason = f"udp_echo exited early with code {echo_proc.returncode}"
                break
            if (pub_proc.poll() is not None) and (pub_proc.returncode != 0):
                failure_reason = f"udp_time_pub exited early with code {pub_proc.returncode}"
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

    if passed:
        print("Example smoke test passed: observed echoed demo/time timestamp.")
        return 0

    print(f"Example smoke test failed: {failure_reason}", file=sys.stderr)
    print("--- udp_echo stdout (tail) ---", file=sys.stderr)
    print(short(read_text(echo_files.stdout)), file=sys.stderr)
    print("--- udp_echo stderr (tail) ---", file=sys.stderr)
    print(short(read_text(echo_files.stderr)), file=sys.stderr)
    print("--- udp_time_pub stderr (tail) ---", file=sys.stderr)
    print(short(read_text(pub_files.stderr)), file=sys.stderr)
    return 1


if __name__ == "__main__":
    signal.signal(signal.SIGINT, signal.SIG_DFL)
    signal.signal(signal.SIGTERM, signal.SIG_DFL)
    raise SystemExit(main())
