#!/usr/bin/env python3
"""Remove only Lake setup files whose corresponding successful trace is newer.

The original archive has a very large import graph. Per-module .setup.json files
may otherwise approach a terabyte. This never deletes objects, source, active
setup files, or dependencies. Run as a separate worker beside the owned build.
"""
import argparse
import signal
import time
from pathlib import Path

active = True


def stop(*_):
    global active
    active = False


def sweep(stage):
    ir = stage / ".lake/build/ir"
    lib = stage / ".lake/build/lib/lean"
    removed = size = 0
    for setup in ir.rglob("*.setup.json"):
        relative = setup.relative_to(ir).as_posix().removesuffix(".setup.json")
        trace = lib / (relative + ".trace")
        try:
            stat = setup.stat()
            if trace.is_file() and trace.stat().st_mtime_ns > stat.st_mtime_ns:
                size += stat.st_size
                setup.unlink()
                removed += 1
        except FileNotFoundError:
            pass  # The compiler may have already removed this completed file.
    return removed, size


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("stage", type=Path)
    p.add_argument("--once", action="store_true")
    a = p.parse_args()
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    while active:
        count, size = sweep(a.stage.resolve())
        print(f"completed_setup_cleanup files={count} bytes={size}", flush=True)
        if a.once: break
        # Short intervals keep termination responsive; this process does not
        # block the coordinating agent or the build process.
        for _ in range(30):
            if not active: break
            time.sleep(1)
