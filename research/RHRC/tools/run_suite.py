from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]


def run(cmd: list[str]) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=REPO, check=True)


def main() -> int:
    run([sys.executable, str(ROOT / "tools" / "claim_lint.py")])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "ffbbp" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "ool" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "runner" / "tests"), "-p", "test_*.py", "-v"])
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
