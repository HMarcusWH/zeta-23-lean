from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
COMPILER_RECEIPT = ROOT / "graph" / "compiler" / "REGISTERED_DECLARATION_DEPENDENCIES.jsonl"
BOOTSTRAP_SCHEMA = "RHKG-phase2b-bootstrap-pending"


def compiler_receipt_bootstrap_pending() -> bool:
    lines = [line for line in COMPILER_RECEIPT.read_text(encoding="utf-8").splitlines() if line.strip()]
    if not lines:
        raise RuntimeError("RHKG compiler dependency receipt is empty")
    if len(lines) != 1:
        return False
    row = json.loads(lines[0])
    return row.get("schema_version") == BOOTSTRAP_SCHEMA


def run(cmd: list[str]) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=REPO, check=True)


def main() -> int:
    run([sys.executable, str(ROOT / "tools" / "claim_lint.py")])
    run([sys.executable, str(ROOT / "tools" / "registry_lint.py")])
    run([sys.executable, str(ROOT / "tools" / "promoted_binding_lint.py")])
    run([sys.executable, str(ROOT / "tools" / "registered_theorem_binding_lint.py")])
    run([sys.executable, str(ROOT / "tools" / "lean_imports.py")])
    run([sys.executable, str(ROOT / "tools" / "arithmetic_firewall_lint.py")])
    run([sys.executable, str(ROOT / "tools" / "million_dollar_firewall_lint.py")])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "graph" / "tests"), "-p", "test_*.py", "-v"])
    if compiler_receipt_bootstrap_pending():
        print(
            "RHKG graph checks: DEFERRED (Phase 2B compiler receipt bootstrap pending)",
            flush=True,
        )
    else:
        run([sys.executable, str(ROOT / "graph" / "build.py"), "--check"])
        run([sys.executable, str(ROOT / "graph" / "validate.py")])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "ffbbp" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "ool" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "runner" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "control_v2" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, str(ROOT / "countermodels" / "check_post155_riesz_pointwise_sign.py")])
    run([sys.executable, str(ROOT / "routes" / "R002_multi_probe" / "compare_r002_ccm_probe_families.py")])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
