from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
WORKFLOW_DIR = REPO / ".github" / "workflows"


def bootstrap_materializer_present() -> bool:
    return any(WORKFLOW_DIR.glob("rhrc_*_materializer.yml"))


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
    if bootstrap_materializer_present():
        print(
            "RHRC SUITE: deferring strict RHKG byte-current build/validate "
            "while the one-shot integration materializer exists",
            flush=True,
        )
    else:
        run([sys.executable, str(ROOT / "graph" / "build.py"), "--check"])
        run([sys.executable, str(ROOT / "graph" / "validate.py")])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "ffbbp" / "tests"), "-p", "test_*.py", "-v"])
    if bootstrap_materializer_present():
        print(
            "RHRC SUITE: deferring FFBBP RHKG generated-report byte check "
            "while a one-shot materializer exists",
            flush=True,
        )
    else:
        run([sys.executable, str(ROOT / "ffbbp" / "rhkg_assurance.py"), "--check"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "ool" / "tests"), "-p", "test_*.py", "-v"])
    if bootstrap_materializer_present():
        print(
            "RHRC SUITE: deferring OoL RHKG Phase Atlas byte check "
            "while a one-shot materializer exists",
            flush=True,
        )
    else:
        run([sys.executable, str(ROOT / "ool" / "rhkg_phase_atlas.py"), "--check"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "runner" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "control_v2" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "integration" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, str(ROOT / "integration" / "integration_lint.py")])
    run([sys.executable, str(ROOT / "countermodels" / "check_post155_riesz_pointwise_sign.py")])
    run([sys.executable, str(ROOT / "routes" / "R002_multi_probe" / "compare_r002_ccm_probe_families.py")])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
