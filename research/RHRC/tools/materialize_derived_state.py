from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]


def run(cmd: list[str]) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=REPO, check=True)


def materialize() -> None:
    # Ordering is intentional:
    # 1. exact registered compiler dependencies feed RHKG;
    # 2. RHKG source census feeds source-candidate exactification;
    # 3. exactified source candidates feed FFBBP/source-only dependency export;
    # 4. source-only compiler products feed the contact-quotient view;
    # 5. those products plus RHKG frontiers feed the OoL phase atlas.
    run([sys.executable, str(ROOT / "tools" / "lean_dependency_extract.py"), "--write"])
    run([sys.executable, str(ROOT / "graph" / "build.py"), "--write"])
    run([sys.executable, str(ROOT / "graph" / "validate.py")])
    run([sys.executable, str(ROOT / "integration" / "candidate_exactify.py"), "--write"])
    run([sys.executable, str(ROOT / "ffbbp" / "rhkg_assurance.py"), "--write"])
    run([
        sys.executable,
        str(ROOT / "integration" / "source_only_dependency_extract.py"),
        "--write",
    ])
    run([sys.executable, str(ROOT / "graph" / "contact_quotient_dependency_extract.py"), "--write"])
    run([sys.executable, str(ROOT / "graph" / "contact_quotient_view.py"), "--write"])
    run([sys.executable, str(ROOT / "ool" / "rhkg_phase_atlas.py"), "--write"])


def check() -> None:
    run([sys.executable, str(ROOT / "tools" / "lean_dependency_extract.py"), "--check"])
    run([sys.executable, str(ROOT / "graph" / "build.py"), "--check"])
    run([sys.executable, str(ROOT / "graph" / "validate.py")])
    run([sys.executable, str(ROOT / "integration" / "candidate_exactify.py"), "--check"])
    run([sys.executable, str(ROOT / "ffbbp" / "rhkg_assurance.py"), "--check"])
    run([
        sys.executable,
        str(ROOT / "integration" / "source_only_dependency_extract.py"),
        "--check",
    ])
    run([sys.executable, str(ROOT / "graph" / "contact_quotient_dependency_extract.py"), "--check"])
    run([sys.executable, str(ROOT / "graph" / "contact_quotient_view.py"), "--check"])
    run([sys.executable, str(ROOT / "ool" / "rhkg_phase_atlas.py"), "--check"])


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Materialize/check the complete deterministic RHKG-derived state in "
            "dependency order"
        )
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument(
        "--write",
        action="store_true",
        help="regenerate the complete derived-state stack in the working tree",
    )
    group.add_argument(
        "--check",
        action="store_true",
        help="verify the complete derived-state stack is byte-current",
    )
    args = parser.parse_args()

    if args.write:
        materialize()
        print("RHRC DERIVED STATE: MATERIALIZED")
    else:
        check()
        print("RHRC DERIVED STATE: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
