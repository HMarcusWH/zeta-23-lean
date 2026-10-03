from __future__ import annotations

import argparse
import subprocess
import sys
import shutil
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]


def run(cmd: list[str]) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=REPO, check=True)


GENERATED_TARGETS = [
    ROOT / "graph" / "compiler",
    ROOT / "graph" / "generated",
    ROOT / "integration" / "generated",
    ROOT / "ffbbp" / "generated",
    ROOT / "ool" / "generated",
]

def _snapshot_generated(tmp: Path) -> None:
    for target in GENERATED_TARGETS:
        if target.exists():
            rel = target.relative_to(ROOT)
            dst = tmp / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(target, dst)

def _restore_generated(tmp: Path) -> None:
    for target in GENERATED_TARGETS:
        if target.exists():
            shutil.rmtree(target)
        src = tmp / target.relative_to(ROOT)
        if src.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(src, target)

def materialize() -> None:
    # Transactional materialization: a failed downstream producer must not
    # leave a half-new / half-stale derived-state bundle in the checkout.
    tmp = Path(tempfile.mkdtemp(prefix="rhrc-derived-state-"))
    _snapshot_generated(tmp)
    try:
        _materialize_impl()
    except BaseException:
        _restore_generated(tmp)
        raise
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

def _materialize_impl() -> None:
    # Ordering is intentional:
    # 1. exact registered compiler dependencies feed RHKG;
    # 2. RHKG source census feeds source-candidate exactification;
    # 3. exactified source candidates feed FFBBP/source-only dependency export;
    # 4. source-only compiler products feed the contact-quotient view;
    # 5. those products plus RHKG frontiers feed the OoL phase atlas.
    run([sys.executable, str(ROOT / "tools" / "lean_dependency_extract.py"), "--write"])
    run([sys.executable, str(ROOT / "graph" / "build.py"), "--write"])
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
    # Validate only after every declared generated product exists. The
    # contact-quotient products are generated downstream of source-only
    # exactification and therefore do not exist immediately after graph/build.
    run([sys.executable, str(ROOT / "graph" / "validate.py")])


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
