from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
def run(cmd: list[str], *, cwd: Path = REPO) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def run_base_suite(args: argparse.Namespace, *, include_ancestor: bool = True) -> None:
    opica = ROOT / "integration" / "opica"
    if include_ancestor:
        run([sys.executable, str(opica / "validate_contract.py")])
        run([sys.executable, "-m", "unittest", "discover", "-s", str(opica / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, str(ROOT / "tools" / "claim_lint.py")])
    run([sys.executable, str(ROOT / "tools" / "registry_lint.py")])
    run([sys.executable, str(ROOT / "tools" / "promoted_binding_lint.py")])
    run([sys.executable, str(ROOT / "tools" / "registered_theorem_binding_lint.py")])
    run([sys.executable, str(ROOT / "tools" / "lean_imports.py")])
    run([sys.executable, str(ROOT / "tools" / "arithmetic_firewall_lint.py")])
    run([sys.executable, str(ROOT / "tools" / "million_dollar_firewall_lint.py")])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "graph" / "tests"), "-p", "test_*.py", "-v"])
    if not args.skip_derived_state:
        run([sys.executable, str(ROOT / "graph" / "build.py"), "--check"])
        run([sys.executable, str(ROOT / "graph" / "validate.py")])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "ffbbp" / "tests"), "-p", "test_*.py", "-v"])
    if not args.skip_derived_state:
        run([sys.executable, str(ROOT / "ffbbp" / "rhkg_assurance.py"), "--check"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "ool" / "tests"), "-p", "test_*.py", "-v"])
    if not args.skip_derived_state:
        run([sys.executable, str(ROOT / "ool" / "rhkg_phase_atlas.py"), "--check"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "runner" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "control_v2" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "integration" / "tests"), "-p", "test_*.py", "-v"])
    run([sys.executable, str(ROOT / "integration" / "integration_lint.py")])
    run([sys.executable, str(ROOT / "routes" / "R003_ccm_bridge" / "check_post281_generated_contact_build.py")])
    run([sys.executable, str(ROOT / "routes" / "R003_ccm_bridge" / "check_post282_contact_calculus_contract.py")])
    contact_quotient = ROOT / "routes" / "R003_ccm_bridge" / "contact_quotient"
    # Heavy contact-quotient symbolic/countermodel tests run in the dedicated
    # R003 workflow, which installs the numerical research dependency set.
    # Keep only the dependency-light authority lint in the base RHRC suite.
    run([sys.executable, str(contact_quotient / "source_authority_lint.py")])
    run([sys.executable, str(ROOT / "countermodels" / "check_post155_riesz_pointwise_sign.py")])
    run([sys.executable, str(ROOT / "routes" / "R002_multi_probe" / "compare_r002_ccm_probe_families.py")])


def source_snapshot(repo: Path = REPO) -> dict:
    """Read every committed source byte before execution; build caches are excluded.

    This records source identity only. It never grants compiler, CI or release
    authority and rejects ignored/untracked Lean/Python source providers.
    """
    repo = repo.resolve()
    def git(*args: str) -> bytes:
        return subprocess.check_output(["git", "-C", str(repo), *args])
    if git("status", "--porcelain", "--untracked-files=all").strip():
        raise ValueError("Source freeze requires a clean committed checkout")
    rows = []
    for record in git("ls-tree", "-r", "-z", "HEAD").split(b"\0"):
        if not record:
            continue
        metadata, name = record.split(b"\t", 1)
        mode, kind, blob = metadata.decode("ascii").split()
        relative = name.decode("utf-8")
        path = repo / relative
        if kind != "blob" or mode not in {"100644", "100755"} or path.is_symlink():
            raise ValueError("Unsupported or linked source: " + relative)
        if not path.resolve().is_relative_to(repo) or not path.is_file():
            raise ValueError("Missing or escaping source: " + relative)
        data = path.read_bytes()
        actual_blob = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()
        if actual_blob != blob:
            raise ValueError("Source differs from committed Git blob: " + relative)
        rows.append({"path": relative, "mode": mode, "git_blob": blob,
                     "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()})
    tracked = {row["path"] for row in rows}
    for base, directories, files in os.walk(repo, followlinks=False):
        directories[:] = [d for d in directories if d not in {".git", ".lake"}]
        current = Path(base)
        if any((current / d).is_symlink() for d in directories):
            raise ValueError("Linked project source directory")
        for name in files:
            path = current / name
            if path.suffix.lower() in {".lean", ".py"} and path.relative_to(repo).as_posix() not in tracked:
                raise ValueError("Untracked or ignored executable source provider")
    return {"schema": "OPICA2_WORKFLOW_SOURCE_FREEZE_V1",
            "checked_commit": git("rev-parse", "HEAD").decode().strip(),
            "checked_tree": git("rev-parse", "HEAD^{tree}").decode().strip(),
            "sources": sorted(rows, key=lambda r: r["path"]),
            "authority": "SOURCE_IDENTITY_ONLY", "full_core_accepted": False,
            "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}


def freeze_source(output: Path, *, repo: Path = REPO) -> None:
    output = output.resolve()
    if output.is_relative_to(repo.resolve()):
        raise ValueError("Source-freeze evidence must be external to the checkout")
    snapshot = source_snapshot(repo)
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x", encoding="utf-8") as stream:
        json.dump(snapshot, stream, indent=2)
        stream.write("\n")


def verify_source_freeze(source: Path, *, repo: Path = REPO) -> None:
    if json.loads(source.read_bytes()) != source_snapshot(repo):
        raise ValueError("Source identity changed during workflow commands")


def run_round2_suite(args: argparse.Namespace) -> None:
    """Frozen predicates run only in the authenticated ancestor projection."""
    if args.ancestor_projection is None:
        raise ValueError("Round2 suite requires explicit --ancestor-projection PATH")
    projection = args.ancestor_projection.resolve()
    os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
    round2 = ROOT / "integration" / "opica_round2"
    run([sys.executable, "-B", str(round2 / "ancestor_projection.py"), "verify",
         "--repo", str(REPO), "--destination", str(projection)])
    for name in ("opica", "opica_followup"):
        run([sys.executable, "-B", str(ROOT / "integration" / name / "validate_contract.py"),
             "--phase", "preflight", "--ancestor-projection", str(projection)])
        for mode in ([], ["-O"]):
            run([sys.executable, *mode, "-B", "-m", "unittest", "discover", "-s",
                 str(ROOT / "integration" / name / "tests"), "-p", "test_contract.py",
                 "-k", "Round2DescendantDispatchTests", "-v"])
    old_suite = projection / "research/RHRC/tools/run_suite.py"
    old_command = [sys.executable, "-B", str(old_suite)]
    if args.skip_derived_state:
        old_command.append("--skip-derived-state")
    run(old_command, cwd=projection)
    for mode in ([], ["-O"]):
        run([sys.executable, *mode, "-m", "unittest", "discover", "-s",
             str(projection / "research/RHRC/integration/opica_followup/tests"), "-p", "test_*.py", "-v"],
            cwd=projection)
    run_base_suite(args, include_ancestor=False)
    run([sys.executable, "-B", str(round2 / "run_checks.py"), "contract", "--scope", "full-core"])
    for mode in ([], ["-O"]):
        run([sys.executable, *mode, "-m", "unittest", "discover", "-s", str(round2 / "tests"),
             "-p", "test_*.py", "-v"])
    run([sys.executable, "-B", str(round2 / "ancestor_projection.py"), "verify",
         "--repo", str(REPO), "--destination", str(projection)])


# BEGIN REVIEWED WORKFLOW CLASSIFICATION INVENTORY
WORKFLOW_CLASSIFICATIONS = json.loads(r'''
{
  "schema": "OPICA2_REVIEWED_WORKFLOW_CLASSIFICATIONS_V1",
  "jobs": [
    {
      "workflow_path": ".github/workflows/rhrc_post268_audit.yml",
      "name": "Complete 44-check execution harvest",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post268_audit.yml",
      "name": "Extended audit shard 4",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post268_audit.yml",
      "name": "Extended audit shard 1",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post268_audit.yml",
      "name": "Extended audit shard 3",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post268_audit.yml",
      "name": "Extended audit shard 6",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post268_audit.yml",
      "name": "Extended audit shard 2",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post268_audit.yml",
      "name": "Extended audit shard 5",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post268_audit.yml",
      "name": "Extended audit shard 7",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post268_audit.yml",
      "name": "Extended audit shard 0",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post268_audit.yml",
      "name": "Audit runner adversarial regressions",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Eight deterministic shards execute all44 historical checks with hashed completeness harvest; preserves historical claims/falsifiers, execution harvest capRH_OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_followup.yml",
      "name": "followup-summary",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_followup.yml",
      "name": "followup-research-delta",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_followup.yml",
      "name": "followup-generated",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica.yml",
      "name": "opica-component-summary",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original P0 exact contract/formal/source-bound compiler/dependency and frozen regression gates, with RH/Step4 OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original P0 exact contract/formal/source-bound compiler/dependency and frozen regression gates, with RH/Step4 OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica.yml",
      "name": "opica-dependency-delta",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original P0 exact contract/formal/source-bound compiler/dependency and frozen regression gates, with RH/Step4 OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original P0 exact contract/formal/source-bound compiler/dependency and frozen regression gates, with RH/Step4 OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_followup.yml",
      "name": "followup-aggregate",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post282_contact_calculus.yml",
      "name": "contact-calculus-complete",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "Formal compressed/production/contact calculus plus calibration and bounded transport panel; no eligible inherited contact in one panel; near-contact transport-defect panel completed. No global barrier.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Formal compressed/production/contact calculus plus calibration and bounded transport panel; no eligible inherited contact in one panel; near-contact transport-defect panel completed. No global barrier.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post282_contact_calculus.yml",
      "name": "arb-contact-balance",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Formal compressed/production/contact calculus plus calibration and bounded transport panel; no eligible inherited contact in one panel; near-contact transport-defect panel completed. No global barrier.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Formal compressed/production/contact calculus plus calibration and bounded transport panel; no eligible inherited contact in one panel; near-contact transport-defect panel completed. No global barrier.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post287_numerical.yml",
      "name": "wp4-k3-fourth-order-alternative",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "WP2 independent1310 rational interval transcript verification; K2odd350 intervals verified. Dedicated384bit frozenK3 feasibility18/18PASS; fourth-order fallback skipped because gatePASS. Finite boxes not continuousK3 positivity.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. WP2 independent1310 rational interval transcript verification; K2odd350 intervals verified. Dedicated384bit frozenK3 feasibility18/18PASS; fourth-order fallback skipped because gatePASS. Finite boxes not continuousK3 positivity.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_closure_campaign.yml",
      "name": "campaign-complete",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_followup.yml",
      "name": "followup-formal (arithmetic)",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_followup.yml",
      "name": "followup-formal (local)",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_followup.yml",
      "name": "followup-regression",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_followup.yml",
      "name": "followup-formal (heat)",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_followup.yml",
      "name": "followup-formal (spectral)",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica.yml",
      "name": "opica-formal",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original P0 exact contract/formal/source-bound compiler/dependency and frozen regression gates, with RH/Step4 OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original P0 exact contract/formal/source-bound compiler/dependency and frozen regression gates, with RH/Step4 OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post284_source_inertia.yml",
      "name": "post287-full-k3",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Formal source-inertia identities plus frozen falsifiers and bounded probes. Some exact finite identities, some interval evidence, some unresolved. post287-full-k3 skipped by workflow trigger policy.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Formal source-inertia identities plus frozen falsifiers and bounded probes. Some exact finite identities, some interval evidence, some unresolved. post287-full-k3 skipped by workflow trigger policy.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post284_source_inertia.yml",
      "name": "source-falsifier-research",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Formal source-inertia identities plus frozen falsifiers and bounded probes. Some exact finite identities, some interval evidence, some unresolved. post287-full-k3 skipped by workflow trigger policy.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Formal source-inertia identities plus frozen falsifiers and bounded probes. Some exact finite identities, some interval evidence, some unresolved. post287-full-k3 skipped by workflow trigger policy.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post282_contact_calculus.yml",
      "name": "lean-compressed-calculus",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Formal compressed/production/contact calculus plus calibration and bounded transport panel; no eligible inherited contact in one panel; near-contact transport-defect panel completed. No global barrier.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Formal compressed/production/contact calculus plus calibration and bounded transport panel; no eligible inherited contact in one panel; near-contact transport-defect panel completed. No global barrier.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post192_parity_trajectory_rigidity.yml",
      "name": "post192-parity-trajectory-rigidity",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Exact scalar source identity plus frozen first-order enclosure; general reflected-production layers unresolved and no universal sign rigidity.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact scalar source identity plus frozen first-order enclosure; general reflected-production layers unresolved and no universal sign rigidity.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post284_source_inertia.yml",
      "name": "lean-source-inertia",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Formal source-inertia identities plus frozen falsifiers and bounded probes. Some exact finite identities, some interval evidence, some unresolved. post287-full-k3 skipped by workflow trigger policy.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Formal source-inertia identities plus frozen falsifiers and bounded probes. Some exact finite identities, some interval evidence, some unresolved. post287-full-k3 skipped by workflow trigger policy.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post287_focused.yml",
      "name": "wp5-modified-prime",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Formal fixed componentStep3 checks plus altered-prime same-cell crossing negative control; altered source is not actualzeta and divisor law rejects it.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Formal fixed componentStep3 checks plus altered-prime same-cell crossing negative control; altered source is not actualzeta and divisor law rejects it.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post282_contact_calculus.yml",
      "name": "research-calibration",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Formal compressed/production/contact calculus plus calibration and bounded transport panel; no eligible inherited contact in one panel; near-contact transport-defect panel completed. No global barrier.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Formal compressed/production/contact calculus plus calibration and bounded transport panel; no eligible inherited contact in one panel; near-contact transport-defect panel completed. No global barrier.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_followup.yml",
      "name": "followup-contract",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original100roots/28units in4formal lanes; exact-head aggregateCOMPILER_VERIFIED_FULL_100; current-parentP0exact-headPASS;39920frozen checks/mode and33noninterval consistency cases; generated state/repository suite; dependency delta; summaryexplicitlynotreleaseacceptance.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post287_numerical.yml",
      "name": "wp4-k2-odd-prerequisite",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "WP2 independent1310 rational interval transcript verification; K2odd350 intervals verified. Dedicated384bit frozenK3 feasibility18/18PASS; fourth-order fallback skipped because gatePASS. Finite boxes not continuousK3 positivity.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. WP2 independent1310 rational interval transcript verification; K2odd350 intervals verified. Dedicated384bit frozenK3 feasibility18/18PASS; fourth-order fallback skipped because gatePASS. Finite boxes not continuousK3 positivity.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post287_focused.yml",
      "name": "lean-step3",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Formal fixed componentStep3 checks plus altered-prime same-cell crossing negative control; altered source is not actualzeta and divisor law rejects it.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Formal fixed componentStep3 checks plus altered-prime same-cell crossing negative control; altered source is not actualzeta and divisor law rejects it.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc.yml",
      "name": "rhkg-compiler-receipt",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Registered294bindings and allowed-axiom audits;4OPENunbound; registered18915declaration extraction, canonical freshness and adversarial stale-state gates; numerical audit preserves unresolved/falsified scientific dispositions.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Registered294bindings and allowed-axiom audits;4OPENunbound; registered18915declaration extraction, canonical freshness and adversarial stale-state gates; numerical audit preserves unresolved/falsified scientific dispositions.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post194_parity_trajectory_sharp_enclosure.yml",
      "name": "post194-parity-trajectory-sharp-enclosure",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Finite second-derivative implementation check and frozen refined enclosure. Baseline33 J_UNRESOLVED+63 H1_UNRESOLVED; refined48 J_POSITIVE+48 J_UNRESOLVED,0 H1_UNRESOLVED. Not full trajectory rigidity.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Finite second-derivative implementation check and frozen refined enclosure. Baseline33 J_UNRESOLVED+63 H1_UNRESOLVED; refined48 J_POSITIVE+48 J_UNRESOLVED,0 H1_UNRESOLVED. Not full trajectory rigidity.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post287_numerical.yml",
      "name": "wp4-k3-frozen-feasibility",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "WP2 independent1310 rational interval transcript verification; K2odd350 intervals verified. Dedicated384bit frozenK3 feasibility18/18PASS; fourth-order fallback skipped because gatePASS. Finite boxes not continuousK3 positivity.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. WP2 independent1310 rational interval transcript verification; K2odd350 intervals verified. Dedicated384bit frozenK3 feasibility18/18PASS; fourth-order fallback skipped because gatePASS. Finite boxes not continuousK3 positivity.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post290_step123_output.yml",
      "name": "lean-components",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Exact synthetic/adversarial controls,176finite/7symbolic native observation coverage with independent1024bit reconstruction, exact component types and unapproved44field semantic dossier; complete generated detector/D2 producer acceptance remains distinct.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact synthetic/adversarial controls,176finite/7symbolic native observation coverage with independent1024bit reconstruction, exact component types and unapproved44field semantic dossier; complete generated detector/D2 producer acceptance remains distinct.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post198_q14_parity_source_mechanism.yml",
      "name": "post198-q14-source-mechanism",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED for four-way and collapsed-three-way representations; no unique collapsed uniform lock.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED for four-way and collapsed-three-way representations; no unique collapsed uniform lock.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post200_q14_discrepancy_mechanism.yml",
      "name": "post200-q14-discrepancy-mechanism",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED; no unique primary lock.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED; no unique primary lock.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc.yml",
      "name": "lean",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Registered294bindings and allowed-axiom audits;4OPENunbound; registered18915declaration extraction, canonical freshness and adversarial stale-state gates; numerical audit preserves unresolved/falsified scientific dispositions.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Registered294bindings and allowed-axiom audits;4OPENunbound; registered18915declaration extraction, canonical freshness and adversarial stale-state gates; numerical audit preserves unresolved/falsified scientific dispositions.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post282_contact_calculus.yml",
      "name": "lean-contact-completion",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Formal compressed/production/contact calculus plus calibration and bounded transport panel; no eligible inherited contact in one panel; near-contact transport-defect panel completed. No global barrier.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Formal compressed/production/contact calculus plus calibration and bounded transport panel; no eligible inherited contact in one panel; near-contact transport-defect panel completed. No global barrier.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post196_q14_residual_cell_replay.yml",
      "name": "post196-q14-residual-cell-replay",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Frozen unique post195 budget-leaf replay preserves unresolved A/J classification; no newly signed exact source law.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Frozen unique post195 budget-leaf replay preserves unresolved A/J classification; no newly signed exact source law.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc.yml",
      "name": "python-rhrc",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "Registered294bindings and allowed-axiom audits;4OPENunbound; registered18915declaration extraction, canonical freshness and adversarial stale-state gates; numerical audit preserves unresolved/falsified scientific dispositions.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Registered294bindings and allowed-axiom audits;4OPENunbound; registered18915declaration extraction, canonical freshness and adversarial stale-state gates; numerical audit preserves unresolved/falsified scientific dispositions.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_closure_campaign.yml",
      "name": "lean-strength-audit",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_closure_campaign.yml",
      "name": "lean-c",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_closure_campaign.yml",
      "name": "lean-a",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post287_numerical.yml",
      "name": "wp2-k2-transcript",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "WP2 independent1310 rational interval transcript verification; K2odd350 intervals verified. Dedicated384bit frozenK3 feasibility18/18PASS; fourth-order fallback skipped because gatePASS. Finite boxes not continuousK3 positivity.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. WP2 independent1310 rational interval transcript verification; K2odd350 intervals verified. Dedicated384bit frozenK3 feasibility18/18PASS; fourth-order fallback skipped because gatePASS. Finite boxes not continuousK3 positivity.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post290_step123_output.yml",
      "name": "native-observations",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Exact synthetic/adversarial controls,176finite/7symbolic native observation coverage with independent1024bit reconstruction, exact component types and unapproved44field semantic dossier; complete generated detector/D2 producer acceptance remains distinct.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact synthetic/adversarial controls,176finite/7symbolic native observation coverage with independent1024bit reconstruction, exact component types and unapproved44field semantic dossier; complete generated detector/D2 producer acceptance remains distinct.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_closure_campaign.yml",
      "name": "lean-b",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_closure_campaign.yml",
      "name": "lean-first-crossing",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_closure_campaign.yml",
      "name": "lean-d-bindings",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/permansson-formal.yml",
      "name": "lean-permansson",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Compiles separate Permansson formal surface; useful repository regression, no RH theorem.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Compiles separate Permansson formal surface; useful repository regression, no RH theorem.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_closure_campaign.yml",
      "name": "lean-contact",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post290_step123_output.yml",
      "name": "exact-controls",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Exact synthetic/adversarial controls,176finite/7symbolic native observation coverage with independent1024bit reconstruction, exact component types and unapproved44field semantic dossier; complete generated detector/D2 producer acceptance remains distinct.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact synthetic/adversarial controls,176finite/7symbolic native observation coverage with independent1024bit reconstruction, exact component types and unapproved44field semantic dossier; complete generated detector/D2 producer acceptance remains distinct.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc.yml",
      "name": "r003-normalization-audit",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Registered294bindings and allowed-axiom audits;4OPENunbound; registered18915declaration extraction, canonical freshness and adversarial stale-state gates; numerical audit preserves unresolved/falsified scientific dispositions.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Registered294bindings and allowed-axiom audits;4OPENunbound; registered18915declaration extraction, canonical freshness and adversarial stale-state gates; numerical audit preserves unresolved/falsified scientific dispositions.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post214_kernel_dual_geometry.yml",
      "name": "post214-kernel-dual-geometry",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Exact frozen kernel-dual controls certify full-space dual independence and sign indefiniteness; Q13/Q15 control transfer survives. Not source-specific positivity.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact frozen kernel-dual controls certify full-space dual independence and sign indefiniteness; Q13/Q15 control transfer survives. Not source-specific positivity.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post222_biregular_zero_shift_scalar.yml",
      "name": "post222-biregular-zero-shift-scalar",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Frozen biregular zero-shift scalar isolation and adversarial controls; no independent all-source Step4 upper.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Frozen biregular zero-shift scalar isolation and adversarial controls; no independent all-source Step4 upper.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post287_wp6.yml",
      "name": "wp6-source-specific-signed-ray",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "EXPERIMENTAL_SIGNAL: signs [[true,false],[false,true]] on the bounded actual K2 shifted-ray panel; not a universal sign theorem.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. EXPERIMENTAL_SIGNAL: signs [[true,false],[false,true]] on the bounded actual K2 shifted-ray panel; not a universal sign theorem.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post202_q14_composite_parity_gap.yml",
      "name": "post202-q14-composite-parity-gap",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED; pattern falsified before full cover. Upstream discrepancy dependency remains unresolved.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED; pattern falsified before full cover. Upstream discrepancy dependency remains unresolved.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_closure_campaign.yml",
      "name": "fast-integrity",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact builds of A/B/C/D/contact/first-crossing/strength-audit conditional components and axiom checks; campaign completion does not discharge closure antecedents.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica.yml",
      "name": "opica-contract",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original P0 exact contract/formal/source-bound compiler/dependency and frozen regression gates, with RH/Step4 OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original P0 exact contract/formal/source-bound compiler/dependency and frozen regression gates, with RH/Step4 OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_post190_canonical_realizability.yml",
      "name": "post190-canonical-realizability",
      "classification": "RESEARCH_PRODUCING_CHECK",
      "evidence_scope": "Exact scalar-aperture restrictions reject one old negative-scalar witness; general positive-scalar reflected model survives this restriction; layers3-5 unresolved.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. Exact scalar-aperture restrictions reject one old negative-scalar witness; general positive-scalar reflected model survives this restriction; layers3-5 unresolved.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica.yml",
      "name": "opica-regression",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original P0 exact contract/formal/source-bound compiler/dependency and frozen regression gates, with RH/Step4 OPEN.",
      "on_success": "Provider job completed; inspect the exact source-bound artifacts before assigning new mathematical authority. For a declared Round2 descendant this workflow executes the authenticated frozen baseline only; current-tree compatibility is a separate Round2 ancestry gate. Original P0 exact contract/formal/source-bound compiler/dependency and frozen regression gates, with RH/Step4 OPEN.",
      "on_failure": "The stated gate has not been established by this execution. Preserve failure, skipped, pending and cancellation dispositions."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "contract",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Frozen specification, exact descendant source policy, 40 mandatory family coverage and declared input/source guards; preflight proves no theorem.",
      "on_success": "Provider execution completed; exact artifacts must establish the stated scope. Frozen specification, exact descendant source policy, 40 mandatory family coverage and declared input/source guards; preflight proves no theorem.",
      "on_failure": "This required gate is missing, unsuccessful or incomplete; no acceptance inferred."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "controls",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "Actual complete runtime controls and adversarial test suites in normal and optimized Python, with hash-locked python-flint.",
      "on_success": "Provider execution completed; exact artifacts must establish the stated scope. Actual complete runtime controls and adversarial test suites in normal and optimized Python, with hash-locked python-flint.",
      "on_failure": "This required gate is missing, unsuccessful or incomplete; no acceptance inferred."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "ancestry",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Authenticated exact frozen 76/100 baseline compiler replay plus separately produced current-tree original-root type/axiom/dependency compatibility.",
      "on_success": "Provider execution completed; exact artifacts must establish the stated scope. Authenticated exact frozen 76/100 baseline compiler replay plus separately produced current-tree original-root type/axiom/dependency compatibility.",
      "on_failure": "This required gate is missing, unsuccessful or incomplete; no acceptance inferred."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "aggregate",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Exact current-source complete compiler export and component/control reparse; project build objects absent at the start, only pinned package caches admitted.",
      "on_success": "Provider execution completed; exact artifacts must establish the stated scope. Exact current-source complete compiler export and component/control reparse; project build objects absent at the start, only pinned package caches admitted.",
      "on_failure": "This required gate is missing, unsuccessful or incomplete; no acceptance inferred."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "generated",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "Check all 81 committed canonical products before any producer write; independently regenerate in a disposable exact-head checkout and require identical bytes.",
      "on_success": "Provider execution completed; exact artifacts must establish the stated scope. Check all 81 committed canonical products before any producer write; independently regenerate in a disposable exact-head checkout and require identical bytes.",
      "on_failure": "This required gate is missing, unsuccessful or incomplete; no acceptance inferred."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "harvest",
      "classification": "REGRESSION_GATE",
      "evidence_scope": "Complete provider pagination and attempt/job dispositions. The workflow observes itself pending; separate completed post-run review remains required.",
      "on_success": "Provider execution completed; exact artifacts must establish the stated scope. Complete provider pagination and attempt/job dispositions. The workflow observes itself pending; separate completed post-run review remains required.",
      "on_failure": "This required gate is missing, unsuccessful or incomplete; no acceptance inferred."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "acceptance",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Independent exact compiler/component/control/ancestry evidence revalidation only; no human approval, completed workflow harvest or full-release acceptance inferred.",
      "on_success": "Provider execution completed; exact artifacts must establish the stated scope. Independent exact compiler/component/control/ancestry evidence revalidation only; no human approval, completed workflow harvest or full-release acceptance inferred.",
      "on_failure": "This required gate is missing, unsuccessful or incomplete; no acceptance inferred."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "formal(causal)",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Compile the frozen causal target list and its independent Validation modules at the requested current head; lane success alone is not full-core or release acceptance.",
      "on_success": "Provider execution completed; exact artifacts must establish the stated scope. Compile the frozen causal target list and its independent Validation modules at the requested current head; lane success alone is not full-core or release acceptance.",
      "on_failure": "This required gate is missing, unsuccessful or incomplete; no acceptance inferred."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "formal(filtered)",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Compile the frozen filtered target list and its independent Validation modules at the requested current head; lane success alone is not full-core or release acceptance.",
      "on_success": "Provider execution completed; exact artifacts must establish the stated scope. Compile the frozen filtered target list and its independent Validation modules at the requested current head; lane success alone is not full-core or release acceptance.",
      "on_failure": "This required gate is missing, unsuccessful or incomplete; no acceptance inferred."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "formal(gram)",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Compile the frozen gram target list and its independent Validation modules at the requested current head; lane success alone is not full-core or release acceptance.",
      "on_success": "Provider execution completed; exact artifacts must establish the stated scope. Compile the frozen gram target list and its independent Validation modules at the requested current head; lane success alone is not full-core or release acceptance.",
      "on_failure": "This required gate is missing, unsuccessful or incomplete; no acceptance inferred."
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "formal(structural)",
      "classification": "FORMAL_VALIDITY_GATE",
      "evidence_scope": "Compile the frozen structural target list and its independent Validation modules at the requested current head; lane success alone is not full-core or release acceptance.",
      "on_success": "Provider execution completed; exact artifacts must establish the stated scope. Compile the frozen structural target list and its independent Validation modules at the requested current head; lane success alone is not full-core or release acceptance.",
      "on_failure": "This required gate is missing, unsuccessful or incomplete; no acceptance inferred."
    }
  ],
  "required_jobs": [
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "contract"
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "controls"
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "ancestry"
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "aggregate"
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "generated"
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "harvest"
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "acceptance"
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "formal(causal)"
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "formal(filtered)"
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "formal(gram)"
    },
    {
      "workflow_path": ".github/workflows/rhrc_opica_round2.yml",
      "name": "formal(structural)"
    }
  ],
  "historical_scope_reference": "PR294 exact416 source workflow audit; current source and outcomes are independently recollected at each run."
}
''')
# END REVIEWED WORKFLOW CLASSIFICATION INVENTORY

def main() -> int:
    parser = argparse.ArgumentParser(description="Run current RHRC checks and explicitly scoped historical replay")
    parser.add_argument("--skip-derived-state", action="store_true",
        help="Development-only omission of generated checks; never full acceptance")
    parser.add_argument("--ancestor-projection", type=Path,
        help="Authenticated exact frozen source checkout for original 76/100 predicates")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--workflow-classifications", type=Path)
    group.add_argument("--freeze-source", type=Path)
    group.add_argument("--verify-source-freeze", type=Path)
    args = parser.parse_args()
    if args.workflow_classifications:
        output=args.workflow_classifications.resolve()
        if output.is_relative_to(REPO.resolve()):
            raise ValueError("Workflow observation configuration must be external")
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("x", encoding="utf-8") as stream:
            json.dump(WORKFLOW_CLASSIFICATIONS, stream, indent=2)
            stream.write("\n")
    elif args.freeze_source:
        freeze_source(args.freeze_source)
    elif args.verify_source_freeze:
        verify_source_freeze(args.verify_source_freeze)
    elif (ROOT / "integration/opica_round2/BUILD_MANIFEST.json").is_file():
        run_round2_suite(args)
    else:
        run_base_suite(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
