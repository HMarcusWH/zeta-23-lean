"""Kernel axiom audit for selected promoted Lean modules.

Re-elaborates each module with `lake env lean` and parses its
`#print axioms` output.  Fails if any printed declaration depends on an axiom
outside Lean's standard three (in particular `sorryAx` or a project axiom), if
elaboration fails, or if a module prints no axiom report at all.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS = re.compile(r"'([^']+)' does not depend on any axioms")

# Require complete proof-authority receipts for the current contact-calculus
# promotion surface. A successful unrelated #print must not hide a missing
# frontier theorem report.
EXPECTED_REPORTS: dict[str, set[str]] = {
    "Zeta23/CCM/FirstCrossingGeneratedStrictEvenFrontier.lean": {
        "Zeta23.CCM.GeneratedStrictEvenContact.firstOrder_is_fresh",
        "Zeta23.CCM.GeneratedStrictEvenContact.production_frontier",
        "Zeta23.CCM.GeneratedStrictEvenContact.firstVariation_eq_zero_of_inherited",
        "Zeta23.CCM.GeneratedStrictEvenContact.production_stationary_saturation",
        "Zeta23.CCM.GeneratedStrictEvenContact.completed_production_frontier",
        "Zeta23.CCM.GeneratedStrictEvenContact.inherited_completed_production_frontier",
        "Zeta23.CCM.GeneratedGlobalFirstCrossing.exists_generatedStrictEvenContact_of_evenStrict",
        "Zeta23.CCM.GeneratedStrictEvenContact.frontier",
        "Zeta23.CCM.GeneratedStrictEvenContact.sourceValue_pos",
        "Zeta23.CCM.GeneratedStrictEvenContact.stationary_saturation_frontier",
        "Zeta23.CCM.production_stationary_schur_curvature_eq_zero",
        "Zeta23.CCM.GeneratedStrictEvenContact.actual_stationary_curvature_eq_zero",
    },
    "Zeta23/RHRC/ContactCalculusContract.lean": {
        "Zeta23.CCM.canonicalFirstVariation_eq_physical",
        "Zeta23.CCM.canonicalFixedSecondEuler_eq_physical",
        "Zeta23.CCM.canonicalMixedFirstVariation_eq_physical",
        "Zeta23.CCM.GeneratedStrictEvenContact.actual_stationary_curvature_eq_zero",
        "Zeta23.CCM.GeneratedStrictEvenContact.production_stationary_saturation",
        "Zeta23.CCM.GeneratedStrictEvenContact.completed_production_frontier",
        "Zeta23.CCM.GeneratedStrictEvenContact.inherited_production_saturation",
        "Zeta23.CCM.GeneratedStrictEvenContact.inherited_completed_production_frontier",
    },
}


def missing_expected_reports(path: str, printed: set[str]) -> list[str]:
    return sorted(EXPECTED_REPORTS.get(Path(path).as_posix(), set()) - printed)


DEFAULT_MODULES = (
    "Zeta23/CCM/CanonicalPrimeRemainder.lean",
    "Zeta23/ExceptionalZero/CanonicalArithmeticCriterion.lean",
    # PR #247 — Million Dollar PR promoted stack.
    "Zeta23/CCM/GlobalParityBottomSpectrum.lean",
    "Zeta23/CCM/GlobalParityBottomSecular.lean",
    "Zeta23/CCM/GlobalParityBottomCrossParity.lean",
    "Zeta23/CCM/GlobalParityBottomIntertwining.lean",
    "Zeta23/CCM/GlobalParityBottomSourceMoment.lean",
    "Zeta23/CCM/GlobalFirstBadParityBottom.lean",
    "Zeta23/CCM/GlobalFirstBadParityBottomAlignment.lean",
    "Zeta23/CCM/GlobalParityBottomRetainedGeometry.lean",
    "Zeta23/CCM/GlobalParityBottomEvenStrictNormalForm.lean",
    "Zeta23/CCM/GlobalParityBottomOddStrictNormalForm.lean",
    "Zeta23/CCM/GlobalParityBottomReverseGroundTransfer.lean",
    "Zeta23/CCM/GlobalParityBottomTieNormalForm.lean",
    "Zeta23/CCM/GlobalParityBottomResidualState.lean",
    "Zeta23/CCM/GlobalParityBottomBranchPackage.lean",
    "Zeta23/CCM/GlobalParityBottomGroundTrial.lean",
    "Zeta23/CCM/GlobalParityBottomPrimeRemainder.lean",
    "Zeta23/CCM/GlobalParityBottomPrimeWeight.lean",
    "Zeta23/CCM/GlobalParityBottomArithmeticTarget.lean",
    "Zeta23/ExceptionalZero/GlobalParityBottomGeneratedState.lean",
    "Zeta23/ExceptionalZero/GlobalParityBottomTerminalTarget.lean",
    "Zeta23/ExceptionalZero/GlobalParityBottomArithmeticEquivalenceAudit.lean",
    "Zeta23/ExceptionalZero/GlobalParityBottomConditionalRH.lean",
)


def audit(path: str) -> list[str]:
    proc = subprocess.run(
        ["lake", "env", "lean", path],
        cwd=REPO,
        capture_output=True,
        text=True,
    )
    output = proc.stdout + proc.stderr
    errors: list[str] = []
    if proc.returncode != 0:
        errors.append(f"{path}: elaboration failed\n{output}")
        return errors
    reports = REPORT.findall(output)
    clean = NO_AXIOMS.findall(output)
    if not reports and not clean:
        errors.append(f"{path}: no #print axioms report found")
    printed = {name for name, _ in reports} | set(clean)
    missing = missing_expected_reports(path, printed)
    if missing:
        errors.append(f"{path}: missing mandatory #print axioms reports: {missing}")
    for name, axioms in reports:
        used = {a.strip() for a in axioms.split(",") if a.strip()}
        extra = sorted(used - STANDARD)
        if extra:
            errors.append(f"{path}: {name} depends on non-standard axioms {extra}")
        else:
            print(f"  {name}: {sorted(used)}")
    for name in clean:
        print(f"  {name}: []")
    return errors


def main(argv: list[str]) -> int:
    modules = argv[1:] or list(DEFAULT_MODULES)
    errors: list[str] = []
    for module in modules:
        print(f"axiom audit: {module}")
        errors.extend(audit(module))
    if errors:
        print("RHRC AXIOM AUDIT: FAIL")
        for error in errors:
            print(" -", error)
        return 1
    print("RHRC AXIOM AUDIT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
