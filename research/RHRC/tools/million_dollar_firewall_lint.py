"""Claim/dependency firewall for PR #247 ("Million Dollar PR").

This guard enforces architecture, not mathematical truth:
- the active route may not import earlier RH-equivalent shortcut gates;
- the active terminal reduction must actually depend on the typed branch package,
  true global-ground trial, and prime-weight layers;
- audit-only equivalence modules may not leak back into the active route;
- if a future premise-free RH closure file appears, an independent Lean exact-
  type audit file must appear with it.

Compiler/axiom checks remain authoritative for theorem validity.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
ZETA = REPO / "Zeta23"

FORBIDDEN_SHORTCUTS = {
    "Zeta23.ExceptionalZero.GeneratedFamilyFinalGate",
    "Zeta23.ExceptionalZero.GeneratedFamilyFinalGateEquivalence",
    "Zeta23.ExceptionalZero.CanonicalArithmeticCriterion",
}

AUDIT_ONLY = {
    "Zeta23.ExceptionalZero.CofinalArithmeticEquivalenceAudit",
    "Zeta23.ExceptionalZero.CofinalArithmeticConditionalRH",
    "Zeta23.ExceptionalZero.CofinalLowerBoundConditionalRH",
    "Zeta23.ExceptionalZero.GlobalParityBottomArithmeticEquivalenceAudit",
    "Zeta23.ExceptionalZero.GlobalParityBottomConditionalRH",
    "Zeta23.ExceptionalZero.GlobalParityBottomObstruction",
}

ACTIVE_CCM = {
    "Zeta23.CCM.GlobalParityBottomSpectrum",
    "Zeta23.CCM.GlobalParityBottomSecular",
    "Zeta23.CCM.GlobalParityBottomCrossParity",
    "Zeta23.CCM.GlobalParityBottomIntertwining",
    "Zeta23.CCM.GlobalParityBottomSourceMoment",
    "Zeta23.CCM.GlobalFirstBadParityBottom",
    "Zeta23.CCM.GlobalFirstBadParityBottomAlignment",
    "Zeta23.CCM.GlobalParityBottomRetainedGeometry",
    "Zeta23.CCM.GlobalParityBottomEvenStrictNormalForm",
    "Zeta23.CCM.GlobalParityBottomOddStrictNormalForm",
    "Zeta23.CCM.GlobalParityBottomReverseGroundTransfer",
    "Zeta23.CCM.GlobalParityBottomTieNormalForm",
    "Zeta23.CCM.GlobalParityBottomResidualState",
    "Zeta23.CCM.GlobalParityBottomBranchPackage",
    "Zeta23.CCM.GlobalParityBottomGroundTrial",
    "Zeta23.CCM.GlobalParityBottomPrimeRemainder",
    "Zeta23.CCM.GlobalParityBottomPrimeWeight",
    "Zeta23.CCM.GlobalParityBottomArithmeticTarget",
}

ACTIVE_TERMINAL = {
    "Zeta23.ExceptionalZero.GlobalParityBottomGeneratedState",
    "Zeta23.ExceptionalZero.GlobalParityBottomTerminalTarget",
}

IMPORT = re.compile(r"(?m)^import\s+(\S+)")


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO).with_suffix("").parts)


def graph() -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for path in list(ZETA.rglob("*.lean")) + [REPO / "Zeta23.lean"]:
        text = path.read_text(encoding="utf-8")
        out[module_name(path)] = [
            x for x in IMPORT.findall(text)
            if x == "Zeta23" or x.startswith("Zeta23.")
        ]
    return out


def closure(g: dict[str, list[str]], start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        node = stack.pop()
        for dep in g.get(node, []):
            if dep not in seen:
                seen.add(dep)
                stack.append(dep)
    return seen


def lint() -> list[str]:
    errors: list[str] = []
    g = graph()

    for module in sorted(ACTIVE_CCM | ACTIVE_TERMINAL):
        if module not in g:
            errors.append(f"active PR247 module missing: {module}")
            continue
        reached = closure(g, module)
        bad_shortcuts = reached & FORBIDDEN_SHORTCUTS
        if bad_shortcuts:
            errors.append(
                f"{module} reaches RH-equivalent shortcut modules "
                f"{sorted(bad_shortcuts)}"
            )
        bad_audits = reached & AUDIT_ONLY
        if bad_audits:
            errors.append(
                f"{module} reaches audit-only modules {sorted(bad_audits)}"
            )

    terminal = "Zeta23.ExceptionalZero.GlobalParityBottomTerminalTarget"
    required_terminal = {
        "Zeta23.CCM.GlobalParityBottomArithmeticTarget",
        "Zeta23.CCM.GlobalParityBottomPrimeWeight",
        "Zeta23.CCM.GlobalParityBottomPrimeRemainder",
        "Zeta23.CCM.GlobalParityBottomGroundTrial",
        "Zeta23.CCM.GlobalParityBottomBranchPackage",
    }
    if terminal in g:
        missing = required_terminal - closure(g, terminal)
        if missing:
            errors.append(
                "active terminal route bypasses required global-bottom layers: "
                f"{sorted(missing)}"
            )

    arithmetic = "Zeta23.CCM.GlobalParityBottomArithmeticTarget"
    required_arithmetic = {
        "Zeta23.CCM.GlobalParityBottomPrimeWeight",
        "Zeta23.CCM.GlobalParityBottomPrimeRemainder",
        "Zeta23.CCM.GlobalParityBottomGroundTrial",
        "Zeta23.CCM.GlobalParityBottomBranchPackage",
    }
    if arithmetic in g:
        missing = required_arithmetic - closure(g, arithmetic)
        if missing:
            errors.append(
                "arithmetic residual bypasses required branch/ground layers: "
                f"{sorted(missing)}"
            )

    exceptional_root = "Zeta23.ExceptionalZero"
    if exceptional_root in g:
        leaked = set(g[exceptional_root]) & AUDIT_ONLY
        if leaked:
            errors.append(
                "audit-only global-bottom modules imported by active "
                f"ExceptionalZero root: {sorted(leaked)}"
            )

    target = REPO / "Zeta23/ExceptionalZero/GlobalParityBottomTerminalTarget.lean"
    if target.exists():
        text = target.read_text(encoding="utf-8")
        if "RH remains OPEN." not in text:
            errors.append("active terminal target must explicitly retain RH OPEN status")

    closure_file = REPO / "Zeta23/ExceptionalZero/GlobalParityBottomRHClosure.lean"
    exact_audit = REPO / "Zeta23/ExceptionalZero/GlobalParityBottomExactTypeAudit.lean"
    if closure_file.exists():
        if not exact_audit.exists():
            errors.append(
                "premise-free closure file exists without independent exact-type audit"
            )
        else:
            audit_text = exact_audit.read_text(encoding="utf-8")
            required = (
                "theorem millionDollarExactTypeAudit :\n"
                "    RiemannHypothesis :="
            )
            if required not in audit_text:
                errors.append(
                    "exact-type audit must declare theorem "
                    "millionDollarExactTypeAudit : RiemannHypothesis"
                )
            if "#print axioms" not in audit_text:
                errors.append("exact-type audit lacks #print axioms")
    elif exact_audit.exists():
        errors.append("exact-type audit exists before a premise-free closure file")

    return errors


def main() -> int:
    errors = lint()
    if errors:
        print("PR247 MILLION DOLLAR FIREWALL: FAIL")
        for error in errors:
            print(" -", error)
        return 1
    print(
        "PR247 MILLION DOLLAR FIREWALL: PASS "
        f"({len(ACTIVE_CCM)} active CCM modules; "
        f"{len(ACTIVE_TERMINAL)} active terminal modules; "
        f"{len(AUDIT_ONLY)} audit-only modules)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
