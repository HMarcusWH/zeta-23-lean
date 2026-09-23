"""Claim firewall for PR #247 ("Million Dollar PR").

This is a source/import-graph guard, not mathematical theorem authority.

The global-bottom reduction may use unconditional CCM arithmetic, but its
terminal target must not borrow any theorem that already packages an
RH-equivalent endpoint.  If a literal RH-closure module is later added, this
linter also checks that it does not reach those shortcut modules.

Logical strength is *not* inferred from imports: a genuine unconditional
residual-state contradiction would itself be RH-strength.  The purpose here is
only to prevent accidental circularity through already-proved equivalences.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
ZETA = REPO / "Zeta23"

FORBIDDEN = {
    "Zeta23.ExceptionalZero.GeneratedFamilyFinalGate",
    "Zeta23.ExceptionalZero.GeneratedFamilyFinalGateEquivalence",
    "Zeta23.ExceptionalZero.CanonicalArithmeticCriterion",
}

PR247_CCM = {
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
    "Zeta23.CCM.GlobalParityBottomPrimeRemainder",
    "Zeta23.CCM.GlobalParityBottomPrimeWeight",
}

PR247_TERMINAL = {
    "Zeta23.ExceptionalZero.GlobalParityBottomObstruction",
    "Zeta23.ExceptionalZero.GlobalParityBottomGeneratedState",
    "Zeta23.ExceptionalZero.GlobalParityBottomTerminalTarget",
    "Zeta23.ExceptionalZero.GlobalParityBottomRHClosure",
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

    for module in sorted(PR247_CCM):
        if module not in g:
            errors.append(f"PR247 CCM module missing: {module}")
            continue
        reached = closure(g, module) & FORBIDDEN
        if reached:
            errors.append(
                f"{module} reaches RH-equivalent shortcut modules {sorted(reached)}"
            )

    for module in sorted(PR247_TERMINAL):
        # The literal closure file is optional until an assumption-free theorem
        # actually exists; all other listed terminal modules are required.
        if module not in g:
            if module.endswith("GlobalParityBottomRHClosure"):
                continue
            errors.append(f"PR247 terminal module missing: {module}")
            continue
        reached = closure(g, module) & FORBIDDEN
        if reached:
            errors.append(
                f"{module} reaches RH-equivalent shortcut modules {sorted(reached)}"
            )

    target = REPO / "Zeta23/ExceptionalZero/GlobalParityBottomTerminalTarget.lean"
    if target.exists():
        text = target.read_text(encoding="utf-8")
        if "OPEN: no proof of this proposition is supplied" not in text:
            errors.append(
                "terminal target must explicitly retain its OPEN status until closure"
            )

    closure_file = REPO / "Zeta23/ExceptionalZero/GlobalParityBottomRHClosure.lean"
    if closure_file.exists():
        text = closure_file.read_text(encoding="utf-8")
        required = "theorem riemannHypothesis_globalParityBottom"
        if required not in text:
            errors.append(f"closure module exists but lacks {required}")
        if "RiemannHypothesis" not in text:
            errors.append("closure module exists but has no literal RiemannHypothesis target")

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
        f"({len(PR247_CCM)} CCM modules; "
        f"{len(PR247_TERMINAL) - 1} required terminal modules; "
        f"{len(FORBIDDEN)} shortcut modules fenced)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
