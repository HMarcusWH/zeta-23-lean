"""Anti-circularity firewall for the post-#245 arithmetic layer.

PR #245 proved that the terminal certificate gates are equivalent to Mathlib's
`RiemannHypothesis`.  Any further "closing" argument must therefore contain
genuinely new unconditional mathematics, and it must be impossible for such an
argument to borrow the terminal layer by import.

Rules enforced here (text/import-graph level; the Lean kernel remains the
authority on the mathematics itself):

1. No `Zeta23.CCM` module may transitively import a terminal module
   (the Mathlib RH seam, the generated-family gate, its RH equivalence, or the
   canonical arithmetic criterion).
2. No source file under `Zeta23/CCM` may mention `RiemannHypothesis`.
3. The unconditional arithmetic modules listed in `ARITHMETIC_MODULES` must
   exist and must not reach a terminal module.
4. No kernel-escape mechanism appears in the promoted subtrees.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
ZETA = REPO / "Zeta23"

TERMINAL_MODULES = {
    "Zeta23.ExceptionalZero.RHTerminalConfigAttempt",
    "Zeta23.ExceptionalZero.GeneratedFamilyFinalGate",
    "Zeta23.ExceptionalZero.GeneratedFamilyFinalGateEquivalence",
    "Zeta23.ExceptionalZero.CanonicalArithmeticCriterion",
}

ARITHMETIC_MODULES = (
    "Zeta23.CCM.CanonicalPrimeRemainder",
)

KERNEL_ESCAPES = re.compile(
    r"native_decide|implemented_by|@\[extern|debug\.skipKernelTC|"
    r"^\s*unsafe\s|Lean\.ofReduceBool|trustCompiler",
    re.MULTILINE,
)

IMPORT = re.compile(r"(?m)^import\s+(\S+)")


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO).with_suffix("").parts)


def import_graph() -> dict[str, list[str]]:
    graph: dict[str, list[str]] = {}
    for path in list(ZETA.rglob("*.lean")) + [REPO / "Zeta23.lean"]:
        text = path.read_text(encoding="utf-8")
        graph[module_name(path)] = [
            m for m in IMPORT.findall(text) if m == "Zeta23" or m.startswith("Zeta23.")
        ]
    return graph


def closure(graph: dict[str, list[str]], start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        for dep in graph.get(stack.pop(), []):
            if dep not in seen:
                seen.add(dep)
                stack.append(dep)
    return seen


def lint() -> list[str]:
    errors: list[str] = []
    graph = import_graph()

    for terminal in TERMINAL_MODULES:
        if terminal not in graph:
            errors.append(f"terminal module missing from tree: {terminal}")

    for module in sorted(graph):
        if module == "Zeta23.CCM" or module.startswith("Zeta23.CCM."):
            reached = closure(graph, module) & TERMINAL_MODULES
            if reached:
                errors.append(f"{module} transitively imports terminal modules {sorted(reached)}")

    for path in sorted((ZETA / "CCM").rglob("*.lean")):
        if re.search(r"\bRiemannHypothesis\b", path.read_text(encoding="utf-8")):
            errors.append(f"{path.relative_to(REPO)} mentions RiemannHypothesis")

    for module in ARITHMETIC_MODULES:
        if module not in graph:
            errors.append(f"arithmetic module missing: {module}")
            continue
        reached = closure(graph, module) & TERMINAL_MODULES
        if reached:
            errors.append(f"arithmetic module {module} reaches terminal modules {sorted(reached)}")

    for sub in ("CCM", "ExceptionalZero"):
        for path in sorted((ZETA / sub).rglob("*.lean")):
            match = KERNEL_ESCAPES.search(path.read_text(encoding="utf-8"))
            if match:
                errors.append(
                    f"{path.relative_to(REPO)} contains kernel escape {match.group(0)!r}"
                )

    return errors


def main() -> int:
    errors = lint()
    if errors:
        print("RHRC ARITHMETIC FIREWALL: FAIL")
        for error in errors:
            print(" -", error)
        return 1
    print(
        "RHRC ARITHMETIC FIREWALL: PASS "
        f"({len(TERMINAL_MODULES)} terminal modules fenced; "
        f"{len(ARITHMETIC_MODULES)} arithmetic modules checked)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
