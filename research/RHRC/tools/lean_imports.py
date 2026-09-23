"""Shared Lean import extraction for RHRC text-level graph/firewall tooling.

This is deliberately conservative: it preserves the existing import regex
semantics while removing Lean line comments and nested block comments first.
It is not a replacement for Lean elaboration and must not be used to infer
declaration-level theorem dependencies.
"""

from __future__ import annotations

import re

IMPORT = re.compile(r"(?m)^import\s+(\S+)")


def strip_lean_comments(text: str) -> str:
    """Replace comments with spaces while preserving newlines and string literals."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    escaped = False

    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                ch = text[i]
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        ch = text[i]
        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if text.startswith("--", i):
            out.extend((" ", " "))
            i += 2
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue

        if text.startswith("/-", i):
            block_depth = 1
            out.extend((" ", " "))
            i += 2
            continue

        out.append(ch)
        if ch == '"':
            in_string = True
        i += 1

    return "".join(out)


def import_modules(text: str) -> list[str]:
    """Return first-token module imports using the shared RHRC text semantics."""
    return IMPORT.findall(strip_lean_comments(text))


def _self_test() -> None:
    sample = """-/ not a comment
/- outer
import Fake.Block
/- nested import Fake.Nested -/
-/
import Real.One
-- import Fake.Line
def s := "import Fake.String"
import Real.Two -- import Fake.Trailing
"""
    assert import_modules(sample) == ["Real.One", "Real.Two"]

    historical_false_positive = """-/-
No.
-/
"""
    assert import_modules(historical_false_positive) == []

    prose_block = """/-
import this file.
import to Something.
-/
import Zeta23.CCM
"""
    assert import_modules(prose_block) == ["Zeta23.CCM"]


def main() -> int:
    _self_test()
    print("RHRC LEAN IMPORT PARSER: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
