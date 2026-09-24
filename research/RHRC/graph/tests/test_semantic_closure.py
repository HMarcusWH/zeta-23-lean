from __future__ import annotations

import unittest

from source_surface import exact_token_mentions, scan_named_source_declarations


def strip_comments(text: str) -> str:
    out = []
    in_block = False
    for line in text.splitlines(True):
        if "/-" in line:
            in_block = True
        if in_block:
            out.append("\n" if line.endswith("\n") else "")
            if "-/" in line:
                in_block = False
            continue
        before = line.split("--", 1)[0]
        out.append(before + ("\n" if line.endswith("\n") and not before.endswith("\n") else ""))
    return "".join(out)


class SemanticClosureTests(unittest.TestCase):
    def test_named_source_surface_is_discovery_only(self) -> None:
        text = """namespace Demo
-- theorem Fake : True := by trivial
private theorem hidden : True := by trivial
noncomputable def weight : Nat := 1
instance namedInst : Inhabited Nat := inferInstance
instance : Nonempty Nat := ⟨0⟩
/-
lemma Blocked : True := by trivial
-/
end Demo
"""
        rows = scan_named_source_declarations(
            path="Zeta23/Demo.lean",
            module="Zeta23.Demo",
            trust_zone="AUXILIARY_FORMALIZATION",
            source_locator={"repository": "HMarcusWH/zeta-23-lean", "path": "Zeta23/Demo.lean"},
            text=text,
            strip_comments=strip_comments,
        )
        self.assertEqual(
            [(row["command_kind"], row["declared_name"]) for row in rows],
            [("THEOREM", "hidden"), ("DEF", "weight"), ("INSTANCE", "namedInst")],
        )
        self.assertTrue(all(row["authority_role"] == "SOURCE_DISCOVERY_ONLY" for row in rows))

    def test_exact_token_mentions_do_not_substring_match(self) -> None:
        text = "R003_TEST and ROUTE_A; not R003_TEST_EXTRA"
        self.assertEqual(
            exact_token_mentions(text, {"R003_TEST", "R003_TEST_EXTRA", "R003_TE"}),
            ["R003_TEST", "R003_TEST_EXTRA"],
        )


if __name__ == "__main__":
    unittest.main()
