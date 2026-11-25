"""Negative controls for source slicing and import admission (not mathematics)."""
import tempfile
import unittest
from pathlib import Path
from stage_common import cut_between, exactly_remove, trim, import_closure
from lean_header import imports, rewrite_imports

class Controls(unittest.TestCase):
    def test_ambiguous_cut(self):
        with self.assertRaises(RuntimeError):
            cut_between("before CUT CUT END","CUT","END")
    def test_missing_cut(self):
        with self.assertRaises(RuntimeError):
            exactly_remove("unchanged","missing")
    def test_reversed_cut(self):
        with self.assertRaises(RuntimeError):
            cut_between("end start","start","end")
    def test_unexpected_suffix(self):
        with self.assertRaises(RuntimeError):
            trim("before CUT wrong","CUT","END")
    def test_endpoint_import(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            (p/"Root.lean").write_text("import Main\n")
            with self.assertRaises(RuntimeError):
                import_closure(p,["Root"])
    def test_unresolved_import(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            (p/"Root.lean").write_text("import Unknown.Source\n")
            with self.assertRaises(RuntimeError):
                import_closure(p,["Root"])
    def test_cycle_terminates(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            (p/"Root.lean").write_text("import Other\n")
            (p/"Other.lean").write_text("import Root\n")
            self.assertEqual(set(import_closure(p,["Root"])),{"Root","Other"})

    def test_prose_is_not_import(self):
        s = "/-! comment\nimport this module\n/- import Main -/\n-/\nimport Mathlib\n/- import Unknown.Source -/\ndef x := \"import Main\"\n"
        self.assertEqual([i.name for i in imports(s)], ["Mathlib"])
    def test_module_modifiers_and_multiline(self):
        s = "module\nprelude\npublic /- nested /- comment -/ -/ meta import Lean.Parser\nimport all\n Mathlib.Data.Real.Basic -- note\npublic section\n"
        self.assertEqual([i.name for i in imports(s)], ["Lean.Parser","Mathlib.Data.Real.Basic"])
    def test_quoted_identifier(self):
        self.assertEqual([i.name for i in imports("import A.«B-c».D\n")], ["A.B-c.D"])
    def test_bad_header(self):
        for s in ["import /- open", "import A.", "import\n", "public import A", "module\npublic import all A"]:
            with self.subTest(s=s), self.assertRaises(RuntimeError):
                imports(s)
    def test_rewrite_only_real_import_identifiers(self):
        s = "/- import Old.Fake -/\nmodule\npublic meta import Old.Real\nimport all Old.Other\n\ndef x := \"import Old.Text\"\n"
        expected = s.replace("import Old.Real","import New.Real").replace("all Old.Other","all New.Other")
        self.assertEqual(rewrite_imports(s,"Old.","New."), expected)
        self.assertEqual(rewrite_imports(expected,"New.","Old."), s)
    def test_prose_and_real_denied_import(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p/"Root.lean").write_text("/- import this\nimport Main -/\nimport Safe\n")
            (p/"Safe.lean").write_text("def x := \"import this\"\n")
            self.assertEqual(set(import_closure(p,["Root"])),{"Root","Safe"})
            (p/"Safe.lean").write_text("module\npublic meta import Main\n")
            with self.assertRaisesRegex(RuntimeError, "Main imported by Safe:2"):
                import_closure(p,["Root"])
    def test_unresolved_includes_importer(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p/"Root.lean").write_text("/- import this -/\nimport Missing.Module\n")
            with self.assertRaisesRegex(RuntimeError, "Missing.Module imported by Root:2"):
                import_closure(p,["Root"])

if __name__=="__main__":
    unittest.main()
