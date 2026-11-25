"""Negative controls for source slicing and import admission (not mathematics)."""
import tempfile
import unittest
from pathlib import Path
from stage_common import cut_between, exactly_remove, trim, import_closure

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

if __name__=="__main__":
    unittest.main()
