"""Negative controls for source slicing and import admission (not mathematics)."""
import tempfile
import unittest
from pathlib import Path
from stage_common import cut_between, exactly_remove, trim, import_closure, DENIED, EXTERNAL
from source_census import scan_imports, require_clean, reviewed_cut, git_blob_sha
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

    def test_full_bad_edge_inventory(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            (p/"Root.lean").write_text("import Left\nimport Right\n")
            (p/"Left.lean").write_text("import Main\nimport Missing.Mod\n")
            (p/"Right.lean").write_text("import Main\nimport Solution\n")
            c=scan_imports(p,["Root","Left"],DENIED,EXTERNAL)
            self.assertEqual(len(c["violations"]),4)
            left=[x for x in c["violations"] if x["importer"]=="Left" and x["target"]=="Main"][0]
            self.assertEqual(left["paths"],[["Root","Left","Main"],["Left","Main"]])
            self.assertEqual(len(left["importer_sha256"]),64)
            with self.assertRaisesRegex(RuntimeError,"4 source closure violation"):
                require_clean(c)

    def test_malformed_frontier_does_not_hide_sibling(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            (p/"Root.lean").write_text("import Bad\nimport Other\n")
            (p/"Bad.lean").write_text("import /- unterminated")
            (p/"Other.lean").write_text("import Solution\n")
            c=scan_imports(p,["Root"],DENIED,EXTERNAL)
            self.assertEqual({x["kind"] for x in c["violations"]},{"malformed","forbidden"})

    def test_unreviewed_cut(self):
        with self.assertRaisesRegex(RuntimeError,"unreviewed source cut"):
            reviewed_cut("x","original",lambda s:"cut",{})

    def test_changed_original_blob(self):
        reviews={"x":(git_blob_sha(b"original"),[])}
        with self.assertRaisesRegex(RuntimeError,"changed original source blob"):
            reviewed_cut("x","changed",lambda s:"cut",reviews)

    def test_retained_declaration(self):
        source="theorem producer\nimport denied\n"
        reviews={"x":(git_blob_sha(source.encode()),["theorem producer"])}
        self.assertEqual(reviewed_cut("x",source,lambda s:s.replace("import denied\n",""),reviews),"theorem producer\n")
        with self.assertRaisesRegex(RuntimeError,"retained declaration"):
            reviewed_cut("x",source,lambda s:"deleted",reviews)

    def test_restored_terminal_import(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            (p/"Root.lean").write_text("import Alias\n")
            (p/"Alias.lean").write_text("module\npublic meta import Main\n")
            c=scan_imports(p,["Root"],DENIED,EXTERNAL)
            self.assertEqual(c["violations"][0]["paths"],[["Root","Alias","Main"]])

    def test_reviewed_cut_hash_in_census(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            (p/"Root.lean").write_text("import Main\n")
            review={"before":"old","after":"new","retained_markers":["producer"]}
            c=scan_imports(p,["Root"],DENIED,EXTERNAL,{"Root.lean":review})
            self.assertEqual(c["violations"][0]["original_sha256"],"old")
            self.assertEqual(c["violations"][0]["reviewed_cut"],review)

if __name__=="__main__":
    unittest.main()
