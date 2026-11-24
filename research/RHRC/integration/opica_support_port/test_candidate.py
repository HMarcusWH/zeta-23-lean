import unittest
from unittest.mock import patch
from check_candidate import Reject, axiom_reports, delta, verify_delta, POLICY, VALIDATOR, check

class Boundary(unittest.TestCase):
    def test_exact_source(self):
        d=check()
        self.assertEqual(d["public_root_count"],167)
        self.assertEqual(d["source_port_modules"],24)
        self.assertFalse(d["proof_acceptance"])

    def test_delta_rejects_extra_deleted_or_changed(self):
        a={"mode":"100644","type":"blob","sha":"a"*40}
        b={"mode":"100644","type":"blob","sha":"b"*40}
        base={"native":a}; good={**base,"candidate":b,POLICY:a,VALIDATOR:b}
        verify_delta(base,good,{"candidate":b},a["sha"],b["sha"])
        self.assertEqual(axiom_reports("'x' depends on axioms: [propext,\n  Classical.choice,\n  Quot.sound]\n", ["x"]), {"x":["Classical.choice","Quot.sound","propext"]})
        for bad in ({**good,"extra":b},{**good,"native":b},{k:v for k,v in good.items() if k!="native"},{**good,"candidate":a}):
            with self.assertRaises(Reject): verify_delta(base,bad,{"candidate":b},a["sha"],b["sha"])

    def test_named_axioms_fail_closed(self):
        self.assertEqual(axiom_reports("'x' depends on axioms: [propext]\n'y' does not depend on any axioms",["x","y"]),{"x":["propext"],"y":[]})
        for bad in ("'x' depends on axioms: [sorryAx]","'x' depends on axioms: [unknown]","'x' depends on axioms: [propext]\n'x' depends on axioms: [propext]",""):
            with self.assertRaises(Reject): axiom_reports(bad,["x"])

    def test_cross_pin_type_differences_report_exact_roots(self):
        from check_candidate import compare_type_rows
        import sys
        import check_candidate as c
        sys.path.insert(0,str(c.ROOT))
        a=[{"name":"x","expression":{"root":"x"},"sha256":"a"*64}]
        b=[{"name":"x","expression":{"root":"y"},"sha256":"b"*64}]
        with patch("research.RHRC.integration.opica_composition.inventory.expression_hash",
                   side_effect=lambda e: ("a" if e["root"]=="x" else "b")*64):
            self.assertEqual(compare_type_rows(a,a,["x"]),[])
            self.assertEqual([r["name"] for r in compare_type_rows(a,b,["x"])],["x"])
            with self.assertRaises(Reject): compare_type_rows(a,b,["y"])


    def test_pinned_absent_import_root(self):
        from independent_port import import_roots
        from pathlib import Path
        import json, os, tempfile
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            native = repo/".lake/build/lib/lean"
            core = repo/"runtime/lib/lean"
            pkg = repo/".lake/packages/Cli"
            for p in (native, core, pkg): p.mkdir(parents=True)
            (repo/"lake-manifest.json").write_text(json.dumps({"packagesDir":".lake/packages","packages":[{"name":"Cli","rev":"a"*40}]}))
            missing = pkg/".lake/build/lib/lean"
            with patch("independent_port.subprocess.check_output", return_value="a"*40+"\n"):
                paths, receipt = import_roots(repo, os.pathsep.join(map(str,(missing,native,native))), core)
                self.assertEqual(paths,[native,core])
                self.assertEqual(len(receipt["absent_pinned_package_roots"]),1)
                self.assertEqual(len(receipt["duplicate_canonical_roots"]),1)
                with self.assertRaises(Reject):
                    import_roots(repo, os.pathsep.join(map(str,(native,repo/"unknown"))), core)
                with self.assertRaises(Reject):
                    import_roots(repo,str(missing),core)
            with patch("independent_port.subprocess.check_output", return_value="b"*40+"\n"):
                with self.assertRaises(Reject):
                    import_roots(repo,os.pathsep.join(map(str,(missing,native))),core)

if __name__=="__main__": unittest.main()
