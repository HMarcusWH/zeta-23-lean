"""Adversarial fixtures for the receipt verifier (not proof acceptance)."""
import json
import tempfile
import unittest
from pathlib import Path
from verify_audit_receipts import (
    PREFIX, REQUIRED, DIRECT_FORBIDDEN, NATIVE_ROOTS, COMMON_ROOTS, STOCK_ROOTS, EXPECTED_EXCLUDED, validate_root, compare,
)

class EvidenceControls(unittest.TestCase):
    def row(self, root):
        deps = {x:"Zeta23.Test" for x in REQUIRED[root]|{root}}
        for x in deps:
            if x.startswith("Deduction."):
                deps[x]="Zeta23.OPICATerminal.Analytic.Test"
        return {"schema":"OPICA_TERMINAL_DECLARATION_AUDIT_V2","root":root,
                "root_type":"RiemannHypothesis" if root in STOCK_ROOTS else "test type",
                "root_type_const":"RiemannHypothesis" if root in STOCK_ROOTS else "",
                "root_type_expr":"Expr.const RiemannHypothesis",
                "axioms":["propext"],"required":sorted(REQUIRED[root]),"excluded":sorted(EXPECTED_EXCLUDED.get(root,set())),
                "native_only":root in NATIVE_ROOTS,"constants":len(deps),
                "dependencies":[{"name":n,"module":m} for n,m in deps.items()]}

    def add(self, row, name, module):
        row["dependencies"].append({"name":name,"module":module})
        row["constants"]+=1

    def test_valid_native_fixture(self):
        root=PREFIX+"eventual_literalGEnergy_ge_rpow"
        result=validate_root(self.row(root),root,set(),"native")
        self.assertIn(root,result["dependencies"])

    def test_wrong_origin_in_arbitrary_namespace(self):
        root=PREFIX+"powerDetectorSupply_proved"
        row=self.row(root)
        self.add(row,"Unfamiliar.Name","Development.AbelianVarietyTheory.Proof")
        with self.assertRaisesRegex(RuntimeError,"nonanalytic original module"):
            validate_root(row,root,set(),"common")

    def test_endpoint_declaration_under_safe_module(self):
        root=PREFIX+"powerDetectorSupply_proved"
        row=self.row(root)
        self.add(row,"UpperTheory.zeta_ne_zero_of_everyCharacter","Zeta23.Test")
        with self.assertRaisesRegex(RuntimeError,"forbidden declaration"):
            validate_root(row,root,set(),"native")

    def test_missing_required_root(self):
        root=PREFIX+"directEnergyToC1_proved"
        row=self.row(root)
        row["dependencies"].pop(0)
        row["constants"]-=1
        with self.assertRaises(RuntimeError):
            validate_root(row,root,set(),"native")

    def test_direct_crosscheck_cannot_use_detector(self):
        root=PREFIX+"riemannHypothesis_of_nativeEnergySubpower_direct"
        row=self.row(root)
        self.add(row,sorted(DIRECT_FORBIDDEN)[0],"Zeta23.Test")
        with self.assertRaisesRegex(RuntimeError,"detector contamination|excluded dependency present"):
            validate_root(row,root,set(),"native")

    def test_unapproved_axiom(self):
        root=PREFIX+"eventual_literalGEnergy_ge_rpow"
        row=self.row(root)
        row["axioms"].append("sorryAx")
        with self.assertRaisesRegex(RuntimeError,"unapproved axioms"):
            validate_root(row,root,set(),"native")

    def test_exact_stock_rh_type(self):
        root=PREFIX+"riemannHypothesis_step4_arithmetic_supplied"
        row=self.row(root)
        row["root_type"]="P → RiemannHypothesis"
        with self.assertRaisesRegex(RuntimeError,"not exact stock RH"):
            validate_root(row,root,set(),"common")

    def test_required_policy_cannot_be_weakened(self):
        root=PREFIX+"powerDetectorSupply_proved"
        row=self.row(root)
        row["required"].pop()
        with self.assertRaisesRegex(RuntimeError,"required audit policy drift"):
            validate_root(row,root,set(),"native")

    def test_excluded_policy_cannot_be_weakened(self):
        root=PREFIX+"riemannHypothesis_of_nativeEnergySubpower_direct"
        row=self.row(root)
        row["excluded"].pop()
        with self.assertRaisesRegex(RuntimeError,"excluded audit policy drift"):
            validate_root(row,root,set(),"native")

    def test_stock_type_const_is_checked(self):
        root=PREFIX+"riemannHypothesis_step4_direct_crosscheck"
        row=self.row(root)
        row["root_type_const"]="Fake.RiemannHypothesis"
        with self.assertRaisesRegex(RuntimeError,"not exact stock RH constant"):
            validate_root(row,root,set(),"common")

    def test_denied_prefix_matches_lean_policy(self):
        root=PREFIX+"powerDetectorSupply_proved"
        row=self.row(root)
        self.add(row,"UpperTheory.zeta_ne_zero_of_everyCharacter_variant","Zeta23.Test")
        with self.assertRaisesRegex(RuntimeError,"forbidden declaration"):
            validate_root(row,root,set(),"native")

    def test_replay_rejects_empty_root_inventory(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            (p/"a").write_text("{}")
            with self.assertRaisesRegex(RuntimeError,"incomplete root inventory"):
                compare(p/"a",p/"a",p/"out")

    def test_replay_receipt_mismatch(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            a={"schema":"OPICA_TERMINAL_EVIDENCE_V2","mode":"common",
               "native_head":"a","native_tree":"t","original_head":"o","original_tree":"ot",
               "toolchain":"v","lean_version":"v","packages":{},"roots":{r:{} for r in COMMON_ROOTS},"module_source_hashes":{"M":"test"},
               "status":"CANDIDATE_AUDIT_ONLY","proof_acceptance":False}
            b={**a,"native_tree":"wrong"}
            (p/"a").write_text(json.dumps(a))
            (p/"b").write_text(json.dumps(b))
            with self.assertRaisesRegex(RuntimeError,"independent replay mismatch: native_tree"):
                compare(p/"a",p/"b",p/"result")
            self.assertFalse((p/"result").exists())

if __name__=="__main__":
    unittest.main()
