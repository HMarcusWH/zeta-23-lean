import json
import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from ool.semantics import (
    CertificateStatus,
    ClaimResult,
    DomainCompleteness,
    EvidenceReceipt,
    EvidenceValue,
    LeafEvaluationReceipt,
    RouteBinding,
    absence_result,
    confirmatory_binding_status,
    exists_result,
    forall_result,
    issue_certificate,
    k_and,
    k_not,
    k_or,
    unconditional_provenance_result,
    validate_leaf_receipt,
)


class OoL276RuntimeTests(unittest.TestCase):
    def test_reference_is_exact_v2_7_6_release(self):
        ref = json.loads((RHRC / "ool" / "OOL_REFERENCE.json").read_text())
        self.assertEqual(ref["version"], "2.7.6")
        self.assertEqual(ref["source_archive"]["sha256"], "35eef74477b97cfa0f0c5367b51747022ba78c4df16e54869c41614d99e184f2")
        self.assertEqual(ref["canonical_authority"]["claim_registry_semantic_hash"], "22dfbf6413b8317ab3ef7400b3e966da4d52d2b60868932b0b5adba509aafe9f")
        self.assertEqual(ref["local_reverification_2026_08_19"]["total"], 530)
        self.assertEqual(ref["local_reverification_2026_08_19"]["failures"], 0)

    def test_strong_kleene_core(self):
        self.assertEqual(k_not(EvidenceValue.NA), EvidenceValue.NA)
        self.assertEqual(k_and([EvidenceValue.PASS, EvidenceValue.NA]), EvidenceValue.NA)
        self.assertEqual(k_and([EvidenceValue.FAIL, EvidenceValue.NA]), EvidenceValue.FAIL)
        self.assertEqual(k_or([EvidenceValue.FAIL, EvidenceValue.NA]), EvidenceValue.NA)
        self.assertEqual(k_or([EvidenceValue.PASS, EvidenceValue.NA]), EvidenceValue.PASS)

    def test_open_world_quantifiers(self):
        self.assertEqual(exists_result([EvidenceValue.FAIL], DomainCompleteness.PARTIAL), EvidenceValue.NA)
        self.assertEqual(exists_result([EvidenceValue.FAIL], DomainCompleteness.COMPLETE), EvidenceValue.FAIL)
        self.assertEqual(forall_result([EvidenceValue.PASS], DomainCompleteness.UNKNOWN), EvidenceValue.NA)
        self.assertEqual(forall_result([EvidenceValue.PASS], DomainCompleteness.COMPLETE), EvidenceValue.PASS)

    def test_missing_raw_evidence_is_na(self):
        leaf = LeafEvaluationReceipt("P", ("E1",), EvidenceValue.PASS)
        self.assertEqual(validate_leaf_receipt(leaf, {}), EvidenceValue.NA)
        raw = {"E1": EvidenceReceipt("E1", "abc")}
        self.assertEqual(validate_leaf_receipt(leaf, raw), EvidenceValue.PASS)

    def test_valid_fail_certificate_is_allowed(self):
        result = ClaimResult("C", EvidenceValue.FAIL, ("support",), "registry")
        cert = issue_certificate(result, physical_witness_ref="w", raw_support_complete=True, binding_valid=True)
        self.assertEqual(cert.claim_result, EvidenceValue.FAIL)
        self.assertEqual(cert.certificate_status, CertificateStatus.VALID)

    def test_na_certificate_is_incomplete(self):
        result = ClaimResult("C", EvidenceValue.NA, (), "registry")
        cert = issue_certificate(result, physical_witness_ref="w", raw_support_complete=False, binding_valid=True)
        self.assertEqual(cert.certificate_status, CertificateStatus.INCOMPLETE)

    def test_binding_mismatch_is_invalid(self):
        result = ClaimResult("C", EvidenceValue.PASS, ("support",), "registry")
        cert = issue_certificate(result, physical_witness_ref="w", raw_support_complete=True, binding_valid=False)
        self.assertEqual(cert.certificate_status, CertificateStatus.INVALID)

    def test_confirmatory_route_change_requires_new_digest(self):
        expected = RouteBinding("R001", "B0", "bhash", "routehash", "CONFIRMATORY_FROZEN")
        changed = RouteBinding("R001", "B0", "bhash", "different", "CONFIRMATORY_FROZEN")
        self.assertEqual(confirmatory_binding_status(expected, changed), "NEW_ROUTE_REQUIRED")
        self.assertEqual(confirmatory_binding_status(expected, expected), "BOUND")

    def test_discovery_is_not_fake_confirmatory(self):
        discovery = RouteBinding("R001", "B0", "bhash", "routehash", "DISCOVERY")
        self.assertEqual(confirmatory_binding_status(discovery, discovery), "ROUTE_NOT_FROZEN")

    def test_unconditional_provenance_is_positive_closure(self):
        nodes = ["A", "B"]
        admitted = {"A": "ADMITTED_UNCONDITIONAL_ROOT", "B": "DESCENDANT_OF_ADMITTED_UNCONDITIONAL_ROOT"}
        self.assertEqual(unconditional_provenance_result(nodes, admitted, complete=True), EvidenceValue.PASS)
        unknown = {"A": "ADMITTED_UNCONDITIONAL_ROOT"}
        self.assertEqual(unconditional_provenance_result(nodes, unknown, complete=True), EvidenceValue.NA)
        conditional = {"A": "ADMITTED_UNCONDITIONAL_ROOT", "B": "CONJECTURAL"}
        self.assertEqual(unconditional_provenance_result(nodes, conditional, complete=True), EvidenceValue.FAIL)

    def test_absence_requires_complete_domain(self):
        self.assertEqual(absence_result(forbidden_observed=False, search_domain_complete=False), EvidenceValue.NA)
        self.assertEqual(absence_result(forbidden_observed=False, search_domain_complete=True), EvidenceValue.PASS)
        self.assertEqual(absence_result(forbidden_observed=True, search_domain_complete=False), EvidenceValue.FAIL)

    def test_route_registry_stays_discovery_until_real_freeze(self):
        reg = json.loads((RHRC / "routes" / "ROUTE_REGISTRY.json").read_text())
        self.assertEqual(reg["ool_kernel_version"], "2.7.6")
        for route in reg["routes"]:
            self.assertEqual(route["phase"], "DISCOVERY")
            self.assertIsNone(route["route_spec_digest"])
            self.assertFalse(route["confirmatory_execution_authorized"])

    def test_boundary_declares_ool_2_7_6_semantics(self):
        b = json.loads((RHRC / "BOUNDARY.json").read_text())
        self.assertEqual(b["route_closure_engine"]["kernel_version"], "2.7.6")
        self.assertEqual(b["route_closure_engine"]["missing_or_unresolved_evidence"], "NA")
        self.assertTrue(b["route_closure_engine"]["claim_result_separate_from_certificate_integrity"])


if __name__ == "__main__":
    unittest.main()
