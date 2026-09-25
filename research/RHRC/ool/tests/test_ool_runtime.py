import json
import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from ool.semantics import (
    CertificateStatus,
    ClaimResult,
    DomainCompleteness,
    DomainReceipt,
    EvidenceReceipt,
    EvidenceValue,
    LeafEvaluationReceipt,
    RouteBinding,
    RouteInterfaceQualification,
    VerifierPolicy,
    absence_result,
    absence_result_for_domain,
    confirmatory_binding_status,
    exists_result,
    forall_result,
    integrated_route_freeze_status,
    issue_certificate,
    k_and,
    k_not,
    k_or,
    stable_digest,
    unconditional_provenance_result,
    validate_leaf_receipt,
)
from ool.v277_authority import sign_reviewed_object


class OoL277RuntimeTests(unittest.TestCase):
    def test_reference_is_exact_v2_7_7_release(self):
        ref = json.loads((RHRC / "ool" / "OOL_REFERENCE.json").read_text())
        self.assertEqual(ref["version"], "2.7.7")
        self.assertEqual(ref["source_release"]["outer_zip_sha256"], "c47c7d568e9822524ccc05b8a2f346cd20ae3218799700b708d78fe5b35ded30")
        self.assertEqual(ref["canonical_authority"]["runtime_hash"], "64a15111f3bb655c274d993ae46bb250cf04fda55a05b08256d16d0f93c4f2ad")
        self.assertEqual(ref["canonical_authority"]["registry_hash"], "e043d62d11311d7e054735ee3f1b5bf5ce3854ded92dd10fe651ee5fb169872e")
        self.assertEqual(ref["packaged_validation"]["counted_total"], "1710/1710 PASS")
        self.assertEqual(ref["physical_claim_count"], 24)
        self.assertTrue(ref["all_v276_claim_expression_asts_unchanged"])

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

    def test_closed_typed_digest_has_no_default_str_fallback(self):
        self.assertNotEqual(stable_digest(1), stable_digest("1"))
        with self.assertRaises(ValueError):
            stable_digest(float("nan"))
        with self.assertRaises(TypeError):
            stable_digest({1: "not a string key"})

    def test_missing_raw_evidence_is_na(self):
        leaf = LeafEvaluationReceipt("P", ("E1",), EvidenceValue.PASS)
        self.assertEqual(validate_leaf_receipt(leaf, {}), EvidenceValue.NA)
        raw = {"E1": EvidenceReceipt("E1", origin="REPOSITORY")}
        self.assertEqual(validate_leaf_receipt(leaf, raw), EvidenceValue.PASS)

    def test_default_certificate_is_incomplete_without_policy(self):
        result = ClaimResult("C", EvidenceValue.PASS, ("support",), "registry", runtime_digest="runtime")
        cert = issue_certificate(result, physical_witness_ref="w", raw_support_complete=True, binding_valid=True)
        self.assertEqual(cert.certificate_status, CertificateStatus.INCOMPLETE)
        self.assertIn("trusted_verifier_policy_required", cert.reason_codes)

    def test_binding_mismatch_is_invalid(self):
        result = ClaimResult("C", EvidenceValue.PASS, ("support",), "registry", runtime_digest="runtime")
        cert = issue_certificate(result, physical_witness_ref="w", raw_support_complete=True, binding_valid=False)
        self.assertEqual(cert.certificate_status, CertificateStatus.INVALID)

    def test_attested_policy_can_validate_binding_but_not_truth(self):
        key = Ed25519PrivateKey.generate()
        pub = key.public_key().public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        )
        result = ClaimResult("C", EvidenceValue.FAIL, ("support",), "registry", runtime_digest="runtime")
        policy = VerifierPolicy("P", ("registry",), ("runtime",), (("reviewer", pub),))
        att = sign_reviewed_object(result, "CLAIM_RESULT", "reviewer", key, signed_at="2026-09-25T12:00:00+00:00")
        cert = issue_certificate(
            result, physical_witness_ref="w", raw_support_complete=True, binding_valid=True,
            policy=policy, attestations=(att,)
        )
        self.assertEqual(cert.certificate_status, CertificateStatus.VALID)
        self.assertEqual(cert.claim_result, EvidenceValue.FAIL)
        self.assertEqual(cert.assurance_scope, "ATTESTED_EVIDENCE_BINDING")
        self.assertEqual(cert.scientific_validation, "NOT_ESTABLISHED_BY_SOFTWARE")

    def test_attestation_for_different_object_does_not_validate_claim(self):
        key = Ed25519PrivateKey.generate()
        pub = key.public_key().public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        )
        result = ClaimResult("C", EvidenceValue.PASS, ("support",), "registry", runtime_digest="runtime")
        other = ClaimResult("OTHER", EvidenceValue.PASS, ("support",), "registry", runtime_digest="runtime")
        policy = VerifierPolicy("P", ("registry",), ("runtime",), (("reviewer", pub),))
        att = sign_reviewed_object(other, "CLAIM_RESULT", "reviewer", key, signed_at="2026-09-25T12:00:00+00:00")
        cert = issue_certificate(
            result, physical_witness_ref="w", raw_support_complete=True, binding_valid=True,
            policy=policy, attestations=(att,)
        )
        self.assertEqual(cert.certificate_status, CertificateStatus.INCOMPLETE)
        self.assertIn("reviewed_attestation_for_exact_claim_result_required", cert.reason_codes)

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

    def test_absence_completeness_is_route_scoped(self):
        domain = DomainReceipt(
            "LEAN_DECLARATIONS", ("a", "b"), DomainCompleteness.COMPLETE,
            enumeration_method="compiler_receipt", evidence_ref="receipt",
            scope_route_digest="route-a",
        )
        self.assertEqual(
            absence_result_for_domain(forbidden_observed=False, domain=domain, route_digest="route-a"),
            EvidenceValue.PASS,
        )
        self.assertEqual(
            absence_result_for_domain(forbidden_observed=False, domain=domain, route_digest="route-b"),
            EvidenceValue.NA,
        )

    def test_integrated_route_freeze_requires_actual_output_and_lineage(self):
        interfaces = [
            RouteInterfaceQualification("A->B", EvidenceValue.PASS, True, True),
            RouteInterfaceQualification("B->C", EvidenceValue.PASS, True, True),
        ]
        self.assertEqual(integrated_route_freeze_status(interfaces), "FULL_ROUTE_FREEZE_ELIGIBLE")
        self.assertEqual(
            integrated_route_freeze_status([RouteInterfaceQualification("A->B", EvidenceValue.PASS, False, True)]),
            "NOT_READY_FOR_FREEZE",
        )
        self.assertEqual(
            integrated_route_freeze_status([RouteInterfaceQualification("A->B", EvidenceValue.NA, True, True)]),
            "NOT_READY_FOR_FREEZE",
        )

    def test_route_registry_stays_discovery_until_real_freeze(self):
        reg = json.loads((RHRC / "routes" / "ROUTE_REGISTRY.json").read_text())
        self.assertEqual(reg["ool_kernel_version"], "2.7.7")
        for route in reg["routes"]:
            self.assertEqual(route["phase"], "DISCOVERY")
            self.assertIsNone(route["route_spec_digest"])
            self.assertFalse(route["confirmatory_execution_authorized"])

    def test_boundary_declares_ool_2_7_7_and_ffbbp_1_7_assurance(self):
        b = json.loads((RHRC / "BOUNDARY.json").read_text())
        self.assertEqual(b["route_closure_engine"]["kernel_version"], "2.7.7")
        self.assertEqual(b["assurance_architecture"]["version"], "1.7")
        self.assertFalse(b["assurance_architecture"]["inherits_runtime_qualification"])
        self.assertEqual(b["route_closure_engine"]["missing_or_unresolved_evidence"], "NA")
        self.assertTrue(b["route_closure_engine"]["default_certificate_incomplete_without_policy_attestation"])
        self.assertTrue(b["route_closure_engine"]["claim_bearing_lineage_must_be_continuous"])


if __name__ == "__main__":
    unittest.main()
