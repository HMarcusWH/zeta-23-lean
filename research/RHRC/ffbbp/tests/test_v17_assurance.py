import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from ffbbp.v17_contracts import GateStatus, QualificationIdentity, TypedGateResult, required_gate_satisfied
from ffbbp.v17_gates import reduction_assurance_gate


class FFBBPV17AssuranceTests(unittest.TestCase):
    def gate(self, key, status):
        return TypedGateResult(
            key=key,
            status=status,
            owner="REFERENCE",
            identity="execution",
            scope="STATIC_REPOSITORY_SNAPSHOT",
            evidence_kind="EXACT_REPOSITORY_RECEIPT",
            evidence_ref="receipt",
        )

    def test_only_pass_satisfies_required_gate(self):
        self.assertTrue(required_gate_satisfied(self.gate("a", GateStatus.PASS)))
        self.assertFalse(required_gate_satisfied(self.gate("a", GateStatus.FAIL)))
        self.assertFalse(required_gate_satisfied(self.gate("a", GateStatus.NOT_EVALUATED)))
        self.assertFalse(required_gate_satisfied(self.gate("a", GateStatus.NOT_APPLICABLE)))

    def test_not_applicable_cannot_waive_required_gate(self):
        out = reduction_assurance_gate(required_results=(self.gate("a", GateStatus.NOT_APPLICABLE),))
        self.assertFalse(out.passed)
        self.assertIn("a:REQUIRED_GATE_CANNOT_BE_NOT_APPLICABLE", out.blockers)

    def test_structural_nonapplicability_is_separate(self):
        out = reduction_assurance_gate(
            required_results=(self.gate("a", GateStatus.PASS),),
            structurally_inapplicable=("stateful_transition_closure",),
        )
        self.assertTrue(out.passed)

    def test_qualification_identity_requires_three_hash_bound_levels(self):
        q = QualificationIdentity(
            "profile", "0" * 64, "protocol", "1" * 64, "execution", "2" * 64
        )
        q.validate()
        with self.assertRaises(ValueError):
            QualificationIdentity("profile", "bad", "protocol", "1" * 64, "execution", "2" * 64).validate()


if __name__ == "__main__":
    unittest.main()
