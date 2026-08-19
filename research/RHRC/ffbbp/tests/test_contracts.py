import math
import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from ffbbp.contracts import (
    EvidencePartition, FidelityMode, InformationPartition, KnockoffRecord,
    QualificationKey, RefitSemantics, RunPhase, certificate_shrink,
    existence_weight, lift_validation, masked_renormalized_distance_sq,
)


class FFBBPImplementationClosureTests(unittest.TestCase):
    def test_partition_build_is_train_union_select(self):
        p = InformationPartition(frozenset({'a'}), frozenset({'b'}), frozenset({'c'}), frozenset({'d'}))
        p.validate()
        self.assertEqual(p.build_ids, frozenset({'a','b'}))
        self.assertFalse(p.construction_allowed('c'))
        self.assertFalse(p.confirm_feedback_allowed())

    def test_partition_overlap_rejected(self):
        p = InformationPartition(frozenset({'a'}), frozenset({'a'}), frozenset(), frozenset())
        with self.assertRaises(ValueError):
            p.validate()

    def test_run_phase_and_fidelity_are_orthogonal(self):
        self.assertNotEqual(RunPhase.CONFIRM.value, FidelityMode.REFERENCE.value)

    def test_run42b_lift_and_weight(self):
        lift = lift_validation(0.4, 1.0)
        self.assertAlmostEqual(lift, 0.6)
        self.assertAlmostEqual(existence_weight(lift, tau=0.12, slope=24), 0.9999900703, places=8)

    def test_certificate_shrink(self):
        self.assertAlmostEqual(certificate_shrink(10.0, weight=0.0, minimum_shrink=0.02), 0.2)
        self.assertAlmostEqual(certificate_shrink(10.0, weight=1.0, minimum_shrink=0.02), 10.0)

    def test_masked_distance_renormalizes_and_gates_overlap(self):
        d = masked_renormalized_distance_sq([0.0, 1.0, None, 2.0], [0.0, 2.0, None, 2.0], [1,1,1,1], [1,1,1,1], softclip=4.0, min_overlap_fraction=0.5)
        self.assertGreater(d, 0.0)
        with self.assertRaises(ValueError):
            masked_renormalized_distance_sq([None,None,1.0], [None,None,1.1], [1,1,1], [1,1,1], softclip=4.0, min_overlap_fraction=0.67)

    def test_reference_refit_semantics(self):
        RefitSemantics().validate()
        with self.assertRaises(ValueError):
            RefitSemantics(ordinary_train_parameters_refit=False).validate()

    def test_knockoff_cannot_be_generated_from_confirm(self):
        k = KnockoffRecord(('time_slice_marginals',), ('source_correspondence',), EvidencePartition.CONFIRM, RefitSemantics(), 83)
        with self.assertRaises(ValueError):
            k.validate()

    def test_qualification_pair_is_explicit(self):
        self.assertEqual(str(QualificationKey('RUN42B_A0_CORE','RH_R001_ADAPTER_V2')), 'RUN42B_A0_CORE::RH_R001_ADAPTER_V2')

if __name__ == '__main__':
    unittest.main()
