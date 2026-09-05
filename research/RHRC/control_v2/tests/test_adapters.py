import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from control_v2.adapters.ffbbp import load_ffbbp_snapshot
from control_v2.adapters.ool import load_ool_snapshot


class AdapterTests(unittest.TestCase):
    def test_ffbbp_snapshot_preserves_qualification_boundary(self):
        snap = load_ffbbp_snapshot(RHRC)
        self.assertIn("RUN42C", snap.qualified_reference_version)
        self.assertEqual(snap.qualified_profile, "RUN42C_A0_INDUCTIVE_FIREWALL")
        self.assertEqual(snap.v16_theory_version, "1.6.0")
        self.assertFalse(snap.v16_inherits_qualification)

    def test_ool_snapshot_reads_existing_route_registry(self):
        snap = load_ool_snapshot(RHRC)
        self.assertTrue(snap.kernel_version)
        self.assertGreater(snap.registered_route_count, 0)


if __name__ == "__main__":
    unittest.main()
