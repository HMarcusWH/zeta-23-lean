#!/usr/bin/env python3
"""Synthetic mutations of the D2 seven-file checker provenance. No new D2 run."""
import unittest
from d2_source_equivalence import FROZEN_CONTINUATION_FILES, verify_continuation_digest_map

class FrozenCheckerProvenance(unittest.TestCase):
    def fixture(self):
        checks={name:str(i).zfill(64) for i,name in enumerate(FROZEN_CONTINUATION_FILES)}
        return {"continuation_source_digests":checks.copy()}, checks

    def test_all_seven_exact(self):
        identity, digests=self.fixture()
        self.assertEqual(len(digests),7)
        verify_continuation_digest_map(identity,digests)

    def test_missing_checker_source_rejected(self):
        identity,digests=self.fixture()
        identity["continuation_source_digests"].pop("k3_replay_shards.py")
        with self.assertRaisesRegex(ValueError,"seven-file"):
            verify_continuation_digest_map(identity,digests)

    def test_claimed_and_actual_hash_maps_are_independent(self):
        identity,digests=self.fixture()
        self.assertIsNot(identity['continuation_source_digests'],digests)
        identity['continuation_source_digests']['k3_replay_all.py']='f'*64
        self.assertNotEqual(identity['continuation_source_digests'],digests)
        self.assertNotEqual(identity['continuation_source_digests']['k3_replay_all.py'],
                            digests['k3_replay_all.py'])

    def test_changed_checker_digest_rejected(self):
        identity,digests=self.fixture()
        identity["continuation_source_digests"]["k3_replay_all.py"]="f"*64
        with self.assertRaisesRegex(ValueError,"seven-file"):
            verify_continuation_digest_map(identity,digests)

    def test_added_unfrozen_source_rejected(self):
        identity,digests=self.fixture()
        identity["continuation_source_digests"]["invented_checker.py"]="a"*64
        with self.assertRaisesRegex(ValueError,"seven-file"):
            verify_continuation_digest_map(identity,digests)

    def test_absent_digest_map_rejected(self):
        with self.assertRaisesRegex(ValueError,"seven-file"):
            verify_continuation_digest_map({},self.fixture()[1])

if __name__=="__main__":
    unittest.main()
