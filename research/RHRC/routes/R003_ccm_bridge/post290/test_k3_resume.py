#!/usr/bin/env python3
"""Exact ancestry, partition and fail-closed controls for the D2 continuation."""
import copy
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from k3_resume_partition import coalesce, split, pair, intake, LAYERS
from certificate_integrity import validate_layer


class PartitionControls(unittest.TestCase):
    def test_coalesce_only_adjacent_preserves_original_ids(self):
        raw=[{"left":[3,4],"right":[1,1]},{"left":[0,1],"right":[1,4]},{"left":[1,4],"right":[1,2]}]
        got=coalesce(raw)
        self.assertEqual([(c["left"],c["right"],c["parents"]) for c in got],[(Fraction(0),Fraction(1,2),[1,2]),(Fraction(3,4),Fraction(1),[0])])

    def test_exact_eighths_and_fourths(self):
        lo,hi=Fraction(379,1000),Fraction(498,1000)
        pieces=split(lo,hi,8)
        self.assertEqual(pieces[0][0],lo);self.assertEqual(pieces[-1][1],hi)
        self.assertTrue(all(b==c for (_,b),(c,_) in zip(pieces,pieces[1:])))
        self.assertTrue(all(b-a==(hi-lo)/8 for a,b in pieces))
        children=split(*pieces[3],4)
        self.assertEqual(sum(b-a for a,b in children),pieces[3][1]-pieces[3][0])

    def test_overlap_and_unordered_rejected(self):
        for raw in ([{"left":[0,1],"right":[2,1]},{"left":[1,1],"right":[3,1]}],[{"left":[2,1],"right":[1,1]}]):
            with self.assertRaises(ValueError):coalesce(raw)

    def test_continuous_cover_cannot_be_point_samples(self):
        s={"cell":9,"parity":"even","file":"k3_Q09_even.json","status":"PASS","intervals":1,"unresolved_count":0}
        r={"Q":9,"parity":"even","status":"PASS","left":[0,1],"right":[1,1],"accepted":[{"left":[1,2],"right":[1,2],"accepted":True,"method":"SECOND"}],"unresolved":[]}
        with self.assertRaises(AssertionError):validate_layer(s,r,"SECOND")

    def test_missing_interval_not_accepted(self):
        s={"cell":9,"parity":"even","file":"k3_Q09_even.json","status":"PASS","intervals":1,"unresolved_count":0}
        r={"Q":9,"parity":"even","status":"PASS","left":[0,1],"right":[1,1],"accepted":[{"left":[0,1],"right":[1,2],"accepted":True,"method":"SECOND"}],"unresolved":[]}
        with self.assertRaises(AssertionError):validate_layer(s,r,"SECOND")

    def test_historical_source_and_layer_mutations(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            p=Path(td)
            base={"source_commit":"forged-current-source","method":"SECOND","terminal_claim":"RH_OPEN","records":[]}
            (p/"manifest.json").write_text(json.dumps(base))
            with self.assertRaises(ValueError):intake(p)
            base["source_commit"]="31512dbb698dd59b90cfa32549f0e9273a5163f9"
            (p/"manifest.json").write_text(json.dumps(base))
            with self.assertRaises(ValueError):intake(p)


if __name__=="__main__":
    unittest.main()
