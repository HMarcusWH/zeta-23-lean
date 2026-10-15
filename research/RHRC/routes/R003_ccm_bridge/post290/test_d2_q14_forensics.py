#!/usr/bin/env python3
"""Falsifiers for rational D2 candidate partition bookkeeping, no search."""
import copy
import unittest
from d2_q14_forensics import inspect_row

def tile(a,b,reason=None):
    row={"left":[a,1],"right":[b,1]}
    if reason:
        row["reason"]=reason
    else:
        row.update({"accepted":True,"method":"SECOND"})
    return row

def fixture():
    return {"Q":14,"parity":"even","left":[0,1],"right":[5,1],
            "accepted":[tile(0,1),tile(3,4)],
            "unresolved":[tile(1,2,"HARD_WALL_TIMEOUT"),
                          tile(2,3,"HARD_WALL_TIMEOUT"),
                          tile(4,5,"MISSING_CONTINUATION_RECEIPT")]}

class D2RationalForensics(unittest.TestCase):
    def test_contiguous_islands_and_exact_width(self):
        report=inspect_row(fixture())
        self.assertEqual(report["unresolved_piece_count"],3)
        self.assertEqual(report["unresolved_island_count"],2)
        self.assertEqual(report["unresolved_fraction"],[3,5])
        self.assertTrue(report["not_a_mathematical_positivity_certificate"])
    def test_missing_hole_fails_closed(self):
        x=fixture();x["unresolved"].pop(1)
        with self.assertRaisesRegex(ValueError,"gap or overlap"):
            inspect_row(x)
    def test_overlap_fails_closed(self):
        x=fixture();x["unresolved"][0]["right"]=[4,1]
        with self.assertRaisesRegex(ValueError,"gap or overlap"):
            inspect_row(x)
    def test_false_positive_tile_rejected(self):
        x=fixture();x["accepted"][0]["accepted"]=False
        with self.assertRaisesRegex(ValueError,"SECOND"):
            inspect_row(x)
    def test_wrong_sector_rejected(self):
        x=fixture();x["parity"]="odd"
        with self.assertRaisesRegex(ValueError,"wrong numerical sector"):
            inspect_row(x)

if __name__=="__main__":
    unittest.main()
