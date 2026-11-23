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
        for bad in ({**good,"extra":b},{**good,"native":b},{k:v for k,v in good.items() if k!="native"},{**good,"candidate":a}):
            with self.assertRaises(Reject): verify_delta(base,bad,{"candidate":b},a["sha"],b["sha"])

    def test_named_axioms_fail_closed(self):
        self.assertEqual(axiom_reports("'x' depends on axioms: [propext]\n'y' does not depend on any axioms",["x","y"]),{"x":["propext"],"y":[]})
        for bad in ("'x' depends on axioms: [sorryAx]","'x' depends on axioms: [unknown]","'x' depends on axioms: [propext]\n'x' depends on axioms: [propext]",""):
            with self.assertRaises(Reject): axiom_reports(bad,["x"])

if __name__=="__main__": unittest.main()
