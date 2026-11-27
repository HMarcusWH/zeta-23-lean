import unittest
from review import check_delta, axiom_reports

class ReviewTest(unittest.TestCase):
    def test_delta(self):
        check_delta({"a":"A","b":"M"},{"a"},{"b"})
    def test_delta_escape(self):
        for d in ({"a":"A","b":"M","c":"M"},{"a":"A"},{"a":"D","b":"M"}):
            with self.assertRaises(RuntimeError):
                check_delta(d,{"a"},{"b"})
    def test_axioms(self):
        self.assertEqual(axiom_reports("'x' depends on axioms: [propext, Quot.sound]\n'y' does not depend on any axioms\n",["x","y"]),{"x":["Quot.sound","propext"],"y":[]})
    def test_axiom_reject(self):
        for s in ("'x' depends on axioms: [sorryAx]\n","'x' depends on axioms: [projectAxiom]\n","'x' does not depend on any axioms\n'x' does not depend on any axioms\n",""):
            with self.assertRaises(RuntimeError):
                axiom_reports(s,["x"])

if __name__=="__main__":
    unittest.main()
