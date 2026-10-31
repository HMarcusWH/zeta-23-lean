import unittest
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from schedule import Candidate,Decision,choose

class SchedulerTest(unittest.TestCase):
    def test_empty(self):self.assertEqual(choose((),frozenset(),0).tag,'STOP')
    def test_missing_dependency(self):self.assertEqual(choose((Candidate('b',('a',),2,1),),frozenset(),10).tag,'STOP')
    def test_budget(self):self.assertEqual(choose((Candidate('b',(),2,3),),frozenset(),2).tag,'STOP')
    def test_equal_priority(self):self.assertEqual(choose((Candidate('b',(),6,4),Candidate('a',(),3,2)),frozenset(),5).candidate_id,'a')
    def test_exact_priority(self):self.assertEqual(choose((Candidate('a',(),10,3),Candidate('b',(),9,2)),frozenset(),5).candidate_id,'b')
    def test_duplicate_rejected(self):
        c=Candidate('a',(),1,1)
        with self.assertRaises(ValueError):choose((c,c),frozenset(),1)
    def test_negative_budget(self):
        with self.assertRaises(ValueError):choose((),frozenset(),-1)
    def test_boolean_budget(self):
        with self.assertRaises(ValueError):choose((),frozenset(),True)
    def test_stop_must_not_select(self):
        with self.assertRaises(ValueError):Decision('STOP','x','bad')
    def test_negative_score(self):
        with self.assertRaises(ValueError):Candidate('x',(),-1,1)
    def test_self_dependency(self):
        with self.assertRaises(ValueError):Candidate('x',('x',),1,1)
    def test_all_completed(self):self.assertEqual(choose((Candidate('x',(),1,1),),frozenset({'x'}),1).tag,'STOP')
    def test_broken_completed_type(self):
        with self.assertRaises(TypeError):choose((),{'a'},1)
