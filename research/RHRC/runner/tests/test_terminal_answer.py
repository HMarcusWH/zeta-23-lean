import json, tempfile, unittest
from pathlib import Path
import sys
RHRC=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(RHRC))
from runner.terminal_answer import derive_answer

class TerminalAnswerTests(unittest.TestCase):
    def registry(self, root, status='OPEN', deps=None):
        p=root/'claims.json'; p.write_text(json.dumps({'claims':[{'id':'C_RH','statement':'RH','status':status,'dependencies':deps or []},{'id':'A','status':'OPEN','dependencies':[]}]})); return p
    def test_open_even_with_valid_diagnostic(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d); reg=self.registry(r,'OPEN',['A']); rec=r/'r.json'; rec.write_text(json.dumps({'bounded_claim':{'result':'PASS','certificate_status':'VALID'}}))
            a=derive_answer(reg,[rec]); self.assertEqual(a.answer_code,'RH_OPEN'); self.assertEqual(a.research_signal,'FINITE_DIAGNOSTIC_PASS')
    def test_only_unconditional_closed_chain_prints_true(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d); p=r/'claims.json'; p.write_text(json.dumps({'claims':[{'id':'C_RH','statement':'RH','status':'PROVED_UNCONDITIONAL','dependencies':['A']},{'id':'A','status':'PROVED_UNCONDITIONAL','dependencies':[]}]}))
            a=derive_answer(p,[]); self.assertEqual(a.answer_code,'RH_PROVED_TRUE'); self.assertEqual(a.answer,'TRUE')
    def test_invalid_receipt_blocks(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d); reg=self.registry(r); rec=r/'r.json'; rec.write_text(json.dumps({'bounded_claim':{'result':'PASS','certificate_status':'INVALID'}}))
            self.assertEqual(derive_answer(reg,[rec]).answer_code,'INVALID_EVIDENCE')

if __name__=='__main__': unittest.main()
