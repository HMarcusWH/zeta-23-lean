#!/usr/bin/env python3
"""Compiler log mutations; synthetic logs supply no Lean theorem authority."""
import unittest
from build_formal_receipt import compiler_records


class CompilerLogMutations(unittest.TestCase):
    head='a'*40;tree='b'*40;roots={'Mock.theorem':'Mock.Module'}
    def fixture(self):
        return '\n'.join(['POST290_COMPILER_CONTEXT\t'+self.head+'\t'+self.tree,
            'RHRC_CANDIDATE_RESULT\tMock.theorem\tRESOLVED_UNIQUE\t1\tMock.theorem\tMock.Module\tTHEOREM\t0\tVALIDATOR_CONTROL_TYPE\tcontrol',
            'POST290_AXIOMS\tMock.theorem\tpropext,Classical.choice,Quot.sound'])
    def test_unique_current_complete_control(self):
        types,axioms=compiler_records(self.fixture(),self.roots,self.head,self.tree)
        self.assertEqual(list(types),['Mock.theorem']);self.assertEqual(len(axioms['Mock.theorem']),3)
    def test_stale_head_or_tree_rejected(self):
        for old,new in ((self.head,'c'*40),(self.tree,'d'*40)):
            with self.assertRaisesRegex(ValueError,'compiler head/tree context'):
                compiler_records(self.fixture().replace(old,new),self.roots,self.head,self.tree)
    def test_missing_or_duplicate_context_rejected(self):
        log=self.fixture()
        for altered in ('\n'.join(log.splitlines()[1:]),log+'\n'+log.splitlines()[0]):
            with self.assertRaises(ValueError):compiler_records(altered,self.roots,self.head,self.tree)
    def test_late_compiler_failure_rejected(self):
        with self.assertRaisesRegex(ValueError,'failed check'):
            compiler_records(self.fixture()+'\nZeta23/RHRC/Step123OutputBindings.lean:99:0: error: broken proof',self.roots,self.head,self.tree)
    def test_missing_or_duplicate_axiom_rejected(self):
        log=self.fixture()
        for altered in ('\n'.join(log.splitlines()[:-1]),log+'\n'+log.splitlines()[-1]):
            with self.assertRaises(ValueError):compiler_records(altered,self.roots,self.head,self.tree)
    def test_wrong_binding_or_axiom_rejected(self):
        log=self.fixture()
        for altered in (log.replace('Mock.Module','Other.Module'),log.replace('Quot.sound','sorryAx'),log.replace('THEOREM\t0','THEOREM\t1')):
            with self.assertRaises(ValueError):compiler_records(altered,self.roots,self.head,self.tree)
    def test_empty_scope_rejected(self):
        with self.assertRaisesRegex(ValueError,'empty compiler root scope'):
            compiler_records(self.fixture().splitlines()[0],{},self.head,self.tree)


if __name__=='__main__':unittest.main()
