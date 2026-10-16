#!/usr/bin/env python3
"""Compiler log mutations; synthetic logs supply no Lean theorem authority."""
import unittest
from build_formal_receipt import compiler_records,audit_roots


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
    def test_constructor_requires_explicit_definition_kind(self):
        log=self.fixture().replace('THEOREM\t0','DEFINITION\t0')
        with self.assertRaisesRegex(ValueError,'identity/kind mismatch'):
            compiler_records(log,self.roots,self.head,self.tree)
        compiler_records(log,self.roots,self.head,self.tree,{'Mock.theorem':'DEFINITION'})
        with self.assertRaisesRegex(ValueError,'identity/kind mismatch'):
            compiler_records(self.fixture(),self.roots,self.head,self.tree,{'Mock.theorem':'DEFINITION'})
    def test_multiline_source_inventory_keeps_exact_kinds(self):
        source='''(``Mock.theorem, "Mock.Module", "THEOREM"),
        (``Mock.constructor,
          "Mock.Module", "DEF")'''
        roots,kinds=audit_roots(source)
        self.assertEqual(roots,{'Mock.theorem':'Mock.Module','Mock.constructor':'Mock.Module'})
        self.assertEqual(kinds,{'Mock.theorem':'THEOREM','Mock.constructor':'DEFINITION'})
    def test_real_binding_inventory_accepts_all_exact_kinds(self):
        from build_formal_receipt import AUDIT
        roots,kinds=audit_roots(AUDIT.read_text(encoding='utf-8'))
        self.assertGreaterEqual(len(roots),1248)
        names=[n for n in roots if n.startswith('Zeta23.RHRC.mc')]
        self.assertEqual(len(names),16)
        self.assertEqual(sum(kinds[n]=='DEFINITION' for n in names),8)
        self.assertEqual(sum(kinds[n]=='THEOREM' for n in names),8)

    def test_m07_05_exact_origin_is_defining_geometry_module(self):
        from build_formal_receipt import AUDIT
        roots,kinds=audit_roots(AUDIT.read_text(encoding='utf-8'))
        name='Zeta23.CCM.poleNeutralIndexEquiv'
        self.assertEqual(roots[name],'Zeta23.CCM.CanonicalPoleNeutralGeometry')
        self.assertEqual(kinds[name],'DEFINITION')
        self.assertNotEqual(roots[name],'Zeta23.CCM.CanonicalPoleNeutralCarrier')

    def test_m07_05_wrong_importing_module_rejected_by_compiler_receipt(self):
        name='Zeta23.CCM.poleNeutralIndexEquiv'
        module='Zeta23.CCM.CanonicalPoleNeutralGeometry'
        testlog='\n'.join([
            'POST290_COMPILER_CONTEXT\t'+self.head+'\t'+self.tree,
            'RHRC_CANDIDATE_RESULT\t'+name+'\tRESOLVED_UNIQUE\t1\t'+
            name+'\t'+module+'\tDEFINITION\t0\tEXACT_INDEX_EQUIV_TYPE\t-',
            'POST290_AXIOMS\t'+name+'\tpropext,Classical.choice,Quot.sound'
        ])
        roots={name:module}; kinds={name:'DEFINITION'}
        types,axioms=compiler_records(testlog,roots,self.head,self.tree,kinds)
        self.assertEqual(types[name],'EXACT_INDEX_EQUIV_TYPE')
        self.assertEqual(len(axioms[name]),3)
        importing='Zeta23.CCM.CanonicalPoleNeutralCarrier'
        with self.assertRaisesRegex(ValueError,'identity/kind mismatch'):
            compiler_records(testlog.replace(module,importing),roots,
                             self.head,self.tree,kinds)

    def test_source_kind_canonical_spelling(self):
        roots,kinds=audit_roots('''(``Mock.a, "Mock", "DEFINITION"),
            (``Mock.b, "Mock", "STRUCTURE")''')
        self.assertEqual(kinds,{'Mock.a':'DEFINITION','Mock.b':'INDUCTIVE'})

    def test_missing_duplicate_or_unknown_source_kind_rejected(self):
        for source in ['(``Mock.root, "Mock.Module")',
            '(``Mock.root, "Mock.Module", "UNREVIEWED")',
            '(``Mock.root, "Mock.Module", "DEF"), (``Mock.root, "Mock.Module", "DEF")']:
            with self.assertRaises(ValueError):audit_roots(source)


if __name__=='__main__':unittest.main()
