from __future__ import annotations
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('opica_delta',HERE/'dependency_delta.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class StructuralDelta(unittest.TestCase):
    def setUp(self):
        self.roots = [{'full_name':'Zeta23.OPICA.new','module':'Zeta23.OPICA.Composition','paper_id':'C2'}]
        self.old = [{'declaration':'old','dependencies':[{'constant':'shared','used_in_type':True,
            'used_in_value':False,'used_in_structure':False}]}]
        self.receipt = {'schema':'OPICA_COMPILER_RECEIPT_V1','status':'COMPILER_VERIFIED',
            'checked_commit':'a'*40,'checked_tree':'b'*40,
            'declarations':[{'name':'Zeta23.OPICA.new','module':'Zeta23.OPICA.Composition','kind':'THEOREM'}],
            'dependency_declarations':[
                {'name':'Zeta23.OPICA.new','module':'Zeta23.OPICA.Composition','kind':'THEOREM','internal':False},
                {'name':'shared','module':'Mathlib.Shared','kind':'DEFINITION','internal':False}],
            'dependencies':[{'source':'Zeta23.OPICA.new','channel':c,'targets':['shared'] if c=='VALUE' else []}
                for c in ('TYPE','VALUE','STRUCTURE')]}

    def test_sharing_is_not_equivalence(self):
        result = module.delta(self.old,self.receipt,self.roots)
        self.assertEqual(result['shared_dependency_count'],1)
        self.assertEqual(result['added_compiler_uses'][0]['channel'],'VALUE')
        self.assertFalse(result['logical_equivalence_inferred'])
        self.assertFalse(result['semantic_clause_coverage_inferred'])
        self.assertEqual(result['baseline_sources_not_revisited'],['old'])

    def test_missing_provenance_channel(self):
        self.receipt['dependencies'].pop()
        with self.assertRaisesRegex(ValueError,'provenance'): module.delta(self.old,self.receipt,self.roots)

    def test_old_dependency_drift(self):
        self.receipt['dependency_declarations'].append({'name':'old','module':'Zeta23.Old',
            'kind':'THEOREM','internal':False})
        self.receipt['dependencies'][1]['targets'] = ['old']
        self.receipt['dependencies'] += [{'source':'old','channel':c,'targets':['shared'] if c=='VALUE' else []}
            for c in ('TYPE','VALUE','STRUCTURE')]
        with self.assertRaisesRegex(ValueError,'drift'): module.delta(self.old,self.receipt,self.roots)

    def test_missing_primary_root(self):
        self.receipt['declarations'] = []
        with self.assertRaisesRegex(ValueError,'primary root'): module.delta(self.old,self.receipt,self.roots)

    def test_duplicate_channel(self):
        self.receipt['dependencies'].append(copy.deepcopy(self.receipt['dependencies'][0]))
        with self.assertRaisesRegex(ValueError,'duplicate'): module.delta(self.old,self.receipt,self.roots)

    def test_unverified_receipt(self):
        self.receipt['status'] = 'PLANNED'
        with self.assertRaisesRegex(ValueError,'compiler receipt'): module.delta(self.old,self.receipt,self.roots)

    def test_reachable_helper_cannot_omit_all_provenance_channels(self):
        self.receipt['dependency_declarations'][1]['module'] = 'Zeta23.Helper'
        with self.assertRaisesRegex(ValueError,'incomplete project dependency channels'):
            module.delta(self.old,self.receipt,self.roots)

    def test_missing_public_dependency_expansion_rejected(self):
        self.receipt['dependencies'] = []
        with self.assertRaisesRegex(ValueError,'incomplete project dependency channels'):
            module.delta(self.old,self.receipt,self.roots)

    def test_stale_receipt_head_or_tree_rejected_at_cli_boundary(self):
        manifest = {'base_commit':'c'*40,'mathlib_commit':'d'*40,'create':[],'modify':[]}
        self.receipt.update(requested_base=manifest['base_commit'],mathlib_commit=manifest['mathlib_commit'],sources={})
        for head,tree in [('e'*40,'b'*40),('a'*40,'e'*40)]:
            with self.subTest(head=head,tree=tree), patch.object(module.subprocess,'check_output',side_effect=[head,tree]):
                with self.assertRaisesRegex(ValueError,'stale formal receipt'):
                    module.validate_source_identity(HERE,self.receipt,manifest)


class DeltaReceiptBoundaryMutations(unittest.TestCase):
    def setUp(self):
        structural = StructuralDelta()
        structural.setUp()
        self.receipt,self.roots = structural.receipt,structural.roots
        self.roots[0]['kind'] = 'THEOREM'
        self.manifest = json.loads((HERE/'BUILD_MANIFEST.json').read_text(encoding='utf-8'))
        expression = {'format':'LEAN_EXPR_DAG_V1','root':'0','nodes':[['const',['str',['anonymous'],'True'],[]]]}
        encoded = json.dumps(expression,ensure_ascii=False,separators=(',',':'))
        self.receipt['declarations'][0].update(type_expression=expression,
            type_sha256=hashlib.sha256(encoded.encode()).hexdigest(),
            type_metrics={'format':'LEAN_EXPR_DAG_V1','unique_nodes':1,'closed':True},axioms=[],full_type='True')
        self.reviewed = {self.roots[0]['full_name']:self.receipt['declarations'][0]['type_sha256']}
        targets = self.manifest['no_root_api_pollution']['required_build_targets']
        commands = [{'argv':argv,'log':log,'log_sha256':'f'*64,'exit_code':0} for argv,log in [
            (['lake','env','lean','--version'],'lean-version.log'),
            (['lake','build',*targets],'build.log'),
            (['lake','env','lean','Zeta23/RHRC/OpicaBindings.lean'],'bindings.log')]]
        self.receipt.update(constructors={},requested_head=self.receipt['checked_commit'],checkout_kind='PR_HEAD',
            requested_base=self.manifest['base_commit'],mathlib_commit=self.manifest['mathlib_commit'],
            lean='Lean (version 4.33.0-rc2, fixture)',commands=commands)

    def validate(self):
        with patch.object(module,'validate_source_identity') as identity:
            module.validate_receipt_for_delta(HERE,self.receipt,self.manifest,self.roots,self.reviewed)
            identity.assert_called_once_with(HERE,self.receipt,self.manifest)

    def test_complete_compiler_evidence_is_checked_at_delta_cli_boundary(self):
        self.validate()

    def test_delta_boundary_rejects_removed_or_mutated_dag_under_old_digest(self):
        self.receipt['declarations'][0]['type_expression']['nodes'][0][1][-1] = 'False'
        with self.assertRaisesRegex(ValueError,'DAG digest mismatch'): self.validate()
        del self.receipt['declarations'][0]['type_expression']
        with self.assertRaisesRegex(ValueError,'missing public declaration evidence'): self.validate()

    def test_delta_boundary_rejects_missing_constructor_inventory(self):
        del self.receipt['constructors']
        with self.assertRaisesRegex(ValueError,'constructor inventory'): self.validate()

    def test_delta_boundary_rejects_extra_axiom_or_fake_export_command(self):
        self.receipt['declarations'][0]['axioms'] = ['sorryAx']
        with self.assertRaisesRegex(ValueError,'unadmitted mathematical axiom'): self.validate()
        self.receipt['declarations'][0]['axioms'] = []
        self.receipt['commands'][-1]['argv'] = ['echo','stale cached export']
        with self.assertRaisesRegex(ValueError,'command identity'): self.validate()

    def test_delta_source_boundary_checks_actual_parent_identity(self):
        self.receipt.update(requested_head='f'*40,checkout_kind='SYNTHETIC_MERGE')
        git = ['a'*40,'b'*40,'a'*40+' '+'c'*40+' '+'d'*40]
        with patch.object(module.subprocess,'check_output',side_effect=git):
            with self.assertRaisesRegex(ValueError,'foreign compiler requested head'):
                module.validate_source_identity(HERE,self.receipt,self.manifest)

    def test_delta_repaired_hash_does_not_approve_a_new_hidden_premise(self):
        record = self.receipt['declarations'][0]
        record['type_expression'] = {'format':'LEAN_EXPR_DAG_V1','root':'1','nodes':[
            ['const',['str',['anonymous'],'True'],[]],
            ['forall',['str',['anonymous'],'hidden'],'instImplicit','0','0']]}
        encoded = json.dumps(record['type_expression'],ensure_ascii=False,separators=(',',':'))
        record['type_sha256'] = hashlib.sha256(encoded.encode()).hexdigest()
        record['type_metrics'] = {'format':'LEAN_EXPR_DAG_V1','unique_nodes':2,'closed':True}
        with self.assertRaisesRegex(ValueError,'reviewed expected type changed'): self.validate()

    def test_delta_requires_exact_reviewed_root_digest_inventory(self):
        self.reviewed['Zeta23.OPICA.unrequested'] = 'a'*64
        with self.assertRaisesRegex(ValueError,'reviewed root type inventory'): self.validate()


if __name__ == '__main__':
    unittest.main()
