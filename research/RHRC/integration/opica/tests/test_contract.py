from __future__ import annotations
import copy
import hashlib
import json
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('opica_contract', HERE/'validate_contract.py')
contract = importlib.util.module_from_spec(spec)
spec.loader.exec_module(contract)


class ContractMutations(unittest.TestCase):
    def setUp(self):
        self.manifest = contract.read_json(HERE/'BUILD_MANIFEST.json')
        self.public = contract.read_json(HERE/'PUBLIC_ROOTS.json')
        self.crosswalk = contract.read_json(HERE/'PAPER_CROSSWALK.json')

    def errors(self):
        return contract.metadata_errors(self.manifest, self.public, self.crosswalk)

    def test_frozen_metadata_consistent(self):
        self.assertEqual(self.errors(), [])

    def test_duplicate_root_rejected(self):
        self.public['primary_roots'].append(copy.deepcopy(self.public['primary_roots'][0]))
        self.assertTrue(any('duplicate root' in e for e in self.errors()))

    def test_wrong_module_path_rejected(self):
        self.public['primary_roots'][0]['path'] = 'Zeta23/OPICA/Wrong.lean'
        self.assertTrue(any('module/path mismatch' in e for e in self.errors()))

    def test_missing_subclause_root_rejected(self):
        self.crosswalk['statements'][0]['required_roots'].pop()
        self.assertTrue(any('subclause root mismatch' in e for e in self.errors()))

    def test_missing_family_rejected(self):
        self.crosswalk['statements'].pop()
        self.assertTrue(any('paper family' in e for e in self.errors()))

    def test_every_new_lean_module_is_in_the_unique_inventory(self):
        self.manifest['modules'].pop()
        self.assertTrue(any('all 26 unique new Lean modules' in e for e in self.errors()))

    def test_module_inventory_cannot_duplicate_a_source(self):
        self.manifest['modules'][-1] = copy.deepcopy(self.manifest['modules'][0])
        self.assertTrue(any('all 26 unique new Lean modules' in e for e in self.errors()))

    def test_placeholder_and_trust_extensions_rejected(self):
        for token in ['sorry', 'admit', 'axiom', 'native_decide', 'ofReduceBool']:
            with self.subTest(token=token):
                self.assertIn(token, contract.forbidden_lean('theorem bad : True := by '+token))

    def test_nested_comment_tokens_are_not_declarations(self):
        self.assertEqual(contract.forbidden_lean('/- sorry /- axiom -/ admit -/\n-- sorry\ntheorem ok : True := by trivial'), [])

    def test_unterminated_nested_comment_cannot_hide_real_code(self):
        self.assertIn('sorry', contract.forbidden_lean('/- /- nested -/ -/\ntheorem bad : True := by sorry'))

    def test_import_cycle_rejected(self):
        self.assertTrue(contract.import_cycle_errors({'A':['B'],'B':['A']}))
        self.assertEqual(contract.import_cycle_errors({'A':['B'],'B':[]}),[])

    def test_stale_formal_source_identity_rejected(self):
        receipt = {'status':'COMPILER_VERIFIED','checked_commit':'0'*40,'checked_tree':'1'*40,
            'requested_base':self.manifest['base_commit'],'mathlib_commit':self.manifest['mathlib_commit']}
        errors = contract.formal_receipt_errors(contract.REPO,receipt,self.manifest,self.public['primary_roots'])
        self.assertIn('stale formal receipt head/tree',errors)
        self.assertIn('formal receipt source inventory mismatch',errors)
        self.assertTrue(any('source identity mismatch' in error for error in errors))

    def test_missing_files_fail_closed(self):
        result = contract.check(contract.REPO)
        if result['missing_files'] or result['missing_roots']:
            self.assertEqual(result['status'], 'FAIL')
        self.assertEqual(result['formal_acceptance'], 'PENDING_COMPILER_AND_SEMANTIC_REVIEW')


class RegistrationMutations(unittest.TestCase):
    def setUp(self):
        self.root = {'id':'OPICA_TEST','full_name':'Zeta23.OPICA.test','path':'Zeta23/OPICA/Test.lean'}
        self.protection = {'claim_objects_all_existing':[{'id':'OLD'}],
            'registered_bindings_all_existing':[{'id':'OLD'}]}
        self.manifest = {'registry':{'expected_final_claim_count':2,'expected_final_binding_count':2}}
        self.claims = [{'id':'OLD'},{'id':'OPICA_TEST','source':self.root['path'],
            'theorem':self.root['full_name'],'statement':'Under the stated analytic hypotheses, the conclusion holds.',
            'status':'PROVED_UNCONDITIONAL','promotion_cap':'PROVED_UNCONDITIONAL','dependencies':['OLD']}]
        self.bindings = [{'id':'OLD'},{'id':'OPICA_TEST','source':self.root['path'],'theorem':self.root['full_name']}]

    def errors(self):
        return contract.registration_errors(self.claims,self.bindings,[self.root],self.protection,self.manifest)

    def test_exact_protected_plus_required_identities(self):
        self.assertEqual(self.errors(),[])

    def test_equal_counts_cannot_replace_required_claim_and_binding(self):
        self.claims[-1]['id'] = self.bindings[-1]['id'] = 'UNRELATED'
        errors = self.errors()
        self.assertTrue(any('claim identities' in e for e in errors))
        self.assertTrue(any('binding identities' in e for e in errors))
        self.assertIn('required OPICA claim absent: OPICA_TEST',errors)
        self.assertIn('required OPICA binding absent: OPICA_TEST',errors)

    def test_missing_binding_never_silently_skipped(self):
        self.bindings.pop()
        self.assertIn('required OPICA binding absent: OPICA_TEST',self.errors())

    def test_claim_and_binding_are_both_source_bound(self):
        self.claims[-1]['source'] = self.bindings[-1]['source'] = 'Zeta23/OPICA/Other.lean'
        self.assertTrue(any('claim source/root mismatch' in e for e in self.errors()))
        self.assertTrue(any('OPICA source/root mismatch' in e for e in self.errors()))

    def test_new_supporting_claim_cannot_become_route_authority(self):
        self.claims[-1]['route'] = 'R001_exceptional_zero'
        self.bindings[-1]['route'] = 'R001_exceptional_zero'
        self.assertEqual(sum('route-less' in e for e in self.errors()),2)

    def test_new_claim_status_and_cap_remain_exact(self):
        for key,value in [('status','OPEN'),('promotion_cap','RH_PROVED')]:
            with self.subTest(key=key):
                original = self.claims[-1][key]
                self.claims[-1][key] = value
                self.assertTrue(any('proof status or promotion cap' in e for e in self.errors()))
                self.claims[-1][key] = original

    def test_new_claim_requires_quantified_statement(self):
        self.claims[-1]['statement'] = ''
        self.assertTrue(any('quantified implication statement' in e for e in self.errors()))

    def test_unknown_or_duplicate_registered_dependencies_rejected(self):
        for dependencies in [['UNKNOWN'],['OLD','OLD'],['OPICA_TEST']]:
            with self.subTest(dependencies=dependencies):
                self.claims[-1]['dependencies'] = dependencies
                self.assertTrue(any('dependency identities' in e for e in self.errors()))


class FrozenSourceMutations(unittest.TestCase):
    def setUp(self):
        self.register = contract.read_json(HERE/'SOURCE_REGISTER.json')

    def test_exact_eight_original_descriptors_are_anchored(self):
        self.assertEqual(contract.frozen_source_errors(self.register),[])
        expected = {**contract.FROZEN_PAPER_SHA256,**contract.FROZEN_SPECIFICATION_SHA256}
        self.assertEqual(len(expected),8)
        for path,digest in expected.items():
            self.assertEqual(hashlib.sha256((HERE/path).read_bytes()).hexdigest(),digest)

    def test_paired_data_and_descriptor_hash_swap_cannot_refreeze_input(self):
        replacement = hashlib.sha256(b'changed input with an honestly updated descriptor').hexdigest()
        for field in ('paper_inputs','specification_sources'):
            with self.subTest(field=field):
                changed = copy.deepcopy(self.register)
                changed[field][0]['sha256'] = replacement
                self.assertTrue(any('descriptor identity changed' in error
                    for error in contract.frozen_source_errors(changed)))

    def test_descriptor_omission_cannot_remove_input_from_hash_census(self):
        for field in ('paper_inputs','specification_sources'):
            with self.subTest(field=field):
                changed = copy.deepcopy(self.register)
                changed[field].pop()
                self.assertTrue(any('descriptor inventory changed' in error
                    for error in contract.frozen_source_errors(changed)))

    def test_duplicate_or_substituted_path_cannot_preserve_inventory_count(self):
        for path in [self.register['paper_inputs'][0]['path'],'paper/replacement.md']:
            with self.subTest(path=path):
                changed = copy.deepcopy(self.register)
                changed['paper_inputs'][-1]['path'] = path
                self.assertTrue(any('descriptor inventory changed' in error
                    for error in contract.frozen_source_errors(changed)))

    def test_adapted_checker_identity_is_separate_from_original_input_anchors(self):
        changed = copy.deepcopy(self.register)
        changed['adapted_sources'][0]['sha256'] = '0'*64
        self.assertEqual(contract.frozen_source_errors(changed),[])


class ReleaseDependencyMutations(unittest.TestCase):
    def setUp(self):
        self.a,self.b,self.old = 'Zeta23.OPICA.a','Zeta23.OPICA.b','Zeta23.CCM.old'
        self.roots = [{'id':'NEW_A','full_name':self.a,'module':'Zeta23.OPICA.LocalObstruction','kind':'THEOREM'}]
        self.bindings = [{'id':'NEW_A','theorem':self.a},{'id':'NEW_B','theorem':self.b},
            {'id':'OLD','theorem':self.old},{'id':'UNRELATED','theorem':'Zeta23.OPICA.other'}]
        self.claims = [{'id':'NEW_A','dependencies':['NEW_B','OLD']}]
        uses = {self.a:{'TYPE':['helper'],'VALUE':[self.b]},'helper':{'STRUCTURE':[self.old]},
            self.b:{},self.old:{}}
        self.dependencies = [{'source':source,'channel':channel,'targets':channels.get(channel,[])}
            for source,channels in uses.items() for channel in ('TYPE','VALUE','STRUCTURE')]

    def errors(self):
        return contract.registered_dependency_errors(self.claims,self.bindings,self.roots,self.dependencies)

    def test_exact_mapped_compiler_uses_pass(self):
        self.assertEqual(self.errors(),[])

    def test_omitted_new_or_old_mapped_root_is_rejected(self):
        for dependencies in [[],['OLD'],['NEW_B']]:
            with self.subTest(dependencies=dependencies):
                self.claims[0]['dependencies'] = dependencies
                self.assertTrue(any('differ from transitive compiler uses' in e for e in self.errors()))

    def test_unrelated_registered_root_cannot_be_added(self):
        self.claims[0]['dependencies'].append('UNRELATED')
        self.assertTrue(self.errors())

    def test_release_receipt_validation_invokes_the_mapping_check(self):
        self.claims[0]['dependencies'] = []
        expression = {'format':'LEAN_EXPR_DAG_V1','root':'0','nodes':[['const',['str',['anonymous'],'True'],[]]]}
        payload = json.dumps(expression,ensure_ascii=False,separators=(',',':'))
        digest = hashlib.sha256(payload.encode('utf-8')).hexdigest()
        records = [{'name':name,'module':'Zeta23.OPICA.LocalObstruction','kind':'THEOREM',
            'axioms':[],'type_sha256':digest,'full_type':'True','type_expression':copy.deepcopy(expression),
            'type_metrics':{'format':'LEAN_EXPR_DAG_V1','unique_nodes':1,'closed':True}}
            for name in [self.a,self.b]]
        nodes = [{'name':name,'module':'Zeta23.OPICA.LocalObstruction','kind':'THEOREM','internal':False}
            for name in [self.a,self.b]] + [
            {'name':self.old,'module':'Zeta23.CCM.Old','kind':'THEOREM','internal':False},
            {'name':'helper','module':'Zeta23.OPICA.LocalObstruction','kind':'DEFINITION','internal':True}]
        targets = ['Zeta23.OPICA','Zeta23.OPICA.Validation','Zeta23.RHRC.OpicaBindings']
        manifest = {'base_commit':'c'*40,'mathlib_commit':'e'*40,'create':[],'modify':[],
            'no_root_api_pollution':{'required_build_targets':targets}}
        commands = [{'argv':argv,'log':log,'log_sha256':'f'*64,'exit_code':0,'seconds':0.0}
            for argv,log in [(['lake','env','lean','--version'],'lean-version.log'),
                (['lake','build',*targets],'build.log'),
                (['lake','env','lean','Zeta23/RHRC/OpicaBindings.lean'],'bindings.log')]]
        formal = {'schema':'OPICA_COMPILER_RECEIPT_V1','status':'COMPILER_VERIFIED',
            'checked_commit':'a'*40,'checked_tree':'b'*40,'requested_base':'c'*40,
            'requested_head':'a'*40,'checkout_kind':'PR_HEAD','lean':'Lean (version 4.33.0-rc2, fixture)',
            'mathlib_commit':'e'*40,'sources':{},'commands':commands,'constructors':{},
            'declarations':records,'dependency_declarations':nodes,'dependencies':self.dependencies}
        def read(path):
            return {'WORKFLOW_CONTRACT.json':{'reviewed_root_type_sha256':{self.a:digest}},
                'CLAIM_REGISTRY.json':{'claims':self.claims},
                'REGISTERED_THEOREM_BINDINGS.json':{'bindings':self.bindings}}[Path(path).name]
        with patch.object(contract.subprocess,'check_output',side_effect=['a'*40,'b'*40]),patch.object(contract,'read_json',side_effect=read):
            errors = contract.formal_receipt_errors(HERE,formal,manifest,self.roots)
        self.assertEqual(errors,['registered OPICA dependencies differ from transitive compiler uses: NEW_A'])


class ReleaseEvidenceBoundaryMutations(unittest.TestCase):
    def setUp(self):
        import test_receipt as fixtures
        fixture = fixtures.SharedReceiptMutations()
        fixture.setUp()
        self.fixture = fixture
        self.formal,self.root = fixture.payload,fixture.root
        self.manifest = {**fixture.manifest,'create':[],'modify':[]}
        self.formal['sources'] = {}

    def errors(self):
        def read(path):
            return {'WORKFLOW_CONTRACT.json':{'reviewed_root_type_sha256':{
                    self.root['full_name']:self.root['expected_type_sha256']}},
                'CLAIM_REGISTRY.json':{'claims':[{'id':self.root['id'],'dependencies':[]}]},
                'REGISTERED_THEOREM_BINDINGS.json':{'bindings':[{'id':self.root['id'],
                    'theorem':self.root['full_name']}]}}[Path(path).name]
        with patch.object(contract.subprocess,'check_output',side_effect=['a'*40,'b'*40]),patch.object(contract,'read_json',side_effect=read):
            return contract.formal_receipt_errors(HERE,self.formal,self.manifest,[self.root])

    def test_complete_receipt_passes_release_body_guard(self):
        self.assertEqual(self.errors(),[])

    def test_release_rejects_dag_deletion_or_hidden_premise_under_unchanged_reviewed_digest(self):
        self.formal['declarations'][0]['type_expression'] = {'format':'LEAN_EXPR_DAG_V1','root':'1',
            'nodes':[['const',['str',['anonymous'],'True'],[]],
                ['forall',['str',['anonymous'],'hidden'],'instImplicit','0','0']]}
        self.assertTrue(any('DAG digest mismatch' in e for e in self.errors()))
        del self.formal['declarations'][0]['type_expression']
        self.assertTrue(any('missing public declaration evidence' in e for e in self.errors()))

    def test_release_rejects_omitted_constructor_or_changed_constructor_type(self):
        _,ctor = self.fixture.add_constructor()
        self.formal['constructors'][ctor]['type_expression'] = copy.deepcopy(self.formal['declarations'][0]['type_expression'])
        self.assertTrue(any('constructor full type mismatch' in e for e in self.errors()))
        self.formal['constructors'] = {}
        self.assertTrue(any('constructor inventory differs' in e for e in self.errors()))

    def test_release_rejects_forged_successful_command_or_log_digest(self):
        self.formal['commands'][2]['argv'] = ['echo','cached green']
        self.assertTrue(any('command identity' in e for e in self.errors()))
        self.formal['commands'][2]['argv'] = ['lake','env','lean','Zeta23/RHRC/OpicaBindings.lean']
        self.formal['commands'][2]['log_sha256'] = 'not-a-sha'
        self.assertTrue(any('log digest' in e for e in self.errors()))

    def test_release_rejects_wrong_checkout_kind(self):
        self.formal['checkout_kind'] = 'SYNTHETIC_MERGE'
        self.assertTrue(any('checkout kind' in e for e in self.errors()))


if __name__ == '__main__':
    unittest.main()
