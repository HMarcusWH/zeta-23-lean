"""Protocol tests only; synthetic anchors never supply actual review authority."""
from copy import deepcopy
import ast
import importlib.util
import json
import subprocess
import os
import re
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
sys.path.insert(0,str(HERE.parent))
sys.path.insert(0,str(REPO/'research/RHRC/tools'))
sys.path.insert(0,str(REPO/'research/RHRC/routes/R003_ccm_bridge/post290'))
import exact_extension as candidate


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    sys.modules[name]=module
    spec.loader.exec_module(module)
    return module


class ExactSubjectFixture:
    @classmethod
    def setUpClass(cls):
        path = REPO / candidate.FOLDER / 'tests/test_parent_extension.py'
        spec = importlib.util.spec_from_file_location('_unchanged_original_protocol_fixture', path)
        cls.fixtures = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.fixtures)
        cls.original = candidate.load_original(REPO)
    def setUp(self):
        f = self.fixtures.ParentExtensionTests('test_exact_projection_preserves_every_parent_value')
        f.setUp()
        self.parent, self.raw, self.contract = deepcopy(f.parent), deepcopy(f.raw), deepcopy(f.contract)
        self.raw['checked_commit'] = 'a' * 40
        self.raw['checked_tree'] = 'b' * 40
        self.contract['manifest_bytes']=(REPO/candidate.FOLDER/'BUILD_MANIFEST.json').read_bytes()
        manifest=json.loads(self.contract['manifest_bytes'])
        files={r['path']:r for r in self.raw['files']}
        self.raw['direct_import_snapshots'] = [{'module':m['module'],'path':m['path'],
            'source_sha256':files[m['path']]['sha256'],'actual_all_ordered_imports':[]}
            for m in manifest['modules']]
        self.raw['added_audit_sources_in_math_facade'] = []
        extra = {'path':'research/RHRC/integration/opica_followup/continuation/example.lean',
                 'mode':'100644', 'git_blob':'1'*40, 'bytes':7, 'sha256':'1'*64}
        self.raw['files'].append(extra)
        original_doc = deepcopy(next(r for r in self.parent['files'] if r['path'] == 'AUDIT.md'))
        current_doc = next(r for r in self.raw['files'] if r['path'] == 'AUDIT.md')
        current_doc['sha256'] = '3'*64
        current_doc['git_blob'] = '3'*40
        current_doc['bytes'] += 1
        self.a = {'schema':'OPICA_EXACT_EXTENSION_AMENDMENT_PROPOSAL_V1',
            'status':'UNACCEPTED_SOURCE_PINNED_REVIEW_INPUT',
            'parent_head':candidate.PARENT, 'parent_tree':candidate.PARENT_TREE,
            'checked_commit':self.raw['checked_commit'], 'checked_tree':self.raw['checked_tree'],
            'descriptor_sha256':candidate.digest(self.contract['descriptor_bytes']),
            'roots_sha256':candidate.digest(self.contract['roots_bytes']),
            'manifest_sha256':candidate.MANIFEST_SHA256,
            'original_projection_sha256':candidate.ORIGINAL_IMPLEMENTATION_SHA256,
            'complete_file_inventory_sha256':candidate.inventory_digest(self.raw['files']),
            'additional_exact_paths':[{'file':deepcopy(extra),
                'role':'CONTINUATION_AUDIT_LEAN_SOURCE_REQUIRES_EXACT_CLASS_REVIEW',
                'theorem_authority':'NONE', 'review_status':'OPEN_REQUIRES_INDEPENDENT_REVIEW'}],
            'protected_documentation_edits':[{'original':original_doc,'current':deepcopy(current_doc),
                'role':'DOCUMENTATION_ONLY_NO_THEOREM_AUTHORITY'}],
            'direct_import_snapshots':deepcopy(self.raw['direct_import_snapshots']),
            'claim_or_type_amendments':[], 'new_primary_roots':0}

parent=load('_proposed_parent_wrapper',REPO/'research/RHRC/integration/opica/validate_contract.py')
builder=load('_proposed_child_builder',REPO/'research/RHRC/integration/opica_followup/build_receipt.py')
child=load('_proposed_child_validator',REPO/'research/RHRC/integration/opica_followup/validate_contract.py')


class V2ExactPolicyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ExactSubjectFixture.setUpClass()

    def setUp(self):
        fixture=ExactSubjectFixture()
        fixture.setUp()
        self.raw,self.old,self.contract=deepcopy(fixture.raw),deepcopy(fixture.parent),deepcopy(fixture.contract)
        self.original=fixture.original
        self.policy=candidate.policy_from_v1(fixture.a,self.raw['files'],self.contract['descriptor_bytes'])
        rule=self.policy['additional_audit_file_class']
        if rule is not None:
            rules=self.raw['file_classes']['rules']
            position=next(i for i,row in enumerate(rules) if row['id']=='zeta_lean')
            rules.insert(position,deepcopy(rule))
        self.raw['file_classes']['rules'].append(deepcopy(self.policy['original_planned_artifact_file_class']))
        artifact_rule=self.policy['additional_audit_artifact_file_class']
        if artifact_rule is not None:
            self.raw['file_classes']['rules'].append(deepcopy(artifact_rule))
        self.anchor=candidate.digest(candidate.canonical(self.policy))

    def check(self):
        return candidate.validate_policy_context(self.raw,self.old,self.contract,
            candidate.canonical(self.policy),self.anchor,self.original)

    def reanchor_fixture(self):
        # Explicit synthetic fixture only: never written as an accepted policy.
        self.anchor=candidate.digest(candidate.canonical(self.policy))

    def reject(self):
        with self.assertRaises((ValueError,KeyError,TypeError)):
            self.check()

    def test_valid_exact_subject_projection_preserves_every_parent_value(self):
        initial_inventory=candidate.inventory_digest(self.raw['files'])
        context=self.check()
        expected={key:deepcopy(self.old[key]) for key in
            ['claim_registry','theorem_bindings','file_classes','semantic_closure']}
        self.assertEqual(dict(candidate.project(context)),expected)
        self.raw['claim_registry']['claims'][0]['statement']='later mutation'
        self.assertEqual(dict(candidate.project(context)),expected)
        self.assertEqual(context.actual_source_inventory_sha256,initial_inventory)

    def test_no_anchor_or_status_self_approval(self):
        for anchor in [None,'','f'*64]:
            with self.assertRaises(ValueError):
                candidate.validate_policy_context(self.raw,self.old,self.contract,
                    candidate.canonical(self.policy),anchor,self.original)
        self.policy['status']='APPROVED_BY_EVERYONE'
        self.reject()

    def test_actual_head_may_change_without_changing_exact_subjects(self):
        self.raw['checked_commit']='c'*40
        self.raw['checked_tree']='d'*40
        context=self.check()
        self.assertEqual(context.actual_commit,'c'*40)
        self.assertEqual(context.actual_tree,'d'*40)

    def test_current_identity_still_required_for_actual_evidence(self):
        self.raw.pop('checked_tree')
        self.reject()

    def test_original_seal_holder_contents_avoid_self_reference(self):
        name=candidate.FOLDER+'SOURCE_REGISTER.json'
        row=next(row for row in self.raw['files'] if row['path']==name)
        before=self.check()
        row.update(sha256='7'*64,git_blob='7'*40,bytes=row['bytes']+10)
        after=self.check()
        self.assertEqual(before.policy_sha256,after.policy_sha256)
        self.assertNotEqual(before.actual_source_inventory_sha256,after.actual_source_inventory_sha256)
        self.assertIn(name,self.policy['original_content_authorities'])

    def test_extra_contents_cannot_use_mutable_path_exclusion(self):
        self.raw['files'][-1]['sha256']='8'*64
        self.reject()

    def test_unlisted_path_and_mode_changes_are_rejected(self):
        self.raw['files'][-1]['path']+='unexpected'
        self.reject()

    def test_original_mutable_mode_is_still_pinned(self):
        row=next(row for row in self.raw['files'] if row['path']==candidate.FOLDER+'SOURCE_REGISTER.json')
        row['mode']='100755' if row['mode']=='100644' else '100644'
        self.reject()

    def test_directory_content_exclusion_and_parent_exclusion_are_rejected(self):
        self.policy['original_content_authorities'].append('research/')
        self.reanchor_fixture();self.reject()

    def test_planned_math_contents_remain_exact_source_subjects(self):
        name=self.policy['direct_import_snapshots'][0]['path']
        row=next(row for row in self.raw['files'] if row['path']==name)
        row['sha256']='9'*64
        self.reject()

    def test_import_change_or_source_pinning_omission_rejected(self):
        self.raw['direct_import_snapshots'][0]['actual_all_ordered_imports']=['Zeta23.Forged']
        self.reject()

    def test_missing_43rd_source_subject_rejected(self):
        self.policy['direct_import_snapshots'].pop()
        self.raw['direct_import_snapshots'].pop()
        self.reanchor_fixture();self.reject()

    def test_audit_import_into_facade_rejected(self):
        self.raw['added_audit_sources_in_math_facade']=[self.raw['files'][-1]['path']]
        self.reject()

    def test_protected_doc_actual_bytes_not_just_path_rejected(self):
        row=next(row for row in self.raw['files'] if row['path']=='AUDIT.md')
        row['sha256']='6'*64
        self.reject()

    def test_protected_runtime_cannot_be_reclassified_as_documentation(self):
        row=next(row for row in self.old['files'] if row['path'].endswith('.lean'))
        current=next(item for item in self.raw['files'] if item['path']==row['path'])
        current['sha256']='5'*64
        self.policy['protected_documentation_edits'].append({'original':deepcopy(row),
            'current':deepcopy(current),'role':'DOCUMENTATION_ONLY_NO_THEOREM_AUTHORITY'})
        self.reanchor_fixture();self.reject()

    def test_old_open_claim_cannot_be_promoted_by_projection(self):
        self.raw['claim_registry']['claims'][0]['status']='PROVED_UNCONDITIONAL'
        self.reject()

    def test_parent_class_rule_and_historical_role_preserved(self):
        self.raw['file_classes']['rules'][0]['pattern']='.*'
        self.reject()

    def test_separate_original_release_gates_cannot_be_removed(self):
        self.policy['separate_required_gates']=[]
        self.reanchor_fixture();self.reject()

    def test_policy_cannot_grant_theorem_or_rh_authority(self):
        self.policy['policy_grants_theorem_authority']=True
        self.reanchor_fixture();self.reject()

    def test_policy_cannot_change_frozen_descriptor(self):
        descriptor=json.loads(self.contract['descriptor_bytes'])
        descriptor['new_exact_paths'].append('Anything.lean')
        self.contract['descriptor_bytes']=candidate.canonical(descriptor)
        self.policy['descriptor_sha256']=candidate.digest(self.contract['descriptor_bytes'])
        self.reanchor_fixture();self.reject()


class WrapperHookTests(unittest.TestCase):
    def test_legacy_v1_function_body_and_semantics_are_preserved(self):
        old=ast.parse(subprocess.check_output(['git','-C',str(REPO),'show','2440dcde7607baa7bcff2ce9626effa1ae9f3f07:research/RHRC/integration/opica/validate_contract.py']).decode('utf-8'))
        new=ast.parse((REPO/'research/RHRC/integration/opica/validate_contract.py').read_text(encoding='utf-8'))
        old_fn=next(n for n in old.body if isinstance(n,ast.FunctionDef) and n.name=='_source_bound_followup_context')
        new_fn=next(n for n in new.body if isinstance(n,ast.FunctionDef) and n.name=='_source_bound_followup_context_v1')
        new_fn.name=old_fn.name
        self.assertEqual(ast.dump(old_fn),ast.dump(new_fn))

    def test_no_child_still_dispatches_original_untouched_parent_path(self):
        with TemporaryDirectory() as temp:
            with patch.object(parent,'_source_bound_followup_context_v1',return_value=None) as legacy:
                self.assertIsNone(parent._source_bound_followup_context(Path(temp)))
                legacy.assert_called_once()

    def test_pending_v2_does_not_fall_back_to_legacy_acceptance(self):
        with TemporaryDirectory() as temp:
            root=Path(temp)
            folder=root/candidate.FOLDER
            folder.mkdir(parents=True)
            (folder/'SOURCE_REGISTER.json').write_text(json.dumps({'exact_source_extension_policy':{
                'schema':'OPICA_EXACT_SUBJECT_EXTENSION_POLICY_V2'}}),encoding='utf-8')
            with patch.object(parent,'TRUSTED_EXACT_EXTENSION_POLICY_SHA256',None), patch.object(parent,'_source_bound_followup_context_v1',return_value=({'forged':True},set())) as legacy:
                with self.assertRaisesRegex(ValueError,'anchor is not established'):
                    parent._source_bound_followup_context(root)
                legacy.assert_not_called()

    def test_provider_source_hash_and_child_wrapper_pins_agree(self):
        provider=REPO/'research/RHRC/integration/opica_followup/exact_extension.py'
        wrapper=REPO/'research/RHRC/integration/opica/validate_contract.py'
        self.assertEqual(parent.EXACT_EXTENSION_PROVIDER_SHA256,candidate.digest(provider.read_bytes()))
        self.assertEqual(builder.PARENT_PROJECTION_VALIDATOR_SHA256,candidate.digest(wrapper.read_bytes()))
        self.assertEqual(child.PARENT_EXACT_WRAPPER_SHA256,candidate.digest(wrapper.read_bytes()))

    def test_registry_projection_registers_the_loaded_parent_module(self):
        # This is a loader fixture, not actual registry or semantic approval.
        with TemporaryDirectory() as temp:
            root=Path(temp);folder=root/'research/RHRC/integration/opica';folder.mkdir(parents=True)
            source=b'''import sys
def _source_bound_followup_context(repo):
    if sys.modules.get(__name__) is None:
        raise ValueError("FIXTURE_ONLY: parent module was not registered")
    return ({},frozenset())
def exact_extension_binding(repo):
    return {"scope":"FIXTURE_ONLY_LOADER_PROTOCOL"}
'''
            (folder/'validate_contract.py').write_bytes(source)
            claims=[{'id':'FIXTURE_ONLY_'+str(i),'dependencies':[]} for i in range(298)]
            registry=root/'research/RHRC/CLAIM_REGISTRY.json'
            registry.write_text(json.dumps({'claims':claims}),encoding='utf-8')
            name='opica_parent_contract_for_full_child'
            with patch.dict(sys.modules):
                sys.modules.pop(name,None)
                with patch.object(builder,'PARENT_PROJECTION_VALIDATOR_SHA256',candidate.digest(source)):
                    result=builder.full_registry_projection(root,{'roots':[{
                        'id':'FIXTURE_ONLY_0','full_name':'FixtureOnly.root'}]}, {'FixtureOnly.root':[]})
                self.assertEqual(result['exact_source_extension_policy']['scope'],'FIXTURE_ONLY_LOADER_PROTOCOL')

    def test_missing_semantic_or_policy_authority_cannot_be_replaced_by_status(self):
        # Actual authorized anchors may later be configured. This fixture
        # explicitly removes authority and must still fail before inference.
        with patch.object(parent,'TRUSTED_EXACT_EXTENSION_POLICY_SHA256',None), \
             patch.object(builder,'FULL_REVIEW_SHA256',None):
            with self.assertRaisesRegex(ValueError,'anchor is configured'):
                candidate.source_bound_context(REPO,{},None,parent)
            with self.assertRaisesRegex(ValueError,'review seal is not established'):
                builder.reviewed_full_contract(REPO,{})

    def test_raw_status_or_boolean_cannot_supply_child_policy(self):
        with TemporaryDirectory() as temp:
            root=Path(temp);folder=root/candidate.FOLDER;folder.mkdir(parents=True)
            (folder/'SOURCE_REGISTER.json').write_text(json.dumps({'exact_source_extension_policy':True}),encoding='utf-8')
            with self.assertRaisesRegex(ValueError,'wrapper changed'):
                child.exact_policy_context(root)

    def test_provider_no_anchor_fails_before_checkout_or_registry_inference(self):
        with patch.object(candidate,'capture_working_source',side_effect=AssertionError('must not read')):
            with self.assertRaisesRegex(ValueError,'anchor is configured'):
                candidate.source_bound_context(REPO,{},None,parent)

    def test_actual_git_source_capture_keeps_all_bytes_and_rejects_drift(self):
        with TemporaryDirectory() as temp:
            root=Path(temp)
            subprocess.run(['git','init','-q',str(root)],check=True)
            subprocess.run(['git','-C',str(root),'config','core.autocrlf','false'],check=True)
            (root/'Example.lean').write_bytes(b'def fixture : Nat := 1\n')
            subprocess.run(['git','-C',str(root),'add','Example.lean'],check=True)
            subprocess.run(['git','-C',str(root),'-c','user.name=FIXTURE_ONLY',
                '-c','user.email=fixture@example.invalid','commit','-qm','FIXTURE ONLY'],check=True)
            head,tree,files,blobs=candidate.capture_working_source(root)
            self.assertEqual(head,candidate.git(root,'rev-parse','HEAD').decode().strip())
            self.assertEqual(tree,candidate.git(root,'rev-parse','HEAD^{tree}').decode().strip())
            self.assertEqual(files[0]['sha256'],candidate.digest(blobs['Example.lean']))
            (root/'Example.lean').write_bytes(b'def fixture : Nat := 2\n')
            with self.assertRaisesRegex(ValueError,'completely clean'):
                candidate.capture_working_source(root)

    def test_git_clean_newline_normalization_does_not_pass_exact_byte_capture(self):
        with TemporaryDirectory() as temp:
            root=Path(temp)
            subprocess.run(['git','init','-q',str(root)],check=True)
            subprocess.run(['git','-C',str(root),'config','core.autocrlf','true'],check=True)
            (root/'Example.lean').write_bytes(b'def fixture : Nat := 1\r\n')
            subprocess.run(['git','-C',str(root),'add','Example.lean'],check=True)
            subprocess.run(['git','-C',str(root),'-c','user.name=FIXTURE_ONLY',
                '-c','user.email=fixture@example.invalid','commit','-qm','FIXTURE ONLY'],check=True)
            self.assertEqual(candidate.git(root,'status','--porcelain').strip(),b'')
            with self.assertRaisesRegex(ValueError,'actual bytes differ'):
                candidate.capture_working_source(root)

    def test_untracked_source_cannot_escape_actual_census(self):
        with TemporaryDirectory() as temp:
            root=Path(temp)
            subprocess.run(['git','init','-q',str(root)],check=True)
            (root/'Unlisted.lean').write_text('def fixture : Nat := 0\n',encoding='utf-8')
            with self.assertRaisesRegex(ValueError,'completely clean'):
                candidate.capture_working_source(root)

    def test_source_alias_flag_rejected_without_claiming_os_symlink_capability(self):
        with TemporaryDirectory() as temp:
            root=Path(temp);target=root/'Example.lean';target.write_bytes(b'def fixture : Nat := 1\n')
            original=Path.is_symlink
            with patch.object(Path,'is_symlink',lambda path:path==target or original(path)):
                with self.assertRaisesRegex(ValueError,'symlink/junction'):
                    candidate.regular_source(root,'Example.lean')

    def test_release_stays_closed_even_if_fresh_compiler_gate_passes(self):
        with TemporaryDirectory() as temp:
            output=Path(temp)/'result.json'
            args=['validator','--phase','release','--formal-receipt',str(Path(temp)/'input.json'),
                  '--output',str(output)]
            with patch.object(sys,'argv',args),patch.object(child,'full_compiler_gate',return_value={'status':'PASS_FULL_COMPILER'}),\
                 patch.object(child,'preflight',return_value={'errors':[],'status':'PASS_PREPARATION_ONLY','release_ready':False}):
                self.assertEqual(child.main(),1)
            report=json.loads(output.read_bytes())
            self.assertEqual(report['status'],'FAIL_RELEASE_INCOMPLETE')
            self.assertFalse(report['release_ready'])
            self.assertTrue(report['errors'], 'A compiler-only success cannot satisfy the other mandatory release gates')

    def test_exact_doc_context_does_not_exempt_other_protected_bytes_or_old_claims(self):
        with TemporaryDirectory() as temp:
            root=Path(temp)
            (root/'AUDIT.md').write_text('new audit',encoding='utf-8')
            (root/'Other.md').write_text('unauthorized change',encoding='utf-8')
            research=root/'research/RHRC';research.mkdir(parents=True)
            old_claim={'id':'OLD_OPEN','status':'OPEN'}
            (research/'CLAIM_REGISTRY.json').write_text(json.dumps({'claims':[old_claim]}),encoding='utf-8')
            (research/'REGISTERED_THEOREM_BINDINGS.json').write_text(json.dumps({'bindings':[]}),encoding='utf-8')
            protection={'byte_protected_files':[{'path':name,'bytes':3,
                'sha256':candidate.digest(b'old')} for name in ['AUDIT.md','Other.md']],
                'claim_objects_all_existing':[deepcopy(old_claim)],'registered_bindings_all_existing':[]}
            class ValidatedFixtureContext:
                documentation_paths=frozenset({'AUDIT.md'})
            with patch.object(parent,'PROTECTED_STATE_OBJECT_SHA256',parent._canonical_object_sha256(protection)),\
                 patch.object(parent,'_exact_source_extension_context',return_value=ValidatedFixtureContext()):
                errors=parent.protected_errors(root,protection)
                self.assertIn('protected bytes changed: Other.md',errors)
                self.assertNotIn('protected bytes changed: AUDIT.md',errors)
                (research/'CLAIM_REGISTRY.json').write_text(json.dumps({'claims':[{'id':'OLD_OPEN','status':'PROVED'}]}),encoding='utf-8')
                self.assertIn('historical registry object changed: OLD_OPEN',parent.protected_errors(root,protection))


class ExactAuditClassificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ExactSubjectFixture.setUpClass()
    check=V2ExactPolicyTests.check
    reject=V2ExactPolicyTests.reject
    reanchor_fixture=V2ExactPolicyTests.reanchor_fixture
    def setUp(self):
        V2ExactPolicyTests.setUp(self)

    def insert_rule(self):
        rules=self.raw['file_classes']['rules']
        rule=self.policy['additional_audit_file_class']
        if rule is not None:
            at=next(i for i,r in enumerate(rules) if r['id']=='zeta_lean')
            rules.insert(at,deepcopy(rule))

    def remove_rule(self):
        self.raw['file_classes']['rules']=[r for r in self.raw['file_classes']['rules']
            if r.get('id')!=candidate.AUDIT_CLASSIFICATION_ID]

    def rule(self):
        return next(r for r in self.raw['file_classes']['rules']
                    if r.get('id')==candidate.AUDIT_CLASSIFICATION_ID)

    def change_both_rules(self,**fields):
        self.policy['additional_audit_file_class'].update(fields)
        self.rule().update(fields)
        self.reanchor_fixture()

    def test_exact_rule_preserves_every_parent_and_original_child_class(self):
        before=deepcopy(self.raw['file_classes'])
        projected=candidate.project_exact_audit_classification(before,
            self.policy['additional_exact_paths'],self.policy['additional_audit_file_class'])
        expected=deepcopy(before)
        expected['rules']=[r for r in expected['rules'] if r['id']!=candidate.AUDIT_CLASSIFICATION_ID]
        self.assertEqual(projected,expected)
        self.assertEqual(before,self.raw['file_classes'])
        self.assertEqual(dict(candidate.project(self.check()))['file_classes'],self.old['file_classes'])

    def test_literal_regex_matches_only_exact_subject_not_sibling(self):
        path=self.policy['additional_exact_paths'][0]['file']['path']
        pattern=self.rule()['pattern']
        self.assertTrue(re.search(pattern,path))
        for name in [path+'.unexpected',path.replace('example.lean','exampleXlean'),
                     path.replace('example.lean','another.lean'),'Zeta23/Counterfeit.lean',
                     path+'\n',path+'\r\n','\n'+path]:
            self.assertIsNone(re.search(pattern,name))
        self.check()

    def test_policy_and_actual_rule_cannot_broaden_regex(self):
        self.change_both_rules(pattern='^research/.*\\.lean$');self.reject()

    def test_policy_and_actual_rule_cannot_change_class(self):
        self.change_both_rules(file_class='LEAN_SOURCE');self.reject()

    def test_policy_and_actual_rule_cannot_change_trust(self):
        self.change_both_rules(trust_zone='RH_FORMAL_CORE');self.reject()

    def test_actual_rule_cannot_differ_from_pinned_policy(self):
        self.rule()['pattern']='.*';self.reject()

    def test_missing_actual_rule_rejected(self):
        self.remove_rule();self.reject()

    def test_missing_policy_rule_rejected(self):
        del self.policy['additional_audit_file_class'];self.reanchor_fixture();self.reject()

    def test_duplicate_rule_rejected(self):
        self.raw['file_classes']['rules'].insert(0,deepcopy(self.rule()));self.reject()

    def test_mispositioned_rule_rejected(self):
        rule=deepcopy(self.rule());self.remove_rule();self.raw['file_classes']['rules'].insert(0,rule);self.reject()

    def test_changed_original_child_rule_rejected(self):
        original_ids={r['id'] for r in self.old['file_classes']['rules']}
        row=next(r for r in self.raw['file_classes']['rules'] if r['id'] not in original_ids
                 and r['id']!=candidate.AUDIT_CLASSIFICATION_ID)
        row['pattern']='^Zeta23/UndeclaredChild\\.lean$';self.reject()

    def test_unrelated_class_metadata_change_rejected(self):
        self.raw['file_classes']['unknown_class']='FORGED_DEFAULT';self.reject()

    def test_wrong_audit_role_rejected(self):
        self.policy['additional_exact_paths'][0]['role']='CONTINUATION_RESEARCH_DOCUMENT_OR_LOG'
        self.reanchor_fixture();self.reject()

    def test_unlisted_extra_path_rejected_even_when_class_rule_rebound(self):
        row=deepcopy(self.policy['additional_exact_paths'][0])
        row['file']['path']='research/Another.lean'
        self.policy['additional_exact_paths'].append(row)
        self.policy['additional_audit_file_class']=candidate.exact_audit_classification(
            self.policy['additional_exact_paths'])
        self.remove_rule();self.insert_rule();self.reanchor_fixture();self.reject()

    def test_duplicate_audit_subject_rejected(self):
        rows=deepcopy(self.policy['additional_exact_paths']);rows.append(deepcopy(rows[0]))
        with self.assertRaises(ValueError):candidate.exact_audit_classification(rows)

    def test_regex_metacharacters_are_literal_not_permissions(self):
        row=deepcopy(self.policy['additional_exact_paths'][0]);row['file']['path']='research/a+[b](c).lean'
        pattern=candidate.exact_audit_classification([row])['pattern']
        self.assertTrue(re.search(pattern,row['file']['path']))
        for name in ['research/aaaabc.lean','research/a+[b](c)Xlean','research/other.lean']:
            self.assertIsNone(re.search(pattern,name))

    def test_first_matching_rule_must_be_exact_audit_rule(self):
        self.raw['file_classes']['rules'].insert(0,{'id':'shadow','pattern':'^research/',
            'file_class':'LEAN_SOURCE','trust_zone':'AUXILIARY_FORMALIZATION'})
        self.reject()

    def test_empty_audit_set_requires_no_rule(self):
        classes=deepcopy(self.raw['file_classes']);self.remove_rule()
        no_rule=deepcopy(self.raw['file_classes'])
        self.assertIsNone(candidate.exact_audit_classification([]))
        self.assertEqual(candidate.project_exact_audit_classification(no_rule,[],None),no_rule)
        with self.assertRaises(ValueError):candidate.project_exact_audit_classification(classes,[],None)

def classify(classes,path):
    return next(((row['file_class'],row['trust_zone'],row['id']) for row in classes['rules']
        if re.search(row['pattern'],path)),(classes['unknown_class'],classes['unknown_trust_zone'],'none'))


class MixedArtifactClassificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ExactSubjectFixture.setUpClass()
    check=V2ExactPolicyTests.check
    reject=V2ExactPolicyTests.reject
    reanchor_fixture=V2ExactPolicyTests.reanchor_fixture
    def setUp(self):
        V2ExactPolicyTests.setUp(self)
        self.before_artifact=deepcopy(self.raw['file_classes'])
        root=candidate.FOLDER+'continuation/'
        for suffix,role in [('literal+[a](b).log','CONTINUATION_SOURCE_PINNED_EVIDENCE_OR_METADATA'),
                            ('fixture.py','CONTINUATION_AUDIT_RUNTIME_SOURCE'),
                            ('handoff.md','CONTINUATION_RESEARCH_DOCUMENT_OR_LOG')]:
            row={'path':root+suffix,'mode':'100644','git_blob':'4'*40,'bytes':12,'sha256':'4'*64}
            self.raw['files'].append(row)
            self.policy['additional_exact_paths'].append({'file':deepcopy(row),'role':role,
                'theorem_authority':'NONE','review_status':'OPEN_REQUIRES_INDEPENDENT_REVIEW'})
        self.policy['complete_path_mode_census']=candidate.path_modes(self.raw['files'])
        self.policy['additional_audit_artifact_file_class']=candidate.exact_audit_artifact_classification(
            self.policy['additional_exact_paths'])
        self.raw['file_classes']['rules'].append(deepcopy(self.artifact_policy()))
        self.reanchor_fixture()

    def artifact_policy(self):return self.policy['additional_audit_artifact_file_class']
    def artifact_rule(self):
        return next(r for r in self.raw['file_classes']['rules']
                    if r['id']==candidate.AUDIT_ARTIFACT_CLASSIFICATION_ID)
    def remove_artifact_rule(self):
        self.raw['file_classes']['rules']=[r for r in self.raw['file_classes']['rules']
            if r['id']!=candidate.AUDIT_ARTIFACT_CLASSIFICATION_ID]
    def change_both_artifact_rules(self,**fields):
        self.artifact_policy().update(fields);self.artifact_rule().update(fields);self.reanchor_fixture()

    def test_fallback_fills_only_unknown_and_preserves_prior_first_matches(self):
        rows=self.policy['additional_exact_paths']
        for row in rows:
            name=row['file']['path'];before=classify(self.before_artifact,name)
            after=classify(self.raw['file_classes'],name)
            if name.endswith('.log'):
                self.assertEqual(before[:2],('UNKNOWN_FILE_CLASS','UNKNOWN'))
                self.assertEqual(after,('RESEARCH_FIXTURE','AUDIT_ONLY',candidate.AUDIT_ARTIFACT_CLASSIFICATION_ID))
            else:self.assertEqual(after,before)
        self.assertEqual(dict(candidate.project(self.check()))['file_classes'],self.old['file_classes'])

    def test_fallback_literal_anchors_reject_newline_suffix_and_regex_aliases(self):
        name=next(r['file']['path'] for r in self.policy['additional_exact_paths']
                  if r['file']['path'].endswith('.log'))
        pattern=self.artifact_rule()['pattern'];self.assertTrue(re.search(pattern,name))
        for other in [name+'\n',name+'\r\n',name+'.unexpected','\n'+name,
                      name.replace('literal+[a](b)','literalaab'),name.replace('.log','Xlog')]:
            self.assertIsNone(re.search(pattern,other))
        self.check()

    def test_wrong_artifact_regex_rejected(self):
        self.change_both_artifact_rules(pattern='\\A(?:research/.*)\\Z');self.reject()
    def test_wrong_artifact_class_rejected(self):
        self.change_both_artifact_rules(file_class='RESEARCH_EXECUTABLE');self.reject()
    def test_wrong_artifact_trust_rejected(self):
        self.change_both_artifact_rules(trust_zone='RH_FORMAL_CORE');self.reject()
    def test_missing_artifact_rule_rejected(self):
        self.remove_artifact_rule();self.reject()
    def test_missing_artifact_policy_rejected(self):
        del self.policy['additional_audit_artifact_file_class'];self.reanchor_fixture();self.reject()
    def test_duplicate_artifact_rule_rejected(self):
        self.raw['file_classes']['rules'].append(deepcopy(self.artifact_rule()));self.reject()
    def test_artifact_rule_must_be_last_even_when_next_rule_does_not_match(self):
        rule=deepcopy(self.artifact_rule());self.remove_artifact_rule()
        self.raw['file_classes']['rules'].insert(-1,rule);self.reject()
    def test_rule_cannot_be_inserted_before_preexisting_python_class(self):
        rule=deepcopy(self.artifact_rule());self.remove_artifact_rule()
        self.raw['file_classes']['rules'].insert(0,rule);self.reject()
    def test_actual_artifact_rule_cannot_differ_from_policy(self):
        self.artifact_rule()['pattern']='.*';self.reject()
    def test_non_audit_role_rejected(self):
        row=next(r for r in self.policy['additional_exact_paths'] if r['file']['path'].endswith('.log'))
        row['role']='RH_FORMAL_CORE';self.reanchor_fixture();self.reject()
    def test_artifact_theorem_authority_rejected(self):
        row=next(r for r in self.policy['additional_exact_paths'] if r['file']['path'].endswith('.log'))
        row['theorem_authority']='PROVED';self.reanchor_fixture();self.reject()
    def test_exact_artifact_row_contents_still_authenticated(self):
        self.raw['files'][-1]['sha256']='8'*64;self.reject()
    def test_unlisted_artifact_is_not_a_directory_permission(self):
        self.raw['files'][-1]['path']+='unlisted';self.reject()
    def test_duplicate_artifact_subject_rejected(self):
        row=next(r for r in self.policy['additional_exact_paths'] if r['file']['path'].endswith('.log'))
        with self.assertRaises(ValueError):candidate.exact_audit_artifact_classification([row,row])
    def test_lean_only_rows_require_no_artifact_fallback(self):
        rows=[r for r in self.policy['additional_exact_paths'] if r['file']['path'].endswith('.lean')]
        self.assertIsNone(candidate.exact_audit_artifact_classification(rows))
        self.remove_artifact_rule();classes=deepcopy(self.raw['file_classes'])
        self.assertEqual(candidate.project_exact_audit_artifact_classification(classes,rows,None),classes)
        classes['rules'].append(deepcopy(self.artifact_policy()))
        with self.assertRaises(ValueError):candidate.project_exact_audit_artifact_classification(classes,rows,None)
    def test_nonlean_fallback_never_matches_lean_subject(self):
        pattern=self.artifact_rule()['pattern']
        for row in self.policy['additional_exact_paths']:
            if row['file']['path'].endswith('.lean'):self.assertIsNone(re.search(pattern,row['file']['path']))

class OriginalPlannedLockClassificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ExactSubjectFixture.setUpClass()
    check=V2ExactPolicyTests.check
    reject=V2ExactPolicyTests.reject
    reanchor_fixture=V2ExactPolicyTests.reanchor_fixture
    artifact_policy=MixedArtifactClassificationTests.artifact_policy
    artifact_rule=MixedArtifactClassificationTests.artifact_rule
    remove_artifact_rule=MixedArtifactClassificationTests.remove_artifact_rule
    change_both_artifact_rules=MixedArtifactClassificationTests.change_both_artifact_rules
    def setUp(self):
        MixedArtifactClassificationTests.setUp(self)
        self.lock=candidate.FOLDER+'python-checks.lock'

    def lock_policy(self):return self.policy['original_planned_artifact_file_class']
    def lock_rule(self):
        return next(r for r in self.raw['file_classes']['rules'] if r['id']==self.lock_policy()['id'])
    def remove_lock_rule(self):
        identity=candidate.original_planned_lock_classification()['id']
        self.raw['file_classes']['rules']=[r for r in self.raw['file_classes']['rules'] if r['id']!=identity]
    def change_both_lock_rules(self,**fields):
        actual=self.lock_rule();self.lock_policy().update(fields);actual.update(fields);self.reanchor_fixture()

    def test_lock_literal_absolute_pattern_has_no_alias_permission(self):
        pattern=self.lock_rule()['pattern'];self.assertTrue(re.search(pattern,self.lock))
        for name in [self.lock+'\n',self.lock+'\r\n',self.lock+'.other','\n'+self.lock,
                     self.lock.replace('checks.lock','checksXlock'),self.lock.replace('python','other')]:
            self.assertIsNone(re.search(pattern,name))
        self.check()
    def test_missing_lock_policy_fails(self):
        del self.policy['original_planned_artifact_file_class'];self.reanchor_fixture();self.reject()
    def test_missing_lock_rule_fails(self):
        self.remove_lock_rule();self.reject()
    def test_wrong_lock_path_fails_even_when_policy_and_rule_rebound(self):
        self.change_both_lock_rules(pattern=r'\Aresearch/RHRC/forged\.lock\Z');self.reject()
    def test_wrong_lock_class_fails(self):
        self.change_both_lock_rules(file_class='LEAN_SOURCE');self.reject()
    def test_wrong_lock_trust_fails(self):
        self.change_both_lock_rules(trust_zone='RH_FORMAL_CORE');self.reject()
    def test_wrong_lock_position_fails(self):
        rule=deepcopy(self.lock_rule());self.remove_lock_rule()
        self.raw['file_classes']['rules'].insert(0,rule);self.reject()
    def test_duplicate_lock_rule_fails(self):
        self.raw['file_classes']['rules'].insert(-1,deepcopy(self.lock_rule()));self.reject()
    def test_lock_must_belong_to_frozen_planned_creates(self):
        classes=deepcopy(self.raw['file_classes']);classes['rules'].pop()
        with self.assertRaisesRegex(ValueError,'not an original frozen planned path'):
            candidate.project_original_planned_lock_classification(classes,self.lock_policy(),set())
    def test_unrelated_planned_lock_does_not_authorize_this_lock(self):
        classes=deepcopy(self.raw['file_classes']);classes['rules'].pop()
        with self.assertRaises(ValueError):candidate.project_original_planned_lock_classification(
            classes,self.lock_policy(),{candidate.FOLDER+'other.lock'})
    def test_actual_original_planned_lock_must_still_exist(self):
        self.raw['files']=[r for r in self.raw['files'] if r['path']!=self.lock]
        self.policy['complete_path_mode_census']=candidate.path_modes(self.raw['files'])
        self.reanchor_fixture();self.reject()
    def test_original_lock_cannot_be_relabelled_as_extra(self):
        row=deepcopy(next(r for r in self.raw['files'] if r['path']==self.lock))
        self.policy['additional_exact_paths'].append({'file':row,
            'role':'CONTINUATION_SOURCE_PINNED_EVIDENCE_OR_METADATA','theorem_authority':'NONE',
            'review_status':'OPEN_REQUIRES_INDEPENDENT_REVIEW'})
        self.reanchor_fixture();self.reject()
    def test_projection_changes_only_exact_named_lock_rule(self):
        classes=deepcopy(self.raw['file_classes']);classes['rules'].pop()
        before=deepcopy(classes)
        result=candidate.project_original_planned_lock_classification(classes,self.lock_policy(),{self.lock})
        self.assertEqual(result['rules'],before['rules'][:-1])
        self.assertEqual(classes,before)
        self.assertEqual({k:v for k,v in result.items() if k!='rules'},
                         {k:v for k,v in before.items() if k!='rules'})
    def test_lean_only_fixture_has_lock_last_and_no_extra_artifact_rule(self):
        paths={r['file']['path'] for r in self.policy['additional_exact_paths'] if not r['file']['path'].endswith('.lean')}
        self.raw['files']=[r for r in self.raw['files'] if r['path'] not in paths]
        self.policy['additional_exact_paths']=[r for r in self.policy['additional_exact_paths'] if r['file']['path'] not in paths]
        self.policy['complete_path_mode_census']=candidate.path_modes(self.raw['files'])
        self.policy['additional_audit_artifact_file_class']=None
        self.remove_artifact_rule();self.reanchor_fixture()
        self.assertEqual(self.raw['file_classes']['rules'][-1],self.lock_rule())
        self.assertEqual(dict(candidate.project(self.check()))['file_classes'],self.old['file_classes'])

if __name__=='__main__':
    unittest.main(verbosity=2)
