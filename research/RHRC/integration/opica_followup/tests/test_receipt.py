"""The child must retain complete private TYPE/VALUE/STRUCTURE provenance."""
from copy import deepcopy
from contextlib import ExitStack
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('followup_receipt', HERE / 'build_receipt.py')
receipt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(receipt)


class DependencyReceiptTests(unittest.TestCase):
    def setUp(self):
        self.root = 'Zeta23.OPICAFollowup.fixture'
        self.private = '_private.Zeta23.OPICAFollowup.Fixture.0.helper'
        self.external = 'Real.log'
        module = 'Zeta23.OPICAFollowup.NormFirstTransfer'
        self.public = [{'name': self.root, 'module': module, 'kind': 'THEOREM'}]
        self.nodes = [
            {'name': self.root, 'module': module, 'kind': 'THEOREM', 'internal': False},
            {'name': self.private, 'module': module, 'kind': 'THEOREM', 'internal': True},
            {'name': self.external, 'module': 'Mathlib.Analysis.SpecialFunctions.Log.Basic',
             'kind': 'DEFINITION', 'internal': False}]
        self.channels = [{'source': source, 'channel': channel, 'targets': targets}
                         for source, value in [(self.root, self.private), (self.private, self.external)]
                         for channel, targets in [('TYPE', []), ('VALUE', [value]), ('STRUCTURE', [])]]

    def check(self):
        receipt.validate_dependency_closure(self.public, self.nodes, self.channels)

    def reject(self):
        with self.assertRaises(ValueError):
            self.check()

    def test_complete_private_closure(self):
        self.check()

    def test_private_type_channel_cannot_be_omitted(self):
        self.channels = [row for row in self.channels if not
                         (row['source'] == self.private and row['channel'] == 'TYPE')]
        self.reject()

    def test_structure_channel_cannot_be_omitted(self):
        self.channels.pop()
        self.reject()

    def test_unknown_dependency_target(self):
        self.channels[1]['targets'] = ['unexported.hiddenPremise']
        self.reject()

    def test_private_node_cannot_disappear(self):
        self.nodes.pop(1)
        self.reject()

    def test_duplicate_channel_rejected(self):
        self.channels.append(deepcopy(self.channels[0]))
        self.reject()

    def test_external_boundaries_cannot_be_fabricated_project_expansions(self):
        self.channels.append({'source': self.external, 'channel': 'TYPE', 'targets': []})
        self.reject()

    def test_unreachable_metadata_rejected(self):
        self.nodes.append({'name': 'Unrelated', 'module': '-', 'kind': 'AXIOM', 'internal': False})
        self.reject()

    def test_all_implemented_roots_remain_original_names(self):
        self.assertEqual(len(receipt.IMPLEMENTED_ROOT_NAMES), 41)
        self.assertTrue(all(name.startswith('Zeta23.OPICAFollowup.')
                            for name in receipt.IMPLEMENTED_ROOT_NAMES))


class GeneratedEquationTests(unittest.TestCase):
    def setUp(self):
        self.origin = 'Zeta23.CCM.nativeOriginalPrimeField'
        self.name = self.origin + '.eq_1'
        self.equations = {self.name: self.origin}
        self.declarations = {self.name: {'kind': 'THEOREM'}}
        self.channels = {(self.name, 'TYPE'): [self.origin]}
        self.nodes = {self.origin: ('Zeta23.CCM.OriginalSincNativeSource', 'DEFINITION', '0')}

    def check(self):
        receipt.validate_generated_equations(self.equations, self.declarations, self.channels, self.nodes)

    def test_reserved_equation_receives_complete_audit(self):
        self.check()

    def test_arbitrary_foreign_name_is_not_a_generated_equation(self):
        self.equations = {'Zeta23.CCM.hiddenPremise': self.origin}
        self.declarations['Zeta23.CCM.hiddenPremise'] = {'kind': 'THEOREM'}
        with self.assertRaises(ValueError):
            self.check()

    def test_reserved_suffix_alone_is_insufficient(self):
        self.channels[(self.name, 'TYPE')] = []
        with self.assertRaises(ValueError):
            self.check()

    def test_generated_equation_cannot_be_a_project_axiom(self):
        self.declarations[self.name]['kind'] = 'AXIOM'
        with self.assertRaises(ValueError):
            self.check()

    def test_original_definition_cannot_escape_dependency_audit(self):
        self.nodes = {}
        with self.assertRaises(ValueError):
            self.check()


class FullSourceIdentityTests(unittest.TestCase):
    def test_immutable_blob_census_and_dirty_checkout_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            payload = b'exact LF bytes\n'
            (repo/'source.lean').write_bytes(payload)
            oid = hashlib.sha1(b'blob '+str(len(payload)).encode()+b'\0'+payload).hexdigest()
            tree = ('100644 blob '+oid+'\tsource.lean\0').encode()
            with patch.object(receipt.subprocess,'check_output',side_effect=[b'',tree]):
                rows = receipt.full_source_manifest(repo)
                self.assertEqual(rows[0]['git_blob'],oid)
            with patch.object(receipt.subprocess,'check_output',return_value=b' M source.lean\n'):
                with self.assertRaisesRegex(ValueError,'clean committed'):
                    receipt.full_source_manifest(repo)
            (repo/'source.lean').write_bytes(payload.replace(b'\n',b'\r\n'))
            with patch.object(receipt.subprocess,'check_output',side_effect=[b'',tree]):
                with self.assertRaisesRegex(ValueError,'immutable tree'):
                    receipt.full_source_manifest(repo)

    def test_symlink_tree_mode_is_rejected_without_native_symlink_privilege(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(receipt.subprocess,'check_output',
                side_effect=[b'',b'120000 blob '+b'a'*40+b'\tlink\0']):
            with self.assertRaisesRegex(ValueError,'source mode'):
                receipt.full_source_manifest(Path(tmp))

    def test_synthetic_merge_requires_both_actual_parents_and_accepted_tree(self):
        head,merge,tree = 'a'*40,'b'*40,'c'*40
        parent = receipt.ACCEPTED_PARENT
        outputs = [merge.encode(),tree.encode(),(parent+' '+head).encode(),
            receipt.ACCEPTED_PARENT_TREE.encode(),parent.encode()]
        with patch.object(receipt.subprocess,'check_output',side_effect=outputs):
            result = receipt.full_checkout_identity(Path('.'),head,parent)
            self.assertEqual(result['checkout_kind'],'SYNTHETIC_MERGE')
        for parents in [head,head+' '+'d'*40,head+' '+parent+' '+'d'*40]:
            with patch.object(receipt.subprocess,'check_output',side_effect=
                    [merge.encode(),tree.encode(),parents.encode()]):
                with self.assertRaisesRegex(ValueError,'exact synthetic merge'):
                    receipt.full_checkout_identity(Path('.'),head,parent)

    def test_unverified_mathlib_directory_cannot_inherit_enclosing_git_pin(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(receipt.subprocess,'check_output') as git:
            with self.assertRaisesRegex(ValueError,'actual mathlib Git checkout'):
                receipt.verify_mathlib_checkout(Path(tmp),{'manifest':{'mathlib_commit':'a'*40}})
            git.assert_not_called()

    def test_import_headers_ignore_nested_comments_and_strings(self):
        self.assertEqual(receipt.lean_header_imports('/- outer /- inner -/ -/\n'
            'import Actual.Module -- comment\n\ndef text := "/- not a comment"\n'
            'import Not.AnActualHeader\n'),['Actual.Module'])

    def test_unsupported_cold_clone_symlinks_fail_closed_without_deleting_shared_cache(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)/'source'
            (repo/'.lake/packages').mkdir(parents=True)
            marker = repo/'.lake/packages/KEEP'
            marker.write_bytes(b'keep')
            identity = {'checked_commit':'a'*40,'checked_tree':'b'*40,
                'requested_head':'a'*40,'requested_base':receipt.ACCEPTED_PARENT}
            def run(argv,**kwargs):
                if 'clone' in argv:
                    self.assertIn('--shared',argv)
                    self.assertIn('core.autocrlf=false',argv)
                    Path(argv[-1]).mkdir()
            with patch.object(receipt,'pinned_package_cache',return_value=[]), \
                    patch.object(receipt,'full_checkout_identity',return_value=identity), \
                    patch.object(receipt,'full_source_manifest',return_value=[]), \
                    patch.object(receipt.subprocess,'run',side_effect=run), \
                    patch.object(Path,'symlink_to',side_effect=OSError('symlink privilege unavailable')):
                with self.assertRaisesRegex(OSError,'symlink privilege'):
                    receipt.cold_compiler_checkout(repo,Path(tmp),identity,[])
            self.assertEqual(marker.read_bytes(),b'keep')


class FullReceiptTests(unittest.TestCase):
    """Synthetic protocol fixtures test rejection logic, never mathematical truth.

    Git/runtime/registry side effects are mocked explicitly. Type DAG parsing,
    all100 frozen contracts, review seals, deterministic rendering, consumer
    linkage and on-disk log/object integrity use the actual implementations.
    """
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)/'repo'
        self.folder = self.repo/'research/RHRC/integration/opica_followup'
        self.folder.mkdir(parents=True)
        for name in receipt.FROZEN_FULL_INPUTS:
            (self.folder/name).write_bytes((HERE/name).read_bytes())
        self.contract = receipt.full_contract(self.repo)
        for row in self.contract['manifest']['modules']:
            if row['module'] not in self.contract['export_modules']:
                continue
            path = self.repo/row['path']
            path.parent.mkdir(parents=True,exist_ok=True)
            imports = self.contract['mathematical_modules'] if row['module']=='Zeta23.OPICAFollowup' else []
            path.write_text(''.join('import '+n+'\n' for n in imports if n!=row['module'])+
                '-- SYNTHETIC FIXTURE; NOT A PROOF\n',encoding='utf-8')
        template = self.repo/'Zeta23/RHRC/OpicaFollowupBindings.lean'
        template.parent.mkdir(parents=True,exist_ok=True)
        template.write_bytes((receipt.REPO/'Zeta23/RHRC/OpicaFollowupBindings.lean').read_bytes())
        self.expression = {'format':'LEAN_EXPR_DAG_V1','root':'0','nodes':[['sort',['zero']]]}
        self.encoded = json.dumps(self.expression,separators=(',',':'))
        self.type_sha = hashlib.sha256(self.encoded.encode()).hexdigest()
        roots, consumers = [], []
        for i,frozen in enumerate(self.contract['roots']):
            expected = receipt.VALIDATION_MODULE+'.'+frozen['expected_type_consumer']
            physical = receipt.VALIDATION_MODULE+'.synthetic_domain_'+str(i)
            roots.append({'full_name':frozen['full_name'],
                'frozen_contract_sha256':receipt.object_sha256(frozen),'type_sha256':self.type_sha,
                'expected_type_consumer':expected,'physical_or_domain_consumers':[physical],
                'review_status':'FULL_FROZEN_CLAUSES_AND_ACTUAL_DOMAINS_REVIEWED',
                'domain_review':'Synthetic validator fixture only; no domain proof.'})
            for name in [expected,physical]:
                consumers.append({'name':name,'module':receipt.VALIDATION_MODULE,
                    'path':receipt.VALIDATION_PATH,'type_sha256':self.type_sha,
                    'review_status':'INDEPENDENT_EXPLICIT_TYPE_AND_DOMAIN_REVIEWED'})
        by_name = {r['full_name']:r for r in roots}
        self.review = {'schema':receipt.FULL_REVIEW_SCHEMA,
            'status':'INDEPENDENT_EXPECTED_TYPES_AND_PHYSICAL_DOMAINS_REVIEWED',
            'scope':'FULL_100_ORIGINAL_ROOTS','primary_roots':100,'acceptance_units':28,
            'frozen_input_sha256':self.contract['input_sha256'],'RH':'OPEN','Step4':'OPEN',
            'independent_closing_inequalities':'OPEN','roots':roots,'consumers':consumers,
            'source_sha256':{row['path']:hashlib.sha256((self.repo/row['path']).read_bytes()).hexdigest()
                for row in self.contract['manifest']['modules'] if row['module'] in self.contract['export_modules']},
            'units':[{'paper_id':u['paper_id'],'frozen_contract_sha256':receipt.object_sha256(u),
                'review_status':'ALL_CLAUSES_AND_PHYSICAL_DOMAINS_REVIEWED',
                'consumers':sorted({n for root in u['required_roots'] for n in
                    [by_name[root]['expected_type_consumer'],*by_name[root]['physical_or_domain_consumers']]})}
                for u in self.contract['units']]}
        self.registry_review = {'fixture':'SYNTHETIC_NOT_COMPILER_OR_REGISTRY_AUTHORITY'}
        self.amendment = json.loads((HERE/'SOURCE_REGISTER.json').read_text(encoding='utf-8'))[
            'implementation_dependency_amendment']
        self.review['implementation_dependency_amendment_sha256'] = receipt.object_sha256(self.amendment)
        self.review['required_definitions'] = [{'original_module':row['module'],
            'full_name':'Zeta23.OPICAFollowup.'+name,'actual_module':row['module'],'kind':'DEFINITION',
            'type_sha256':self.type_sha,'review_status':'CANONICAL_DEFINITION_SEMANTICS_AND_ORIGIN_REVIEWED',
            'reason':'Synthetic canonical-origin fixture, not semantic proof.','relocation_amendment_id':None}
            for row in self.contract['manifest']['modules'] if row['module'] in self.contract['mathematical_modules']
            for name in row.get('required_definitions',[])]
        self.table = {r['full_name']:self.type_sha for r in roots}
        self.review['accepted_registry_extension_sha256'] = receipt.object_sha256(self.registry_review)
        self.review['registered_type_table_sha256'] = receipt.object_sha256(self.table)
        self.write_review()
        self.seal = patch.object(receipt,'FULL_REVIEW_SHA256',receipt.object_sha256(self.review))
        self.seal.start()
        self.addCleanup(self.seal.stop)
        self.reviewed = receipt.reviewed_full_contract(self.repo,self.contract)
        self.artifacts = Path(self.tmp.name)/'artifacts'
        self.artifacts.mkdir()
        self.driver = receipt.render_full_exporter(self.repo,self.contract,self.reviewed)
        (self.artifacts/'FullOpicaFollowupExport.lean').write_bytes(self.driver)
        (self.artifacts/'FullOpicaFollowupExport.olean').write_bytes(b'SYNTHETIC_NOT_COMPILED')
        self.wire = self.make_wire()
        parsed = receipt.parse_compiler_output(self.wire,self.reviewed['queries'],
            mathematical_modules=self.contract['export_modules'])
        self.identity = {'requested_head':'a'*40,'requested_base':receipt.ACCEPTED_PARENT,
            'checked_commit':'a'*40,'checked_tree':'b'*40,'checkout_kind':'PR_HEAD'}
        self.sources = [{'path':'SYNTHETIC_SOURCE_CENSUS_NOT_GIT','sha256':'c'*64}]
        self.package_pins = [{'name':'mathlib','commit':'d'*40,'tree':'e'*40}]
        self.mapped = {r['full_name']:[] for r in roots}
        self.projection = {'status':'SYNTHETIC_PROJECTION_NOT_ACCEPTANCE'}
        logs = {'lean-version.log':'Lean (version 4.33.0-rc2, commit '+receipt.COMPILER_COMMIT+')\n',
            'build.log':'SYNTHETIC BUILD\n','bindings.log':self.wire}
        commands = []
        for argv,log in receipt.full_commands(self.contract):
            payload = logs[log].encode()
            (self.artifacts/log).write_bytes(payload)
            commands.append({'argv':argv,'log':log,'exit_code':0,'seconds':0.01,
                'log_sha256':hashlib.sha256(payload).hexdigest()})
        self.data = {'schema':receipt.FULL_RECEIPT_SCHEMA,'status':'COMPILER_VERIFIED_FULL_100',
            **self.identity,'original_primary_count':100,'acceptance_units':28,
            'working_tree_dirty':False,'release_ready':False,'full_release_accepted':False,
            'RH':'OPEN','Step4':'OPEN','independent_closing_inequalities':'OPEN',
            'independent_human_review':'NOT_ESTABLISHED','source_manifest':self.sources,
            'source_manifest_sha256':receipt.object_sha256(self.sources),
            'compiler_isolation':receipt.expected_isolation(self.identity,self.sources,self.package_pins),
            'frozen_input_sha256':self.contract['input_sha256'],
            'full_review_sha256':receipt.object_sha256(self.review),
            'original_primary_roots':[r['full_name'] for r in roots],
            'consumer_queries':self.reviewed['consumer_queries'],
            'required_definition_inventory':self.reviewed['required_definitions'],
            'query_inventory_sha256':receipt.object_sha256(self.reviewed['queries']),
            'export_modules':self.contract['export_modules'],
            'exporter_template_sha256':receipt.FULL_TEMPLATE_SHA256,
            'exporter_driver_sha256':hashlib.sha256(self.driver).hexdigest(),
            'mathlib_commit':self.contract['manifest']['mathlib_commit'],
            'import_graph':receipt.full_import_graph(self.repo,self.contract),
            'lean':logs['lean-version.log'].strip(),'commands':commands,
            'compiled_export_sha256':hashlib.sha256(b'SYNTHETIC_NOT_COMPILED').hexdigest(),
            'mapped_registered_dependencies':self.mapped,'registry_projection':self.projection,**parsed}
        self.stack = ExitStack()
        self.addCleanup(self.stack.close)
        for name,result in [('full_checkout_identity',self.identity),('full_source_manifest',self.sources),
                ('verify_mathlib_checkout',self.contract['manifest']['mathlib_commit']),
                ('full_registered_dependencies',self.mapped),('full_registry_projection',self.projection),
                ('pinned_package_cache',self.package_pins)]:
            self.stack.enter_context(patch.object(receipt,name,return_value=result))

    def write_review(self):
        (self.folder/'SOURCE_REGISTER.json').write_text(json.dumps({'full_receipt_review':self.review,
            'accepted_registry_extension':self.registry_review,
            'implementation_dependency_amendment':self.amendment}),encoding='utf-8')
        (self.folder/'WORKFLOW_CONTRACT.json').write_text(json.dumps(
            {'implemented_root_type_sha256':self.table}),encoding='utf-8')

    def make_wire(self):
        lines = []
        rows = [*self.reviewed['queries'],*({'full_name':row['full_name'],'module':row['actual_module'],
            'kind':row['kind']} for row in self.reviewed['required_definitions'])]
        for row in rows:
            lines.append('\t'.join(['OPICA_FOLLOWUP_DECL',row['full_name'],row['module'],row['kind'],self.encoded,'']))
            if 'id' in row:
                lines.append('\t'.join(['RHRC_CANDIDATE_RESULT',row['id'],'RESOLVED_UNIQUE','1',
                    row['full_name'],row['module'],row['kind'],'0','synthetic fixture type','-']))
        assigned = {name:root['full_name'] for root in self.review['roots'] for name in
            [root['expected_type_consumer'],*root['physical_or_domain_consumers']]}
        for row in rows:
            name = row['full_name']
            lines.append('\t'.join(['RHKG_DEP_DECL',name,row['module'],row['kind'],'0']))
            for channel in ['TYPE','VALUE','STRUCTURE']:
                targets = [assigned[name]] if channel=='VALUE' and name in assigned else []
                lines.append('\t'.join(['RHKG_DEP_CHANNEL',name,channel,*targets]))
        lines.extend(['OPICA_FOLLOWUP_PUBLIC_COUNT\t'+str(len(rows)),
            'OPICA_FOLLOWUP_COMPLETE\t'+str(len(rows))])
        return '\n'.join(lines)+'\n'

    def check(self):
        return receipt.validate_full_receipt_structure(self.data,self.repo,self.artifacts)

    def reject(self):
        with self.assertRaises((ValueError,KeyError,TypeError)):
            self.check()

    def test_complete_synthetic_structure_has_no_release_authority(self):
        self.assertIn('REPLAY_STILL_REQUIRED',self.check()['status'])
        self.assertFalse(self.data['release_ready'])

    def test_unset_independent_review_blocks_before_any_compiler(self):
        with patch.object(receipt,'FULL_REVIEW_SHA256',None), patch.object(receipt.subprocess,'run') as run:
            with self.assertRaisesRegex(ValueError,'review seal'):
                receipt.produce_full_receipt(self.repo,Path(self.tmp.name)/'fresh','a'*40,receipt.ACCEPTED_PARENT)
            run.assert_not_called()

    def test_self_consistent_editable_review_is_not_authority(self):
        self.review['roots'][0]['domain_review'] = 'Invented narrower domain'
        self.write_review()
        self.data['full_review_sha256'] = receipt.object_sha256(self.review)
        self.reject()

    def test_parent_and_subset_schemas_are_rejected(self):
        for schema in ['OPICA_COMPILER_RECEIPT_V1','OPICA_FOLLOWUP_SUBSET_COMPILER_RECEIPT_V1']:
            with self.subTest(schema=schema):
                self.data['schema'] = schema
                self.reject()

    def test_primary_subset_cannot_claim_full_scope(self):
        self.data['original_primary_roots'] = self.data['original_primary_roots'][:41]
        self.reject()

    def test_unreviewed_consumer_type_is_rejected(self):
        self.data['declarations'][100]['type_sha256'] = '0'*64
        self.reject()
        for wire in [self.wire.replace(self.encoded,'{"format":"TRUNCATED_PRETTY_TYPE"}',1),
                self.wire.replace(self.encoded+'\t\n',self.encoded+'\tsorryAx\n',1)]:
            with self.subTest(wire=wire[:100]), self.assertRaises(ValueError):
                receipt.parse_compiler_output(wire,self.reviewed['queries'],
                    mathematical_modules=self.contract['export_modules'])

    def test_missing_physical_consumer_is_rejected(self):
        self.data['consumer_queries'].pop()
        self.reject()

    def test_missing_or_wrong_kind_canonical_definition_is_rejected(self):
        reviewed = self.reviewed
        name = reviewed['required_definitions'][0]['full_name']
        self.assertTrue(receipt.validate_required_definitions(self.data,reviewed))
        for mode in ['missing','wrong_kind']:
            data = deepcopy(self.data)
            record = next(row for row in data['declarations'] if row['name']==name)
            if mode=='missing':
                data['declarations'].remove(record)
            else:
                record['kind'] = 'THEOREM'
            with self.subTest(mode=mode),self.assertRaisesRegex(ValueError,'canonical public definition'):
                receipt.validate_required_definitions(data,reviewed)

    def test_origin_relocation_requires_explicit_sealed_origin_review(self):
        name = self.review['required_definitions'][0]['full_name']
        record = next(row for row in self.data['declarations'] if row['name']==name)
        other = next(module for module in self.contract['mathematical_modules'] if module!=record['module'])
        record['module'] = other
        with self.assertRaisesRegex(ValueError,'reviewed origin'):
            receipt.validate_required_definitions(self.data,self.reviewed)
        entry = self.review['required_definitions'][0]
        entry['actual_module'] = other
        entry['relocation_amendment_id'] = self.amendment['id']
        entry['reason'] = 'Synthetic separately reviewed relocation, not real approval.'
        self.write_review()
        with self.assertRaisesRegex(ValueError,'independent hardcoded seal'):
            receipt.reviewed_full_contract(self.repo,self.contract)
        with patch.object(receipt,'FULL_REVIEW_SHA256',receipt.object_sha256(self.review)):
            resealed = receipt.reviewed_full_contract(self.repo,self.contract)
            self.assertTrue(receipt.validate_required_definitions(self.data,resealed))
        entry['relocation_amendment_id'] = None
        self.write_review()
        with patch.object(receipt,'FULL_REVIEW_SHA256',receipt.object_sha256(self.review)), \
                self.assertRaisesRegex(ValueError,'relocation lacks'):
            receipt.reviewed_full_contract(self.repo,self.contract)

    def test_consumer_without_real_compiler_use_is_rejected(self):
        for row in self.data['dependencies']:
            if row['source']==self.review['roots'][0]['physical_or_domain_consumers'][0]:
                row['targets'] = []
        # Keep receipt and wire self-consistent; actual linkage must still fail.
        name = self.review['roots'][0]['physical_or_domain_consumers'][0]
        wire = self.wire.replace('RHKG_DEP_CHANNEL\t'+name+'\tVALUE\t'+
            self.review['roots'][0]['full_name'],'RHKG_DEP_CHANNEL\t'+name+'\tVALUE')
        payload = wire.encode()
        (self.artifacts/'bindings.log').write_bytes(payload)
        self.data['commands'][2]['log_sha256'] = hashlib.sha256(payload).hexdigest()
        self.reject()

    def test_missing_acceptance_unit_review_is_rejected_even_if_resealed(self):
        self.review['units'].pop()
        self.write_review()
        with patch.object(receipt,'FULL_REVIEW_SHA256',receipt.object_sha256(self.review)):
            self.reject()

    def test_missing_frozen_clause_binding_is_rejected_even_if_resealed(self):
        self.review['roots'][0]['frozen_contract_sha256'] = '0'*64
        self.write_review()
        with patch.object(receipt,'FULL_REVIEW_SHA256',receipt.object_sha256(self.review)):
            self.reject()

    def test_source_changes_invalidate_review(self):
        (self.repo/receipt.VALIDATION_PATH).write_text('-- changed\n')
        self.reject()

    def test_foreign_or_injected_query_is_rejected(self):
        self.reviewed['queries'][0]['full_name'] = 'x\naxiom fake : False'
        with self.assertRaisesRegex(ValueError,'code-free'):
            receipt.render_full_exporter(self.repo,self.contract,self.reviewed)

    def test_unsealed_exporter_template_is_rejected(self):
        path = self.repo/'Zeta23/RHRC/OpicaFollowupBindings.lean'
        path.write_bytes(path.read_bytes()+b'\n-- changed')
        self.reject()

    def test_external_driver_edit_is_rejected_even_with_updated_receipt_hash(self):
        payload = self.driver+b'\naxiom falseProof : False\n'
        (self.artifacts/'FullOpicaFollowupExport.lean').write_bytes(payload)
        self.data['exporter_driver_sha256'] = hashlib.sha256(payload).hexdigest()
        self.reject()

    def test_compiler_object_and_logs_are_byte_bound(self):
        for file in ['FullOpicaFollowupExport.olean','bindings.log','build.log']:
            with self.subTest(file=file):
                path = self.artifacts/file
                before = path.read_bytes()
                path.write_bytes(before+b'changed')
                self.reject()
                path.write_bytes(before)

    def test_missing_or_failed_required_build_target_is_rejected(self):
        self.data['commands'][1]['argv'].pop()
        self.reject()

    def test_nonfinite_timing_and_boolean_exit_are_rejected(self):
        for key,value in [('seconds',float('nan')),('exit_code',False)]:
            before = deepcopy(self.data['commands'][0])
            self.data['commands'][0][key] = value
            self.reject()
            self.data['commands'][0] = before

    def test_claim_firewall_flags_cannot_promote(self):
        for key,value in [('RH','PROVED'),('Step4','CLOSED'),('release_ready',True),
                ('full_release_accepted',True),('original_primary_count',True)]:
            before = self.data[key]
            self.data[key] = value
            self.reject()
            self.data[key] = before

    def test_duplicate_completeness_and_truncated_protocol_are_rejected(self):
        for wire in [self.wire+'OPICA_FOLLOWUP_COMPLETE\t300\n',
                self.wire.rsplit('OPICA_FOLLOWUP_COMPLETE',1)[0]]:
            with self.subTest(wire=wire[-80:]), self.assertRaises(ValueError):
                receipt.parse_compiler_output(wire,self.reviewed['queries'],
                    mathematical_modules=self.contract['export_modules'])

    def test_missing_facade_edge_is_rejected(self):
        (self.repo/'Zeta23/OPICAFollowup.lean').write_text('-- empty facade\n')
        with self.assertRaisesRegex(ValueError,'facade'):
            receipt.full_import_graph(self.repo,self.contract)

    def test_commented_imports_cannot_manufacture_facade_reachability(self):
        path = self.repo/'Zeta23/OPICAFollowup.lean'
        path.write_text('/-\n'+path.read_text()+'\n-/\n')
        with self.assertRaisesRegex(ValueError,'facade'):
            receipt.full_import_graph(self.repo,self.contract)

    def test_warm_or_shared_project_cache_evidence_is_rejected(self):
        for value in [False,1]:
            self.data['compiler_isolation']['cold_project_build_initially_absent'] = value
            self.reject()

    def test_audit_import_in_mathematical_source_is_rejected(self):
        path = self.repo/self.contract['roots'][0]['path']
        path.write_text('import '+receipt.VALIDATION_MODULE+'\n')
        with self.assertRaisesRegex(ValueError,'audit-only'):
            receipt.full_import_graph(self.repo,self.contract)

    def test_safe_source_rejects_escape_and_alias_syntax(self):
        for name in ['../x','/x','C:/x','a\\b','a//b','a/./b','a/../b']:
            with self.subTest(name=name), self.assertRaises(ValueError):
                receipt.safe_source(self.repo,name)

    def test_duplicate_json_keys_are_rejected(self):
        for text in ['{"status":"PASS","status":"FAIL"}','{"seconds":NaN}']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                receipt.unique_json(text)

    def test_fresh_replay_is_mandatory_and_compared(self):
        with patch.object(receipt,'produce_full_receipt',return_value=deepcopy(self.data)) as producer:
            result = receipt.verify_full_receipt_replay(self.data,self.repo,self.artifacts,
                Path(self.tmp.name)/'fresh')
            producer.assert_called_once()
            self.assertEqual(result['status'],'FRESH_COMPILER_REPLAY_VERIFIED_FULL_100')
            self.assertFalse(result['release_ready'])
        forged = deepcopy(self.data)
        forged['declarations'][0]['type_sha256'] = '0'*64
        with patch.object(receipt,'produce_full_receipt',return_value=forged):
            with self.assertRaisesRegex(ValueError,'fresh full compiler replay differs'):
                receipt.verify_full_receipt_replay(self.data,self.repo,self.artifacts,
                    Path(self.tmp.name)/'fresh')


class ExternalExporterRootTests(unittest.TestCase):
    def test_external_exporter_and_object_are_contained_in_explicit_root(self):
        contract={'manifest':{'required_final_build_targets':['Zeta23.OPICAFollowup']}}
        argv=receipt.full_commands(contract)[-1][0]
        folder=Path('external proof artifacts').absolute()
        actual=receipt.instantiate_full_command(argv,folder,'native lake.exe')
        self.assertEqual(actual[:5],['native lake.exe','env','lean','-R',str(folder)])
        self.assertEqual(Path(actual[5]).parent,folder)
        self.assertEqual(actual[6],'-o')
        self.assertEqual(Path(actual[7]).parent,folder)
        self.assertFalse(any('@EXTERNAL_' in token for token in actual))

    def test_unrecognized_root_placeholder_fails_closed(self):
        with self.assertRaisesRegex(ValueError,'placeholder'):
            receipt.instantiate_full_command(['lake','@EXTERNAL_UNREVIEWED_ROOT@'],'.','lake')

    def test_nonlake_command_cannot_enter_full_command_mapping(self):
        with self.assertRaisesRegex(ValueError,'start with lake'):
            receipt.instantiate_full_command(['shell','-c','payload'],'.','lake')

    def test_version_and_build_protocol_are_unaffected(self):
        contract={'manifest':{'required_final_build_targets':['A','B']}}
        rows=receipt.full_commands(contract)
        self.assertEqual(rows[:2],[(['lake','env','lean','--version'],'lean-version.log'),
            (['lake','build','A','B','Zeta23.RHRC.OpicaTypeExprExport'],'build.log')])


if __name__ == '__main__':
    unittest.main()
