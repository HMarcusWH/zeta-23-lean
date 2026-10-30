from copy import deepcopy
from pathlib import Path
from dataclasses import replace
import tempfile,hashlib,json,unittest,os,zipfile,subprocess
from types import SimpleNamespace
from unittest.mock import patch
from research.RHRC.integration.opica_composition.accept import (
 ROUND4_LANES,verify_gate_inventory,verify_lane_bundle,accept_application_scope,require_native_receipt,
 preserve_scientific_disposition)
from research.RHRC.integration.opica_composition.canonical import ContractError,canonical_bytes
from research.RHRC.integration.opica_composition.cache_owner import CacheWriterLease
from research.RHRC.integration.opica_composition.closure import evaluate_closure

class AcceptanceTests(unittest.TestCase):
    def setUp(self):self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)
    def tearDown(self):self.tmp.cleanup()
    def lane(self,scope='CURRENT_HOST'):
        raw=b'{"fixture":"raw-regression-record"}';(self.root/'raw.json').write_bytes(raw)
        expected={'id':'CONTRACT','scope':scope,'checked':{'commit':'a'*40,'tree':'b'*40,'environment':'c'*64}}
        exp={'run_id':'fixture','attempt':1,'requested_commit':'d'*40,'requested_tree':'e'*40,'profile_digest':'f'*64}
        record={'schema':'OPICA4_LANE_BUNDLE_V1','lane_id':'CONTRACT','scope':scope,'experiment':exp,
                'checked':expected['checked'],'conclusion':'success',
                'artifacts':[{'path':'raw.json','bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}],
                'records':['raw.json']}
        self.write(record);return expected,exp,record
    def write(self,row):(self.root/'lane.json').write_bytes(canonical_bytes(row))
    def replay(self,*args):return args[2]['raw.json'].read_bytes()==b'{"fixture":"raw-regression-record"}'
    def test_t64(self):
        leaf={'id':'terminal','kind':'LEAF','proposition':'actual source signed bound','source':'actualzeta',
              'witness':'same','quantifiers':['forall L'],'consumers':[],'status':'OPEN','next_test':'joint error budget'}
        self.assertEqual(evaluate_closure([leaf],'terminal',verified_leaves={})['Step4'],'OPEN')
    def test_t65(self):
        e,x,r=self.lane();r['conclusion']='skipped';self.write(r)
        with self.assertRaises(ContractError):verify_lane_bundle(e,self.root,experiment=x,replay=self.replay)
    def test_t66(self):
        e,x,r=self.lane()
        with self.assertRaises(ContractError):verify_lane_bundle(e,self.root,experiment=x,replay=lambda *_:False)
    def test_t67(self):
        from research.RHRC.integration.opica_composition.descendant import current_compatibility_scope
        with self.assertRaises(ContractError):current_compatibility_scope({'scope':'FROZEN_BASELINE','checked_commit':'a','checked_tree':'b'},'a','b')
    def test_t68(self):
        from research.RHRC.integration.opica_composition.proposals import validate_plan
        for p in ({'tag':'shell','command':'curl https://example.invalid'}, {'tag':'const','constant_id':'a'*64,'run_cmd':'arbitrary'}):
            with self.assertRaises(ContractError):validate_plan(p)
    def test_t69(self):
        with CacheWriterLease(self.root/'cache'):
            with self.assertRaises(ValueError):
                with CacheWriterLease(self.root/'cache'):pass
        with CacheWriterLease(self.root/'cache'):pass
    def test_t70(self):
        a={'source':'same','case':'mixedresidues','scientific_status':'FALSIFIED'}
        self.assertEqual(preserve_scientific_disposition(a,a),'PRESERVED_FALSIFIED')
    def test_t71(self):
        needs={k:'success' for k in ROUND4_LANES};needs['COMPOSITION_FORMAL']='in_progress'
        with self.assertRaises(ContractError):accept_application_scope([{'id':k} for k in ROUND4_LANES],
            {k:self.root for k in ROUND4_LANES},experiment={},checkers={k:lambda *_:True for k in ROUND4_LANES},required_needs=needs)
    def test_t72(self):
        from research.RHRC.integration.opica_composition.baseline import require_unchanged
        with self.assertRaises(ContractError):require_unchanged(b'old provider authority',b'new erases old','FRAMEWORK_REGISTRY.json')
    def test_t87(self):
        e,x,r=self.lane('SELECTED_PROVIDER')
        self.assertNotEqual(e['checked']['commit'],x['requested_commit'])
        self.assertEqual(verify_lane_bundle(e,self.root,experiment=x,replay=self.replay)['scope'],'SELECTED_PROVIDER')
    def test_t88(self):
        e,x,r=self.lane();self.assertEqual(verify_lane_bundle(e,self.root,experiment=x,replay=self.replay)['id'],'CONTRACT')
        y={**x,'attempt':2}
        with self.assertRaises(ContractError):verify_lane_bundle(e,self.root,experiment=y,replay=self.replay)
    def test_t94(self):
        from research.RHRC.integration.opica_composition.descendant import validate_classification_extension,exact_rule
        base={'rules':[{'id':'original','pattern':'original'}]};new=exact_rule('new',['exact.py'],'RESEARCH_EXECUTABLE','AUDIT_ONLY')
        with self.assertRaises(ContractError):validate_classification_extension({'rules':[new]},base,[new])
    def test_t97(self):
        from research.RHRC.integration.opica_composition.contracts import WorkerConfig
        from research.RHRC.integration.opica_composition.executor import worker_capability
        w=WorkerConfig(str(self.root/'MISSINGLEAN'),str(self.root),[str(self.root)],production=False)
        with self.assertRaises(ContractError):worker_capability(w)
    def test_t98(self):
        (self.root/'Uncompiled.lean.in').write_text('example : True := True.intro')
        with self.assertRaises(ContractError):require_native_receipt({'exit_code':0,'native_executed':False,'compiled_object':None})
    def test_t100(self):
        from research.RHRC.integration.opica_composition.historical import preserve_dispositions
        original=[{'id':str(i),'status':'OPEN' if i%2 else 'FALSIFIED'} for i in range(17)]
        with self.assertRaises(ContractError):preserve_dispositions(original,[{'id':str(i),'status':'PROVED'} for i in range(17)])
    def test_t105(self):
        for ids in ([*ROUND4_LANES,'ACCEPTANCE'],list(ROUND4_LANES)[1:]):
            with self.assertRaises(ContractError):verify_gate_inventory(ids)
    def test_t115(self):
        with self.assertRaises(ContractError):verify_gate_inventory(['contract','runtime-regressions','current-formal','source-evaluator'])
    def test_raw_file_mutation_rejected(self):
        e,x,r=self.lane();(self.root/'raw.json').write_bytes(b'forged')
        with self.assertRaises(ContractError):verify_lane_bundle(e,self.root,experiment=x,replay=self.replay)

    def _group_fixture(self):
        from research.RHRC.integration.opica_composition.accept import REPLAY_GROUP_IDS,group_lanes,verify_independent_group
        exp={'run_id':'40992527737','attempt':1,'requested_commit':'a'*40,
             'requested_tree':'b'*40,'profile_digest':'c'*64}
        requirements=[];roots={};originals={};calls=[]
        for lane in ROUND4_LANES:
            expected={'id':lane,'scope':'PROTOCOL_FIXTURE_ONLY','checked':{'commit':'a'*40,'tree':'b'*40}}
            requirements.append(expected);root=self.root/lane;root.mkdir();roots[lane]=root
            raw=canonical_bytes({'protocol_fixture':lane});(root/'raw.json').write_bytes(raw)
            row={'schema':'OPICA4_LANE_BUNDLE_V1','lane_id':lane,'scope':expected['scope'],
                 'experiment':deepcopy(exp),'checked':expected['checked'],'conclusion':'success',
                 'artifacts':[{'path':'raw.json','bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}],
                 'records':['raw.json']}
            (root/'lane.json').write_bytes(canonical_bytes(row));originals[lane]=row
        def replay(expected,record,files):
            calls.append(expected['id'])
            return files['raw.json'].read_bytes()==canonical_bytes({'protocol_fixture':expected['id']})
        groups=[verify_independent_group(group,requirements,{k:roots[k] for k in group_lanes(group)},
                  experiment=exp,checkers={k:replay for k in group_lanes(group)},
                  required_needs={'lanes':'success'}) for group in REPLAY_GROUP_IDS]
        return requirements,roots,originals,exp,groups,replay,calls

    def test_fixed_replay_groups_preserve_complete_original_lane_results(self):
        from research.RHRC.integration.opica_composition.accept import REPLAY_GROUP_IDS,group_lanes,join_independent_groups
        requirements,roots,originals,exp,groups,replay,calls=self._group_fixture()
        self.assertEqual(len(calls),11);self.assertEqual(set(calls),set(ROUND4_LANES))
        self.assertEqual(set().union(*(set(group_lanes(k)) for k in REPLAY_GROUP_IDS)),set(ROUND4_LANES))
        result=join_independent_groups(requirements,originals,groups,experiment=exp,
                                     required_needs={'lanes':'success','independent':'success'})
        old=accept_application_scope(requirements,roots,experiment=exp,
              checkers={k:replay for k in ROUND4_LANES},required_needs={k:'success' for k in ROUND4_LANES})
        self.assertEqual(result['independently_reconstructed_lanes'],old['independently_reconstructed_lanes'])
        self.assertEqual(len(result['independent_groups']),3)
        self.assertEqual(result['RH'],result['Step4']);self.assertEqual(result['Step4'],'OPEN')

    def test_replay_group_join_rejects_missing_duplicate_or_summary_only_evidence(self):
        from research.RHRC.integration.opica_composition.accept import join_independent_groups
        requirements,_,originals,exp,groups,_,_=self._group_fixture()
        mutations=[lambda x:x.pop(),lambda x:x.append(deepcopy(x[0])),lambda x:x.reverse(),
            lambda x:x.__setitem__(1,deepcopy(x[0])),lambda x:x[0].update({'status':'PASS'}),
            lambda x:x[0].update({'conclusion':'skipped'}),
            lambda x:x[0]['independently_reconstructed_lanes'].pop(),
            lambda x:x[0].__setitem__('independently_reconstructed_lanes',[{'status':'PASS'}])]
        for mutate in mutations:
            bad=deepcopy(groups);mutate(bad)
            with self.subTest(bad=bad[0].get('group_id') if bad else 'missing'),self.assertRaises(ContractError):
                join_independent_groups(requirements,originals,bad,experiment=exp,
                                        required_needs={'lanes':'success','independent':'success'})

    def test_replay_group_join_rejects_every_stale_identity_and_changed_producer(self):
        from research.RHRC.integration.opica_composition.accept import join_independent_groups
        requirements,_,originals,exp,groups,_,_=self._group_fixture()
        for key,value in [('run_id','OTHER'),('attempt',2),('requested_commit','d'*40),
                          ('requested_tree','d'*40),('profile_digest','d'*64)]:
            bad=deepcopy(groups);bad[0]['experiment'][key]=value
            with self.subTest(identity=key),self.assertRaises(ContractError):
                join_independent_groups(requirements,originals,bad,experiment=exp,
                                        required_needs={'lanes':'success','independent':'success'})
        for key,value in [('conclusion','skipped'),('scope','OTHER'),('checked',{'commit':'d'*40}),('records',[])]:
            bad=deepcopy(originals);bad['CONTRACT'][key]=value
            with self.subTest(producer=key),self.assertRaises(ContractError):
                join_independent_groups(requirements,bad,groups,experiment=exp,
                                        required_needs={'lanes':'success','independent':'success'})
        bad=deepcopy(originals);bad['CONTRACT']['artifacts'][0]['sha256']='d'*64
        with self.assertRaises(ContractError):
            join_independent_groups(requirements,bad,groups,experiment=exp,
                                    required_needs={'lanes':'success','independent':'success'})

    def test_replay_group_join_requires_both_trusted_workflow_matrices(self):
        from research.RHRC.integration.opica_composition.accept import join_independent_groups
        requirements,_,originals,exp,groups,_,_=self._group_fixture()
        for needs in ({'lanes':'success'},{'lanes':'success','independent':'in_progress'},
                      {'lanes':'cancelled','independent':'success'},
                      {'lanes':'success','independent':'success','extra':'success'}):
            with self.subTest(needs=needs),self.assertRaises(ContractError):
                join_independent_groups(requirements,originals,groups,experiment=exp,required_needs=needs)

    def test_group_replay_runs_real_callbacks_and_preserves_primary_failure(self):
        from research.RHRC.integration.opica_composition.accept import group_lanes,verify_independent_group
        requirements,roots,_,exp,_,_,_=self._group_fixture();members=group_lanes('CORE')
        primary=RuntimeError('actual independent protocol replay failed')
        def failed(*_):raise primary
        with self.assertRaises(RuntimeError) as observed:
            verify_independent_group('CORE',requirements,{k:roots[k] for k in members},experiment=exp,
                checkers={k:failed for k in members},required_needs={'lanes':'success'})
        self.assertIs(observed.exception,primary)
        with self.assertRaises(ContractError):
            verify_independent_group('CORE',requirements,{k:roots[k] for k in members},experiment=exp,
                checkers={k:lambda *_:False for k in members},required_needs={'lanes':'success'})

    def test_group_replay_cannot_accept_mutated_raw_bytes_or_missing_lane(self):
        from research.RHRC.integration.opica_composition.accept import group_lanes,verify_independent_group
        requirements,roots,_,exp,_,replay,_=self._group_fixture();members=group_lanes('CORE')
        (roots['CONTRACT']/'raw.json').write_bytes(b'mutated')
        with self.assertRaises(ContractError):
            verify_independent_group('CORE',requirements,{k:roots[k] for k in members},experiment=exp,
                checkers={k:replay for k in members},required_needs={'lanes':'success'})
        with self.assertRaises(ContractError):
            verify_independent_group('CORE',requirements,{k:roots[k] for k in members[1:]},experiment=exp,
                checkers={k:replay for k in members},required_needs={'lanes':'success'})

    def test_independent_native_scopes_retire_each_lane_and_keep_complete_transport(self):
        from research.RHRC.integration.opica_composition import cli,snapshot
        repo=Path(__file__).resolve().parents[5]
        native=self.root/'native';native.mkdir();(native/'bootstrap').mkdir()
        (native/'bootstrap/worker.json').write_bytes(b'bootstrap fixture remains resident')
        exp={'run_id':'123456','attempt':1,'requested_commit':'a'*40,
             'requested_tree':'b'*40,'profile_digest':'c'*64}
        # This portable storage-lifecycle fixture replaces only Linux storage
        # admission. Every seal, copy, ZIP, extraction and retirement is real;
        # no mathematical checker executes or supplies a simulated PASS.
        with patch.dict(os.environ,{'OPICA_NATIVE_OUTPUT':str(native),'OPICA_ACCEPTANCE_DIAGNOSTICS':'0'}), \
                patch.object(cli,'_independent_native_parent',return_value=native):
            for lane in ('CURRENT_COMPATIBILITY','COMPOSITION_FORMAL'):
                with self.subTest(lane=lane):
                    output=self.root/'acceptance'/lane;output.mkdir(parents=True)
                    self.assertEqual({p.name for p in native.iterdir()},{'bootstrap'})
                    with cli._independent_native_scope(lane,repo,output,exp):
                        scratch=Path(os.environ['OPICA_NATIVE_OUTPUT'])
                        self.assertEqual(scratch.parent,native)
                        (scratch/'empty/nested').mkdir(parents=True);(scratch/'.hidden').mkdir()
                        (scratch/'.hidden/.raw').write_bytes(b'COMPLETE_RAW_FIXTURE')
                        (scratch/'object.bin').write_bytes(b'\x00\xffowned evidence')
                        expected=snapshot.seal_evidence_tree(scratch)[0]
                    self.assertEqual(os.environ['OPICA_NATIVE_OUTPUT'],str(native))
                    self.assertFalse(scratch.exists())
                    self.assertEqual({p.name for p in native.iterdir()},{'bootstrap'})
                    record=json.loads((output/'independent-native-archive.json').read_bytes())
                    self.assertEqual(record['complete_inventory'],expected)
                    self.assertEqual(record['experiment'],exp);self.assertIs(record['scratch_retired'],True)
                    transport=output/'independent-native-transport'
                    with zipfile.ZipFile(transport/'bundle.zip') as archive:
                        self.assertIn('empty/nested/',archive.namelist())
                        self.assertEqual(archive.read('.hidden/.raw'),b'COMPLETE_RAW_FIXTURE')
                        self.assertEqual(archive.read('object.bin'),b'\x00\xffowned evidence')
                    restored=self.root/('restored-'+lane)
                    envelope=snapshot.unpack_evidence_bundle(transport,restored,{'lane_id':lane,'experiment':exp})
                    self.assertEqual(envelope,record['transport'])
                    self.assertEqual(snapshot.seal_evidence_tree(restored)[0],expected)
                    self.assertEqual((native/'bootstrap/worker.json').read_bytes(),b'bootstrap fixture remains resident')
            self.assertFalse((self.root/'acceptance/acceptance.json').exists())

    def test_independent_native_scope_failure_preserves_primary_exception_and_evidence(self):
        from research.RHRC.integration.opica_composition import cli
        repo=Path(__file__).resolve().parents[5]
        native=self.root/'native';native.mkdir();(native/'bootstrap').mkdir()
        (native/'bootstrap/worker.json').write_bytes(b'preserve bootstrap')
        output=self.root/'acceptance/failed';output.mkdir(parents=True)
        exp={'run_id':'123456','attempt':1,'requested_commit':'a'*40,
             'requested_tree':'b'*40,'profile_digest':'c'*64}
        primary=RuntimeError('primary native replay failure')
        with patch.dict(os.environ,{'OPICA_NATIVE_OUTPUT':str(native),'OPICA_ACCEPTANCE_DIAGNOSTICS':'0'}), \
                patch.object(cli,'_independent_native_parent',return_value=native), \
                patch.object(cli,'_collect_failed_native_diagnostics',side_effect=KeyboardInterrupt('diagnostic failure')), \
                patch.object(cli,'copy_evidence_tree',side_effect=AssertionError('failed replay must not archive')) as copied:
            with self.assertRaises(RuntimeError) as observed:
                with cli._independent_native_scope('COMPOSITION_FORMAL',repo,output,exp):
                    scratch=Path(os.environ['OPICA_NATIVE_OUTPUT'])
                    (scratch/'failure.log').write_bytes(b'preserve failed evidence')
                    raise primary
            self.assertIs(observed.exception,primary);copied.assert_not_called()
            self.assertEqual(os.environ['OPICA_NATIVE_OUTPUT'],str(native))
            self.assertEqual((scratch/'failure.log').read_bytes(),b'preserve failed evidence')
        self.assertEqual((native/'bootstrap/worker.json').read_bytes(),b'preserve bootstrap')
        self.assertFalse((output/'independent-native-archive.json').exists())
        self.assertFalse((output/'independent-native-transport').exists())
        self.assertFalse((self.root/'acceptance/acceptance.json').exists())

        for phase in ('copy_evidence_tree', 'pack_evidence_bundle', 'retire_copied_evidence_tree'):
            with self.subTest(phase=phase):
                failed_output=self.root/'acceptance'/('failed-'+phase);failed_output.mkdir()
                failure=RuntimeError('archive boundary failed: '+phase)
                with patch.dict(os.environ,{'OPICA_NATIVE_OUTPUT':str(native)}), \
                        patch.object(cli,'_independent_native_parent',return_value=native), \
                        patch.object(cli,phase,side_effect=failure):
                    with self.assertRaises(RuntimeError) as observed:
                        with cli._independent_native_scope('COMPOSITION_FORMAL',repo,failed_output,exp):
                            scratch=Path(os.environ['OPICA_NATIVE_OUTPUT'])
                            (scratch/'retained.raw').write_bytes(b'archive failure must preserve source')
                    self.assertIs(observed.exception,failure)
                    self.assertEqual(os.environ['OPICA_NATIVE_OUTPUT'],str(native))
                    self.assertEqual((scratch/'retained.raw').read_bytes(),b'archive failure must preserve source')
                self.assertFalse((failed_output/'independent-native-archive.json').exists())
                self.assertFalse((self.root/'acceptance/acceptance.json').exists())

    def test_missing_bundle_aggregate_restores_diagnostic_environment_without_acceptance(self):
        from research.RHRC.integration.opica_composition import cli
        repo=Path(__file__).resolve().parents[5]
        exp={'run_id':'123456','attempt':1,'requested_commit':'a'*40,
             'requested_tree':'b'*40,'profile_digest':'c'*64}
        for prior in (None,'prior-value'):
            with self.subTest(prior=prior),patch.dict(os.environ):
                if prior is None:os.environ.pop('OPICA_ACCEPTANCE_DIAGNOSTICS',None)
                else:os.environ['OPICA_ACCEPTANCE_DIAGNOSTICS']=prior
                output=self.root/('failed-aggregate-'+str(prior))
                with self.assertRaises(FileNotFoundError):
                    cli.aggregate(repo,self.root/'missing-bundles',output,exp)
                self.assertEqual(os.environ.get('OPICA_ACCEPTANCE_DIAGNOSTICS'),prior)
                self.assertFalse((output/'acceptance.json').exists())

    def test_independent_native_storage_admission_rejects_resident_archive_filesystems(self):
        from research.RHRC.integration.opica_composition import cli
        repo=Path(__file__).resolve().parents[5]
        native=self.root/'native';native.mkdir();(native/'bootstrap').mkdir()
        (native/'bootstrap/worker.json').write_bytes(b'preserve bootstrap')
        output=self.root/'acceptance/lane';output.mkdir(parents=True)
        exp={'run_id':'123456','attempt':1,'requested_commit':'a'*40,
             'requested_tree':'b'*40,'profile_digest':'c'*64}
        original_stat=os.stat
        for kind in ('same-device','archive-device','tmpfs','ramfs','empty','multiline','nonzero','malformed'):
            with self.subTest(kind=kind):
                devices={native:102 if kind=='same-device' else 101,output:102,
                         output.parent.parent:103 if kind=='archive-device' else 102}
                def observed_stat(path,*args,**kwargs):
                    info=original_stat(path,*args,**kwargs)
                    key=Path(os.path.abspath(path)) if not isinstance(path,int) else None
                    if key not in devices:return info
                    fields={name:getattr(info,name) for name in dir(info) if name.startswith('st_')}
                    return SimpleNamespace(**{**fields,'st_dev':devices[key]})
                raw={'tmpfs':b'tmpfs\n','ramfs':b'ramfs\n','empty':b'',
                     'multiline':b'ext4\nxfs\n','malformed':b'ext4 unexpected\n'}.get(kind,b'ext4\n')
                mount=subprocess.CompletedProcess([],1 if kind=='nonzero' else 0,stdout=raw,stderr=b'')
                # Worker metadata admission is a trip through the storage guard,
                # never an execution receipt or a substituted proof checker.
                with patch.dict(os.environ,{'OPICA_NATIVE_OUTPUT':str(native)}), \
                        patch.object(cli,'worker_from_environment',return_value=None), \
                        patch.object(cli.sys,'platform','linux'),patch.object(os,'stat',side_effect=observed_stat), \
                        patch.object(cli.subprocess,'run',return_value=mount), \
                        patch.object(cli,'copy_evidence_tree',side_effect=AssertionError('storage admission must reject before copy')) as copied:
                    with self.assertRaises(ContractError):
                        with cli._independent_native_scope('COMPOSITION_FORMAL',repo,output,exp):
                            self.fail('Rejected storage must not enter the replay body')
                    copied.assert_not_called()
                    self.assertEqual(os.environ['OPICA_NATIVE_OUTPUT'],str(native))
                self.assertEqual({p.name for p in native.iterdir()},{'bootstrap'})
                self.assertFalse((output/'independent-native-transport').exists())
        self.assertEqual((native/'bootstrap/worker.json').read_bytes(),b'preserve bootstrap')

if __name__=='__main__':unittest.main()
