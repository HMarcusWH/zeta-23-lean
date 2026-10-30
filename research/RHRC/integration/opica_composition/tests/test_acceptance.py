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
