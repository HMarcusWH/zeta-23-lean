"""Actual runtime refusal boundaries; these tests confer no analytic theorem authority.

Unsupported jet/whole-line/variable-filter inputs cannot silently enter the
finite causal raw evaluator. The corresponding mathematics is checked in Lean.
"""
from copy import deepcopy
import json
import hashlib
import os
import re
import shutil
from datetime import datetime,timezone
from pathlib import Path
import subprocess
import sys
import unittest
import uuid

HERE=Path(__file__).resolve().parents[1]
REPO=HERE.parents[3]
sys.path.insert(0,str(HERE));sys.path.insert(0,str(Path(__file__).resolve().parent))
import native_evaluation as native
from certificate_io import InvalidCertificate
from test_native_evaluation import request_fixture


def execute_typed_semantic_guards(repo,registry,*,output,timeout=180):
    """Fresh positive and rejected-type Lean runs; never count missing tools as a negative result."""
    import build_receipt as compiler
    from certificate_io import canonical_sha256,loads_strict_json
    output=output.resolve();repo=repo.resolve()
    if output.is_relative_to(repo) or output.exists():
        raise InvalidCertificate('typed_control_output','Fresh external evidence directory required')
    committed_payload=subprocess.run(['git','show','HEAD:research/RHRC/integration/opica_round2/CONTROL_REGISTRY.json'],
                                     cwd=repo,capture_output=True,check=True).stdout
    committed_registry=loads_strict_json(committed_payload,16*1024*1024)
    if canonical_sha256(registry)!=canonical_sha256(committed_registry):
        raise InvalidCertificate('typed_control_registry','Fixture payload differs from the committed source registry')
    fixtures=committed_registry.get('runtime_typed_negative_fixtures')
    required={'R2M03','R2M05','R2M07','R2M08','R2M09','R2M13','R2M14'}
    if type(fixtures) is not list or {r.get('id') for r in fixtures}!=required or len(fixtures)!=7:
        raise InvalidCertificate('typed_control_scope','All seven actual typed negative fixture pairs are required')
    lake=shutil.which('lake')
    if not lake:
        raise InvalidCertificate('typed_control_runtime','Pinned Lake/Lean runtime unavailable')
    sources=compiler.source_manifest(repo)
    packages=compiler.validate_packages(repo)
    head=subprocess.run(['git','rev-parse','HEAD'],cwd=repo,capture_output=True,check=True,text=True).stdout.strip()
    tree=subprocess.run(['git','rev-parse','HEAD^{tree}'],cwd=repo,capture_output=True,check=True,text=True).stdout.strip()
    output.mkdir(parents=True)
    (output/'source-manifest.json').write_bytes((json.dumps(sources,indent=2)+'\n').encode('utf-8'))
    (output/'registry-snapshot.json').write_bytes(committed_payload)
    version_argv=[lake,'env','lean','--version']
    version=subprocess.run(version_argv,cwd=repo,capture_output=True,timeout=timeout)
    (output/'lean-version.log').write_bytes(version.stdout+version.stderr)
    if version.returncode or b'version 4.33.0-rc2,' not in version.stdout or \
            b'd8b18978322de05a8f3dba51ef03cf5461676c17' not in version.stdout:
        raise InvalidCertificate('typed_control_runtime','Wrong or failed pinned compiler')
    rows=[]
    for fixture in sorted(fixtures,key=lambda x:x['id']):
        pair=[]
        for mode in ('positive','negative'):
            source=fixture.get(mode+'_source')
            if type(source) is not str or len(source)>100_000:
                raise InvalidCertificate('typed_control_source','Bounded exact Lean fixture source required')
            path=output/(fixture['id']+'_'+mode+'.lean')
            path.write_bytes(source.encode('utf-8'))
            argv=[lake,'env','lean','-R',str(output),str(path),'-o',str(path.with_suffix('.olean'))]
            process=subprocess.run(argv,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
            log=path.with_suffix('.log');log.write_bytes(process.stdout)
            text=process.stdout.decode('utf-8',errors='strict')
            if mode=='positive':
                lists=re.findall(r'depends on axioms:\s*\[(.*?)\]',text,re.S)
                if process.returncode or (not lists and 'does not depend on any axioms' not in text) or 'sorryAx' in text:
                    raise InvalidCertificate('typed_control_positive','Actual positive typed consumer failed: '+fixture['id'])
                if any(set(part.strip() for part in row.split(',') if part.strip())-
                       {'propext','Classical.choice','Quot.sound'} for row in lists):
                    raise InvalidCertificate('typed_control_axioms','Positive control uses a nonstandard axiom')
            else:
                infrastructure=('unknown identifier','unknown constant','unknown tactic','unexpected identifier',
                                'unexpected token','invalid field','invalid dotted identifier','object file',
                                'failed to open','invalid import','unknown module','invalid projection')
                meaningful=('type mismatch','application type mismatch','unsolved goals','tactic `exact` failed',
                            'failed to synthesize','tactic `rfl` failed')
                lower=text.lower()
                if process.returncode==0 or 'error:' not in lower or any(x in lower for x in infrastructure) \
                        or not any(x in lower for x in meaningful):
                    raise InvalidCertificate('typed_control_negative','Expected semantic/type rejection was not established: '+fixture['id'])
            pair.append({'mode':mode,'argv':argv,'returncode':process.returncode,
                'source_file':path.name,'log_file':log.name,
                'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),
                'object_file':path.with_suffix('.olean').name if mode=='positive' else None,
                'object_sha256':hashlib.sha256(path.with_suffix('.olean').read_bytes()).hexdigest() if mode=='positive' else None})
        rows.append({'id':fixture['id'],'result':'POSITIVE_NATIVE_CONSUMER_AND_REJECTED_MUTANT_TYPE',
                     'scope':fixture.get('scope'),'commands':pair})
    if compiler.source_manifest(repo)!=sources or compiler.validate_packages(repo)!=packages:
        raise InvalidCertificate('typed_control_drift','Current source or pinned packages changed during controls')
    result={'schema':'OPICA2_TYPED_NEGATIVE_CONTROL_RUN_V1','optimized_python':bool(sys.flags.optimize),
            'checked_commit':head,'checked_tree':tree,'producer_artifact_root':str(output),
            'registry_sha256':hashlib.sha256(committed_payload).hexdigest(),
            'registry_canonical_sha256':canonical_sha256(committed_registry),'pinned_packages':packages,
            'version_command':{'argv':version_argv,'returncode':version.returncode,
                'log_sha256':hashlib.sha256((output/'lean-version.log').read_bytes()).hexdigest()},
            'source_manifest_sha256':compiler.canonical_sha256(sources),'controls':rows,
            'authority':'SOURCE_BOUND_NATIVE_TYPED_REJECTION_NOT_NEW_MATHEMATICAL_AUTHORITY',
            'full_core_accepted':False,'full_release_accepted':False,'RH':'OPEN','Step4':'OPEN'}
    (output/'receipt.json').write_bytes((json.dumps(result,indent=2)+'\n').encode('utf-8'))
    return result


class NativeTypedSemanticControls(unittest.TestCase):
    def test_seven_positive_and_wrong_type_native_fixtures(self):
        registry=json.loads((HERE/'CONTROL_REGISTRY.json').read_text(encoding='utf-8'))
        prefix=Path(os.environ.get('OPICA2_TYPED_CONTROL_OUTPUT',str(REPO.parent/'opica2-native-negative-controls')))
        output=prefix/(datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:8])
        result=execute_typed_semantic_guards(REPO,registry,output=output)
        self.assertEqual(len(result['controls']),7)
        self.assertFalse(result['full_release_accepted'])


class ScientificInputRefusals(unittest.TestCase):
    def refuse_override(self,key,value):
        request=request_fixture();request[key]=value
        with self.assertRaises(InvalidCertificate) as caught:
            native.evaluate_native(request,expected_source=request['source'])
        self.assertEqual(caught.exception.code,'request_fields')

    def test_R2M03_removable_zero_override_is_not_a_native_construction_input(self):
        self.refuse_override('completion_removable_half','0')

    def test_R2M07_omitted_factorial_override_cannot_enter_raw_evaluator(self):
        self.refuse_override('jet_normalization','derivative_without_factorial')

    def test_R2M08_repeated_spectral_nodes_cannot_be_claimed_independent(self):
        self.refuse_override('spectral_nodes',[{'re':'1','im':'1'},{'re':'1','im':'1'}])

    def test_R2M09_integer_history_cannot_be_relabelled_as_L2_convergence(self):
        self.refuse_override('integer_history_claim','L2_CONVERGENT')

    def test_R2M13_arbitrary_noncausal_input_cannot_omit_leakage(self):
        self.refuse_override('full_line_input',{'negative_time_energy':'0','causal':False})

    def test_R2M14_variable_filter_without_transported_margin_is_refused(self):
        self.refuse_override('varying_filter',{'N':7,'operator_norm':'1/128'})
        request=request_fixture()
        request['source']['filter_definition_sha256']='0'*64
        with self.assertRaises(InvalidCertificate):
            native.evaluate_native(request,expected_source=request['source'])

    def test_a_numerical_request_cannot_claim_RH_or_kernel_authority(self):
        self.refuse_override('RH','PROVED')
        self.refuse_override('outcome','KERNEL_CHECKED_THEOREM')

    def test_original_claim_objects_and_OPEN_caps_are_preserved(self):
        original=json.loads(subprocess.run(['git','show',
            'adab10a37207f75b9a8b415a0fe9eadca2e4c9aa:research/RHRC/CLAIM_REGISTRY.json'],
            cwd=REPO,capture_output=True,check=True).stdout)
        current=json.loads((REPO/'research/RHRC/CLAIM_REGISTRY.json').read_text(encoding='utf-8'))
        by_id={row['id']:row for row in current['claims']}
        for row in original['claims']: self.assertEqual(by_id[row['id']],row)
        self.assertEqual({r['id'] for r in current['claims'] if r['status']=='OPEN'},
                         {r['id'] for r in original['claims'] if r['status']=='OPEN'})

    def test_four_terminal_routes_remain_open_without_Lean_roots(self):
        public=json.loads((HERE/'PUBLIC_ROOTS.json').read_text(encoding='utf-8'))
        names={r.get('proposed_public_name') for r in public['roots']}
        paper=json.loads((HERE/'paper/ROUND2_V2_1.json').read_text(encoding='utf-8'))
        self.assertEqual(len(paper['terminal_targets']),4)
        for target in paper['terminal_targets']:
            self.assertNotIn(target['proposed_lean_name'],names)
        self.assertFalse(public['full_core_accepted'])
        self.assertEqual(public['RH'],'OPEN')
        self.assertEqual(public['Step4'],'OPEN')


if __name__=='__main__': unittest.main()
