import json
from pathlib import Path
import tempfile
import unittest
from research.RHRC.integration.opica_composition.descendant import (
 classification_delta,current_compatibility_scope,require_acyclic_fingerprint,policy_body,
 validate_workflow_migration,validate_classification_extension,exact_rule,BASE,BASE_TREE)
from research.RHRC.integration.opica_composition.canonical import ContractError,canonical_bytes,digest
from research.RHRC.permansson.opica_composition import qualify_provider,PROVIDER_REPO,PROVIDER_COMMIT,PROVIDER_LEAN,SELECTED_APIS

class DescendantTests(unittest.TestCase):
    def test_t01(self):
        with self.assertRaises(ContractError):current_compatibility_scope({'scope':'CURRENT_HOST','checked_commit':'old','checked_tree':'t'},'new','t')
    def test_t02(self):
        self.assertNotEqual(digest({'definition':'old'},domain='world'),digest({'definition':'new'},domain='world'))
        with self.assertRaises(ContractError):current_compatibility_scope({'scope':'CURRENT_HOST','checked_commit':'same','checked_tree':'oldDefs'},'same','newDefs')
    def test_t03(self):
        record={'repository':PROVIDER_REPO,'commit':PROVIDER_COMMIT,'toolchain':'wrong','environment':{},
                'apis':list(SELECTED_APIS),'raw_evidence':{x:{} for x in SELECTED_APIS},'mode':'POLICY_ADAPTER_ONLY'}
        with self.assertRaises(ContractError):qualify_provider(record,expected_environment={},replay=lambda *_:True)
    def test_t04(self):
        from research.RHRC.integration.opica_composition.contracts import WorkerConfig
        with self.assertRaises(ContractError):WorkerConfig.from_dict({'schema':'OPICA_WORKER_CONFIG_V1',
            'lean':'/trusted/lean','toolchain_root':'/trusted','lean_paths':[],
            'bubblewrap':'/usr/bin/bwrap','prlimit':'/usr/bin/prlimit','production':True,
            'budget':None,'LEAN_PATH':'unapprovedCrossCompiler'})
    def test_t74(self):
        with self.assertRaises(ContractError):classification_delta({'old'},{'old','hidden.lean'},{'add':[]})
    def test_t75(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td);(p/'.github/workflows').mkdir(parents=True)
            (p/'.github/workflows/rhrc_opica_round3.yml').write_text('R4_PARENT_SCOPE_V1 '+BASE+' persist-credentials: false')
            (p/'.github/workflows/rhrc_opica_round2.yml').write_text('old selector')
            with self.assertRaises(ContractError):validate_workflow_migration(p)
    def test_t76(self):
        base={'rules':[]};wanted=exact_rule('new',['one.py'],'RESEARCH_EXECUTABLE','AUDIT_ONLY')
        with self.assertRaises(ContractError):validate_classification_extension({'rules':[{'id':'new','pattern':'^research/.*'}]},base,[wanted])
    def test_t77(self):
        with self.assertRaises(ContractError):current_compatibility_scope({'scope':'FROZEN_BASELINE','checked_commit':BASE,'checked_tree':BASE_TREE},BASE,BASE_TREE)
    def test_t85(self):
        with self.assertRaises(ContractError):require_acyclic_fingerprint({'source','view.json'},{'view.json'})
    def test_t86(self):
        # Orchestration IDs stay outside content-addressed semantic data.
        from research.RHRC.integration.opica_composition.views import semantic_projection
        a={'source':'a'*64,'claim':'x','run_id':'one'};b={**a,'run_id':'two'}
        self.assertEqual(canonical_bytes(semantic_projection(a)),canonical_bytes(semantic_projection(b)))
    def test_t103(self):
        from research.RHRC.integration.opica_composition.snapshot import check_snapshot,freeze_source_epoch,file_hash
        from research.RHRC.integration.opica_composition.contracts import ExperimentSpec
        import subprocess
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);p=root/'checker.py';p.write_bytes(b'old')
            for name in ('lean-toolchain','lakefile.toml','lake-manifest.json'):(root/name).write_bytes(b'fixture')
            def git(*args):return subprocess.check_output(['git','-C',str(root),*args],stderr=subprocess.DEVNULL,text=True).strip()
            git('init');git('add','.');git('-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','-m','source fixture')
            files={x.name:file_hash(x) for x in root.iterdir() if x.is_file()}
            spec=ExperimentSpec('FIXTURE',git('rev-parse','HEAD'),files,{},'DRAFT')
            snapshot=freeze_source_epoch(root,spec);p.write_bytes(b'changed')
            with self.assertRaises(ContractError):check_snapshot(snapshot)
    def test_t114(self):
        with self.assertRaises(ContractError):policy_body({'schema':'OPICA4_CLOSED_DESCENDANT_MANIFEST_V1','base':'unmerged','base_tree':BASE_TREE})

if __name__=='__main__':unittest.main()
