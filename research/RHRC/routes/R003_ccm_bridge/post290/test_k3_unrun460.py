#!/usr/bin/env python3
"""Negative and exact-coverage controls for the approved resource extension."""
import copy,json,math,os,subprocess,tempfile,unittest,zipfile
from pathlib import Path
from unittest.mock import patch
import k3_continue_unrun460 as C

JOB={"id":"Q13_C000_P000_R00000_P0","Q":13,"parity":"even","left":[1,2],"right":[3,4],"pass":2,"parent_job":"Q13_C000_P000","parent_leaf":0,"component":0}
HASH="a"*64

class ResourceControls(unittest.TestCase):
    def test_approved_exact_resources(self):
        d=C.approval()
        self.assertEqual(d["max_search_runner_seconds"],460*1800)
        self.assertEqual(len(C.read(C.CHILDREN)["children"]),460)
        self.assertEqual(len({x["id"] for x in C.read(C.CHILDREN)["children"]}),460)
    def test_changed_budget_rejected(self):
        d=C.read(C.PROTOCOL);d["resources"]["seconds"]=1801
        with patch.object(C,"read",return_value=d),self.assertRaises(ValueError):C.approval()
    def test_changed_child_manifest_rejected(self):
        with patch.object(C,"digest",return_value="forged"),self.assertRaises(ValueError):C.approval()
    def test_workflow_retry_rejected(self):
        with self.assertRaises(ValueError):C.guard_single_use(5,2,{"workflow_runs":[{"id":5}]})
    def test_second_dispatch_rejected(self):
        with self.assertRaises(ValueError):C.guard_single_use(5,1,{"workflow_runs":[{"id":4},{"id":5}]})
    def test_incomplete_run_audit_rejected(self):
        with self.assertRaises(ValueError):C.guard_single_use(5,1,{"workflow_runs":[]})
    def test_first_dispatch_accepted(self):C.guard_single_use(5,1,[{"workflow_runs":[{"id":5}]}])
    def test_missing_result_stays_unrun(self):
        v=C.pending(JOB,HASH,"MISSING_CONTINUATION_RECEIPT")
        self.assertEqual(C.validate_result(v,JOB,HASH)["status"],"UNRESOLVED")
        self.assertTrue(v["unresolved"][0]["unrun"])
    def test_timeout_preserves_complete_pending_interval(self):
        v=C.pending(JOB,HASH,"HARD_WALL_TIMEOUT")
        self.assertEqual(C.validate_result(v,JOB,HASH)["unresolved"][0]["left"],JOB["left"])
    def test_gap_or_removed_leaf_rejected(self):
        v=C.pending(JOB,HASH,"MISSING");v["unresolved"]=[]
        v["status"]="PASS"
        with self.assertRaises(ValueError):C.validate_result(v,JOB,HASH)
    def test_widened_child_rejected(self):
        v=C.pending(JOB,HASH,"MISSING");v["unresolved"][0]["left"]=[0,1]
        with self.assertRaises(ValueError):C.validate_result(v,JOB,HASH)
    def test_wrong_resource_or_source_rejected(self):
        for key,value in [("partition_sha256","wrong"),("resources",{**C.RESOURCE,"precision_bits":1024})]:
            v=C.pending(JOB,HASH,"MISSING");v[key]=value
            with self.assertRaises(ValueError):C.validate_result(v,JOB,HASH)
    def test_negative_stop_cannot_be_positive(self):
        v=C.pending(JOB,HASH,"CERTIFIED_NEGATIVE_NATIVE_STOP");v["certified_negative_stop"]=True
        self.assertEqual(C.validate_result(v,JOB,HASH)["status"],"UNRESOLVED")
        v["accepted"]=[{**v["unresolved"][0],"accepted":True,"method":"SECOND"}];v["unresolved"]=[];v["status"]="PASS"
        with self.assertRaises(ValueError):C.validate_result(v,JOB,HASH)
    def test_nonfinite_bound_rejected(self):
        for value in ["NaN","Infinity","-Infinity"]:
            v=C.pending(JOB,HASH,"MISSING");v["diagnostic"]={"lower":value}
            with self.assertRaises(ValueError):C.validate_result(v,JOB,HASH)
    def test_nonfinite_float_rejected(self):
        v=C.pending(JOB,HASH,"MISSING");v["elapsed_seconds"]=math.nan
        with self.assertRaises(ValueError):C.validate_result(v,JOB,HASH)
    def test_boolean_node_count_rejected(self):
        v=C.pending(JOB,HASH,"MISSING");v["tested_nodes"]=True
        with self.assertRaises(ValueError):C.validate_result(v,JOB,HASH)
    def test_duplicate_budget_launch_rejected(self):
        with tempfile.TemporaryDirectory(dir=C.REPO) as t:
            p=Path(t)/"launch.json";C.exclusive(p,{"claim":"first"})
            with self.assertRaises(FileExistsError):C.exclusive(p,{"claim":"retry"})
    def test_unsafe_archive_rejected(self):
        with tempfile.TemporaryDirectory(dir=C.REPO) as t:
            t=Path(t);p=t/"bad.zip"
            with zipfile.ZipFile(p,"w") as z:z.writestr("../escape","bad")
            with patch.object(C,"digest",return_value=C.ARCHIVE_SHA),self.assertRaises(ValueError):C.extract(p,t/"extract")
    def test_workflow_scoped_bootstrap_no_budget_retry_and_max8(self):
        import yaml
        p=C.REPO/".github/workflows/rhrc_post290_unrun460.yml"
        d=yaml.load(p.read_text(encoding="utf-8"),Loader=yaml.BaseLoader)
        self.assertEqual(set(d["on"]),{"workflow_dispatch","push"})
        self.assertEqual(d["on"]["push"],{
            "branches":["research/post290-step123-output"],
            "paths":[".github/workflows/rhrc_post290_unrun460.yml"]})
        self.assertEqual(d["concurrency"]["cancel-in-progress"],"false")
        for name in ["search-wave1","search-wave2"]:
            self.assertEqual(d["jobs"][name]["strategy"]["max-parallel"],"8")
            steps=d["jobs"][name]["steps"]
            self.assertTrue(any('GITHUB_RUN_ATTEMPT' in x.get("run","") for x in steps))
            claim=next(i for i,x in enumerate(steps) if ' claim ' in x.get("run",""))
            run=next(i for i,x in enumerate(steps) if ' run ' in x.get("run","") and "plan.json" in x.get("run",""))
            self.assertLess(claim,run)
            self.assertTrue(any(x.get("if")=="always()" and x.get("uses","").startswith("actions/upload-artifact") for x in steps))
        self.assertIn("search-wave1",d["jobs"]["search-wave2"]["needs"])
        self.assertEqual(d["jobs"]["independent-check-batches"]["strategy"]["max-parallel"],"1")
    def test_scalable_checker_batches_max8(self):
        import yaml
        d=yaml.load((C.REPO/".github/workflows/rhrc_post290_unrun460_check_batch.yml").read_text(encoding="utf-8"),Loader=yaml.BaseLoader)
        self.assertEqual(d["jobs"]["check-leaves"]["strategy"]["max-parallel"],"8")
        self.assertTrue(any("k3_replay_shards.py" in x.get("run","") and " single " in x.get("run","") for x in d["jobs"]["check-leaves"]["steps"]))

    def test_hard_wall_kills_worker_and_budget_cannot_restart(self):
        class Process:
            pid=123456;returncode=None
            def poll(self):return self.returncode
            def kill(self):self.returncode=-9
            def wait(self):self.returncode=-9;return -9
        with tempfile.TemporaryDirectory(dir=C.REPO) as t:
            out=Path(t);plan=out/"plan.json";plan.write_text("{}")
            d={"run_id":7,"jobs":[{"job":JOB}]}
            C.write(out/"budget-claim.json",{"job":JOB,"plan_sha256":HASH,"run_id":7})
            C.write(out/"result.json",C.pending(JOB,HASH,"CLAIMED_NOT_STARTED"))
            process=Process()
            with patch.object(C,"validate",return_value=d),patch.object(C,"digest",return_value=HASH),patch.object(C.subprocess,"Popen",return_value=process),patch.object(C.time,"monotonic",side_effect=[0,1801,1801]),patch.object(C.os,"killpg",create=True):
                v=C.run(plan,0,out,with_upload=False)
                self.assertEqual(process.returncode,-9)
                self.assertEqual(v["unresolved"][0]["reason"],"HARD_WALL_TIMEOUT")
                with self.assertRaises(ValueError):C.run(plan,0,out,with_upload=False)

    def test_checkpoint_uploader_propagates_global_negative_stop(self):
        with tempfile.TemporaryDirectory(dir=C.REPO) as t:
            t=Path(t);module=t/"fake.cjs";file=t/"receipt.json";file.write_text("{}")
            module.write_text("class ArtifactNotFoundError extends Error {}\nclass DefaultArtifactClient {async getArtifact(){if(process.env.FAKE_STOP==='1')return {id:1};throw new ArtifactNotFoundError();} async uploadArtifact(){return {id:2};}}\nmodule.exports={DefaultArtifactClient,ArtifactNotFoundError};")
            helper=C.HERE/"k3_checkpoint_upload.cjs"
            env={**os.environ,"K3_ARTIFACT_MODULE":str(module),"FAKE_STOP":"1"}
            stop=subprocess.run(["node",str(helper),"k3-unrun460-cp-000-000",str(file)],env=env,capture_output=True)
            self.assertEqual(stop.returncode,42)
            same=subprocess.run(["node",str(helper),"k3-unrun460-negative-stop",str(file)],env=env,capture_output=True)
            self.assertEqual(same.returncode,0)
            env["FAKE_STOP"]="0"
            fresh=subprocess.run(["node",str(helper),"k3-unrun460-cp-000-000",str(file)],env=env,capture_output=True)
            self.assertEqual(fresh.returncode,0)

    def test_exact_named_recovery_preserves_all460_without_global_listing(self):
        with tempfile.TemporaryDirectory(dir=C.REPO) as t:
            t=Path(t);module=t/"fake.cjs"
            module.write_text("const fs=require('fs'),path=require('path'); class ArtifactNotFoundError extends Error {} class DefaultArtifactClient {async getArtifact(name){return {artifact:{id:2,digest:'test',name}};} async downloadArtifact(id,o){fs.mkdirSync(o.path,{recursive:true});fs.writeFileSync(path.join(o.path,'receipt.json'),'{}');}} module.exports={DefaultArtifactClient,ArtifactNotFoundError};")
            env={**os.environ,"K3_ARTIFACT_MODULE":str(module)}
            r=subprocess.run(["node",str(C.HERE/"k3_checkpoint_upload.cjs"),"recover-results",str(t/"recovered")],env=env,capture_output=True)
            self.assertEqual(r.returncode,0,r.stderr)
            result=json.loads((t/"recovered/exact-name-recovery.json").read_text())
            self.assertEqual(len(result["downloaded"]),460)
            self.assertEqual(result["missing"],[])
            self.assertEqual(len(list((t/"recovered").glob("*/receipt.json"))),460)

    def test_preflight_roundtrip_starts_no_arithmetic(self):
        with tempfile.TemporaryDirectory(dir=C.REPO) as t:
            t=Path(t);module=t/"fake.cjs"
            module.write_text("const fs=require('fs'),path=require('path'); let bytes; class ArtifactNotFoundError extends Error {} class DefaultArtifactClient {async uploadArtifact(n,files){bytes=fs.readFileSync(files[0]);return {id:2};} async getArtifact(){return {artifact:{id:2}};} async downloadArtifact(id,o){fs.mkdirSync(o.path,{recursive:true});fs.writeFileSync(path.join(o.path,'preflight.json'),bytes);}} module.exports={DefaultArtifactClient,ArtifactNotFoundError};")
            r=subprocess.run(["node",str(C.HERE/"k3_checkpoint_upload.cjs"),"preflight",str(t/"preflight")],env={**os.environ,"K3_ARTIFACT_MODULE":str(module)},capture_output=True)
            self.assertEqual(r.returncode,0,r.stderr)
            self.assertIs(json.loads((t/"preflight/preflight.json").read_text())["arithmetic_started"],False)

if __name__=="__main__":unittest.main(verbosity=2)
