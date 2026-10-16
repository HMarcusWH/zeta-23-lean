#!/usr/bin/env python3
"""Adversarial shard coverage controls; synthetic rows are VALIDATOR_CONTROL only."""
import copy
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch
import test_k3_resume as controls
import k3_replay_shards as S
from k3_resume_partition import current_identity,digest,write,pair,seam_source_bindings
from k3_source_revalidation import compare,function_ast


class ShardControls(unittest.TestCase):
    def setup_fixture(self,root,count=1):
        candidate,_,_=controls.FinalCheckerMutations().fixture(root)
        partition=root/"producer-partition.json";write(partition,{"control":"VALIDATOR_CONTROL"})
        data=json.loads((candidate/"manifest.json").read_text());data["partition_sha256"]=digest(partition)
        if count>1:
            spec=data["records"][0];path=candidate/spec["file"];layer=json.loads(path.read_text())
            lo,hi=Fraction(*layer["left"]),Fraction(*layer["right"])
            layer["accepted"]=[{"left":pair(lo+(hi-lo)*i/count),"right":pair(lo+(hi-lo)*(i+1)/count),"accepted":True,"method":"SECOND","evidence_type":"VALIDATOR_CONTROL"} for i in range(count)]
            write(path,layer);spec.update(intervals=count,sha256=digest(path))
        write(candidate/"manifest.json",data)
        revalidation=root/"revalidation.json";write(revalidation,{"control":"VALIDATOR_CONTROL"})
        review={"validation_source":current_identity()}
        with patch("k3_replay_shards.validate_revalidation",return_value=review):
            frozen=S.freeze(candidate,partition,revalidation)
        plan=root/"checker-partition.json";write(plan,frozen)
        return candidate,revalidation,plan,frozen,review

    def raw_receipts(self,root,candidate,plan,frozen):
        directory=root/"chunks";directory.mkdir()
        positive={"lower":[1,10],"upper":[1,5],"finite":True}
        for chunk in frozen["chunks"]:
            layer=json.loads((candidate/chunk["parent_file"]).read_text())
            rows=[{"index":i,"left":layer["accepted"][i]["left"],"right":layer["accepted"][i]["right"],"accepted":True,"a_interval":positive,"delta_interval":positive} for i in range(chunk["start"],chunk["stop"])]
            value={"chunk":chunk,"plan_sha256":digest(plan),"precision_bits":768,"verified":rows,"failed":[],"unverified":[],"complete":True,"seam_source_bindings":seam_source_bindings(),"evidence_type":"VALIDATOR_CONTROL"}
            path=directory/(chunk["id"]+".json");write(path,value)
            write(directory/("shard_manifest_"+chunk["id"]+".json"),{"plan_sha256":digest(plan),"records":[{"file":path.name,"sha256":digest(path),"id":chunk["id"]}]})
        return directory

    def mutate(self,directory,chunk,operation):
        path=directory/(chunk["id"]+".json");value=json.loads(path.read_text());operation(value);write(path,value)
        manifest=directory/("shard_manifest_"+chunk["id"]+".json")
        summary=json.loads(manifest.read_text());summary["records"][0]["sha256"]=digest(path);write(manifest,summary)

    def test_exact_512_leaf_index_partition(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,revalidation,plan,frozen,review=self.setup_fixture(root,1025)
            first=[c for c in frozen["chunks"] if c["Q"]==1 and c["parity"]=="even"]
            self.assertEqual([(c["start"],c["stop"]) for c in first],[(0,512),(512,1024),(1024,1025)])
            with patch("k3_replay_shards.validate_revalidation",return_value=review):S.validate_plan(plan,candidate,revalidation)
            frozen["chunks"][0]["stop"]-=1;write(plan,frozen)
            with patch("k3_replay_shards.validate_revalidation",return_value=review),self.assertRaisesRegex(ValueError,"omitted, duplicated or reassigned"):
                S.validate_plan(plan,candidate,revalidation)

    def test_full_synthetic_shard_integrity_and_mutations(self):
        for mutation in ("none","missing","duplicate_leaf","nonfinite","shifted_leaf","hidden_unverified"):
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
                root=Path(td);candidate,revalidation,plan,frozen,review=self.setup_fixture(root)
                directory=self.raw_receipts(root,candidate,plan,frozen);chunk=frozen["chunks"][0]
                if mutation=="missing":(directory/("shard_manifest_"+chunk["id"]+".json")).unlink()
                elif mutation=="duplicate_leaf":self.mutate(directory,chunk,lambda r:r["verified"].append(copy.deepcopy(r["verified"][0])))
                elif mutation=="nonfinite":self.mutate(directory,chunk,lambda r:r["verified"][0]["a_interval"].update(finite=False))
                elif mutation=="shifted_leaf":self.mutate(directory,chunk,lambda r:r["verified"][0].update(left=[0,1]))
                elif mutation=="hidden_unverified":self.mutate(directory,chunk,lambda r:r["unverified"].append({"index":0,"left":r["verified"][0]["left"],"right":r["verified"][0]["right"]}))
                with patch("k3_replay_shards.validate_revalidation",return_value=review):
                    if mutation=="none":
                        self.assertEqual(S.assemble(plan,candidate,revalidation,directory,root/"result/full-checker.json"),0)
                        self.assertEqual(json.loads((root/"result/full-checker.json").read_text())["complete_layers"],30)
                    elif mutation=="missing":
                        self.assertEqual(S.assemble(plan,candidate,revalidation,directory,root/"result/full-checker.json"),2)
                        result=json.loads((root/"result/full-checker.json").read_text())
                        self.assertEqual(result["unverified_tiles"],1)
                        self.assertEqual(result["missing_shards"],[chunk["id"]])
                    else:
                        with self.assertRaises(ValueError):S.assemble(plan,candidate,revalidation,directory,root/"result/full-checker.json")

    def test_canonical_input_drift_rejected(self):
        current=current_identity();previous=copy.deepcopy(current)
        previous["source_digests"][next(iter(previous["source_digests"]))]="0"*64
        with self.assertRaisesRegex(ValueError,"changed canonical SOURCE_INPUTS"):compare(previous,current)

    def test_search_source_drift_rejected(self):
        current=current_identity();previous=copy.deepcopy(current)
        previous["continuation_source_digests"]["k3_resume_search.py"]="0"*64
        with self.assertRaisesRegex(ValueError,"SECOND search changed"):compare(previous,current)

    def test_ast_comparison_detects_formula_change(self):
        a="def check(x):\n    return x*x-2\n"
        b="# Display-only comment\r\ndef check(x):\r\n    return x*x-2\r\n"
        c="def check(x):\n    return x*x+2\n"
        self.assertEqual(function_ast(a,"check"),function_ast(b,"check"))
        self.assertNotEqual(function_ast(a,"check"),function_ast(c,"check"))


if __name__=="__main__":unittest.main()
