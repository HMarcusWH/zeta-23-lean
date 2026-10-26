"""Synthetic protocol fixtures test rejection mechanics, not Lean theorem authority."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(HERE))
import build_receipt as receipt
import certificate_io as io
import dependency_delta as delta
import run_checks

MODULE="Zeta23.OPICARound2.CausalProbe"
ROOT="Zeta23.OPICARound2.fixture"
PRIVATE="_private.Zeta23.OPICARound2.CausalProbe.0.helper"
DAG={"format":"LEAN_EXPR_DAG_V1","root":"0","nodes":[["sort",["zero"]]]}
QUERY={"id":"FIXTURE","full_name":ROOT,"module":MODULE,"kind":"THEOREM"}


def wire():
    encoded=json.dumps(DAG,separators=(",",":"))
    rows=["RHRC_CANDIDATE_RESULT\tFIXTURE\tRESOLVED_UNIQUE\t1\t"+ROOT+"\t"+MODULE+"\tTHEOREM\t0\tProp\t-",
        "OPICA2_DECL\t"+ROOT+"\t"+MODULE+"\tTHEOREM\t"+encoded+"\t",
        "OPICA2_PUBLIC_COUNT\t1",
        "RHKG_DEP_DECL\t"+ROOT+"\t"+MODULE+"\tTHEOREM\t0",
        "RHKG_DEP_DECL\t"+PRIVATE+"\t"+MODULE+"\tTHEOREM\t1",
        "RHKG_DEP_DECL\tReal.log\tMathlib.Analysis.SpecialFunctions.Log.Basic\tDEFINITION\t0"]
    for source,target in ((ROOT,PRIVATE),(PRIVATE,"Real.log")):
        for channel in ("TYPE","VALUE","STRUCTURE"):
            rows.append("RHKG_DEP_CHANNEL\t"+source+"\t"+channel+("\t"+target if channel=="VALUE" else ""))
    rows.append("OPICA2_COMPLETE\t1")
    return "\n".join(rows)+"\n"


class CompilerProtocolTests(unittest.TestCase):
    def parse(self,text):
        return receipt.parse_compiler_output(text,[QUERY],mathematical_modules=[MODULE])

    def test_complete_type_and_private_closure(self):
        parsed=self.parse(wire())
        self.assertEqual(len(parsed["declarations"]),1)
        self.assertEqual(len(parsed["dependencies"]),6)
        self.assertEqual(parsed["declarations"][0]["type_expression"],DAG)

    def test_missing_duplicate_truncated_and_unknown_wire_records_rejected(self):
        text=wire()
        mutations=[text.replace("OPICA2_COMPLETE\t1\n",""),text+"output after complete\n",
            text.replace("OPICA2_PUBLIC_COUNT\t1","OPICA2_PUBLIC_COUNT\t2"),
            text.replace("OPICA2_PUBLIC_COUNT\t1","OPICA2_PUBLIC_COUNT\t1\nOPICA2_PUBLIC_COUNT\t1"),
            text.replace("OPICA2_DECL\t","OPICA2_UNKNOWN\t"),
            text.replace("RHKG_DEP_CHANNEL\t"+PRIVATE+"\tTYPE\n",""),
            text.replace("RHKG_DEP_DECL\t"+PRIVATE+"\t"+MODULE+"\tTHEOREM\t1\n","")]
        for bad in mutations:
            with self.subTest(mutation=bad[:50]),self.assertRaises(ValueError):self.parse(bad)

    def test_wrong_module_kind_privacy_hash_and_axioms_rejected(self):
        text=wire()
        for bad in (text.replace("THEOREM\t0\tProp","THEOREM\t1\tProp"),
            text.replace("\tTHEOREM\t{","\tAXIOM\t{"),
            text.replace("OPICA2_DECL\t"+ROOT+"\t"+MODULE,"OPICA2_DECL\t"+ROOT+"\tZeta23.OPICARound2.Other"),
            text.replace(json.dumps(DAG,separators=(",",":"))+"\t",json.dumps(DAG,separators=(",",":"))+"\tUntrusted.oracle"),
            text.replace("\tTHEOREM\t1\n","\tAXIOM\t1\n")):
            with self.subTest(mutation=bad[:50]),self.assertRaises(ValueError):self.parse(bad)
        query={**QUERY,"expected_type_sha256":"0"*64}
        with self.assertRaises(ValueError):receipt.parse_compiler_output(text,[query],mathematical_modules=[MODULE])

    def test_no_source_only_dependency_or_modified_type_receipt(self):
        parsed=self.parse(wire())
        altered=deepcopy(parsed);altered["declarations"][0]["type_sha256"]="0"*64
        with self.assertRaises(ValueError):receipt.validate_compiler_records(altered,[QUERY],mathematical_modules=[MODULE])
        altered=deepcopy(parsed);altered["dependencies"].pop()
        with self.assertRaises(ValueError):receipt.validate_compiler_records(altered,[QUERY],mathematical_modules=[MODULE])

    def test_frozen_exporter_is_deterministic_and_data_only(self):
        plan={"mathematical_modules":[MODULE],"validation_modules":["Zeta23.OPICARound2.Validation.CausalProbe"],"roots":[QUERY]}
        a=receipt.render_exporter(receipt.REPO,plan)
        self.assertEqual(a,receipt.render_exporter(receipt.REPO,plan))
        self.assertIn(b"import Zeta23.RHRC.DeclarationDependencyExport",a)
        self.assertIn(b"OPICA2_COMPLETE",a)
        self.assertNotIn(b"OPICA_FOLLOWUP_",a)
        self.assertNotIn(b"namespace FollowupDependencyExport",a)
        for bad in ({**plan,"roots":[{**QUERY,"full_name":ROOT+'\naxiom injected : False'}]},
                    {**plan,"validation_modules":[MODULE]},
                    {**plan,"self_approved":True}):
            with self.assertRaises(ValueError):receipt.validate_query_plan(bad)

    def test_command_failure_keeps_exact_raw_logs_and_never_overwrites(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)
            argv=[sys.executable,"-c","import sys; print('actual stdout'); print('actual stderr',file=sys.stderr); sys.exit(3)"]
            result=receipt.run_command(out,argv,out,"command","a"*40,timeout=20)
            self.assertEqual(result["returncode"],3)
            self.assertEqual(result["stdout_sha256"],hashlib.sha256((out/"command.stdout.log").read_bytes()).hexdigest())
            self.assertIn(b"actual stderr",(out/"command.stderr.log").read_bytes())
            with self.assertRaises(ValueError):receipt.run_command(out,argv,out,"command","a"*40,timeout=20)

    def test_clean_source_manifest_checks_actual_blob_bytes_and_modes(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo=Path(tmp);payload=b"source\n";(repo/"source.lean").write_bytes(payload)
            blob=hashlib.sha1(b"blob 7\0"+payload).hexdigest()
            response=SimpleNamespace(stdout=("100644 blob "+blob+"\tsource.lean\0").encode())
            with patch.object(receipt.contract,"git",return_value=""),patch.object(receipt.subprocess,"run",return_value=response):
                self.assertEqual(receipt.source_manifest(repo)[0]["git_blob"],blob)
                (repo/"source.lean").write_bytes(b"changed\n")
                with self.assertRaises(ValueError):receipt.source_manifest(repo)
            with patch.object(receipt.contract,"git",return_value="?? uncommitted.lean"):
                with self.assertRaises(ValueError):receipt.source_manifest(repo)

    def test_missing_early_artifact_emits_failure_not_fake_hashes(self):
        failure=io.failure_envelope("compiler",io.InvalidCertificate("missing","No compiler export"))
        self.assertEqual(failure["artifact_hashes"],[])
        self.assertNotIn("exporter_object_sha256",failure)

    def test_ignored_source_providers_cannot_hide_behind_git_status(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo=Path(tmp);(repo/"source.lean").write_text("theorem x : True := by trivial",encoding="utf-8")
            receipt.reject_untracked_source_providers(repo,{"source.lean"})
            (repo/"ignored.py").write_text("shadow = True",encoding="utf-8")
            with self.assertRaises(ValueError):receipt.reject_untracked_source_providers(repo,{"source.lean"})
            (repo/"ignored.py").unlink()
            (repo/".lake").mkdir();(repo/".lake/cache.lean").write_text("cache",encoding="utf-8")
            receipt.reject_untracked_source_providers(repo,{"source.lean"})


class AncestryComparisonTests(unittest.TestCase):
    def setUp(self):self.parsed=receipt.parse_compiler_output(wire(),[QUERY],mathematical_modules=[MODULE])

    def test_exact_compiler_metadata_equality_only(self):
        result=delta.compare_exports(self.parsed,deepcopy(self.parsed),{ROOT})
        self.assertEqual(result["original_roots"],1)
        self.assertEqual(result["RH"],"OPEN")

    def test_private_helper_missing_channel_axiom_or_constructor_change_fails(self):
        for key in ("private","channel","axiom","constructor","root"):
            bad=deepcopy(self.parsed)
            if key=="private":bad["dependency_declarations"][1]["kind"]="AXIOM"
            elif key=="channel":bad["dependencies"].pop()
            elif key=="axiom":bad["declarations"][0]["axioms"]=["Classical.choice"]
            elif key=="constructor":bad["constructors"]={"invented":{}}
            else:bad["declarations"]=[]
            with self.subTest(key=key),self.assertRaises(ValueError):delta.compare_exports(self.parsed,bad,{ROOT})

    def test_reparsed_equality_cannot_set_fresh_ancestry_flags(self):
        def evidence(pop,commit,tree):return {"population":pop,"checked_commit":commit,"checked_tree":tree,
            "parsed":self.parsed,"root_names":[ROOT]}
        result=delta.ancestry_report(evidence(76,delta.contract.FROZEN_COMMIT,delta.contract.FROZEN_TREE),
            evidence(76,"1"*40,"2"*40),evidence(100,delta.contract.FROZEN_COMMIT,delta.contract.FROZEN_TREE),
            evidence(100,"1"*40,"2"*40),current_commit="1"*40,current_tree="2"*40)
        self.assertFalse(result["ancestor_baseline_replay"])
        self.assertFalse(result["ancestor_current_compatibility"])
        with self.assertRaises(ValueError):delta.ancestry_report(evidence(76,"0"*40,"0"*40),
            evidence(76,"1"*40,"2"*40),evidence(100,delta.contract.FROZEN_COMMIT,delta.contract.FROZEN_TREE),
            evidence(100,"1"*40,"2"*40),current_commit="1"*40,current_tree="2"*40)


if __name__=="__main__":unittest.main()
