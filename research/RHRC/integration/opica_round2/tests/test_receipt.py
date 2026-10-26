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

    def test_cold_recipe_builds_frozen_audit_tools_and_sets_external_root(self):
        plan={"mathematical_modules":[MODULE],"validation_modules":["Zeta23.OPICARound2.Validation.CausalProbe"],"roots":[QUERY]}
        output=Path("external-evidence").resolve()
        recipe=receipt.compiler_commands(plan,output,"lake")
        self.assertEqual([name for _,name in recipe],["lean-version","build","bindings"])
        self.assertEqual(recipe[1][0],["lake","build",MODULE,"Zeta23.OPICARound2.Validation.CausalProbe",
            "Zeta23.OPICARound2","Zeta23.OPICARound2.All","Zeta23.OPICARound2.Validation","Zeta23.RHRC.OpicaRound2Bindings",
            "Zeta23.RHRC.DeclarationDependencyExport","Zeta23.RHRC.SourceCandidateResolution","Zeta23.RHRC.OpicaTypeExprExport"])
        self.assertEqual(recipe[2][0],["lake","env","lean","-R",str(output),"-o",str(output/"Round2Export.olean"),str(output/"Round2Export.lean")])
        self.assertNotIn("Zeta23.RHRC.DeclarationDependencyExport",plan["mathematical_modules"])

    def test_relocated_artifacts_keep_exact_producer_paths_and_reject_mixed_roots(self):
        plan={"mathematical_modules":[MODULE],"validation_modules":["Zeta23.OPICARound2.Validation.CausalProbe"],"roots":[QUERY]}
        from pathlib import PurePosixPath, PureWindowsPath
        for producer in (PurePosixPath("/runner/artifacts/original"),PureWindowsPath("C:/runner/original")):
            commands=[{"argv":argv} for argv,_ in receipt.compiler_commands(plan,producer,"lake")]
            self.assertEqual(receipt.recorded_export_root(commands),producer)
            bad=deepcopy(commands);bad[2]["argv"][-1]=str(producer.parent/"different"/"Round2Export.lean")
            with self.assertRaises(ValueError):receipt.recorded_export_root(bad)
            bad=deepcopy(commands);bad[2]["argv"][3]="-R-injected"
            with self.assertRaises(ValueError):receipt.recorded_export_root(bad)
        commands=[{"argv":argv} for argv,_ in receipt.compiler_commands(plan,Path("relative"),"lake")]
        with self.assertRaises(ValueError):receipt.recorded_export_root(commands)

    def test_command_failure_keeps_exact_raw_logs_and_never_overwrites(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)
            argv=[sys.executable,"-c","import sys; print('actual stdout'); print('actual stderr',file=sys.stderr); sys.exit(3)"]
            result=receipt.run_command(out,argv,out,"command","a"*40,timeout=20)
            self.assertEqual(result["returncode"],3)
            self.assertEqual(result["stdout_sha256"],hashlib.sha256((out/"command.stdout.log").read_bytes()).hexdigest())
            self.assertIn(b"actual stderr",(out/"command.stderr.log").read_bytes())
            with self.assertRaises(ValueError):receipt.run_command(out,argv,out,"command","a"*40,timeout=20)

    def test_command_timeout_and_query_shapes_fail_with_bounded_errors(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)
            for timeout in (True,False,0,-1,86401,"20"):
                with self.subTest(timeout=timeout),self.assertRaises(ValueError):
                    receipt.run_command(out,[sys.executable,"-c","raise SystemExit(0)"],out,"never-executed","a"*40,timeout=timeout)
            self.assertEqual(list(out.iterdir()),[])
        plan={"mathematical_modules":[MODULE],"validation_modules":[],"roots":[QUERY]}
        for bad in ({**plan,"roots":[None]},{**plan,"roots":[{**QUERY,"id":[]} ]},
                    {**plan,"mathematical_modules":None}):
            with self.subTest(plan=bad),self.assertRaises(ValueError):receipt.validate_query_plan(bad)

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



class CoreCompositionBoundaryTests(unittest.TestCase):
    """Synthetic graph wiring exercises refusal rules; it is not compiler authority."""
    @classmethod
    def setUpClass(cls):
        cls.crosswalk=io.load_strict_json(HERE/"PAPER_CROSSWALK.json",16*1024*1024)
        cls.public=io.load_strict_json(HERE/"PUBLIC_ROOTS.json",16*1024*1024)
        cls.plan=io.load_strict_json(HERE/"WORKFLOW_CONTRACT.json",16*1024*1024)["compiler_query_plan"]
        cls.synthetic={"declarations":[{"name":q["full_name"],"module":q["module"],"kind":q["kind"],
            "type_sha256":"0"*64,"axioms":[]} for q in cls.plan["roots"]],"dependencies":[]}
        for binding in cls.crosswalk["component_implementation_bindings"]:
            for row in binding.get("consumer_dependency_bindings",[]):
                cls.synthetic["dependencies"].append({"source":row["declaration"],"channel":"VALUE",
                    "targets":row["required_load_bearing_declarations"]})
        classes=["EXISTING_FORMAL_OR_HISTORICAL_RESEARCH_CLASS_MATCHED_TO_AUTHORITY",
            "LEAN_EXPECTED_TYPE_AND_NATIVE_DOMAIN_CONSUMER","LEAN_NEGATIVE_FIXTURE_OR_EXPLICIT_COUNTEREXAMPLE_AS_APPROPRIATE",
            "RUNTIME_NEGATIVE_FIXTURE_NORMAL_AND_OPTIMIZED"]
        cls.controls={row["control_id"]:{"verified":True,"evidence_classes":classes}
            for row in cls.crosswalk["scoped_control_bindings"]}

    def verify(self, *, parsed=None, crosswalk=None, controls=None):
        with patch.object(receipt,"validate_compiler_records"):
            return receipt.verify_component_bindings(receipt.REPO,parsed or self.synthetic,self.plan,
                crosswalk or self.crosswalk,controls or self.controls,public=self.public)

    def test_complete_source_wiring_is_separate_from_compiler_authority(self):
        result=self.verify()
        self.assertEqual(len(result["covered_clauses"]),125)
        self.assertEqual(len(result["disabled_optional_clauses"]),18)
        self.assertEqual(result["independent_human_review"],"NOT_ESTABLISHED")
        self.assertFalse(result["full_release_accepted"])

    def test_type_edges_cannot_replace_load_bearing_proof_value_edges(self):
        parsed=deepcopy(self.synthetic)
        consumer=next(row["source"] for row in parsed["dependencies"] if row["targets"])
        for row in parsed["dependencies"]:
            if row["source"]==consumer:row["channel"]="TYPE"
        with self.assertRaises(ValueError):self.verify(parsed=parsed)

    def test_source_statement_hash_cannot_be_self_attested_by_rehashing_metadata(self):
        crosswalk=deepcopy(self.crosswalk)
        row=next(r for r in crosswalk["component_implementation_bindings"] if r.get("primary_declaration"))
        name=row["expected_type_consumers"][0]
        for key in ("literal_consumer_statements","consumer_dependency_bindings"):
            next(r for r in row[key] if r["declaration"]==name)["literal_statement_sha256"]="f"*64
        row["semantic_binding_sha256"]=io.canonical_sha256({k:row[k] for k in receipt.SEMANTIC_FIELDS})
        with self.assertRaises(ValueError):self.verify(crosswalk=crosswalk)

    def test_optional_acceptance_and_control_class_escalation_fail(self):
        crosswalk=deepcopy(self.crosswalk)
        row=next(r for r in crosswalk["component_implementation_bindings"] if r.get("status")=="OPTIONAL_DISABLED")
        row["status"]="IMPLEMENTED";row["acceptance"]=True
        with self.assertRaises(ValueError):self.verify(crosswalk=crosswalk)
        controls=deepcopy(self.controls)
        controls["R2M01"]["evidence_classes"]=["LEAN_EXPECTED_TYPE_AND_NATIVE_DOMAIN_CONSUMER"]
        with self.assertRaises(ValueError):self.verify(controls=controls)

    def test_exact_runtime_test_selection_cannot_escape_or_select_a_class(self):
        import controls as dispatch
        bindings={f"R2M{k:02d}":{"runtime_test_queries":["test_receipt.CompilerProtocolTests.test_complete_type_and_private_closure"]} for k in range(1,33)}
        inventory=dispatch.runtime_test_inventory(bindings,HERE/"tests")
        self.assertEqual(len(inventory),1)
        for query in ("test_receipt.CompilerProtocolTests","os.system.echo","../escape.Class.test_x",
                      "test_receipt.CompilerProtocolTests.test_absent"):
            bad=deepcopy(bindings);bad["R2M01"]["runtime_test_queries"]=[query]
            with self.subTest(query=query),self.assertRaises(ValueError):dispatch.runtime_test_inventory(bad,HERE/"tests")

    def test_typed_pair_reparse_rejects_infrastructure_failures_and_changed_payloads(self):
        # Deliberately synthetic bytes/logs: this tests verifier refusal mechanics,
        # and never claims that a compiler ran or that an object contains a proof.
        import controls as dispatch
        registry=io.load_strict_json(HERE/"CONTROL_REGISTRY.json",16*1024*1024)
        source_manifest=[{"path":"synthetic-only","sha256":"0"*64}]
        head,tree="1"*40,"2"*40
        producer="/original/provider/typed"
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)
            def save(name,payload):
                (out/name).write_bytes(payload)
                return hashlib.sha256(payload).hexdigest()
            registry_bytes=json.dumps(registry,ensure_ascii=False).encode("utf-8")
            registry_sha=save("registry-snapshot.json",registry_bytes)
            save("source-manifest.json",json.dumps(source_manifest).encode())
            version_sha=save("lean-version.log",b"Lean (version 4.33.0-rc2, commit d8b18978322de05a8f3dba51ef03cf5461676c17)\n")
            rows=[]
            for fixture in sorted(registry["runtime_typed_negative_fixtures"],key=lambda r:r["id"]):
                pair=[]
                for mode in ("positive","negative"):
                    name=fixture["id"]+"_"+mode
                    source_sha=save(name+".lean",fixture[mode+"_source"].encode("utf-8"))
                    theorem="Zeta23.OPICARound2.PairedSemanticFixtures.fixture_"+fixture["id"]
                    text=("'"+theorem+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n") if mode=="positive" else "fixture.lean:1:1: error: type mismatch\n"
                    log_sha=save(name+".log",text.encode())
                    object_sha=save(name+".olean",b"SYNTHETIC_NOT_A_LEAN_OBJECT") if mode=="positive" else None
                    pair.append({"mode":mode,"argv":["lake","env","lean","-R",producer,producer+"/"+name+".lean","-o",producer+"/"+name+".olean"],
                        "returncode":0 if mode=="positive" else 1,"source_file":name+".lean","log_file":name+".log",
                        "source_sha256":source_sha,"log_sha256":log_sha,
                        "object_file":name+".olean" if mode=="positive" else None,"object_sha256":object_sha})
                rows.append({"id":fixture["id"],"result":"POSITIVE_NATIVE_CONSUMER_AND_REJECTED_MUTANT_TYPE","scope":fixture["scope"],"commands":pair})
            data={"schema":"OPICA2_TYPED_NEGATIVE_CONTROL_RUN_V1","optimized_python":False,
                "checked_commit":head,"checked_tree":tree,"producer_artifact_root":producer,
                "registry_sha256":registry_sha,"registry_canonical_sha256":io.canonical_sha256(registry),"pinned_packages":[],
                "version_command":{"argv":["lake","env","lean","--version"],"returncode":0,"log_sha256":version_sha},
                "source_manifest_sha256":io.canonical_sha256(source_manifest),"controls":rows,
                "authority":"SOURCE_BOUND_NATIVE_TYPED_REJECTION_NOT_NEW_MATHEMATICAL_AUTHORITY",
                "full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}
            def write_receipt():save("receipt.json",json.dumps(data).encode())
            def git(_, *args):return tree if args[-1]=="HEAD^{tree}" else head
            with patch.object(receipt,"source_manifest",return_value=source_manifest),patch.object(receipt,"validate_packages",return_value=[]),patch.object(receipt.contract,"git",side_effect=git):
                write_receipt()
                result=dispatch.verify_typed_control_artifacts(receipt.REPO,out,registry,optimized=False)
                self.assertFalse(result["fresh_compiler_replay"])
                self.assertFalse(result["provider_authenticity_established_here"])
                negative=data["controls"][0]["commands"][1]
                negative["returncode"]=True;write_receipt()
                with self.assertRaises(ValueError):dispatch.verify_typed_control_artifacts(receipt.REPO,out,registry,optimized=False)
                negative["returncode"]=1
                old=(out/negative["log_file"]).read_bytes()
                negative["log_sha256"]=save(negative["log_file"],b"fixture:1:1: error: unknown identifier plus type mismatch\n")
                write_receipt()
                with self.assertRaises(ValueError):dispatch.verify_typed_control_artifacts(receipt.REPO,out,registry,optimized=False)
                negative["log_sha256"]=save(negative["log_file"],old)
                positive=data["controls"][0]["commands"][0]
                positive["source_sha256"]=save(positive["source_file"],b"theorem unrelated : True := by trivial\n")
                write_receipt()
                with self.assertRaises(ValueError):dispatch.verify_typed_control_artifacts(receipt.REPO,out,registry,optimized=False)
                data["optimized_python"]=True;write_receipt()
                with self.assertRaises(ValueError):dispatch.verify_typed_control_artifacts(receipt.REPO,out,registry,optimized=False)

    def test_commented_and_string_declarations_cannot_replace_indented_actual_source(self):
        text=('namespace Zeta23.OPICARound2\n/- nested /- theorem fake : False := by trivial -/\n'
              'theorem consumer : False := by trivial\n-/\n'
              'def rawText := r#"\ntheorem shadow : False := by trivial\n"#\n'
              ' theorem consumer : True := by trivial\nend Zeta23.OPICARound2\n')
        masked=receipt.masked_lean_source(text)
        self.assertEqual(len(masked),len(text))
        self.assertEqual([i for i,c in enumerate(masked) if c=='\n'],[i for i,c in enumerate(text) if c=='\n'])
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/"Source.lean";path.write_bytes(text.encode())
            found=receipt.source_declarations(path)
        self.assertNotIn("Zeta23.OPICARound2.fake",found)
        self.assertNotIn("Zeta23.OPICARound2.shadow",found)
        row=found["Zeta23.OPICARound2.consumer"]
        self.assertIn("consumer : True",row["header"])
        self.assertNotIn("consumer : False",row["header"])
        self.assertEqual(row["line"],8)
        for bad in ('/- unclosed','def x := "unclosed','def x := r#"unclosed'):
            with self.subTest(source=bad),self.assertRaises(ValueError):receipt.masked_lean_source(bad)

    def test_runtime_cannot_dispatch_another_checkout_under_current_source_identity(self):
        import controls as dispatch
        self.assertEqual(dispatch.require_runtime_checkout(receipt.REPO),HERE)
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(ValueError):dispatch.require_runtime_checkout(Path(tmp))


if __name__=="__main__":unittest.main()
