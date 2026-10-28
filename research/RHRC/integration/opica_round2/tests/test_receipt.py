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


class RegisteredFortyDependencyTests(unittest.TestCase):
    """Synthetic directed use graphs test metadata rejection, not Lean authority."""
    @classmethod
    def setUpClass(cls):
        # This fixture tests the unchanged, exact334-binding Round2 predicate.
        # New descendant registrations are tested by their own versioned guard.
        baseline="775692f2e72d76b6a97cf66926a86cc96342c109"
        tree=subprocess.check_output(["git","-C",str(receipt.REPO),"rev-parse",baseline+"^{tree}"],text=True).strip()
        if tree!="acd548eb97ddaee68eb6c9df73f82756ee10d13f":
            raise AssertionError("Authenticated exact Round2 fixture tree differs")
        def baseline_json(relative):
            raw=subprocess.check_output(["git","-C",str(receipt.REPO),"show",baseline+":"+relative])
            return io.loads_strict_json(raw,16*1024*1024)
        cls.claims=baseline_json("research/RHRC/CLAIM_REGISTRY.json")
        cls.bindings=baseline_json("research/RHRC/REGISTERED_THEOREM_BINDINGS.json")
        cls.public=io.load_strict_json(HERE/"PUBLIC_ROOTS.json",16*1024*1024)
        def old(relative):
            raw=subprocess.run(["git","-C",str(receipt.REPO),"show",receipt.contract.FROZEN_COMMIT+":"+relative],capture_output=True,check=True).stdout
            return io.loads_strict_json(raw,16*1024*1024)
        cls.old_claims=old("research/RHRC/CLAIM_REGISTRY.json")
        cls.old_bindings=old("research/RHRC/REGISTERED_THEOREM_BINDINGS.json")
        cls.mapper=staticmethod(receipt.frozen_tool(receipt.REPO,"research/RHRC/integration/opica/build_receipt.py",
            "_opica2_mapping_protocol_fixture").mapped_registered_dependencies)
        cls.roots=[row for row in cls.public["roots"] if row["required_for_full_core"]]
        names={row["id"]:row["proposed_public_name"] for row in cls.roots}
        cls.a,cls.b,cls.unrelated=names["OPICA2_P01"],names["OPICA2_P02"],names["OPICA2_P03"]
        cls.old_name=cls.old_bindings["bindings"][0]["theorem"]
        cls.old_id=cls.old_bindings["bindings"][0]["id"]
        cls.private="_private.Zeta23.OPICARound2.Protocol.0.loadBearingHelper"
        uses={name:{} for name in names.values()}
        uses[cls.a]={"VALUE":[cls.private]}
        uses[cls.private]={"TYPE":[cls.b]}
        uses[cls.b]={"STRUCTURE":[cls.old_name]}
        uses[cls.unrelated]={"VALUE":[cls.old_name]}
        uses[cls.old_name]={}
        cls.parsed={"declarations":[{"name":row["proposed_public_name"],"module":row["module"],"kind":"THEOREM","type_sha256":"0"*64} for row in cls.roots],
            "dependencies":[{"source":source,"channel":channel,"targets":edges.get(channel,[])} for source,edges in uses.items() for channel in ("TYPE","VALUE","STRUCTURE")]}
        mapped=cls.mapper([row["proposed_public_name"] for row in cls.roots],cls.bindings["bindings"],cls.parsed["dependencies"])
        cls.correct=deepcopy(cls.claims)
        for claim in cls.correct["claims"]:
            if claim["id"] in names:claim["dependencies"]=mapped[names[claim["id"]]]

    def check(self,claims=None,parsed=None,bindings=None):
        return receipt._registered_dependency_report(claims or self.correct,bindings or self.bindings,
            self.public,self.old_claims,self.old_bindings,parsed or self.parsed,self.mapper)

    def test_exact_transitive_private_all_channel_mapping_excludes_reverse_shared_use(self):
        report=self.check()
        self.assertEqual(len(report["rows"]),40)
        a=next(row for row in report["rows"] if row["claim_id"]=="OPICA2_P01")
        self.assertEqual(a["dependencies"],sorted(["OPICA2_P02",self.old_id]))
        self.assertNotIn("OPICA2_P03",a["dependencies"])
        self.assertFalse(report["full_core_accepted"])
        self.assertIn("not mathematical necessity or independence",report["interpretation"])

    def test_planning_extra_missing_and_pruned_private_dependencies_rejected(self):
        self.assertEqual(len(self.check()["rows"]),40)  # Prove valid fixture before attacking its mapping.
        for kind in ("missing","extra","transitive","private_channel","private_edge"):
            with self.subTest(kind=kind):
                claims,parsed=deepcopy(self.correct),deepcopy(self.parsed)
                target=next(row for row in claims["claims"] if row["id"]=="OPICA2_P01")
                if kind=="missing":target["dependencies"]=[]
                elif kind=="extra":target["dependencies"]=sorted(target["dependencies"]+["OPICA2_P03"])
                elif kind=="transitive":target["dependencies"].remove(self.old_id)
                elif kind=="private_channel":parsed["dependencies"]=[row for row in parsed["dependencies"] if not(row["source"]==self.private and row["channel"]=="STRUCTURE")]
                else:next(row for row in parsed["dependencies"] if row["source"]==self.private and row["channel"]=="TYPE")["targets"]=[]
                with self.assertRaises(ValueError):self.check(claims,parsed)

    def test_original_objects_and_actual_registered_root_identity_are_immutable(self):
        self.assertEqual(len(self.check()["rows"]),40)  # Prevent wrong-population rejection from masking mutations.
        claims=deepcopy(self.correct)
        next(row for row in claims["claims"] if row["id"]==self.old_claims["claims"][0]["id"])["statement"]+=" altered"
        with self.assertRaises(ValueError):self.check(claims=claims)
        bindings=deepcopy(self.bindings)
        next(row for row in bindings["bindings"] if row["id"]==self.old_id)["source"]="Zeta23/Other.lean"
        with self.assertRaises(ValueError):self.check(bindings=bindings)
        parsed=deepcopy(self.parsed)
        parsed["declarations"]=[row for row in parsed["declarations"] if row["name"]!=self.a]
        with self.assertRaises(ValueError):self.check(parsed=parsed)


class PackageGitLinkTests(unittest.TestCase):
    """Gitlink fixtures validate filesystem provenance, never theorem authority."""
    @staticmethod
    def fixture(root, entries):
        index, blobs = {}, {}
        for name, (mode, payload) in entries.items():
            path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(payload)
            oid=hashlib.sha1(b"blob "+str(len(payload)).encode()+b"\0"+payload).hexdigest()
            index[name]={"mode":mode,"git_blob":oid};blobs[oid]=payload
        return index,blobs

    def test_exact_native_mocked_and_materialized_committed_links(self):
        import os
        entries={
            "scripts/bench/size/run.py":("120000",b"run"),
            "scripts/bench/size/run":("100755",b"print('pinned size')\n"),
            "scripts/bench/build/fake-root/bin/lean.py":("120000",b"lean"),
            "scripts/bench/build/fake-root/bin/lean":("100755",b"print('pinned lean')\n"),
            "docs/README.md":("120000",b"../README.md"),
            "README.md":("100644",b"Tracked package documentation\n")}
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);index,blobs=self.fixture(root,entries)
            links=frozenset(name for name,row in index.items() if row["mode"]=="120000")
            self.assertEqual(receipt.validate_package_symlinks(root,index,allow_materialized=True,read_blob=blobs.__getitem__),links)
            with self.assertRaises(ValueError):receipt.validate_package_symlinks(root,index,read_blob=blobs.__getitem__)
            original=Path.is_symlink
            def is_link(path):return path in {root/name for name in links} or original(path)
            def read_link(path):return entries[Path(path).relative_to(root).as_posix()][1].decode()
            with patch.object(Path,"is_symlink",is_link),patch.object(receipt.os,"readlink",side_effect=read_link):
                verified=receipt.validate_package_symlinks(root,index,read_blob=blobs.__getitem__)
                receipt.reject_untracked_source_providers(root,set(index),verified_package_links=verified)
                with self.assertRaises(ValueError):receipt.reject_untracked_source_providers(root,set(index))
            # CI/Linux additionally exercises real symlinks. The mocked native
            # case above covers the same validator branch on Windows without
            # requesting the user's symlink-creation privilege.
            if os.name!="nt":
                for name in links:
                    path=root/name;path.unlink();path.symlink_to(entries[name][1].decode())
                verified=receipt.validate_package_symlinks(root,index,read_blob=blobs.__getitem__)
                self.assertEqual(verified,links)
                receipt.reject_untracked_source_providers(root,set(index),verified_package_links=verified)

    def test_package_link_literal_target_chain_and_blob_mutations_fail(self):
        cases=[
            {"link.py":("120000",b"../outside"),"run":("100755",b"source")},
            {"link.py":("120000",b"/absolute"),"run":("100755",b"source")},
            {"link.py":("120000",b"C:\\outside"),"run":("100755",b"source")},
            {"link.py":("120000",b"missing"),"run":("100755",b"source")},
            {"a.py":("120000",b"b.py"),"b.py":("120000",b"a.py")},
        ]
        for entries in cases:
            with self.subTest(entries=entries),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);index,blobs=self.fixture(root,entries)
                with self.assertRaises(ValueError):receipt.validate_package_symlinks(root,index,allow_materialized=True,read_blob=blobs.__getitem__)
        for mutation in ("literal","target","missing","untracked","reader"):
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);index,blobs=self.fixture(root,{"link.py":("120000",b"run"),"run":("100755",b"pinned")})
                reader=blobs.__getitem__
                if mutation=="literal":(root/"link.py").write_bytes(b"different")
                elif mutation=="target":(root/"run").write_bytes(b"tampered")
                elif mutation=="missing":(root/"link.py").unlink()
                elif mutation=="untracked":del index["run"]
                else:reader=lambda _:b"not the committed blob"
                with self.assertRaises(ValueError):receipt.validate_package_symlinks(root,index,allow_materialized=True,read_blob=reader)
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            entries={f"link{k}.py":("120000",f"link{k+1}.py".encode()) for k in range(33)}
            entries["link33.py"]=("100644",b"plain")
            index,blobs=self.fixture(root,entries)
            with self.assertRaises(ValueError):receipt.validate_package_symlinks(root,index,allow_materialized=True,read_blob=blobs.__getitem__)

    def test_untracked_and_wrong_mode_links_cannot_use_package_exception(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);index,blobs=self.fixture(root,{"link.py":("100644",b"run"),"run":("100755",b"pinned")})
            self.assertEqual(receipt.validate_package_symlinks(root,index,read_blob=blobs.__getitem__),frozenset())
            original=Path.is_symlink
            def is_link(path):return path==root/"link.py" or original(path)
            with patch.object(Path,"is_symlink",is_link):
                with self.assertRaises(ValueError):receipt.reject_untracked_source_providers(root,set(index))
            (root/"ignored.md").write_bytes(b"run")
            def ignored_link(path):return path==root/"ignored.md" or original(path)
            with patch.object(Path,"is_symlink",ignored_link):
                with self.assertRaises(ValueError):receipt.reject_untracked_source_providers(root,set(index))
            (root/"ignored.md").unlink()
            (root/"ignored.py").write_bytes(b"unexpected source")
            with self.assertRaises(ValueError):receipt.reject_untracked_source_providers(root,set(index))

    def test_linked_parent_or_plain_target_cannot_escape_through_filesystem_alias(self):
        for alias in ("parent","leaf"):
            with self.subTest(alias=alias),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp)
                index,blobs=self.fixture(root,{"dir/link.py":("120000",b"run"),"dir/run":("100755",b"pinned")})
                original=Path.is_symlink
                bad=root/"dir" if alias=="parent" else root/"dir/run"
                def is_link(path):return path==bad or original(path)
                with patch.object(Path,"is_symlink",is_link):
                    with self.assertRaises(ValueError):receipt.validate_package_symlinks(root,index,allow_materialized=True,read_blob=blobs.__getitem__)

    def test_package_index_and_pinned_package_integration(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo=Path(tmp);package=repo/".lake/packages/mathlib"
            index,blobs=self.fixture(package,{"scripts/link.py":("120000",b"run"),"scripts/run":("100755",b"pinned")})
            tree=b"".join((row["mode"]+" blob "+row["git_blob"]+"\t"+name).encode()+b"\0" for name,row in index.items())
            self.assertEqual(receipt.package_git_index(tree),index)
            for bad in (tree+tree,tree.replace(b"120000 blob",b"160000 commit"),tree.replace(b"scripts/link.py",b"../escape.py")):
                with self.subTest(tree=bad),self.assertRaises(ValueError):receipt.package_git_index(bad)
            def run(argv,**kwargs):
                if "ls-tree" in argv:return SimpleNamespace(stdout=tree,returncode=0)
                if "config" in argv:return SimpleNamespace(stdout=b"false\n",returncode=0)
                if "cat-file" in argv:return SimpleNamespace(stdout=blobs[argv[-1]],returncode=0)
                raise AssertionError("Unexpected test command")
            def git(_, *args):return "1"*40 if args[0]=="rev-parse" else ""
            manifest={"packages":[{"name":"mathlib","type":"git","rev":"1"*40}]}
            with patch.object(receipt,"load_strict_json",return_value=manifest),patch.object(receipt.contract,"git",side_effect=git),patch.object(receipt.subprocess,"run",side_effect=run):
                self.assertEqual(receipt.validate_packages(repo),[{"name":"mathlib","commit":"1"*40}])
                (package/"scripts/run").write_bytes(b"changed despite clean status")
                with self.assertRaises(ValueError):receipt.validate_packages(repo)


class CompilerJSONBudgetTests(unittest.TestCase):
    def test_default_certificate_limits_remain_unchanged(self):
        self.assertEqual((io.MAX_BYTES, io.MAX_NODES, io.MAX_ITEMS), (4*1024*1024, 1_000_000, 100_000))
        value = [[0]*100_000]*10  # 1,000,011 value nodes; no oversized array.
        raw = json.dumps(value, separators=(",", ":")).encode()
        self.assertLess(len(raw), io.MAX_BYTES)
        with self.assertRaises(io.InvalidCertificate):io.loads_strict_json(raw)
        with self.assertRaises(io.InvalidCertificate):io.canonical_sha256(value)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/"records.json"; path.write_bytes(raw)
            self.assertEqual(receipt.load_compiler_json(path), value)
        self.assertEqual(receipt.compiler_canonical_bytes(value), raw)
        self.assertEqual(receipt.compiler_canonical_sha256(value), hashlib.sha256(raw).hexdigest())

    def test_compiler_structure_budget_is_still_bounded(self):
        self.assertEqual((receipt.COMPILER_MAX_BYTES, receipt.COMPILER_MAX_NODES), (128*1024*1024, 8_000_000))
        # Counts every serialized occurrence, even when Python shares a list.
        with self.assertRaises(io.InvalidCertificate):
            receipt.compiler_canonical_bytes([[0]*100_000]*80)
        self.assertEqual(io.loads_strict_json("[0]", max_nodes=2), [0])
        with self.assertRaises(io.InvalidCertificate):io.loads_strict_json("[0]", max_nodes=1)
        for budget in (True, False, 0, -1, 8_000_001, 1.0):
            with self.subTest(budget=budget), self.assertRaises(io.InvalidCertificate):
                io.canonical_bytes({}, max_nodes=budget)

    def test_compiler_lexer_and_other_structure_guards_are_unchanged(self):
        refused = ('{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}', '{"x":1.5}',
                   '{"x":1e5}', '{"x":-0}', '{"x":'+str(1 << 601)+'}',
                   '['*66+']'*66, json.dumps([0]*100_001), json.dumps("x"*(1024*1024+1)))
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/"bad.json"
            for raw in refused:
                path.write_bytes(raw.encode())
                with self.subTest(prefix=raw[:40]), self.assertRaises(io.InvalidCertificate):
                    receipt.load_compiler_json(path)
        for value in (1.5, {"x":set()}, {"x":1 << 601}):
            with self.subTest(value_type=type(value).__name__), self.assertRaises(io.InvalidCertificate):
                receipt.compiler_canonical_bytes(value)
        self.assertNotEqual(receipt.compiler_canonical_bytes(True), receipt.compiler_canonical_bytes(1))

    def test_compiler_file_and_serialization_byte_caps_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/"large.json"
            with path.open("wb") as handle:
                handle.seek(receipt.COMPILER_MAX_BYTES); handle.write(b"0")
            with self.assertRaises(io.InvalidCertificate):receipt.load_compiler_json(path)
        with patch.object(receipt, "canonical_bytes", return_value=b"x"*11), \
                patch.object(receipt, "COMPILER_MAX_BYTES", 10):
            with self.assertRaises(io.InvalidCertificate):receipt.compiler_canonical_bytes({})

    def test_small_canonical_hashes_are_identical(self):
        for value in ({"z":[1, True, None], "a":"λ"}, [], 0, False):
            self.assertEqual(receipt.compiler_canonical_bytes(value), io.canonical_bytes(value))
            self.assertEqual(receipt.compiler_canonical_sha256(value), io.canonical_sha256(value))


if __name__=="__main__":unittest.main()
