"""Native production cases. Missing tools/configuration fail; no native skips.

The CI evaluator supplies OPICA_NATIVE_CONFIG (closed WorkerConfig JSON) and
OPICA_NATIVE_OUTPUT (fresh external evidence parent). Neither is proposer input.
"""
import functools, hashlib, io, os, platform, signal, subprocess, sys, tempfile, unittest, uuid
from contextlib import redirect_stderr
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch
from research.RHRC.integration.opica_composition import executor
from research.RHRC.integration.opica_composition.canonical import ContractError,canonical_bytes,load_bytes,digest,require
from research.RHRC.integration.opica_composition.contracts import *
from research.RHRC.integration.opica_composition.snapshot import discover_source_paths,file_hash,hash_inventory,git
from research.RHRC.integration.opica_composition.executor import *
from research.RHRC.integration.opica_composition.evidence import verify_application
from research.RHRC.integration.opica_composition.evidence import validate_artifact_manifest
from research.RHRC.integration.opica_composition.proposals import validate_plan,calibration_plan

REPO=Path(__file__).resolve().parents[5]
FINITE="Zeta23.RHRC.OpicaComposition.FiniteWorlds"
CALIBRATION="Zeta23.OPICAComposition.Calibration"

@functools.lru_cache(None)
def native_context():
    require("OPICA_NATIVE_CONFIG" in os.environ,"required native worker configuration absent; native lane cannot skip")
    worker=WorkerConfig.from_dict(load_bytes(Path(os.environ["OPICA_NATIVE_CONFIG"]).read_bytes()))
    worker_capability(worker)
    require("OPICA_NATIVE_OUTPUT" in os.environ,"external native evidence root required")
    output=unlinked(os.environ["OPICA_NATIVE_OUTPUT"]).absolute()
    require(not output.is_relative_to(REPO),"native evidence must be external")
    output.mkdir(parents=True,exist_ok=True)
    paths=discover_source_paths(REPO)|{"lean-toolchain","lake-manifest.json","lakefile.toml"}
    files=hash_inventory(REPO,paths)
    source=digest(files,domain="OPICA_SOURCE_FILES_V1")
    environment={"worker_environment":worker_environment(worker)} if worker.production else {"development":True}
    generation=digest({"source":source,"environment":environment,"profile":"NATIVE_QUALIFICATION_DRAFT"},domain="OPICA_SOURCE_GENERATION_V1")
    snapshot=SnapshotIdentity(str(REPO),git(REPO,"rev-parse","HEAD"),git(REPO,"rev-parse","HEAD^{tree}"),
        source,generation,files,environment,"NATIVE_QUALIFICATION_DRAFT","DRAFT")
    return worker,snapshot,output

def fresh(label): return native_context()[2]/(label+"-"+uuid.uuid4().hex)

@functools.lru_cache(None)
def target_spec(name,module=FINITE,constants=()):
    worker,snapshot,_=native_context(); out=fresh("target"); out.mkdir()
    declaration=("Zeta23.OPICAComposition" if module==CALIBRATION else module)+"."+name
    source="import "+module+"\nimport Zeta23.RHRC.OpicaComposition.Export\nrun_cmd Zeta23.RHRC.OpicaComposition.exportTarget `"+declaration+' "value"\n'
    (out/"Target.lean").write_text(source,encoding="utf-8")
    result=run_worker(worker,out,"Target.lean","Target.olean",SearchBudget(**(worker.budget or {})))
    require(result["exit_code"]==0 and not result["resource_status"],"native target export did not finish")
    rows=[line.split(b"\t",1)[1] for line in (out/"Target.lean.log").read_bytes().splitlines() if line.startswith(b"OPICA_TARGET\t")]
    require(len(rows)==1,"native expected target export incomplete")
    h=expression_hash(load_bytes(rows[0]))
    allowed={hashlib.sha256(n.encode()).hexdigest():n for n in constants}
    return TargetSpec(name,declaration,module,h,allowed,["propext","Classical.choice","Quot.sound"],[module],
        ["SOURCE","KERNEL","AXIOMS","INDEPENDENT_EXPECTED_TYPE"],"value",
        [FINITE+".identityGold",FINITE+".transportGold",FINITE+".packetGold",
         CALIBRATION+".cofinal_newborn_packet_calibration",CALIBRATION+".cofinal_schur_packet_calibration"])

def term_const(name): return {"tag":"const","constant_id":hashlib.sha256(name.encode()).hexdigest()}
def local(slot): return {"tag":"local","binder_slot":slot}
def app(name,*args): return {"tag":"app","function":term_const(name),"arguments":list(args)}

def attempt(target,plan,*,worker_override=None):
    worker,snapshot,_=native_context(); worker=worker_override or worker
    table=[]
    for cid,name in target.allowed_constants.items():
        module=("Zeta23.OPICARound3.CofinalSimultaneousNegative" if name.endswith("cofinally_both_neutral_negative_of_off_line_zero")
                else "Zeta23.OPICARound3.NewbornSource" if name.endswith("first_simultaneous_newborn_source_witnesses")
                else "Zeta23.OPICARound3.FirstSimultaneousNegative" if name.endswith("first_simultaneous_neutral_negative_cutoff")
                else FINITE if name.startswith(FINITE+".") else
                "Init.Core" if name in {"Exists.intro","Eq.mp","Eq.mpr"} else "Init.Prelude")
        table.append({"id":cid,"declaration":name,"module":module,"role":"transport" if name in {"Eq.mp","Eq.mpr"} else "constant"})
    proposal=CompositionProposal(uuid.uuid4().hex,target.target_id,snapshot.generation,plan)
    return execute_attempt(proposal,target,snapshot,fresh("attempt"),worker=worker,constant_table=table)

def independently_verify(artifacts,target):
    worker,snapshot,_=native_context()
    return verify_application(artifacts,target,snapshot,fresh("independent"),worker=worker)

@functools.lru_cache(None)
def calibration(destination="D05"):
    names=("Zeta23.OPICARound3.cofinally_both_neutral_negative_of_off_line_zero",
           "Zeta23.OPICARound3.first_simultaneous_newborn_source_witnesses" if destination=="D05" else
           "Zeta23.OPICARound3.first_simultaneous_neutral_negative_cutoff","And.intro","Exists.intro")
    target=target_spec("CofinalNewbornPacket" if destination=="D05" else "CofinalSchurPacket",CALIBRATION,names)
    constants={"D02":hashlib.sha256(names[0].encode()).hexdigest(),destination:hashlib.sha256(names[1].encode()).hexdigest(),
               "And.intro":hashlib.sha256(b"And.intro").hexdigest(),"Exists.intro":hashlib.sha256(b"Exists.intro").hexdigest()}
    result=attempt(target,calibration_plan(constants,destination))
    require(result.status=="PROVED_CONDITIONAL","restricted actual calibration failed: "+result.reason+" "+result.output)
    verified=independently_verify(result,target)
    require(verified.status=="PROVED_CONDITIONAL","actual calibration consumer failed")
    return target,result,verified

@functools.lru_cache(None)
def checked_identity(generation):
    _,snapshot,_=native_context()
    require(snapshot.generation==generation,"positive twin source generation differs")
    target=target_spec("IdentityTarget")
    result=attempt(target,local(1))
    require(result.status=="PROVED_CONDITIONAL","genuine positive twin failed")
    verified=independently_verify(result,target)
    require(verified.status=="PROVED_CONDITIONAL","genuine independent positive twin failed")
    return target,result,verified

class NativeExecutorCases(unittest.TestCase):
    def positive_identity(self):
        from research.RHRC.integration.opica_composition.snapshot import check_snapshot
        _,snapshot,_=native_context(); check_snapshot(snapshot)
        target,result,verified=checked_identity(snapshot.generation)
        validate_artifact_manifest(result)
        validate_artifact_manifest(AttemptArtifacts.from_dict(verified.independent_replay["replay"]))
        return target,result

    def test_t09(self):
        self.positive_identity()
        target=target_spec("ConvertibleTarget")
        self.assertEqual(attempt(target,local(1)).status,"PROVED_CONDITIONAL")

    def test_t10(self):
        target=target_spec("TransportTarget",FINITE,("Eq.mp",))
        plan={"tag":"transport","constant_id":hashlib.sha256(b"Eq.mp").hexdigest(),"arguments":[local(2),local(3)]}
        result=attempt(target,plan); self.assertEqual(result.status,"PROVED_CONDITIONAL",result.output)
        self.assertEqual(independently_verify(result,target).status,"PROVED_CONDITIONAL")
        self.assertEqual(attempt(target,local(3)).status,"TYPE_REJECTED_THIS_APPLICATION")

    def test_t11(self):
        self.positive_identity()
        self.assertEqual(attempt(target_spec("SeparateWitnessTarget"),local(3)).status,"TYPE_REJECTED_THIS_APPLICATION")

    def test_t12(self):
        self.positive_identity()
        self.assertEqual(attempt(target_spec("IdentityTarget"),local(2)).status,"TYPE_REJECTED_THIS_APPLICATION")

    def test_t13(self):
        names=(FINITE+".instanceCarrier","True.intro")
        plan=app(FINITE+".instanceCarrier",local(0),term_const("True.intro"))
        positive=target_spec("AuthorizedClassTarget",FINITE,names)
        result=attempt(positive,plan)
        self.assertEqual(result.status,"PROVED_CONDITIONAL",result.output)
        verified=independently_verify(result,positive)
        self.assertEqual(verified.status,"PROVED_CONDITIONAL")
        self.assertTrue(verified.context[1]["is_typeclass"])
        negative=attempt(target_spec("ClassObligationTarget",FINITE,names),plan)
        self.assertEqual(negative.status,"UNRESOLVED",negative.output)
        self.assertNotIn("OpicaAttempt.olean",negative.manifest)

    def test_t14(self):
        target=target_spec("PacketTarget")
        self.assertEqual(attempt(target,local(2)).status,"PROVED_CONDITIONAL")
        bad={"tag":"cases","value":local(2),"branches":[local(3)]}
        self.assertEqual(attempt(target,bad).status,"TYPE_REJECTED_THIS_APPLICATION")

    def test_t15(self):
        target=target_spec("EmptyTarget",FINITE,(FINITE+".universeCarrier","Nat","PUnit"))
        positive=attempt(target,app(FINITE+".universeCarrier",term_const("Nat")))
        self.assertEqual(positive.status,"PROVED_CONDITIONAL",positive.output)
        self.assertEqual(independently_verify(positive,target).status,"PROVED_CONDITIONAL")
        negative=attempt(target,app(FINITE+".universeCarrier",term_const("PUnit")))
        self.assertEqual(negative.status,"UNRESOLVED",negative.output)
        self.assertNotIn("OpicaAttempt.olean",negative.manifest)

    def test_t16(self):
        self.positive_identity()
        # The fixed telescope contains p only, never an invented hGoal : p.
        self.assertEqual(attempt(target_spec("ForgedGoalTarget"),local(1)).status,"TYPE_REJECTED_THIS_APPLICATION")

    def test_t17(self):
        _,_,verified=calibration("D05")
        self.assertEqual(len(verified.context),3)
        self.assertTrue(verified.context[1]["is_prop"])
        calibration("D04")

    def test_t18(self):
        self.positive_identity()
        with self.assertRaises(ContractError):
            attempt(target_spec("IdentityTarget"),term_const("unproved_RH_equivalent_upper"))

    def test_t19(self):
        self.positive_identity()
        worker,_,_=native_context()
        limited=replace(worker,budget={"heartbeats":1})
        result=attempt(target_spec("EmptyTarget",FINITE,("True.intro",)),term_const("True.intro"),worker_override=limited)
        self.assertEqual(result.status,"RESOURCE_EXHAUSTED",result.output)

    def test_t20(self):
        self.positive_identity()
        target=target_spec("IdentityTarget")
        broken=replace(target,imports=[FINITE,"Zeta23.DoesNotExist"])
        self.assertEqual(attempt(broken,local(1)).status,"ENVIRONMENT_ERROR")

    def test_t80(self):
        target,_,verified=calibration("D05")
        self.assertEqual(verified.status,"PROVED_CONDITIONAL")
        self.assertNotIn("computed_vector",verified.to_dict())
        self.assertIn("Nonempty",str(target.declaration)+str(verified.constants))
        with self.assertRaises(ContractError):
            VerifiedApplication.from_dict({**verified.to_dict(),"computed_vector":[0,1]})

    def test_t91(self):
        self.positive_identity()
        target=target_spec("IdentityTarget",FINITE,(FINITE+".identityGold",))
        with self.assertRaises(ContractError): attempt(target,term_const(FINITE+".identityGold"))

    def test_t92(self):
        self.positive_identity()
        for payload in ({"tag":"tactic","text":"exact h"},{"tag":"import","module":"Lean"},
                        {"tag":"run_cmd","text":"IO.Process.output"},{"tag":"const","constant_id":"a"*64,"shell":"sh"}):
            with self.assertRaises(ContractError): validate_plan(payload)

    def test_t95(self):
        self.positive_identity()
        result=attempt(target_spec("SeparateWitnessTarget"),local(3))
        self.assertEqual(result.status,"TYPE_REJECTED_THIS_APPLICATION")
        self.assertNotEqual(result.status,"COUNTERMODEL_VERIFIED")

    def test_t96(self):
        target=target_spec("EmptyTarget",FINITE,("True.intro",))
        result=attempt(target,term_const("True.intro"))
        self.assertEqual(result.status,"PROVED_CONDITIONAL",result.output)
        verified=independently_verify(result,target)
        self.assertEqual(verified.context,[]); self.assertTrue(target.required_gates)

    def test_t112(self):
        _,_,verified=calibration("D05")
        self.assertEqual(verified.status,"PROVED_CONDITIONAL")
        self.assertNotIn("w_unit",str(verified.context))
        from research.RHRC.integration.opica_composition.tests.test_evidence import HEADER,native_pair
        positive=HEADER+"""example {L : ℝ} (hL : 0 < L) (p : ReversalParity) (K : ℕ)
    (W : NativeNewbornSourceWitness p L K hL) (hw : ‖W.w‖ ≠ 1) : ‖W.e‖ = 1 := W.e_unit
"""
        negative=positive.replace(": ‖W.e‖ = 1 := W.e_unit",": ‖W.w‖ = 1 := W.e_unit")
        native_pair(positive,negative,"unit_e_nonunit_w_original_contract")

    def test_t116(self):
        self.positive_identity()
        out=fresh("unfinished"); out.mkdir(); log=out/"unfinished.log"
        log.write_text("calibration still running\n",encoding="utf-8")
        with self.assertRaises(ContractError): parse_native(log,"OPICA_NATIVE")


class PortableResourceOutcomeTests(unittest.TestCase):
    """Real small local processes test coordinator behavior, never Lean validity."""
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix="opica-worker-outcomes-")
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.worker=WorkerConfig(sys.executable,str(Path(sys.executable).parent),[str(self.root)],production=False)

    def run_script(self,script,budget=None):
        output=self.root/uuid.uuid4().hex;output.mkdir()
        with patch.object(executor,"_recipe",return_value=([sys.executable,"-c",script],dict(os.environ))), \
                redirect_stderr(io.StringIO()):
            result=run_worker(self.worker,output,"Fixture.lean","Fixture.olean",budget or SearchBudget())
        return result,output

    def test_resource_budget_names_preserve_legacy_effective_limits(self):
        default=SearchBudget()
        self.assertEqual((default.wall_seconds,default.cpu_seconds,default.log_bytes,default.max_file_bytes),
                         (600,600,8388608,8388608))
        short=SearchBudget(wall_seconds=17,output_bytes=512345)
        self.assertEqual((short.cpu_seconds,short.max_file_bytes),(17,512345))
        distinct=SearchBudget(wall_seconds=17,cpu_seconds=13,output_bytes=512345,max_file_bytes=678901)
        self.assertEqual((distinct.cpu_seconds,distinct.log_bytes,distinct.max_file_bytes),(13,512345,678901))
        for kwargs in ({"cpu_seconds":601},{"cpu_seconds":True},{"max_file_bytes":8388609},
                       {"max_file_bytes":True},{"wall_seconds":1,"cpu_seconds":2}):
            with self.subTest(kwargs=kwargs),self.assertRaises(ContractError):SearchBudget(**kwargs)
        self.assertEqual(SearchBudget.from_dict(default.to_dict()),default)
        old={**default.to_dict(),"schema":"OPICA_SEARCH_BUDGET_V1"}
        with self.assertRaises(ContractError):SearchBudget.from_dict(old)

    def test_current_budget_schema_matches_resolved_record(self):
        schema=load_bytes((Path(executor.__file__).parent/"schemas/contracts.schema.json").read_bytes())["$defs"]["SearchBudget"]
        record=SearchBudget().to_dict()
        self.assertEqual(set(schema["required"]),set(record))
        self.assertEqual(set(schema["properties"]),set(record))
        self.assertEqual(schema["properties"]["schema"]["const"],record["schema"])
        self.assertEqual(schema["properties"]["cpu_seconds"]["maximum"],600)
        self.assertEqual(schema["properties"]["max_file_bytes"]["maximum"],8388608)

    def test_signal_classification_requires_actual_wait_signal(self):
        for code,reason in ((-24,"CPU_TIME"),(-25,"FILE_BYTES")):
            result=executor._classify_worker_exit(code,posix_signals=True)
            self.assertEqual((result["resource_status"],result["resource_reason"]),("RESOURCE_EXHAUSTED",reason))
            self.assertTrue(executor.native_resource_failure({"exit_code":code,**result}))
        for code,reason in ((-9,"KILLED_UNATTRIBUTED"),(137,"KILLED_UNATTRIBUTED"),
                            (152,"WRAPPED_EXIT_UNATTRIBUTED"),(-15,"SIGNAL_UNATTRIBUTED")):
            with self.subTest(code=code):
                result=executor._classify_worker_exit(code,posix_signals=True)
                self.assertIsNone(result["resource_status"])
                self.assertIsNone(result["resource_reason"])
                self.assertEqual(result["failure_reason"],reason)
                self.assertTrue(executor.native_resource_failure({"exit_code":code,**result}))
        self.assertIsNone(executor._classify_worker_exit(-24,posix_signals=False)["resource_status"])

    def test_normal_failure_and_generic_stderr_are_not_resource_or_semantic_proof(self):
        result,output=self.run_script("import sys; print('out of memory RESOURCE_EXHAUSTED TYPE_REJECTED_THIS_APPLICATION'); sys.exit(1)")
        self.assertEqual(result["exit_code"],1)
        self.assertIsNone(result["resource_status"])
        self.assertEqual(result["failure_reason"],"UNCLASSIFIED_WORKER_FAILURE")
        self.assertFalse(executor.native_resource_failure(result))
        text=(output/"Fixture.lean.log").read_text()
        self.assertEqual(executor._lean_error_messages(text,output,"Fixture.lean"),[])
        diagnostic="/out/Fixture.lean:4:0: error: TYPE_REJECTED_THIS_APPLICATION: fixture"
        self.assertEqual(executor._lean_error_messages(diagnostic,output,"Fixture.lean"),
                         ["TYPE_REJECTED_THIS_APPLICATION: fixture"])
        self.assertEqual(executor._lean_error_messages(diagnostic.replace("Fixture.lean","Other.lean"),output,"Fixture.lean"),[])

    def test_attempt_failures_cannot_become_semantic_negative_from_stderr_words(self):
        repo=self.root/"repo";repo.mkdir()
        snapshot=SnapshotIdentity(str(repo),"0"*40,"1"*40,"a"*64,"b"*64,
            {"Fixture.lean":"c"*64},{"development":True},"PORTABLE_DISPOSITION_FIXTURE","DRAFT")
        target=TargetSpec("fixture","Fixture.Target.identity","Fixture.Target","d"*64,{},[],["Fixture.Target"],
            ["SOURCE","KERNEL","AXIOMS","INDEPENDENT_EXPECTED_TYPE"])
        proposal=CompositionProposal("fixture",target.target_id,snapshot.generation,{"tag":"local","binder_slot":0})
        typed="/out/OpicaAttempt.lean:4:0: error: TYPE_REJECTED_THIS_APPLICATION: fixture\n"
        generic="out of memory RESOURCE_EXHAUSTED TYPE_REJECTED_THIS_APPLICATION\n"
        cases=((-9,typed,"ENVIRONMENT_ERROR","KILLED_UNATTRIBUTED"),
               (137,typed,"ENVIRONMENT_ERROR","KILLED_UNATTRIBUTED"),
               (-24,typed,"RESOURCE_EXHAUSTED","CPU_TIME"),
               (-25,typed,"RESOURCE_EXHAUSTED","FILE_BYTES"),
               (1,generic,"ENVIRONMENT_ERROR","UNCLASSIFIED_WORKER_FAILURE"),
               (1,typed,"TYPE_REJECTED_THIS_APPLICATION","ordinary Lean rejected application"),
               (1,"/out/OpicaAttempt.lean:4:0: error: maximum number of heartbeats reached\n",
                "RESOURCE_EXHAUSTED","LEAN_HEARTBEATS"))
        for code,text,status,reason in cases:
            with self.subTest(code=code,text=text):
                native={"exit_code":code,**executor._classify_worker_exit(code,posix_signals=True)}
                def dispatch(worker,output,source,object_name,budget):
                    (output/(source+".log")).write_text(text,encoding="utf-8")
                    return native
                with patch.object(executor,"check_snapshot",return_value=snapshot), \
                        patch.object(executor,"run_worker",side_effect=dispatch):
                    result=execute_attempt(proposal,target,snapshot,self.root/uuid.uuid4().hex,worker=self.worker)
                self.assertEqual((result.status,result.reason),(status,reason))
                if status=="RESOURCE_EXHAUSTED":self.assertEqual(result.native["resource_reason"],reason)

    def test_wall_watchdog_records_specific_cause(self):
        result,_=self.run_script("import time; time.sleep(10)",SearchBudget(wall_seconds=1))
        self.assertEqual((result["resource_status"],result["resource_reason"]),("RESOURCE_EXHAUSTED","WALL_TIME"))
        self.assertEqual(worker_failure_reason(result),"WALL_TIME")
        self.assertTrue(executor.native_resource_failure(result))
        self.assertLess(result["elapsed_milliseconds"],5000)

    def test_log_watchdog_is_distinct_from_per_file_limit(self):
        result,_=self.run_script("import sys,time; sys.stdout.write('x'*1000); sys.stdout.flush(); time.sleep(10)",
            SearchBudget(wall_seconds=5,output_bytes=32,max_file_bytes=8388608))
        self.assertEqual((result["resource_status"],result["resource_reason"]),("RESOURCE_EXHAUSTED","LOG_BYTES"))
        self.assertEqual(result["resource_caps"]["log_bytes"],32)
        self.assertEqual(result["resource_caps"]["max_file_bytes"],8388608)
        self.assertEqual(result["output_sizes"]["log_bytes"],1000)

    def test_success_receipt_preserves_wait_scope_and_observed_sizes(self):
        result,output=self.run_script("from pathlib import Path; Path('Fixture.olean').write_bytes(b'object'); print('done')")
        self.assertEqual(result["exit_code"],0)
        self.assertIsNone(result["resource_status"])
        self.assertIsNone(result["failure_reason"])
        self.assertEqual(result["child_status"]["return_code"],0)
        self.assertIsNone(result["child_status"]["signal"])
        self.assertEqual(result["child_status"]["scope"],"COMMAND_PROCESS_ONLY_WRAPPED_CHILD_UNKNOWN")
        self.assertEqual(result["output_sizes"]["object_bytes"],6)
        self.assertEqual(result["log_sha256"],file_hash(output/"Fixture.lean.log"))
        self.assertFalse(result["resource_caps"]["os_limits_enforced"])

    def test_monitor_exception_preserves_original_error_and_reaps_worker(self):
        output=self.root/"exception";output.mkdir()
        class Process:
            pid=1
            def poll(self):return None
            def wait(self):return 0
        failure=RuntimeError("original monitor failure")
        with patch.object(executor,"_recipe",return_value=(["fixed-fixture"],{})), \
                patch.object(executor.subprocess,"Popen",return_value=Process()), \
                patch.object(executor.time,"monotonic",side_effect=[0,failure]), \
                patch.object(executor,"_kill_worker") as kill:
            with self.assertRaises(RuntimeError) as caught:
                run_worker(self.worker,output,"Fixture.lean","Fixture.olean",SearchBudget())
        self.assertIs(caught.exception,failure)
        kill.assert_called_once()

    def test_cgroup_deltas_are_bounded_and_shared_events_do_not_attribute_oom(self):
        for name,raw in (("memory.events","low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\n"),("pids.events","max 0\n")):
            (self.root/name).write_text(raw)
        before=executor._cgroup_event_snapshot(self.root)
        (self.root/"memory.events").write_text("low 0\nhigh 0\nmax 1\noom 1\noom_kill 1\n")
        after=executor._cgroup_event_snapshot(self.root)
        delta=executor._cgroup_event_delta(before,after)
        self.assertEqual(delta["memory.events"]["oom_kill"],1)
        result=executor._classify_worker_exit(-9,posix_signals=True)
        self.assertEqual(result["failure_reason"],"KILLED_UNATTRIBUTED")
        self.assertIsNone(result["resource_reason"])
        (self.root/"pids.events").write_bytes(b"x"*4097)
        with self.assertRaises(ContractError):executor._cgroup_event_snapshot(self.root)


class NativeResourceLimitCases(unittest.TestCase):
    """Mandatory Linux limit probes; configuration absence fails, never skips."""
    def linux_probe(self,args,script):
        worker,_,_=native_context()
        require(platform.system()=="Linux" and worker.production,"real isolated Linux worker required")
        process=subprocess.run([worker.prlimit,"--core=0",*args,"--",sys.executable,"-c",script],
            env={"PATH":str(Path(sys.executable).parent)},stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=10)
        self.assertLessEqual(len(process.stdout)+len(process.stderr),4096)
        return process,executor._classify_worker_exit(process.returncode)

    def test_native_soft_cpu_signal_is_resource_failure(self):
        process,result=self.linux_probe(["--cpu=1:2"],"while True: pass")
        self.assertEqual(process.returncode,-signal.SIGXCPU)
        self.assertEqual(result["resource_reason"],"CPU_TIME")

    def test_native_equal_cpu_caps_kill_remains_unattributed(self):
        process,result=self.linux_probe(["--cpu=1:1"],"while True: pass")
        self.assertEqual(process.returncode,-signal.SIGKILL)
        self.assertIsNone(result["resource_status"])
        self.assertEqual(result["failure_reason"],"KILLED_UNATTRIBUTED")

    def test_native_file_overflow_with_quiet_log_is_resource_failure(self):
        worker,_,root=native_context()
        destination=root/("file-limit-"+uuid.uuid4().hex)
        script="import signal; signal.signal(signal.SIGXFSZ,signal.SIG_DFL); open("+repr(str(destination))+",'wb').write(b'x'*4096)"
        try:
            process,result=self.linux_probe(["--fsize=1024:1024"],script)
            self.assertEqual(process.returncode,-signal.SIGXFSZ)
            self.assertEqual(process.stdout,b"")
            self.assertEqual(process.stderr,b"")
            self.assertEqual(result["resource_reason"],"FILE_BYTES")
        finally:
            if destination.exists():destination.unlink()

    def test_native_enospc_is_environment_failure_without_trusted_cause_record(self):
        script="import os,errno; fd=os.open('/dev/full',os.O_WRONLY)\ntry: os.write(fd,b'x')\nexcept OSError as exc:\n if exc.errno!=errno.ENOSPC: raise\n raise SystemExit(1)"
        process,result=self.linux_probe([],script)
        self.assertEqual(process.returncode,1)
        self.assertIsNone(result["resource_status"])
        self.assertEqual(result["failure_reason"],"UNCLASSIFIED_WORKER_FAILURE")

    def test_native_production_wrapper_keeps_translated_signal_ambiguous(self):
        worker,_,_=native_context()
        require(platform.system()=="Linux" and worker.production,"real isolated Linux worker required")
        require(Path("/usr/bin/python3").is_file(),"trusted Linux test interpreter required")
        output=fresh("wrapper-limit");output.mkdir()
        budget=SearchBudget(wall_seconds=5,cpu_seconds=5,max_file_bytes=1024)
        command,env=executor._recipe(worker,output,"Fixture.lean","Fixture.olean",budget)
        index=command.index(worker.lean)
        script="import signal; signal.signal(signal.SIGXFSZ,signal.SIG_DFL); open('/out/Fixture.olean','wb').write(b'x'*4096)"
        command=command[:index]+["/usr/bin/python3","-c",script]
        with patch.object(executor,"_recipe",return_value=(command,env)),redirect_stderr(io.StringIO()):
            result=run_worker(worker,output,"Fixture.lean","Fixture.olean",budget)
        self.assertIn(result["exit_code"],(-signal.SIGXFSZ,128+signal.SIGXFSZ))
        if result["exit_code"]<0:self.assertEqual(result["resource_reason"],"FILE_BYTES")
        else:
            self.assertIsNone(result["resource_status"])
            self.assertEqual(result["failure_reason"],"WRAPPED_EXIT_UNATTRIBUTED")
        self.assertTrue(executor.native_resource_failure(result))
        self.assertEqual(result["cgroup_events"]["attribution"],"SHARED_COORDINATOR_UNATTRIBUTED")
