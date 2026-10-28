"""Native production cases. Missing tools/configuration fail; no native skips.

The CI evaluator supplies OPICA_NATIVE_CONFIG (closed WorkerConfig JSON) and
OPICA_NATIVE_OUTPUT (fresh external evidence parent). Neither is proposer input.
"""
import functools, hashlib, os, tempfile, unittest, uuid
from dataclasses import replace
from pathlib import Path
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
