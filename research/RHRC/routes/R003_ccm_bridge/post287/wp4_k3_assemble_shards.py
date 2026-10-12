#!/usr/bin/env python3
"""WP4 deterministic consolidation of 30 cell/parity full-range Arb transcripts.

No interval search occurs in this assembler. It validates exact source-byte
hashes from the 30 machine-generated shard manifests and builds the single
canonical global K3 evidence package. Any missing layer or unresolved tile
downgrades the global status to UNRESOLVED. No RH consequence is asserted.
"""
from __future__ import annotations
import argparse,hashlib,json
from pathlib import Path

LAYERS={(q,p) for q in range(1,16) for p in ("even","odd")}
ROOT=Path(__file__).resolve().parents[5]
SOURCE_INPUTS=[
    "research/RHRC/routes/R003_ccm_bridge/post287/wp4_k3_full_continuum.py",
    "research/RHRC/routes/R003_ccm_bridge/post287/wp4_k3_fourth_order_fallback.py",
    "research/RHRC/routes/R003_ccm_bridge/canonical_source_arb.py",
    "research/RHRC/routes/R003_ccm_bridge/post194_fb05_q14_fixed_unit_second_derivative.py",
    "research/RHRC/routes/R003_ccm_bridge/post169_fb05_schur_visibility.py",
]
def local_source_digests():
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
            for path in SOURCE_INPUTS}



def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--input",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    records=[]
    receipts=[]
    expected_digests=local_source_digests()
    source_commits=set()
    methods=set()
    for file in args.input.glob("**/manifest.json"):
        obj=json.loads(file.read_text())
        if obj.get("schema")!="post287.wp4.k3-full-continuum.v1":
            raise AssertionError(("unexpected shard schema",str(file)))
        if obj.get("terminal_claim")!="RH_OPEN":
            raise AssertionError(("unexpected claim status",str(file)))
        if obj.get("source_digests")!=expected_digests:
            raise AssertionError(("source digest mismatch",str(file)))
        if len(obj["records"])!=1:
            raise AssertionError(("not a single dispatched layer",str(file)))
        source_commits.add(obj["source_commit"])
        methods.add(obj["method"])
        checker_file=file.with_name("checker_receipt.json")
        if not checker_file.is_file():
            raise AssertionError(("missing higher precision checker receipt",str(file)))
        verifier=json.loads(checker_file.read_text())
        if verifier.get("manifest_sha256")!=hashlib.sha256(file.read_bytes()).hexdigest():
            raise AssertionError(("checker receipt not bound to manifest",str(file)))
        if verifier.get("source_digests")!=expected_digests or verifier.get("producer_commit")!=obj["source_commit"]:
            raise AssertionError(("checker source/provenance mismatch",str(file)))
        if verifier.get("precision_bits",0)<=obj["precision_bits"] or verifier.get("layers")!=1:
            raise AssertionError(("nonindependent checker precision or shard scope",str(file)))
        for rec in obj["records"]:
            if verifier.get("verified_tiles")!=rec["intervals"]:
                raise AssertionError(("checker/producer interval count mismatch",str(file)))
            if rec["status"]=="PASS" and verifier.get("status")!="PASS":
                raise AssertionError(("producer PASS missing verifier PASS",str(file)))
            receipts.append({"cell":rec["cell"],"parity":rec["parity"],
                             "verifier_status":verifier["status"],
                             "precision_bits":verifier["precision_bits"],
                             "manifest_sha256":verifier["manifest_sha256"]})
            q,p=rec["cell"],rec["parity"]
            if (q,p) not in LAYERS or any((v["cell"],v["parity"])==(q,p)
                                           for v in records):
                raise AssertionError(("duplicate/invalid K3 layer",q,p))
            path=file.parent/rec["file"]
            raw=path.read_bytes()
            if hashlib.sha256(raw).hexdigest()!=rec["sha256"]:
                raise AssertionError(("tampered input",str(path)))
            target=args.output/rec["file"]
            target.write_bytes(raw)
            records.append(dict(rec))
    if len(source_commits)>1:
        raise AssertionError(("shards produced by multiple source commits",sorted(source_commits)))
    if len(methods)>1:
        raise AssertionError(("mixed interval certificate methods",sorted(methods)))
    records.sort(key=lambda r:(r["cell"],r["parity"]))
    missing=sorted(LAYERS-{(r["cell"],r["parity"]) for r in records})
    unresolved=[(r["cell"],r["parity"]) for r in records
                if r["status"]!="PASS" or r["unresolved_count"]]
    completed=not missing and not unresolved and len(records)==30
    result={"schema":"post287.wp4.k3-full-continuum.v1",
            "status":"INTERVAL_EVIDENCE" if completed else "UNRESOLVED",
            "terminal_claim":"RH_OPEN",
            "source":"complete Eq4.4, 2D parity carrier, fixed-Q interval enclosures",
            "method":next(iter(methods),"UNKNOWN"),
            "scope":"K3 even+odd [1/512,log16]" if completed
                    else "partial accepted tiles only",
            "precision_bits":192,
            "source_digests":expected_digests,
            "source_commit":next(iter(source_commits),"UNKNOWN"),
            "independent_verifier_receipts":receipts,
            "all_L_positivity_certified":completed,
            "not_a_lean_proof":True,
            "not_a_proof_of_RH":True,
            "missing_layers":missing,
            "unresolved_layers":unresolved,
            "records":records}
    (args.output/"manifest.json").write_text(
        json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({"status":result["status"],"received":len(records),
                      "missing":len(missing),"unresolved":len(unresolved),
                      "terminal_claim":"RH_OPEN"}))
    return 0


if __name__=="__main__":
    raise SystemExit(main())
