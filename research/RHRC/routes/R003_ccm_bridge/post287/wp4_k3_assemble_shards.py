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


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--input",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    records=[]
    for file in args.input.glob("**/manifest.json"):
        obj=json.loads(file.read_text())
        if obj.get("schema")!="post287.wp4.k3-full-continuum.v1":
            raise AssertionError(("unexpected shard schema",str(file)))
        if obj.get("terminal_claim")!="RH_OPEN":
            raise AssertionError(("unexpected claim status",str(file)))
        for rec in obj["records"]:
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
    records.sort(key=lambda r:(r["cell"],r["parity"]))
    missing=sorted(LAYERS-{(r["cell"],r["parity"]) for r in records})
    unresolved=[(r["cell"],r["parity"]) for r in records
                if r["status"]!="PASS" or r["unresolved_count"]]
    completed=not missing and not unresolved and len(records)==30
    result={"schema":"post287.wp4.k3-full-continuum.v1",
            "status":"INTERVAL_EVIDENCE" if completed else "UNRESOLVED",
            "terminal_claim":"RH_OPEN",
            "source":"complete Eq4.4, 2D parity carrier, fixed-Q interval enclosures",
            "method":"second and single predeclared fourth-order fallback",
            "scope":"K3 even+odd [1/512,log16]" if completed
                    else "partial accepted tiles only",
            "precision_bits":192,
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
