#!/usr/bin/env python3
"""WP4 no-search checker of a frozen K3 full-continuum certificate transcript.

The checker never discovers or widens an interval: it reads the committed
rational partition, validates every byte hash, verifies contiguous coverage
of each Q/parity layer, and recomputes each positive Sylvester enclosure at
a fresh Arb precision. It intentionally uses the canonical Eq4.4 backend
shared with the producer; independent normalization cross-checks remain a
SEPARATE mandatory condition of certificate acceptance.

A partial transcript is not a full certificate, even when every individual
accepted interval is strictly positive. The user-selected D2 target covers
both parities, every seam and all [1/512,log16].
"""
from __future__ import annotations
import argparse
import hashlib
import json
import sys
from pathlib import Path

from flint import ctx
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import canonical_source_arb as C
from wp4_k3_full_continuum import evaluate,interval_bounds,source_input_digests
from certificate_integrity import LAYERS, rational, record_path, validate_layer


def main()->int:
    p=argparse.ArgumentParser()
    p.add_argument("directory",type=Path)
    p.add_argument("--precision-bits",type=int,default=256)
    p.add_argument("--output",type=Path,help="write durable checker receipt")
    p.add_argument("--partial",action="store_true",
                   help="audit accepted fragments, not all-continuum positivity")
    args=p.parse_args()
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    manifest_raw=(args.directory/"manifest.json").read_bytes()
    manifest=json.loads(manifest_raw)
    if (manifest.get("schema") != "post287.wp4.k3-full-continuum.v1" or
            manifest.get("terminal_claim") != "RH_OPEN" or
            manifest.get("source_digests") != source_input_digests() or
            manifest.get("method") not in ("SECOND", "FOURTH")):
        raise AssertionError("certificate schema, claim, source or method mismatch")
    if args.precision_bits<=manifest["precision_bits"]:
        raise ValueError("checker must use independent higher precision")
    if not args.partial:
        if manifest["status"] != "INTERVAL_EVIDENCE" or manifest["all_L_positivity_certified"] is not True:
            raise AssertionError("full certificate is not claimed complete")
    layers=[]
    count=0
    complete_layers=0
    for spec in manifest["records"]:
        q=spec["cell"]; parity=spec["parity"]
        name=spec["file"]
        if (q, parity) in layers:
            raise AssertionError(("duplicate layer", q, parity))
        raw=record_path(args.directory,name).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=spec["sha256"]:
            raise AssertionError(("tampered",name))
        rec=json.loads(raw)
        a,b=interval_bounds(q)
        complete=validate_layer(spec, rec, manifest["method"], (a,b))
        complete_layers += int(complete)
        if rec["unresolved"] and not args.partial:
            raise AssertionError(("unresolved",name))
        if rational(rec["left"])!=a or rational(rec["right"])!=b:
            raise AssertionError(("wrong interval target",name))
        cursor=a
        for tile in rec["accepted"]:
            l,r=rational(tile["left"]),rational(tile["right"])
            if not a<=l<r<=b:raise AssertionError(("out of range",name,l,r))
            if not args.partial and l!=cursor:
                raise AssertionError(("gap or overlap",name,cursor,l))
            if args.partial and l<cursor:
                raise AssertionError(("overlap",name,l,cursor))
            method=tile["method"]
            if method not in ("SECOND","FOURTH"):
                raise AssertionError(("unsanctioned method",method))
            fresh=evaluate((l,r),parity,q,method)
            if not fresh["accepted"]:
                raise AssertionError(("failed fresh rigorous enclosure",name,l,r))
            cursor=r;count+=1
        if not args.partial and cursor!=b:
            raise AssertionError(("trailing interval uncovered",name,cursor,b))
        layers.append((q,parity))
    full = len(layers)==30 and set(layers)==LAYERS and complete_layers==30
    if not args.partial and not full:
        raise AssertionError("full D2 two-parity Q1..Q15 coverage missing")
    if manifest["all_L_positivity_certified"] is True and not full:
        raise AssertionError("claimed global positivity exceeds checked partition")
    has_unresolved = complete_layers != len(layers)
    result={"schema":"post287.wp4.checker.v1",
            "status":"PARTIAL_ACCEPTED_ONLY" if has_unresolved else "PASS",
            "claimed_scope":"PARTIAL_ONLY" if args.partial else "K3_FULL",
            "verified_tiles":count,"layers":len(layers),
            "complete_layers":complete_layers,
            "precision_bits":args.precision_bits,
            "manifest_sha256":hashlib.sha256(manifest_raw).hexdigest(),
            "source_digests":manifest["source_digests"],
            "producer_commit":manifest["source_commit"],
            "terminal_claim":"RH_OPEN","not_a_lean_proof":True}
    if args.output is not None:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True))
    return 0


if __name__=="__main__":
    raise SystemExit(main())
