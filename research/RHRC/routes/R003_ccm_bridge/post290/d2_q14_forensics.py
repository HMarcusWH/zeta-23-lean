#!/usr/bin/env python3
"""Read-only exact-rational census of the FAILED approved D2 Q14-even cover.

This does NOT run a search, certify interval signs or claim any Lean theorem.
The original 460-child resource disposition and 768-bit checker failure stand.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import zipfile
from fractions import Fraction
from pathlib import Path

ARCHIVE_SHA256="67c7ea46d6820e1175fd1723ca0da6d6a12c8f43605a95e0ce18fcbc02658944"
MANIFEST_SHA256="416534359a88b57dabf0efdbcef2b78bdf3c75919abeb79a7affac397083b473"
Q14="k3_Q14_even.json"

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def rational(pair):
    if (not isinstance(pair,list) or len(pair)!=2 or
        any(type(t) is not int for t in pair) or pair[1]<=0):
        raise ValueError("interval endpoint is not a canonical rational pair")
    return Fraction(pair[0],pair[1])

def pair(v):
    return [v.numerator,v.denominator]

def check_partition(row):
    if row.get("Q")!=14 or row.get("parity")!="even":
        raise ValueError("wrong numerical sector")
    good=row.get("accepted",[])
    open_=row.get("unresolved",[])
    if not isinstance(good,list) or not isinstance(open_,list):
        raise ValueError("missing interval arrays")
    pieces=[]
    for x in good:
        if x.get("accepted") is not True or x.get("method")!="SECOND":
            raise ValueError("accepted candidate source tile is not a SECOND tile")
        pieces.append((rational(x["left"]),rational(x["right"]),"accepted",x))
    for x in open_:
        if not isinstance(x.get("reason"),str):
            raise ValueError("unresolved reason missing")
        pieces.append((rational(x["left"]),rational(x["right"]),"unresolved",x))
    pieces.sort(key=lambda v:(v[0],v[1]))
    cursor=rational(row["left"])
    for left,right,_,_ in pieces:
        if left!=cursor or not left<right:
            raise ValueError("candidate interval cover has a gap or overlap")
        cursor=right
    if cursor!=rational(row["right"]):
        raise ValueError("candidate interval cover does not reach final boundary")
    return pieces

def inspect_row(row):
    pieces=check_partition(row)
    unresolved=[x for x in pieces if x[2]=="unresolved"]
    current=None;islands=[]
    for left,right,_,payload in unresolved:
        if current is None or left!=current["right"]:
            current={"left":left,"right":right,"pieces":0,"reasons":collections.Counter(),
                     "children":set()}
            islands.append(current)
        current["right"]=right
        current["pieces"]+=1
        current["reasons"][payload["reason"]]+=1
        ancestry=payload.get("continuation_ancestry",{})
        if type(ancestry.get("index")) is int:
            current["children"].add(ancestry["index"])
    width=sum((right-left for left,right,_,_ in unresolved),Fraction(0))
    domain=rational(row["right"])-rational(row["left"])
    def to_json(island):
        return {
            "left":pair(island["left"]),"right":pair(island["right"]),
            "width":pair(island["right"]-island["left"]),
            "pieces":island["pieces"],"reasons":dict(sorted(island["reasons"].items())),
            "approved_child_indices":sorted(island["children"]),
        }
    return {
        "schema":"POST292_D2_Q14_EVEN_READONLY_FORENSICS_V1",
        "scientific_disposition":"UNRESOLVED",
        "authority":"RATIONAL_CANDIDATE_PARTITION_ONLY_NOT_768_BIT_REPLAY",
        "claim_cap":"RH_OPEN",
        "source_sector":"Q14-even",
        "total_candidate_pieces":len(pieces),
        "accepted_candidate_pieces":len(pieces)-len(unresolved),
        "unresolved_piece_count":len(unresolved),
        "unresolved_reason_counts":dict(sorted(collections.Counter(
            record["reason"] for _,_,_,record in unresolved).items())),
        "domain_width":pair(domain),
        "unresolved_width":pair(width),
        "unresolved_fraction":pair(width/domain),
        "unresolved_island_count":len(islands),
        "islands":[to_json(island) for island in islands],
        "not_a_mathematical_positivity_certificate":True,
        "no_new_search_or_computation":True,
    }

def inspect_archive(path):
    path=Path(path)
    if digest(path.read_bytes())!=ARCHIVE_SHA256:
        raise ValueError("different or modified D2 assembled archive")
    with zipfile.ZipFile(path) as z:
        names=z.namelist()
        if len(names)!=len(set(names)) or Q14 not in names or "manifest.json" not in names:
            raise ValueError("missing or ambiguous approved candidate payload")
        manifest_bytes=z.read("manifest.json")
        if digest(manifest_bytes)!=MANIFEST_SHA256:
            raise ValueError("different approved candidate manifest")
        manifest=json.loads(manifest_bytes)
        records=manifest.get("records",[])
        if (len(records)!=30 or
            {(v.get("cell"),v.get("parity")) for v in records} !=
            {(q,p) for q in range(1,16) for p in ("even","odd")}):
            raise ValueError("approved candidate layer inventory incomplete")
        spec=[v for v in records if v["cell"]==14 and v["parity"]=="even"][0]
        raw=z.read(spec["file"])
        if spec["file"]!=Q14 or digest(raw)!=spec["sha256"]:
            raise ValueError("Q14-even record changed after candidate sealing")
        row=json.loads(raw)
    output=inspect_row(row)
    output["approved_d2_archive_sha256"]=ARCHIVE_SHA256
    output["candidate_manifest_sha256"]=MANIFEST_SHA256
    output["producer_source_tree"]=manifest["current_source"]["tree"]
    output["candidate_status"]=manifest["status"]
    return output

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--candidate",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    args=p.parse_args()
    result=inspect_archive(args.candidate)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":result["scientific_disposition"],
                      "islands":result["unresolved_island_count"],
                      "unresolved_pieces":result["unresolved_piece_count"],
                      "claim_cap":"RH_OPEN"}))

if __name__=="__main__":
    main()
