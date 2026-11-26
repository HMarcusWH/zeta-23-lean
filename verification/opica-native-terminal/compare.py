#!/usr/bin/env python3
"""Compare independent stock terminal replays. No claim promotion."""
import argparse, copy, json, pathlib, tempfile
from receipts import ROOTS, require, read_json, verify, graph_digest, validate_root
P = pathlib.Path

def normalize(row):
    r = copy.deepcopy(row)
    for k in ("axioms", "required"):
        r[k] = sorted(r[k])
    r["dependencies"] = sorted(r["dependencies"], key=lambda d: d["name"])
    return r

def equal_root(x, y):
    require(normalize(x) == normalize(y), "independent root receipt differs " + x["root"])

def compare(a, b):
    qa, qb = verify(a, "terminal"), verify(b, "independent")
    require(read_json(a / "source.json") == read_json(b / "source.json") and
            qa["source_sha256"] == qb["source_sha256"], "source staging receipts differ")
    for spec in ROOTS:
        root = spec["name"]
        equal_root(read_json(a / "audit" / (root + ".json")),
                   read_json(b / "audit" / (root + ".json")))
    require(qa["edge_digests"] == qb["edge_digests"], "independent proof graph drift")
    for root, d in qa["edge_digests"].items():
        print("NATIVE_PROOF_GRAPH_MATCH", root, d)
    print("NATIVE_INDEPENDENT_STOCK_REPLAY_MATCH", len(ROOTS))

def self_test():
    from receipts import expect_text
    spec = {"name": "root", "role": "native", "edges": True}
    good = {"root":"root", "type":"True", "type_expr":"T", "axioms":[],
            "native_only":True, "arithmetic_only":False, "smoke_fixture":False,
            "with_edges":True, "count":2, "required":["dep"],
            "dependencies":[{"name":"root","module":"Zeta23.Test"},{"name":"dep","module":"Init.Prelude"}]}
    def rejects(fn):
        try: fn()
        except (RuntimeError, KeyError, ValueError): return
        raise RuntimeError("mutated receipt accepted")
    members = validate_root(good, spec)
    for key, val in (("type", "False"), ("type_expr", "F"), ("required", [])):
        bad = copy.deepcopy(good); bad[key] = val
        rejects(lambda: equal_root(good, bad))
    bad = copy.deepcopy(good); bad["dependencies"][1]["module"] = "Zeta23Arithmetic.Foreign"
    rejects(lambda: validate_root(bad, spec))
    with tempfile.TemporaryDirectory() as t:
        p=P(t); (p/"audit").mkdir()
        e=p/"audit/root.edges.jsonl"
        rows=[{"name":"root","module":"Zeta23.Test","type_refs":[],"value_refs":["dep"],"structural_refs":[]},
              {"name":"dep","module":"Init.Prelude","type_refs":[],"value_refs":[],"structural_refs":[]}]
        e.write_text("\n".join(map(json.dumps, rows))+"\n")
        graph_digest(p,spec,members)
        e.write_text(json.dumps(rows[0])+"\n")
        rejects(lambda: graph_digest(p,spec,members))
        marker=p/"marker"; marker.write_text("forged\n")
        rejects(lambda: expect_text(marker,"NATIVE_R2_TERMINAL_PASS"))
    print("NATIVE_R2_COMPARATOR_CONTROLS_PASS 6")

if __name__ == "__main__":
    ap=argparse.ArgumentParser(); ap.add_argument("paths",nargs="*",type=P); ap.add_argument("--self-test",action="store_true")
    args=ap.parse_args()
    if args.self_test: self_test()
    else:
        require(len(args.paths)==2,"expected terminal and independent artifact directories")
        compare(*args.paths)
