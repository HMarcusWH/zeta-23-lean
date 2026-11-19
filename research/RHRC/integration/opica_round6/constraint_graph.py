"""Materialize the Round 6 constraint map and replay its open-premise queries."""
from __future__ import annotations

import argparse
from collections import Counter, deque
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT))
from research.RHRC.graph.source_surface import scan_named_source_declarations
from research.RHRC.tools.lean_imports import strip_lean_comments

CATALOG = HERE / "CONSTRAINTS.json"
PRODUCT = HERE / "CONSTRAINT_GRAPH.json"
STATES = {"PROVED", "DERIVED", "EXPERIMENTAL_SIGNAL", "OPEN", "LEAD", "SOURCE_RECORD"}
RELATIONS = {"depends_on": "JOINT_INPUT", "alternatives": "ALTERNATIVE_INPUT", "context": "CONTEXT_ONLY"}
NAME = re.compile(r"Zeta23(?:\.[^\W\d][\w']*)+\Z")
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
HISTORICAL = "research/RHRC/integration/opica_round4/arithmetic_frontier/CONSTRAINT_REGISTER.json"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def encoding(obj):
    return (json.dumps(obj, sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode()


def strings(row, key, *, optional=False):
    value = row.get(key, [] if optional else None)
    require(isinstance(value, list) and all(isinstance(x, str) and x for x in value),
            f"{row.get('id')}.{key} must be a list of nonempty strings")
    require(len(set(value)) == len(value), f"{row.get('id')}.{key}: duplicate value")
    return sorted(value)


def source_file(root, name):
    path = PurePosixPath(name)
    require(not path.is_absolute() and path.as_posix() == name and ".." not in path.parts
            and "\\" not in name and ":" not in name, f"invalid repository source: {name}")
    p = root / path
    require(p.resolve().is_relative_to(root.resolve()) and p.is_file(), f"missing or external source: {name}")
    return p


def build(catalog, root):
    require(catalog.get("schema") == "OPICA_ROUND6_CONSTRAINTS_V1", "unknown catalog schema")
    require(catalog.get("RH") == catalog.get("Step4") == "OPEN", "terminal claim status must be OPEN")
    records = catalog.get("constraints")
    require(isinstance(records, list) and records, "empty constraint register")
    nodes = {}
    edges = []
    bindings = {}

    @lru_cache(maxsize=None)
    def lean_anchors(name):
        module = ".".join(PurePosixPath(name).with_suffix("").parts)
        return scan_named_source_declarations(path=name, module=module, trust_zone="", source_locator={},
                                             text=source_file(root, name).read_text(encoding="utf-8-sig"),
                                             strip_comments=strip_lean_comments)

    for row in records:
        key = row["id"]
        require(isinstance(key, str) and re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", key)
                and key not in nodes, f"invalid or duplicate id: {key}")
        require(row["status"] in STATES and isinstance(row["statement"], str) and row["statement"].strip(),
                f"invalid status or statement: {key}")
        sources = strings(row, "sources")
        require(sources, f"{key} needs a source")
        for name in sources:
            source_file(root, name)
        names = strings(row, "declarations")
        require(row["status"] != "PROVED" or names, f"{key}: PROVED requires a Lean declaration")
        ids = {k: strings(row, k, optional=(k != "depends_on")) for k in RELATIONS}
        require(not set(ids["depends_on"]) & set(ids["alternatives"]), f"{key}: overlapping AND/OR inputs")
        named = []
        for name in names:
            require(NAME.fullmatch(name), f"invalid qualified declaration: {name}")
            matches = [a for s in sources if s.endswith(".lean") for a in lean_anchors(s)
                       if name == a["declared_name"] or name.endswith("." + a["declared_name"])]
            require(len(matches) == 1, f"{key}: {name} needs exactly one named source anchor in cited files")
            a = matches[0]
            info = {"source": a["path"], "module": a["module"], "line": a["line"],
                    "rhkg_source_id": a["id"], "command": a["command_kind"]}
            require(name not in bindings or bindings[name] == info, f"{name}: inconsistent anchors")
            bindings[name] = info
            named.append(info)
        require(row["status"] != "PROVED" or any(a["command"] in {"LEMMA", "THEOREM"} for a in named),
                f"{key}: PROVED needs a theorem or lemma source")
        nodes[key] = {"status": row["status"], "statement": row["statement"], **ids,
                      "declarations": names, "source_files": ["rh:file:" + s for s in sources]}
        if row["status"] == "SOURCE_RECORD":
            for field in ("source_disposition", "closing_relevance", "parameter_order"):
                if field in row:
                    nodes[key][field] = row[field]
        for field, kind in RELATIONS.items():
            edges.extend({"from": other, "to": key, "kind": kind} for other in ids[field])

    for edge in edges:
        require(edge["from"] in nodes, f"dangling edge: {edge}")
        require(edge["kind"] == "CONTEXT_ONLY" or nodes[edge["from"]]["status"] != "SOURCE_RECORD",
                f"historical source record used as an inference: {edge}")
    active = set()
    coverage = {}

    def trace(key):
        if key in coverage:
            return coverage[key]
        require(key not in active, f"cyclic premise route at {key}")
        active.add(key)
        row = nodes[key]
        joint, possible, every = set(), set(), set()
        alternative_branches = []
        for child in row["depends_on"] + row["alternatives"]:
            child_view = trace(child)
            seen = {child} if nodes[child]["status"] == "OPEN" else set()
            possible.update(seen, child_view["open_on_any_input_branch"])
            unavoidable = seen | set(child_view["open_in_every_catalog_route"])
            if child in row["depends_on"]:
                joint.update(seen, child_view["open_on_joint_edges_only"])
                every.update(unavoidable)
            else:
                alternative_branches.append(unavoidable)
        if alternative_branches:
            every.update(set.intersection(*alternative_branches))
        active.remove(key)
        coverage[key] = {"open_on_joint_edges_only": sorted(joint),
                         "open_on_any_input_branch": sorted(possible),
                         "open_in_every_catalog_route": sorted(every)}
        return coverage[key]

    for key in sorted(nodes):
        trace(key)
    return {"schema": "OPICA_ROUND6_CONSTRAINT_GRAPH_V1", "RH": "OPEN", "Step4": "OPEN",
            "catalog_sha256": sha256(encoding(catalog)).hexdigest(),
            "edge_meaning": "Edges point from cited input to consumer. JOINT_INPUT is conjunctive; ALTERNATIVE_INPUT names an alternative for the same consumer. CONTEXT_ONLY has zero inferential weight. No status propagation.",
            "counts_by_status": dict(Counter(n["status"] for n in nodes.values())),
            "nodes": nodes, "edges": sorted(edges, key=lambda e: (e["to"], e["kind"], e["from"])),
            "source_only_declaration_anchors": bindings,
            "open_entries": sorted(k for k,v in nodes.items() if v["status"] == "OPEN"),
            "input_branch_coverage": coverage}


def check_rhkg(graph, folder):
    expected_files = {s for node in graph["nodes"].values() for s in node["source_files"]}
    expected_decls = {a["rhkg_source_id"]: a for a in graph["source_only_declaration_anchors"].values()}
    with (folder / "repository_files.jsonl").open(encoding="utf-8") as rows:
        for line in rows:
            expected_files.discard(json.loads(line)["id"])
    with (folder / "lean_source_declarations.jsonl").open(encoding="utf-8") as rows:
        for line in rows:
            found = json.loads(line)
            if (anchor := expected_decls.get(found["id"])) is not None:
                require((found["path"], found["module"], found["line"], found["command_kind"]) ==
                        (anchor["source"], anchor["module"], anchor["line"], anchor["command"]),
                        f"RHKG named-source mismatch: {found['id']}")
                del expected_decls[found["id"]]
    require(not expected_files and not expected_decls,
            f"committed RHKG is missing {sorted(expected_files)} / {sorted(expected_decls)}")


def check_historical(graph, register):
    old = {r["id"]: r for r in register["constraints"]}
    observed = {key for key in graph["nodes"] if re.fullmatch(r"CR[0-9]+", key)}
    require(len(old) == len(register["constraints"]) and observed == set(old), "historical ID coverage mismatch")
    for key, origin in old.items():
        row = graph["nodes"][key]
        expected = {"status": "SOURCE_RECORD", "source_disposition": origin["native_validity"],
                    "closing_relevance": origin["closing_relevance"], "parameter_order": origin["parameter_order"],
                    "statement": origin["name"] + ". " + origin["statement"]}
        require(all(row.get(field) == value for field, value in expected.items())
                and "rh:file:" + HISTORICAL in row["source_files"], f"historical record differs from original: {key}")


def explain(graph, target):
    nodes = graph["nodes"]
    require(target in nodes, f"unknown constraint: {target}")
    paths = {target: []}
    queue = deque([target])
    while queue:
        node = queue.popleft()
        for field in ("depends_on", "alternatives"):
            for premise in nodes[node][field]:
                if premise not in paths:
                    paths[premise] = [{"from": premise, "kind": RELATIONS[field], "to": node}, *paths[node]]
                    queue.append(premise)
    coverage = graph["input_branch_coverage"][target]
    return {"target": target, **nodes[target], **coverage,
            "shortest_open_routes": {k: paths[k] for k in coverage["open_on_any_input_branch"]}}


def audit_group(graph, group):
    def category(module):
        if module.startswith("Zeta23.OPICARound6."):
            return "round6"
        if module.startswith("Zeta23.OPICARound5."):
            return "prior-parity"
        return "other-history"
    all_names = graph["source_only_declaration_anchors"]
    selected = {n: a for n, a in all_names.items() if group == "all" or category(a["module"]) == group}
    require(selected, f"empty compiler selection: {group}")
    return selected


def audit_input(graph, group="all"):
    anchors = audit_group(graph, group)
    modules = sorted({a["module"] for a in anchors.values()})
    lines = ["import Lean.Elab.Command"] + ["import " + module for module in modules]
    lines.extend(["", "open Lean Elab Command", "run_cmd do", "  let env ← getEnv"])
    for name in sorted(anchors):
        tick = chr(96)
        lines.extend([f"  let some idx := env.getModuleIdxFor? {tick}{tick}{name}",
                      f'    | throwError "missing compiler owner for {name}"',
                      f"  unless env.allImportedModuleNames[idx.toNat]! == {tick}{anchors[name]['module']} do",
                      f'    throwError "wrong compiler owner for {name}"'])
    for name in sorted(anchors):
        lines.extend(["#check " + name, "#print axioms " + name])
    return "\n".join(lines) + "\n"


def check_axioms(graph, log, group="all"):
    pattern = r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
    observed = {}
    for name, raw in re.findall(pattern, log):
        allowed = {a.strip() for a in raw.split(",") if a.strip()}
        require(name not in observed and allowed <= AXIOMS, f"duplicate or unapproved axioms: {name}, {allowed}")
        observed[name] = sorted(allowed)
    require(set(observed) == set(audit_group(graph, group)), "incomplete compiler audit")
    return observed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    command = parser.add_mutually_exclusive_group(required=True)
    command.add_argument("--write", action="store_true")
    command.add_argument("--check", action="store_true")
    command.add_argument("--audit-source", type=Path, metavar="PATH")
    command.add_argument("--check-axioms", type=Path, metavar="LOG")
    command.add_argument("--build-imports", action="store_true")
    command.add_argument("--explain", metavar="CONSTRAINT_ID", help="print the recorded conditions and their open frontiers")
    parser.add_argument("--check-rhkg", action="store_true", help="cross-check source IDs against committed canonical outputs")
    parser.add_argument("--group", choices=["all", "round6", "prior-parity", "other-history"], default="all",
                        help="disjoint module group for compiler audits")
    args = parser.parse_args()
    catalog = json.loads(CATALOG.read_text(encoding="utf-8"))
    graph = build(catalog, ROOT)
    check_historical(graph, json.loads((ROOT / HISTORICAL).read_text(encoding="utf-8")))
    if args.write:
        PRODUCT.write_bytes(encoding(graph))
    elif args.check:
        require(PRODUCT.read_text(encoding="utf-8") == encoding(graph).decode(), "stale constraint graph")
    elif args.audit_source:
        args.audit_source.write_bytes(audit_input(graph, args.group).encode())
    elif args.build_imports:
        print("\n".join(sorted({a["module"] for a in audit_group(graph, args.group).values()})))
    elif args.check_axioms:
        print(json.dumps(check_axioms(graph, args.check_axioms.read_text(encoding="utf-8"), args.group), sort_keys=True, indent=2))
    elif args.explain:
        print(encoding(explain(graph, args.explain)).decode(), end="")
    if args.check_rhkg:
        check_rhkg(graph, ROOT / "research/RHRC/graph/generated")


if __name__ == "__main__":
    main()
