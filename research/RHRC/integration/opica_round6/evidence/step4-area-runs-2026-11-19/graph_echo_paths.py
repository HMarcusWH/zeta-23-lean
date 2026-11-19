"""Reconstruct formal-use paths from a pinned dependency graph for the echo test."""
from collections import defaultdict, deque
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys


PIN = "c867a8f15320ad6ac69177e0a498de4cb9d744f9"
GRAPH = "research/RHRC/graph/generated/"
NAMES = {
    "moment zero": "Zeta23.ExceptionalZero.nativeZeroJet_kernelMoments_eq_zero",
    "zero multiplicity": "Zeta23.ExceptionalZero.nativeActualKernelLaplace_order_of_zero",
    "visible pole": "Zeta23.OPICAFollowup.nativePrimeField_visiblePole",
    "recovery budget": "Zeta23.OPICAFollowup.recovery_subexp_budget",
    "joint noise estimate": "Zeta23.OPICAFollowup.joint_recovery_noise_bound",
    "terminal growth": "Zeta23.OPICAFollowup.native_fixed_source_window_rate",
    "quiet observation": "Zeta23.OPICAFollowup.quiet_balanced_observation_implies_native_cut",
    "integral criterion": "Zeta23.ExceptionalZero.riemannHypothesis_of_step4_AX",
}


def shortest_paths(start, adjacency):
    parent = {start: None}
    pending = deque([start])
    while pending:
        current = pending.popleft()
        for successor in adjacency[current]:
            if successor not in parent:
                parent[successor] = current
                pending.append(successor)
    return parent


def path_to(end, parent):
    path = []
    while end is not None:
        path.append(end)
        end = parent[end]
    return path[::-1]


def analyze(repo):
    def read(path):
        return subprocess.check_output(["git", "--no-lazy-fetch", "-C", repo, "show", PIN + ":" + path])

    vertices = {r["declaration"]: r for r in map(json.loads, read(GRAPH + "lean_declarations.jsonl").splitlines())}
    assert all(name in vertices for name in NAMES.values())
    reverse = defaultdict(list)
    total = proof = 0
    for shard in "0123456789abcdef":
        data = read(GRAPH + "relations/relations-" + shard + ".jsonl")
        for edge in map(json.loads, data.splitlines()):
            total += 1
            if edge["kind"] == "USES_CONSTANT" and edge["provenance"] == "LEAN_ENV_EXACT" and edge["used_in_value"]:
                reverse[edge["target"].removeprefix("rh:decl:")].append(edge["source"].removeprefix("rh:decl:"))
                proof += 1
    for adjacency in reverse.values():
        adjacency.sort()
    walks = {label: shortest_paths(name, reverse) for label, name in NAMES.items()}
    reachable = {
        label: {end: path_to(v, walks[label]) for end, v in NAMES.items() if v in walks[label] and end != label}
        for label in NAMES
    }
    shared = {}
    for a, b in combinations(NAMES, 2):
        common = [v for v in walks[a].keys() & walks[b].keys()
                  if vertices.get(v, {}).get("private_or_internal") is False]
        common.sort(key=lambda v: (len(path_to(v, walks[a])) + len(path_to(v, walks[b])), v))
        shared[a + " + " + b] = {"public_common_consumers": len(common), "nearest": common[:3]}
    types = {}
    for label, name in NAMES.items():
        module = vertices[name]["module"]
        file = module.replace(".", "/") + ".lean"
        lines = read(file).decode("utf-8-sig").splitlines()
        ix = next(i for i, x in enumerate(lines) if x.startswith("theorem " + name.split(".")[-1]) and
                  x.removeprefix("theorem ").split(" ")[0] == name.split(".")[-1])
        text = []
        for line in lines[ix:]:
            text.append(line.partition(":=")[0])
            if ":=" in line:
                break
        types[label] = {"name": name, "signature": "\n".join(text), "url":
                        f"https://github.com/HMarcusWH/zeta-23-lean/blob/{PIN}/{file}#L{ix + 1}"}
    return {"commit": PIN, "tree": subprocess.check_output(["git", "-C", repo, "rev-parse", PIN + "^{tree}"]).decode().strip(),
            "declarations": len(vertices), "relation_rows": total, "proof_edges": proof,
            "transitive_consumers_excluding_self": {k: len(v)-1 for k, v in walks.items()},
            "reachable_selected_pairs": reachable, "pairwise_public_common_consumers": shared,
            "pinned_signatures": types,
            "interpretation": "Directed edges indicate actual uses in Lean proof values. A path can require additional hypotheses. Missing edges are relative to this registry."}


if __name__ == "__main__":
    report = analyze(sys.argv[1])
    Path(__file__).with_name("ECHO_GRAPH.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(report["transitive_consumers_excluding_self"])
    print({k: list(v) for k, v in report["reachable_selected_pairs"].items()})
