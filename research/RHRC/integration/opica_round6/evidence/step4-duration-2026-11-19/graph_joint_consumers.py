"""Find the registered proofs that jointly use OPICA source and Laguerre results."""
import hashlib
import json
import subprocess
import sys
from collections import defaultdict, deque
from pathlib import Path


COMMIT = "c867a8f15320ad6ac69177e0a498de4cb9d744f9"
PREFIX = "Zeta23.OPICAFollowup."
ANCHORS = (
    "native_source_explicit_formula", "monicLaguerre_exact_norm_sq",
    "monicLaguerre_orthogonality", "nativeResidual_laguerre_inner",
    "nativeAuxiliaryStableVector_factorial_bound", "recovery_subexp_budget",
)


def paths(reverse, anchor):
    parent = {anchor: None}
    queue = deque([anchor])
    while queue:
        head = queue.popleft()
        for node in sorted(reverse.get(head, ())):
            if node not in parent:
                parent[node] = head
                queue.append(node)
    return parent


def trace(parent, end):
    result = []
    while end is not None:
        result.append(end)
        end = parent[end]
    return result[::-1]


def main(repo):
    def git(*args):
        return subprocess.check_output(["git", "--no-lazy-fetch", "-C", repo, *args])

    def blob(name):
        return git("show", COMMIT + ":research/RHRC/graph/generated/" + name)

    claims = json.loads(blob("THEOREM_CLAIM_MAP.json"))["entries"]
    reverse = defaultdict(set)
    declared = set()
    hashes = {}
    scanned = used = 0
    for shard in "0123456789abcdef":
        name = "relations/relations-" + shard + ".jsonl"
        data = blob(name)
        hashes[name] = hashlib.sha256(data).hexdigest()
        for line in data.splitlines():
            edge = json.loads(line)
            scanned += 1
            for field in ("source", "target"):
                if edge[field].startswith("rh:decl:"):
                    declared.add(edge[field].removeprefix("rh:decl:"))
            if (edge["kind"] == "USES_CONSTANT" and edge["provenance"] == "LEAN_ENV_EXACT"
                    and edge["used_in_value"]):
                used += 1
                source = edge["source"].removeprefix("rh:decl:")
                target = edge["target"].removeprefix("rh:decl:")
                reverse[target].add(source)
    witness = {}
    for short in ANCHORS:
        anchor = PREFIX + short
        parent = paths(reverse, anchor)
        witness[short] = {c["claim_id"]: trace(parent, c["theorem"])
                          for c in claims if c["theorem"] in parent}
    common = {short: sorted(set(witness[short]) & set(witness[ANCHORS[0]]))
              for short in ANCHORS[1:]}
    report = dict(commit=COMMIT, tree=git("rev-parse", COMMIT + "^{tree}").decode().strip(),
                  relation_rows=scanned, proof_body_edge_rows=used, registered_claims=len(claims),
                  anchor_appears_as_declaration_in_any_relation={s: PREFIX+s in declared for s in ANCHORS},
                  common_registered_consumers_with_native_explicit_formula=common,
                  paths_anchor_to_claim=witness, shard_sha256=hashes,
                  scope="Compiler proof-body uses, transitively, including each anchor itself. "
                        "Logical consequences absent from the registered proof graph are possible.")
    Path(__file__).with_name("GRAPH_JOINT_CONSUMERS.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf8")
    print(scanned, used, len(claims), json.dumps(common))


if __name__ == "__main__":
    main(sys.argv[1])
