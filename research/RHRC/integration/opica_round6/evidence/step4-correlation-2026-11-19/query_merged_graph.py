"""Find registered proof-body consumers of the merged native source and rate theorems."""
from collections import defaultdict, deque
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

COMMIT = "c867a8f15320ad6ac69177e0a498de4cb9d744f9"
ROOT = "research/RHRC/graph/generated/"
NAMESPACE = "Zeta23.OPICAFollowup."
ANCHORS = ("native_source_explicit_formula", "native_fixed_source_window_rate",
           "native_zero_sup_bounds", "recovery_subexp_budget")


def main():
    repo = Path(sys.argv[1]).resolve()
    def git(*args):
        return subprocess.check_output(["git", "--no-lazy-fetch", "-C", str(repo), *args])
    def blob(path):
        return git("show", COMMIT + ":" + ROOT + path)
    registry = json.loads(blob("THEOREM_CLAIM_MAP.json"))["entries"]
    reverse = defaultdict(set)
    hashes = {}
    for shard in "0123456789abcdef":
        name = "relations/relations-" + shard + ".jsonl"
        data = blob(name)
        hashes[name] = sha256(data).hexdigest()
        for line in data.splitlines():
            edge=json.loads(line)
            if (edge["kind"] == "USES_CONSTANT" and edge["provenance"] == "LEAN_ENV_EXACT"
                    and edge["used_in_value"]):
                reverse[edge["target"].removeprefix("rh:decl:")].add(
                    edge["source"].removeprefix("rh:decl:"))
    results={}
    for anchor in ANCHORS:
        full = NAMESPACE+anchor
        assert full in reverse or any(claim["theorem"] == full for claim in registry), full
        prev = {full: None}
        q = deque([full])
        while q:
            target = q.popleft()
            for consumer in sorted(reverse.get(target, ())):
                if consumer not in prev:
                    prev[consumer] = target
                    q.append(consumer)
        witnessed = {}
        for claim in registry:
            node=claim["theorem"]
            if node not in prev:
                continue
            steps=[]
            while node is not None:
                steps.append(node)
                node=prev[node]
            witnessed[claim["claim_id"]]=steps
        results[anchor]=witnessed
    summary={name:list(table) for name,table in results.items()}
    report=dict(head=COMMIT,tree=git("rev-parse",COMMIT+"^{tree}").decode().strip(),
                scope="Reverse reachability, including identity, on all compiler-exact USED_IN_VALUE constant edges. Consumer paths record dependency. A missing edge is not a logical impossibility.",
                registered_claims=len(registry),shards_sha256=hashes,registered_consumers=summary,shortest_witness_paths=results)
    Path(__file__).with_name("MERGED_GRAPH_CONSUMERS.json").write_text(
        json.dumps(report,indent=2)+"\n",encoding="utf8")
    print(json.dumps(summary))


if __name__=="__main__":
    main()
