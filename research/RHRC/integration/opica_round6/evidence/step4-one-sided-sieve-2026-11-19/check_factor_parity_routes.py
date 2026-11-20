"""Audit full pinned proof-value ancestry of arithmetic and parity theorems."""
from collections import defaultdict, deque
from functools import cache
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys


PIN = "c867a8f15320ad6ac69177e0a498de4cb9d744f9"
DIR = "research/RHRC/graph/generated/"
ARITHMETIC = re.compile(r"moebius|möbius|mobius|squarefree|mertens|sieve|divisor|coprime|prime_?factor|rough(number|part|prime|factor|integer)|cardDistinctFactors", re.I)
SEEDS = {"ArithmeticFunction.moebius", "Nat.divisors", "Nat.primeFactors", "Nat.Coprime", "Squarefree"}
CUT = "Zeta23.ExceptionalZero."
CUTS = [CUT + s for s in [
    "canonicalFiniteWeilPositivity_iff_riemannHypothesis",
    "canonicalPrimeRemainderDominance_iff_riemannHypothesis",
    "cofinalCanonicalArithmeticCertificates_iff_riemannHypothesis",
    "globalBottomResidualExclusion_iff_riemannHypothesis",
    "riemannHypothesis_of_nativeInput_allRangeClosure",
    "riemannHypothesis_of_originalPrimeField_allDampedIntegral", "riemannHypothesis_of_step4_AX",
]]
M = "Zeta23.OPICAFollowup."
R = "Zeta23.OPICARound2."
C = "Zeta23.CCM."
CONSUMERS = [M+"moebius_inverse_positive", M+"moebius_inverse_jordan", R+"native_mobius_delayed_barrier_rpow", R+"native_squarefree_omission_bound"]
READ = [M+"moebius_divisor_sum", M+"moebius_plus_minus_card", M+"moebius_lattice_coefficients", M+"moebiusPlus_conv_integerLogComb", M+"moebius_inverse_positive", M+"moebius_inverse_jordan", C+"native_divisor_coefficient_identity", R+"native_mobius_delayed_barrier", R+"native_squarefree_omission_bound"]


def digest(data):
    return sha256(data).hexdigest()


def audit(repo):
    def git(*args):
        return subprocess.check_output(["git", "--no-lazy-fetch", "-C", repo, *args])

    def blob(path):
        return git("show", PIN + ":" + path)

    raw = blob(DIR + "lean_declarations.jsonl")
    hashes = {"lean_declarations.jsonl": digest(raw)}
    declarations = {d["declaration"]: d for d in map(json.loads, raw.splitlines())}
    assert SEEDS <= declarations.keys()
    dependencies = defaultdict(set)
    direct_seed = set()
    n = edges = 0
    for suffix in "0123456789abcdef":
        path = f"relations/relations-{suffix}.jsonl"
        raw = blob(DIR + path)
        hashes[path] = digest(raw)
        for r in map(json.loads, raw.splitlines()):
            n += 1
            if r["kind"] != "USES_CONSTANT" or r["provenance"] != "LEAN_ENV_EXACT":
                continue
            child = r["source"].removeprefix("rh:decl:")
            provider = r["target"].removeprefix("rh:decl:")
            if provider in SEEDS:
                direct_seed.add(child)
            if r["used_in_value"]:
                dependencies[child].add(provider)
                edges += 1
    theorems = {s for s,d in declarations.items() if d["repository_scope"] == "LOCAL"
                and d["declaration_kind"] == "THEOREM" and not d["private_or_internal"]}
    assert theorems, {d["repository_scope"] for d in declarations.values()}
    arithmetic = {s for s in theorems if ARITHMETIC.search(s.rsplit(".",1)[-1]) or s in direct_seed}
    parity = {s for s in theorems if "parity" in (s+" "+declarations[s]["source_path"]).lower()}
    assert set(READ+CONSUMERS+CUTS) <= theorems

    def walk(endpoint):
        parents = {endpoint: None}
        q = deque([endpoint])
        while q:
            x=q.popleft()
            for a in sorted(dependencies.get(x, ())):
                if a not in parents:
                    parents[a]=x
                    q.append(a)
        return parents

    def path(s, parents):
        p=[s]
        while parents[p[-1]]:
            p.append(parents[p[-1]])
        return p

    @cache
    def source_lines(f):
        b=blob(f)
        hashes[f]=digest(b)
        return b.decode("utf-8-sig").splitlines()

    def signature(s):
        f=declarations[s]["source_path"]
        lines=source_lines(f)
        leaf=s.rsplit(".",1)[-1]
        pattern=re.compile(r"^(?:(?:public|private|protected|noncomputable) )?(?:theorem|lemma|def|abbrev|structure) "+re.escape(leaf)+r"(?![\w.])")
        indices=[i for i,x in enumerate(lines) if pattern.search(x)]
        if len(indices)!=1:
            return {"file":f,"status":"nonunique-or-generated spelling"}
        i=indices[0]
        sig="\n".join(lines[i:i+40]).partition(":=")[0].strip()
        return {"file":f,"line":i+1,"signature":sig,"url":f"https://github.com/HMarcusWH/zeta-23-lean/blob/{PIN}/{f}#L{i+1}"}

    source_examples=set(READ+CONSUMERS+CUTS)
    routes={}
    for cut in CUTS+CONSUMERS:
        parents=walk(cut)
        row={}
        for label,candidates in (("arithmetic",arithmetic),("parity",parity)):
            reachable=sorted(candidates & parents.keys()-{cut})
            examples=sorted((path(s,parents) for s in reachable), key=lambda p:(len(p),p))
            chosen=examples[:2]
            if label=="arithmetic":
                chosen.extend(p for p in examples if p[0] in READ and p not in chosen)
            if label=="parity" and cut==CUTS[3]:
                for p in examples:
                    if ".CCM." in p[0] and p not in chosen:
                        chosen.append(p)
                        break
            source_examples.update(p[0] for p in chosen)
            row[label]={"total":len(reachable),"providers":reachable if label=="arithmetic" else None,
                        "sorted_names_sha256":digest("\n".join(reachable).encode()),"shortest_paths_for_selected_providers":chosen}
        routes[cut]=row
    return {"pin":PIN,"tree":git("rev-parse",PIN+"^{tree}").decode().strip(),"shards":16,"registry_size":len(declarations),"edge_rows":n,"proof_value_rows":edges,
            "public_local_theorems":len(theorems),"arithmetic_count":len(arithmetic),"arithmetic_names":sorted(arithmetic),
            "seed_values_or_types":sorted(SEEDS),"arithmetic_leaf_regex":ARITHMETIC.pattern,"parity_count":len(parity),
            "parity_names_sha256":digest("\n".join(sorted(parity)).encode()),"routes":routes,
            "signatures":{s:signature(s) for s in sorted(source_examples)},"hashes":hashes}


if __name__=="__main__":
    if len(sys.argv)!=2:
        raise SystemExit("Pass path to a checkout holding the pinned Git objects.")
    result=audit(sys.argv[1])
    Path(__file__).with_name("FACTOR_PARITY_ROUTES.json").write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n",encoding="utf-8")
