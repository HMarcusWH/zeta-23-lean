"""Check genuine uses of four proposed source bounds in the pinned RH cuts."""
from collections import defaultdict, deque
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys


PIN = "c867a8f15320ad6ac69177e0a498de4cb9d744f9"
GRAPH = "research/RHRC/graph/generated/"
PROVIDERS = (
    "Zeta23.OPICAFollowup.arithmetic_stieltjes_sign_budget",
    "Zeta23.CCM.canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget",
    "Zeta23.CCM.canonicalSourceChannelEnergy_nonneg_iff_budget_le",
    "Zeta23.OPICAFollowup.recovery_subexp_budget",
    "Zeta23.ExceptionalZero.fixedOriginalSincCorrelation_two_signed_late_excursions_of_off_line_zero",
)
CUTS = (
    "Zeta23.ExceptionalZero.canonicalPrimeRemainderDominance_iff_riemannHypothesis",
    "Zeta23.ExceptionalZero.generatedRetainedPrimeRemainderDominance_iff_riemannHypothesis",
    "Zeta23.ExceptionalZero.exists_arbitrarilyLarge_primeRemainderDominance_failure_of_offLine_zero",
    "Zeta23.ExceptionalZero.riemannHypothesis_of_step4_AX",
    "Zeta23.ExceptionalZero.riemannHypothesis_of_originalDetectorSchurSubexponential",
    "Zeta23.OPICARound4.actualCorrelationLongTerm_eventual_lower_iff_combined",
    "Zeta23.OPICARound4.riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower",
    "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_of_longTerm_subexponential",
)
OTHER = (
    "Zeta23.ExceptionalZero.CanonicalPrimeRemainderDominance",
    "Zeta23.ExceptionalZero.GeneratedRetainedPrimeRemainderDominance",
    "Zeta23.CCM.NativeOriginalPrimeFieldAllDampedIntegral",
    "Zeta23.OPICARound4.actualCorrelationNativeDiagonal_bound",
    "Zeta23.OPICARound4.actualCorrelationLongTerm_eq_normalized_combined",
    "Zeta23.OPICARound4.actualCorrelationPrimeField_add_longTerm_rapid_bound",
    "Zeta23.OPICARound4.actualFlatSamplingMass_pos",
    "Zeta23.OPICARound4.ArithmeticFrontier.ActualLongTermFixedRateLowerBound",
    "Zeta23.OPICARound4.ArithmeticFrontier.ActualLongTermSubexponentialLowerBound",
    "Zeta23.OPICARound4.ArithmeticFrontier.correlation_lower_of_longTerm_fixed_rate",
    "Zeta23.OPICARound4.ArithmeticFrontier.abs_re_sub_half_le_of_longTerm_fixed_rate",
    "Zeta23.OPICARound4.ArithmeticFrontier.no_off_line_zero_of_longTerm_subexponential",
)
HYPERBOLA = "Zeta23/OPICARound4/ActualSourceHyperbola.lean"
SUFFICIENCY = "Zeta23/ExceptionalZero/Step4OutputSufficiency.lean"
DOMINANCE = "Zeta23/ExceptionalZero/CanonicalArithmeticCriterion.lean"
GROWTH = "Zeta23/OPICARound4/ArithmeticFrontier/C2GrowthClosure.lean"
LEDGER = "research/RHRC/integration/opica_round4/arithmetic_frontier/OPEN_PREMISES.json"


def reach(graph, source):
    parents = {source: None}
    queue = deque(parents)
    while queue:
        node = queue.popleft()
        for child in sorted(graph.get(node, ())):
            if child not in parents:
                parents[child] = node
                queue.append(child)
    return parents


def trace(parents, end):
    if end not in parents:
        return None
    result = []
    while end is not None:
        result.append(end)
        end = parents[end]
    return result[::-1]


def analyze(repo):
    def git(*args):
        return subprocess.check_output(["git", "--no-lazy-fetch", "-C", repo, *args])

    def blob(path):
        return git("show", PIN + ":" + path)

    registry_bytes = blob(GRAPH + "lean_declarations.jsonl")
    registry = {r["declaration"]: r for r in map(json.loads, registry_bytes.splitlines())}
    graph = defaultdict(set)
    hashes = {"lean_declarations.jsonl": sha256(registry_bytes).hexdigest()}
    rows = value_edges = 0
    for suffix in "0123456789abcdef":
        name = f"relations/relations-{suffix}.jsonl"
        data = blob(GRAPH + name)
        hashes[name] = sha256(data).hexdigest()
        for edge in map(json.loads, data.splitlines()):
            rows += 1
            if (edge["kind"] == "USES_CONSTANT" and edge["provenance"] == "LEAN_ENV_EXACT"
                    and edge["used_in_value"]):
                value_edges += 1
                graph[edge["target"].removeprefix("rh:decl:")].add(
                    edge["source"].removeprefix("rh:decl:"))

    names = PROVIDERS + CUTS + OTHER
    source_info = {}
    source_proof = {}
    files = {}
    for name in names:
        path = (registry[name]["source_path"] if name in registry else
                GROWTH if ".ArithmeticFrontier." in name else
                DOMINANCE if "rimeremainderdominance" in name.lower() else
                HYPERBOLA if ".OPICARound4." in name else SUFFICIENCY)
        if path not in files:
            data = blob(path)
            files[path] = data.decode("utf-8-sig").splitlines()
            hashes[path] = sha256(data).hexdigest()
        lines = files[path]
        short = name.rsplit(".", 1)[-1]
        starts = [i for i, line in enumerate(lines) if re.search(
            r"^(?:(?:noncomputable|protected) )?(?:theorem|def|abbrev|structure) "
            + re.escape(short) + r"(?![\w.])", line)]
        assert len(starts) == 1, (name, starts)
        first = starts[0]
        stop = next((i for i in range(first + 1, len(lines)) if re.match(
            r"^(?:theorem |def |abbrev |structure |end |section |private |/--|#print)", lines[i])), len(lines))
        block = "\n".join(lines[first:stop]).strip()
        head, _, body = block.partition(":=")
        source_info[name] = dict(in_compiler_graph=name in registry, path=path, line=first + 1,
                                 signature=head.strip(), url=f"https://github.com/HMarcusWH/zeta-23-lean/blob/{PIN}/{path}#L{first+1}")
        if "def " in lines[first] or "abbrev " in lines[first]:
            source_info[name]["definition"] = block[:4000]
        source_proof[name] = body

    walks = {n: reach(graph, n) for n in names if n in registry}
    observed = {}
    nearest = {}
    for provider in PROVIDERS:
        for cut in CUTS:
            key = provider + " -> " + cut
            if provider in walks and cut in walks:
                observed[key] = trace(walks[provider], cut)
                common = sorted((c for c in walks[provider].keys() & walks[cut].keys()
                                if c in registry and registry[c]["private_or_internal"] is False),
                                key=lambda c: (len(trace(walks[provider], c)) + len(trace(walks[cut], c)), c))
                nearest[key] = {"count": len(common), "nearest": common[:2]}
            else:
                observed[key] = "UNINDEXED_ENDPOINT"
    direct_mentions = {}
    for cut in CUTS + tuple(name for name in OTHER if ".ArithmeticFrontier." in name):
        direct_mentions[cut] = [n for n in names if n != cut and re.search(
            r"(?<![\w.])" + re.escape(n.rsplit(".", 1)[-1]) + r"(?![\w.])", source_proof[cut])]
    ledger_data = blob(LEDGER)
    hashes[LEDGER] = sha256(ledger_data).hexdigest()
    ledger = json.loads(ledger_data)
    return dict(pin=PIN, tree=git("rev-parse", PIN + "^{tree}").decode().strip(),
                graph_declaration_rows=len(registry), all_relation_rows=rows, proof_value_edges=value_edges,
                paths_provider_to_cut=observed, common_public_downstream_declarations=nearest,
                selected_short_names_explicitly_present_in_local_proof_text=direct_mentions,
                checked_source=source_info, sha256=hashes,
                open_ledger={k: ledger[k] for k in ("RH", "Step4", "combination")} |
                    {"targets": [row for row in ledger["closing_leaves"] if row["id"] in ("C2", "C2-SE")]},
                scope="Exact stored Lean proof-value use paths, counted including endpoints. Source-block mentions are checked separately. Missing graph endpoints have no path decision. This examines formal uses, not abstract logical entailment.")


if __name__ == "__main__":
    result = analyze(sys.argv[1])
    out = Path(__file__).with_name("SIGNED_CLAIM_ROUTES.json")
    out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf8")
    for key, value in result["paths_provider_to_cut"].items():
        if isinstance(value, list):
            print(key, len(value))
    print("Indexed endpoints", sum(v["in_compiler_graph"] for v in result["checked_source"].values()))
