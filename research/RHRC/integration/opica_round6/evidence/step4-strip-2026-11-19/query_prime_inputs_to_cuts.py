"""Trace selected prime-summatory and signed estimates to the Step 4 cuts.

Usage: python query_prime_inputs_to_cuts.py PATH_TO_COMPLETE_PINNED_REPO
All Git reads are immutable and disable lazy network fetches.
"""
import hashlib
import json
import subprocess
import sys
from collections import defaultdict, deque
from pathlib import Path

COMMIT = "c867a8f15320ad6ac69177e0a498de4cb9d744f9"
GENERATED = "research/RHRC/graph/generated/"
CCM = "Zeta23.CCM."
FOLLOWUP = "Zeta23.OPICAFollowup."
EX = "Zeta23.ExceptionalZero."
SOURCES = {
    "cumulative prime identity": CCM + "canonicalPrimeCumulativeWeight_eq_weightedVonMangoldtSqrtSum",
    "finite prime sum": CCM + "weightedVonMangoldtSqrtSum_eq_sum_Icc_two",
    "prime mass monotonicity": CCM + "weightedVonMangoldtSqrtSum_monotone",
    "canonical signed energy identity": CCM + "canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget",
    "signed energy positivity equivalence": CCM + "canonicalSourceChannelEnergy_nonneg_iff_budget_le",
    "K=2 restricted positivity": CCM + "primeTerm_nonneg_of_primeSample_two",
    "residual weighted integral": CCM + "GlobalBottomResidualState.primeRemainderEnergy_eq_weight_integral",
    "signed gap separator": "Zeta23.OPICA.signed_sharp_gap_separator",
    "negative mass budget": "Zeta23.OPICA.signed_gap_negative_mass_budget",
    "Stieltjes positivity budget": FOLLOWUP + "arithmetic_stieltjes_sign_budget",
    "literal divisor identity": "ArithmeticFunction.vonMangoldt_sum",
    "prime weights nonnegative": "ArithmeticFunction.vonMangoldt_nonneg",
    "logarithmic derivative identity": "ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div",
    "native visible pole": FOLLOWUP + "nativePrimeField_visiblePole",
    "native all-damping equivalence": CCM + "nativeOriginalPrimeField_allDampedL2_iff_integral",
    "native integral sufficiency": EX + "riemannHypothesis_of_step4_AX",
}
CUTS = {
    "balanced native cut": FOLLOWUP + "quiet_balanced_observation_implies_native_cut",
    "native AX": EX + "riemannHypothesis_of_step4_AX",
    "native terminal rate": FOLLOWUP + "native_fixed_source_window_rate",
    "canonical dominance iff RH": EX + "canonicalPrimeRemainderDominance_iff_riemannHypothesis",
    "cofinal arithmetic implies RH": EX + "riemannHypothesis_of_cofinalCanonicalArithmeticCertificates",
    "scalar growth iff critical line": EX + "arithmeticSideSubexponential_iff_criticalLine",
}
SOURCE_CHECKS = (
    ("Zeta23/CCM/CanonicalPrimeRemainder.lean", "theorem weightedVonMangoldtSqrtSum_monotone"),
    ("Zeta23/CCM/CanonicalPrimeRemainder.lean", "theorem canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget"),
    ("Zeta23/CCM/CanonicalK2SourceSignInterval.lean", "theorem primeTerm_nonneg_of_primeSample_two"),
    ("Zeta23/OPICAFollowup/WeightedSpectralMeasure.lean", "theorem arithmetic_stieltjes_sign_budget"),
    ("Zeta23/OPICAFollowup/Consumers.lean", "theorem quiet_balanced_observation_implies_native_cut"),
    ("Zeta23/ExceptionalZero/Step4OutputSufficiency.lean", "theorem riemannHypothesis_of_step4_AX"),
    ("Zeta23/CCM/NativeCompletionEquation.lean", "theorem nativeCompletedInput_equation "),
    ("Zeta23/CCM/NativeCompletedInputRangeOfPrimeLp.lean", "theorem nativeDampedCompletedInput_equation "),
    ("Zeta23/CCM/NativeCompletedInputRangeOfPrimeLp.lean", "theorem nativeCompletedInput_operator_eq_of_prime_memLp"),
    ("Zeta23/ExceptionalZero/NativeAnalyticOutputSufficiency.lean", "def NativeOriginalPrimeFieldAllDampedIntegral "),
    ("Zeta23/ExceptionalZero/NativeAnalyticOutputSufficiency.lean", "theorem nativeInput_allRangeClosure_of_originalPrimeField_allDampedL2"),
    ("Zeta23/ExceptionalZero/CanonicalArithmeticCriterion.lean", "def CanonicalPrimeRemainderDominance"),
    ("Zeta23/ExceptionalZero/CanonicalArithmeticCriterion.lean", "theorem canonicalPrimeRemainderDominance_iff_riemannHypothesis"),
    ("Zeta23/ExceptionalZero/CofinalArithmeticConditionalRH.lean", "def CofinalCanonicalArithmeticCertificates"),
    ("Zeta23/ExceptionalZero/CofinalArithmeticConditionalRH.lean", "theorem riemannHypothesis_of_cofinalCanonicalArithmeticCertificates"),
    ("Zeta23/CCM/CanonicalWeightedChebyshevAbel.lean", "theorem abs_psi_sub_self_sub_one_le"),
    ("Zeta23/OPICARound4/PrimeDiscrepancyIntegral.lean", "theorem native_prime_discrepancy_integral"),
    ("Zeta23/OPICARound4/OperatorSignedBound.lean", "theorem native_even_signed_upper"),
    ("Zeta23/OPICARound4/OperatorSignedBound.lean", "theorem native_odd_signed_upper"),
)
SOURCE_ONLY = (
    CCM + "abs_psi_sub_self_sub_one_le",
    "Zeta23.OPICARound4.native_prime_discrepancy_integral",
    "Zeta23.OPICARound4.native_even_signed_upper",
    "Zeta23.OPICARound4.native_odd_signed_upper",
)


def main(repo):
    def git(*args):
        return subprocess.check_output(["git", "--no-lazy-fetch", "-C", repo, *args])

    def read(path):
        return git("show", f"{COMMIT}:{path}")

    declarations = {
        row["declaration"]: row
        for row in map(json.loads, read(GENERATED + "lean_declarations.jsonl").splitlines())
    }
    claims = json.loads(read(GENERATED + "THEOREM_CLAIM_MAP.json"))["entries"]
    reverse = defaultdict(list)
    hashes = {}
    scanned = used = 0
    for shard in "0123456789abcdef":
        name = f"relations/relations-{shard}.jsonl"
        data = read(GENERATED + name)
        hashes[name] = hashlib.sha256(data).hexdigest()
        for edge in map(json.loads, data.splitlines()):
            scanned += 1
            if (edge["kind"] == "USES_CONSTANT" and edge["provenance"] == "LEAN_ENV_EXACT"
                    and edge["used_in_value"]):
                used += 1
                target = sys.intern(edge["target"].removeprefix("rh:decl:"))
                source = sys.intern(edge["source"].removeprefix("rh:decl:"))
                reverse[target].append(source)
    for neighbors in reverse.values():
        neighbors.sort()

    by_anchor = {}
    for label, anchor in SOURCES.items():
        assert anchor in declarations, anchor
        parents = {anchor: None}
        queue = deque([anchor])
        while queue:
            head = queue.popleft()
            for neighbor in reverse.get(head, ()):
                if neighbor not in parents:
                    parents[neighbor] = head
                    queue.append(neighbor)
        paths = {}
        for tag, target in CUTS.items():
            assert target in declarations, target
            if target not in parents:
                continue
            path = []
            while target is not None:
                path.append(target)
                target = parents[target]
            paths[tag] = path[::-1]
        registered = sorted(c["claim_id"] for c in claims if c["theorem"] in parents)
        by_anchor[label] = {
            "name": anchor,
            "graph_role": declarations[anchor]["graph_role"],
            "transitive_consumers_excluding_self": len(parents)-1,
            "registered_consumers_including_self": len(registered),
            "reachable_selected_cuts": paths,
        }

    excerpts = {}
    for file, prefix in SOURCE_CHECKS:
        lines = read(file).decode("utf8").splitlines()
        start = next(i for i, line in enumerate(lines) if line.startswith(prefix))
        extracted = [lines[start]]
        if prefix.startswith("def "):
            for line in lines[start+1:]:
                if not line.strip():
                    break
                extracted.append(line)
        else:
            while ":=" not in extracted[-1]:
                extracted.append(lines[start+len(extracted)])
            extracted[-1] = extracted[-1].split(":=", maxsplit=1)[0].rstrip()
        excerpts[prefix.rstrip()] = {
            "file": file, "line": start + 1,
            "url": f"https://github.com/HMarcusWH/zeta-23-lean/blob/{COMMIT}/{file}#L{start+1}",
            "statement": "\n".join(extracted),
        }
    result = {
        "commit": COMMIT, "tree": git("rev-parse", COMMIT+"^{tree}").decode().strip(),
        "relation_rows": scanned, "proof_value_rows": used,
        "declared_vertices_in_registry": len(declarations),
        "registered_claims": len(claims), "cuts": CUTS, "reachability": by_anchor,
        "extra_pinned_source_lemmas_present_in_graph_registry":
            {name: name in declarations for name in SOURCE_ONLY},
        "signatures_from_pinned_source": excerpts, "relation_shard_sha256": hashes,
        "scope": "Breadth-first shortest paths from input to consumer in reverse LEAN_ENV_EXACT "
                 "USES_CONSTANT proof-value edges, including self. A path records use of a constant, "
                 "not derivation of each theorem hypothesis. A missing path covers only this registry.",
    }
    path = Path(__file__).with_name("PRIME_INPUTS_TO_CUTS.json")
    path.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n", encoding="utf8")
    for tag, row in by_anchor.items():
        print(tag, row["registered_consumers_including_self"], list(row["reachable_selected_cuts"]))


if __name__ == "__main__":
    main(sys.argv[1])
