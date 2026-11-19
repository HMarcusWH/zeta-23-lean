"""Read the installed Git tree and qualified PR 302 receipts. Run with Python 3."""
import collections
import hashlib
import itertools
import json
import os
import re
import subprocess
import zipfile
from fractions import Fraction
from pathlib import Path


HERE = Path(__file__).resolve().parent
WORK = HERE.parents[2]
EVIDENCE = WORK / "pr300-301-merge-readiness-2026-11-16"
REPO = EVIDENCE / "repo"
MAIN = "c867a8f15320ad6ac69177e0a498de4cb9d744f9"
DIAGNOSTIC = "5b2bd397e733cee16d63d111269aafd64e02a6b4"
BASE = "research/RHRC/integration/"
ROUND = BASE + "opica_round4/"
FRONTIER = ROUND + "arithmetic_frontier/"
COMPOSITION = BASE + "opica_composition/"
PROVENANCE = {}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source(path):
    data = subprocess.check_output(
        ["git", "-C", str(REPO), "show", MAIN + ":" + path],
        env={**os.environ, "GIT_NO_LAZY_FETCH": "1"},
    )
    PROVENANCE[path] = digest(data)
    return data.decode("utf-8")


def document(path):
    return json.loads(source(path))


def restrict(row, keys):
    return {k: row[k] for k in keys if k in row}


def forward(seed, rules):
    have = set(seed)
    while True:
        extra = {target for antecedents, target in rules if set(antecedents) <= have}
        if extra <= have:
            return have
        have |= extra


def minimal_subsets(items, qualifies):
    minimum = []
    for size in range(len(items) + 1):
        for chosen in itertools.combinations(items, size):
            if not any(set(previous) <= set(chosen) for previous in minimum) and qualifies(chosen):
                minimum.append(chosen)
    return minimum


def lean_rule(file, name, required):
    text = source(file)
    line = re.search(r"(?m)^theorem " + re.escape(name) + r"\b", text)
    assert line, name
    statement = text[line.start():].split(":=", 1)[0]
    for token in required:
        assert token in statement, (name, token)
    return {"theorem": name, "path": file, "line": text[:line.start()].count("\n") + 1}


def native_routes():
    c = document(ROUND + "CLOSURE_OBLIGATIONS.json")
    assert c["registration_authority"] == "RESEARCH_GRAPH_ONLY" and not c["metadata_can_discharge_leaf"]
    by_id = {n["id"]: n for n in c["nodes"]}
    root = by_id[c["terminal"]]
    assert root["kind"] == "OR" and all(by_id[k]["kind"] == "LEAF" for k in root["children"])
    current = [k for k in root["children"] if by_id[k]["status"] != "OPEN"]
    assert not current
    f = "Zeta23/OPICARound4/ClosureConsumers.lean"
    out = "PointwiseNoBothNeg"
    specs = [
        (["EvenRayComparison"], "EvenNegativeGroundRestriction", "even_negative_ground_restriction_of_all_ray"),
        (["OddAdjointRayComparison"], "OddNegativeGroundRestriction", "odd_negative_ground_restriction_of_all_ray"),
        (["EvenRayComparison", "OddAdjointRayComparison", "SharedGroundExclusion"], out, "noBothNeg_of_research_targets"),
        (["EvenNegativeGroundRestriction", "OddNegativeGroundRestriction", "SharedGroundExclusion"], out,
         "noBothNeg_of_ground_restrictions"),
    ]
    edges = []
    for parents, target, theorem in specs:
        # Positive L and K >= 3 are retained as domain conditions on the pointwise output.
        guards = parents + (["0 < L", "3 ≤ K", "¬ BothNeutralNegative L K"] if target == out else [target])
        edges.append({**lean_rule(f, theorem, guards), "all_inputs": parents, "output": target})
    rules = [(p, q) for p, q, theorem in specs]
    inputs = sorted({p for pp, _, _ in specs for p in pp})
    paths = minimal_subsets(inputs, lambda s: out in forward(s, rules))
    cuts = minimal_subsets(inputs, lambda s: all(set(s) & set(path) for path in paths))
    return {
        "root": root, "native_nodes": c["nodes"], "closed_leaf_count": len(current),
        "or_minimal_sufficient_hypotheses": [[p] for p in root["children"]],
        "retained_historical_root": next(x for x in c["retained_research_nodes"] if x["kind"] == "OR"),
        "actual_pointwise_edges": edges, "pointwise_symbolic_minimal_input_sets": paths,
        "pointwise_minimal_blocking_sets": cuts,
        "pointwise_scope": "Four Lean implications only. Inputs are global research predicates. Output at 0<L and K>=3. Sets are symbolic supplier patterns, never evidence.",
    }


def registers():
    frontier = document(FRONTIER + "OPEN_PREMISES.json")
    constraints = document(FRONTIER + "CONSTRAINT_REGISTER.json")
    by_cr = {r["id"]: r for r in constraints["constraints"]}
    leaves = frontier["closing_leaves"]
    assert all(r["register"] in by_cr and r["status"] == "OPEN" for r in leaves)
    rules = [([r["id"]], r["implies"]) for r in leaves if "implies" in r]
    keys = ("id", "name", "statement", "native_validity", "closing_relevance", "scope", "consumers", "budget_improved")
    s = document(ROUND + "SOURCE_CONSTRAINTS.json")
    geometry = s["contracts"]["geometry"]
    overlaps = []
    for left, right in itertools.combinations(geometry, 2):
        common = sorted(set(left["dependencies"]) & set(right["dependencies"]))
        if common:
            overlaps.append({"left":left["id"],"right":right["id"],"shared_labels":common})
    public = document(COMPOSITION + "PUBLIC_TARGETS.json")
    state = document(BASE + "INTEGRATION_STATE.json")
    frameworks = document(BASE + "FRAMEWORK_REGISTRY.json")
    provider = document(COMPOSITION + "FRAMEWORK_PROVIDERS.json")
    provider_api = document(COMPOSITION + "providers/permansson/selected_exports.json")
    assert provider["selected_provider"] == provider_api
    menu = document(COMPOSITION + "SEARCH_CONTRACTS.json")
    source_targets = [r for r in public["intermediate"] if r["id"] == "INTEGRATION_SOURCE"]
    assert len(source_targets) == 1
    src_file = "Zeta23/OPICARound4/IntegrationTargets.lean"
    src = source(src_file)
    assert "nativeCompleteRowBudget L K" in src and "poleNeutralEvenShiftedRay hL K hK lam hlam" in src
    by_name = {r["declaration"]: r for r in menu["statements"]}
    menu_rows = {}
    for target in public["intermediate"]:
        exact = [by_name[row["declaration"]] for row in target["approved_constants"]]
        menu_rows[target["id"]] = [restrict(row, ["declaration", "type_sha256", "source_sha256"]) for row in exact]
    return {
        "historical_canonical_state":restrict(state,["current_operation","candidate_scope","graph_theorem_promotion","repository_graph_authority"]),
        "framework_claim_caps":{r["id"]:restrict(r,["scope","claim_cap","status"]) for r in frameworks["frameworks"]},
        "frontier": {"combination": frontier["combination"], "closing_leaves": leaves,
                     "supporting_statuses": dict(collections.Counter(r["status"] for r in frontier["supporting_leaves"])),
                     "explicit_implications": rules,
                     "reachable_by_explicit_implications": {r["id"]: sorted(forward([r["id"]],rules)-{r["id"]}) for r in leaves}},
        "constraint_axes": constraints["axes"], "constraint_count": len(by_cr),
        "constraint_to_named_consumers": {k: v["consumers"] for k,v in by_cr.items()},
        "selected_native_constraints": [restrict(by_cr[f"CR{i:02d}"],keys) for i in [1,4,16,17,18,25,26,31,32,37,38,40,41,42,43,46,47,50,51,52,53]],
        "source_open_targets": s["open_arithmetic_targets"], "state_binding_rules": s["state_binding_rules"],
        "source_contract_dependency_entries": [restrict(r,["id","assumptions","conclusion","dependencies","evidence_declarations","status"]) for r in geometry],
        "source_contract_exact_label_intersections":overlaps,
        "closure_frontier": document(ROUND+"CLOSURE_OBLIGATIONS.json")["source_constraint_frontier"],
        "historical_cuts": document(BASE+"post290/STEP4_CUTS.json")["cuts"],
        "composition": {"open_targets": [restrict(r,["id","declaration","status","truth_established"]) for r in public["open_research"]],
                        "approved_intermediate_edges": menu_rows, "search_kernel_acceptance": menu["kernel_acceptance"],
                        "catalogue_grants_proof": public["target_registration_grants_proof"],
                        "provider_exports": provider_api["apis"], "provider_mode": provider_api["mode"],
                        "provider_commit": provider_api["commit"], "model_optimality": provider_api["model_optimality"],
                        "host_interfaces":provider["host_interfaces"],"direct_cross_version_imports":provider["cross_version_imports"]},
    }


def relative_sign(interval, base=0):
    lo, hi = Fraction(interval["lower"]), Fraction(interval["upper"])
    assert lo <= hi
    return "above" if lo > base else "below" if hi < base else "contains"


def contain(outer, inner):
    if isinstance(inner, dict):
        assert outer.keys() == inner.keys()
        if inner.keys() == {"lower","upper"}:
            assert Fraction(outer["lower"]) <= Fraction(inner["lower"]) <= Fraction(inner["upper"]) <= Fraction(outer["upper"])
            return 1
        return sum(contain(outer[k],v) for k,v in inner.items())
    if isinstance(inner, list):
        assert len(outer) == len(inner)
        return sum(contain(x,y) for x,y in zip(outer,inner))
    assert type(outer) is type(inner) and outer == inner
    return 0


def stacked():
    folder = EVIDENCE / "PR302_POST_GREEN_5B2BD397"
    reg_data = (folder/"VERIFIED_ARTIFACTS.json").read_bytes()
    registry = json.loads(reg_data)
    used = {}
    def read(key, member):
        item = registry[key]["current"]
        file = folder/item["file"]
        if key not in used:
            assert digest(file.read_bytes()) == item["sha256"]
            used[key] = {"id":item["id"],"sha256":item["sha256"],"members":{}}
        with zipfile.ZipFile(file) as zin:
            raw = zin.read(member)
        assert digest(raw) == item["members"][member]
        used[key]["members"][member] = digest(raw)
        return json.loads(raw)
    c = read("opica5-composite-evidence","composite-candidate-evidence.json")
    assert c["current_head"] == DIAGNOSTIC and c["workflow_attempt"] == 2
    results = {}
    comparisons = 0
    for case in c["case_digests"]:
        refined_name = "fresh-refined/"+case+".json"
        row = read("opica5-fresh-refined",refined_name)
        assert used["opica5-fresh-refined"]["members"][refined_name] == c["case_digests"][case]
        assert row["request"]["id"] == case and not row["is_zero_generated_detector"]
        counts = {}
        for mode in ["normal","optimized"]:
            producer = read("opica5-fresh-source",mode+"/"+case+".json")
            assert producer["request"] == row["request"]
            counts[mode] = contain(producer["enclosures"],row["enclosures"])
        comparisons += sum(counts.values())
        spectrum = row["enclosures"]["spectrum"]
        results[case] = {"request":row["request"],"authority":row["authority"],"is_zero_generated_detector":False,
                         "rational_containment_recheck":counts}
        if isinstance(spectrum,dict) and "signed_response_at_zero" in spectrum:
            results[case].update({
                "signed_endpoint_relative_to_one":relative_sign(spectrum["signed_response_at_zero"],1),
                "positive_reciprocal_mass_relative_to_one":relative_sign(spectrum["positive_reciprocal_mass"],1),
                "residue_signs":[relative_sign(r["residue"]) for r in spectrum["groups"]],
                "derivative_channel_signs":{t:relative_sign(q) for t,q in spectrum["negative_derivative_at_minus_t"].items()},
            })
    k3 = read("post287-wp4-k3-gate","wp4-k3-feasibility.json")
    panel = read("post290-native-observations","CONSTRAINTS.json")
    ray = read("post287-wp6-signed-ray","post287-wp6.json")
    assert comparisons == c["direct_interval_containments"]
    return {"composite":c,"six_interval_cases":results,"total_exact_containments_rechecked":comparisons,
            "k3":{"box_verdicts":dict(collections.Counter(b["verdict"] for b in k3["boxes"])),
                  **restrict(k3,["all_aperture_positivity_certified","certified_negative_stop","tested_boxes","terminal_claim"])},
            "panel":restrict(panel,["consistent_pair_count","prohibited_identification","step4_upper_law","independent_rh_theorem_authority"]),
            "wp6": restrict(ray,["disposition","status","tested_target","not_claimed"]),
            "registry_sha256":digest(reg_data),"recomputed_artifact_hashes":used}


if __name__ == "__main__":
    result = {"installed_main":MAIN,"native":native_routes(),"registers":registers(),"separate_stacked_diagnostic":stacked()}
    result["main_file_sha256"] = PROVENANCE
    (HERE/"computed.json").write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n",encoding="utf-8")
