"""Finite restricted plans; joins retrieve candidates and never certify a match."""
from __future__ import annotations
from .canonical import require, closed_keys, digest_text, canonical_bytes, digest
from .contracts import CompositionProposal, CandidateBatch, TargetSpec, GrammarProfile, SearchBudget

def validate_plan(plan, budget=None):
    budget = budget or SearchBudget()
    count = 0
    pending = [(plan, 0)]
    while pending:
        p, depth = pending.pop(); count += 1
        require(count <= budget.term_nodes and depth <= budget.term_depth, "RESOURCE_EXHAUSTED: plan budget")
        require(type(p) is dict and type(p.get("tag")) is str, "closed plan node required")
        tag = p["tag"]
        shapes = {"const": {"tag", "constant_id"}, "local": {"tag", "binder_slot"},
            "app": {"tag", "function", "arguments"}, "lambda": {"tag", "body"},
            "let": {"tag", "value", "body"}, "project": {"tag", "constant_id", "value"},
            "cases": {"tag", "value", "branches"}, "transport": {"tag", "constant_id", "arguments"}}
        require(tag in shapes, "unknown grammar tag")
        closed_keys(p, shapes[tag])
        if "constant_id" in p: digest_text(p["constant_id"], "constant ID")
        if tag == "local": require(type(p["binder_slot"]) is int and 0 <= p["binder_slot"] < 10000, "invalid rigid local slot")
        for key in ("value", "body", "function"):
            if key in p: pending.append((p[key], depth + 1))
        for key in ("arguments", "branches"):
            if key in p:
                require(type(p[key]) is list and len(p[key]) <= budget.term_nodes, "bounded node array required")
                pending.extend((x, depth + 1) for x in p[key])
    canonical_bytes(plan)
    return count

def used_constant_ids(plan):
    validate_plan(plan)
    found = set(); pending = [plan]
    while pending:
        p = pending.pop()
        if "constant_id" in p: found.add(p["constant_id"])
        pending += [p[k] for k in ("value", "body", "function") if k in p]
        for k in ("arguments", "branches"): pending += p.get(k, [])
    return found

def enumerate_candidates(inventory, target, grammar, budget, *, search_contract=None):
    require(type(target) is TargetSpec and type(grammar) is GrammarProfile and type(budget) is SearchBudget,
            "trusted typed enumeration inputs required")
    forbidden = set(grammar.excluded_declarations) | set(target.forbidden_constants or []) | {target.declaration}
    rows = []
    # Reviewed first-calibration menu. The producer receives only D02, the
    # actual D05/D04 theorem and logical constructors; the answer wrapper and
    # evaluator target remain excluded. This is recovery of a known endpoint.
    reverse={name:cid for cid,name in target.allowed_constants.items()}
    endpoint=("D05","Zeta23.OPICARound3.first_simultaneous_newborn_source_witnesses") if target.declaration=="Zeta23.OPICAComposition.CofinalNewbornPacket" else (
        ("D04","Zeta23.OPICARound3.first_simultaneous_neutral_negative_cutoff") if target.declaration=="Zeta23.OPICAComposition.CofinalSchurPacket" else None)
    if endpoint is not None:
        needed={"D02":"Zeta23.OPICARound3.cofinally_both_neutral_negative_of_off_line_zero",
                endpoint[0]:endpoint[1],"And.intro":"And.intro","Exists.intro":"Exists.intro"}
        if all(name in reverse and name not in forbidden for name in needed.values()):
            plan=calibration_plan({key:reverse[name] for key,name in needed.items()},endpoint[0])
            validate_plan(plan,budget)
            rows.append({"action_id":digest(plan,domain="OPICA_REVIEWED_CALIBRATION_PLAN_V1"),
                         "declaration":None,"term_plan":plan,"scientific_scope":"KNOWN_ENDPOINT_CALIBRATION"})
    search_complete = True
    if search_contract is not None:
        from .composition_search import retrieve
        require(set(search_contract) in ({"expected_expression","statements"},{"expected_expression","statements","proof_constants"}), "closed retrieval contract required")
        proposed, search_complete, provenance = retrieve(inventory,target,grammar,budget,
            search_contract["expected_expression"],search_contract["statements"],search_contract.get('proof_constants',[]))
        rows.extend({**row,"search_provenance":provenance} for row in proposed)
    for cid, name in sorted(target.allowed_constants.items()):
        if name in forbidden: continue
        # This is a finite menu, not a claim that a bare theorem solves the goal.
        rows.append({"action_id": cid, "declaration": name, "term_plan": {"tag": "const", "constant_id": cid}})
    complete = len(rows) <= budget.candidates and search_complete
    return CandidateBatch(inventory.digest, target.target_id, rows[:budget.candidates], complete,
                          ("ENUMERATED" if rows else "NO_MATCH_IN_GRAMMAR") if complete else "RESOURCE_EXHAUSTED")

def calibration_plan(constants, destination="D05"):
    """D02 to D05/D04 by shared scoped eliminations. No answer constant appears.

    Slots 0..2 are rho, off-line premise, R. Every cases node appends its
    own binders; the dependent D05 packet is preserved as one shared term.
    """
    def c(name): return {"tag": "const", "constant_id": constants[name]}
    def l(slot): return {"tag": "local", "binder_slot": slot}
    def app(name,*args): return {"tag":"app","function":c(name),"arguments":list(args)}
    def cases(value,body): return {"tag":"cases","value":value,"branches":[body]}
    def ex(w,p): return app("Exists.intro",w,p)
    def pair(a,b): return app("And.intro",a,b)
    # D02 gives L and hRL/hL/K/hK/hboth, appended in that order.
    # The D05/D04 output gives Ke, Ko, one full packet; never splice witnesses.
    end = ex(l(3),pair(l(5),ex(l(7),ex(l(13),ex(l(15),l(16))))))
    out = cases(app(destination,l(7),l(11),l(12)),
                cases(l(14),end))
    out = cases(l(10),out)
    out = cases(l(8),out)
    out = cases(l(6),out)
    out = cases(l(4),out)
    out = cases(app("D02",l(0),l(1),l(2)),out)
    validate_plan(out)
    return out
