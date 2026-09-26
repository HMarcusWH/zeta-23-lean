from __future__ import annotations

import argparse
import json
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
ROOT = RHRC.parent.parent
STATE = RHRC / "control_v2" / "CONTROL_STATE.json"

LIVING_SURFACES = (
    ROOT / "README.md",
    ROOT / "AUDIT.md",
    ROOT / "FORK_NOTES.md",
    RHRC / "CURRENT_RESEARCH_PLAN.md",
    RHRC / "DOCUMENTATION_AUTHORITY.md",
    RHRC / "FB05_INCOMPATIBILITY_PROGRAM.md",
    RHRC / "OBSTRUCTION_LEDGER.md",
    RHRC / "DEAD_ROUTES.md",
    RHRC / "README.md",
    RHRC / "RESEARCH_LEADS.md",
    RHRC / "VALIDATION_PROTOCOL.md",
    RHRC / "control_v2" / "README.md",
    RHRC / "routes" / "R003_ccm_bridge" / "README.md",
    RHRC / "countermodels" / "README.md",
)

BEGIN = "<!-- RHRC_CURRENT_STATE_BEGIN -->"
END = "<!-- RHRC_CURRENT_STATE_END -->"


def render_current_state_block(state: dict) -> str:
    theorem = state["merged_theorem_anchor"]
    route = state["active_research_route"]
    research = state["latest_research_evidence"]
    control = state["merged_control_anchor"]
    candidate = state.get("candidate_branch") or {}
    return f"""## Current RHRC state

THEOREM AUTHORITY
- merged theorem authority = PR #{theorem['pr']}
- validated final head = {theorem['validated_head']}
- merge commit = {theorem['merge_commit']}
- tree = {theorem['tree']}
- status = {theorem['status']}
- PR #269 legal parity-ground simplicity iff strict parity separation = PROVED
- PR #269 parity tie -> parity-split ground finrank >= 2 = PROVED
- PR #269 carrier-wide source-weight derivative nonnegativity = REFUTED / FORMAL COUNTEREXAMPLE
- PR #269 canonical arithmetic lower-bound normal form = PROVED
- PR #271 arithmetic all-vector certificate -> global legal bottom lower bound = PROVED
- PR #271 cofinal canonical arithmetic certificates -> Mathlib RiemannHypothesis = PROVED / AUDIT-ONLY / CONDITIONAL
- PR #272 CofinalCanonicalArithmeticCertificates <-> Mathlib RiemannHypothesis = PROVED / AUDIT-ONLY
- RH = OPEN

POST-#272 RESEARCH FRONTIER
- current PR = #{candidate.get('pr', 'NONE')} / {candidate.get('status', 'NONE')}
- direct cofinal certificate construction = {route['post271_cofinal_arithmetic_certificate_construction']}
- #272 equivalence audit = {route['post272_cofinal_arithmetic_rh_equivalence']}
- active obstruction = {route['current_obstruction']}
- active subobligation = {route['current_active_subobligation']}
- next research target = {route['current_next_research_target']}
- required new information = {route['current_required_new_information']}
- RH-equivalent terminal formulations are not counted as independent sub-RH progress

FRAMEWORK / GRAPH STATE
- PR #270 = FFBBP 1.7 / OoL-MVS 2.7.7 framework architecture authority
- post-#272 exactified source-only theorem/lemma roots = {route['post272_source_only_public_theorem_count']}
- post-#272 FFBBP source-only module cohorts = {route['post272_ffbbp_source_only_module_cohort_count']}
- post-#272 OoL theorem-value-erased frontier contacts = {route['post272_ool_frontier_contact_count']}
- post-#272 RHKG relations = {route['post272_graph_relation_count']}
- framework output -> Lean theorem authority = FORBIDDEN

RESEARCH / CONTROL FIREWALL
- latest independent bounded research evidence = PR #{research['pr']}
- post-249 = EXPERIMENTAL_SIGNAL_ONLY / no asymptotic rate / no exact first-zero switch
- frozen Control-v2 semantic authority = PR #{control['pr']}
- selected formal first break = E4A4-SCHUR-FB-05 (historical/frozen control semantics)
- R003 phase = DISCOVERY
- confirmatory execution = NOT AUTHORIZED
- terminal claim = {state['terminal_claim']}"""


def replace_block(text: str, block: str) -> str:
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise ValueError("expected exactly one current-state marker pair")
    prefix, rest = text.split(BEGIN, 1)
    _old, suffix = rest.split(END, 1)
    return prefix + BEGIN + "\n" + block + "\n" + END + suffix


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()

    state = json.loads(STATE.read_text(encoding="utf-8"))
    block = render_current_state_block(state)

    stale: list[str] = []
    for path in LIVING_SURFACES:
        text = path.read_text(encoding="utf-8")
        expected = replace_block(text, block)
        if text != expected:
            if args.write:
                path.write_text(expected, encoding="utf-8")
            else:
                stale.append(str(path.relative_to(ROOT)))

    if stale:
        raise SystemExit("current_state_renderer: stale surfaces: " + ", ".join(stale))
    if args.write:
        print(f"current_state_renderer: WROTE {len(LIVING_SURFACES)} living surfaces")
    else:
        print(f"current_state_renderer: PASS ({len(LIVING_SURFACES)} living surfaces)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
