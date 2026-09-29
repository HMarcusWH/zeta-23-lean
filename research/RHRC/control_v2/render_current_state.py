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
    experimental = state.get("merged_experimental_research_evidence") or {}
    control = state["merged_control_anchor"]
    candidate = state.get("candidate_branch") or {}
    return f"""## Current RHRC state

THEOREM AUTHORITY
- merged theorem authority = PR #{theorem['pr']}
- validated final head = {theorem['validated_head']}
- merge commit = {theorem['merge_commit']}
- tree = {theorem['tree']}
- status = {theorem['status']}
- PR #275 full-space small-aperture coercive base = PROVED
- PR #276 exact legal successor ground >= 1 on 0 < L <= 1/512 = PROVED
- PR #272 CofinalCanonicalArithmeticCertificates <-> Mathlib RiemannHypothesis = PROVED / AUDIT-ONLY
- RH = OPEN

CURRENT RESEARCH FRONTIER
- current candidate PR = #{candidate.get('pr', 'NONE')} / {candidate.get('status', 'NONE')}
- candidate theorem-validation head = {candidate.get('theorem_validation_head', 'NONE')}
- candidate theorem-validation status = {candidate.get('theorem_validation', 'NONE')}
- merged experimental research evidence = PR #{experimental.get('pr', 'NONE')} / {experimental.get('disposition', 'NONE')}
- fixed-N sign opposition = {route.get('post277_fixedN_ground_sign_opposition', 'OPEN')}
- global ground propagation strength = {route.get('post277_global_ground_propagation_strength', 'UNAUDITED')}
- uniform domination strength = {route.get('post277_uniform_domination_strength', 'UNAUDITED')}
- active obstruction = {route['current_obstruction']}
- active subobligation = {route['current_active_subobligation']}
- next research target = {route['current_next_research_target']}
- required new information = {route['current_required_new_information']}
- RH-sufficient terminal formulations are not counted as independent sub-RH progress

FRAMEWORK / GRAPH STATE
- PR #270 = FFBBP 1.7 / OoL-MVS 2.7.7 framework architecture authority
- post-#276 exactified source-only theorem/lemma roots = {route['post276_source_only_public_theorem_count']}
- post-#276 FFBBP source-only module cohorts = {route['post276_ffbbp_source_only_module_cohort_count']}
- post-#276 OoL theorem-value-erased frontier contacts = {route['post276_ool_frontier_contact_count']}
- post-#276 RHKG relations = {route['post276_graph_relation_count']}
- framework output -> Lean theorem authority = FORBIDDEN

RESEARCH / CONTROL FIREWALL
- latest independent bounded research evidence = PR #{research['pr']}
- merged first-contact atlas evidence = PR #{experimental.get('pr', 'NONE')} / EXPERIMENTAL_SIGNAL_ONLY
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
