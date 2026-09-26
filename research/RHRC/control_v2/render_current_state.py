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
- PR #269 jointly cofinal bottom lower bounds -> finite-bottom nonnegativity = PROVED
- PR #269 cofinal lower certificates -> Mathlib RiemannHypothesis = PROVED / AUDIT-ONLY / CONDITIONAL
- RH = OPEN

CURRENT IMPLEMENTATION / OPEN TARGET
- current PR target = CANONICAL_ARITHMETIC_TO_GLOBAL_BOTTOM_AND_COFINAL_CERTIFICATE_BRIDGE
- arithmetic all-vector certificate -> -epsilon <= globalParitySuccessorBottom = CURRENT PR THEOREM TARGET
- CofinalCanonicalArithmeticCertificates -> RiemannHypothesis = CURRENT PR AUDIT TARGET
- cofinal arithmetic certificate construction = OPEN
- active obstruction = {route['current_obstruction']}
- next research target = {route['current_next_research_target']}
- required new information = {route['current_required_new_information']}
- no reverse RH-equivalence claim is made for CofinalCanonicalArithmeticCertificates

FRAMEWORK / GRAPH AUTHORITY
- PR #270 = FFBBP 1.7 assurance + OoL-MVS 2.7.7 governance + strict RHKG steady state
- FFBBP RUN46F executable authority = NOT PROMOTED
- OoL certificate VALID = attested binding, NOT physical or mathematical truth
- post-270 source-only theorem/lemma roots = {route['post270_source_only_public_theorem_count']}
- post-270 FFBBP source-only module cohorts = {route['post270_ffbbp_source_only_module_cohort_count']}
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
