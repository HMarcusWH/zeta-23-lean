#!/usr/bin/env python3
"""Mutation controls for executable Lean wiring and non-zeta claim discipline."""
from pathlib import Path
from check_implementation_completeness import validate_focused_workflow
from check_post287_ledgers import validate_wp5_model_scope

root = Path(__file__).resolve().parents[4]
focused = (root / ".github/workflows/rhrc_post287_focused.yml").read_text()
validate_focused_workflow(focused)

def must_reject(thunk):
    try:
        thunk()
    except (AssertionError, KeyError):
        return
    raise AssertionError("tampered implementation or claim scope accepted")

must_reject(lambda: validate_focused_workflow(
    focused.replace("Zeta23.CCM.ReciprocalApertureConcavity", "Zeta23.CCM.MISSING")))
must_reject(lambda: validate_focused_workflow(
    focused.replace('if lake build "$target"; then', 'if echo "$target"; then')))

valid = {"model_scope":"NON_ZETA_MODIFIED_PRIME","model_is_actual_zeta":False,
         "rh_counterexample_claim":False}
validate_wp5_model_scope(valid)
for key, bad in (("model_scope", "GENUINE_ZETA"),
                 ("model_is_actual_zeta", True),
                 ("rh_counterexample_claim", True)):
    tampered = {**valid, key: bad}
    must_reject(lambda tampered=tampered: validate_wp5_model_scope(tampered))
print("POST287 FAIL-CLOSED MUTATION CHECK: PASS (5 negative controls)")
