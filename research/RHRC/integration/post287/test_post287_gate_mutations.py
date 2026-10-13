#!/usr/bin/env python3
"""Mutation controls for executable Lean wiring and non-zeta claim discipline."""
from pathlib import Path
import copy
import json
from check_implementation_completeness import validate_focused_workflow
from check_post287_ledgers import validate_wp5_model_scope, validate_d2_deferral, validate_wp4_gate

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

ledger = json.loads((root / "research/RHRC/integration/post287/OPEN_OBLIGATIONS.json").read_text())
validate_d2_deferral(ledger)
validate_wp4_gate(ledger)
def mutated(changes):
    obj=copy.deepcopy(ledger)
    changes(obj)
    return obj
def must_reject_scope(fn):
    must_reject(lambda: validate_d2_deferral(mutated(fn)))
def must_reject_wp4(fn):
    must_reject(lambda: validate_wp4_gate(mutated(fn)))
must_reject_scope(lambda d: d['requirements'].__setitem__('D2','WEAKER_D2'))
must_reject_scope(lambda d: d['merge_scope'].__setitem__('D2_full_status','COMPLETE'))
must_reject_scope(lambda d: d['merge_scope'].__setitem__('authorized_by','UNKNOWN'))
must_reject_scope(lambda d: d['merge_scope']['original_campaign'].__setitem__('source_commit','0'*40))
must_reject_scope(lambda d: d['merge_scope']['original_campaign'].__setitem__('unresolved_intervals',0))
must_reject_scope(lambda d: d.__setitem__('terminal_claim','RH_PROVED'))
must_reject_wp4(lambda d: d['packages'][4].__setitem__('status','PROVED'))
must_reject_wp4(lambda d: d['packages'][4].__setitem__('full_window_status','INTERVAL_EVIDENCE'))
must_reject_wp4(lambda d: d['packages'][4].__setitem__('source_campaign_commit','f'*40))
must_reject_wp4(lambda d: d['packages'][4].__setitem__('remaining_layer_intervals',{}))
must_reject_wp4(lambda d: d['packages'][4].__setitem__('fallback','missing.py'))
must_reject_wp4(lambda d: d['packages'][4].__setitem__('frozen_second_gate','UNRESOLVED'))
print("POST287 FAIL-CLOSED MUTATION CHECK: PASS (17 negative controls; D2 deferral and original-source guards)")

