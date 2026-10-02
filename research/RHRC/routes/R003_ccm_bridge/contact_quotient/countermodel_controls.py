from __future__ import annotations

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
RHRC = HERE.parents[2]
CLOSURE_BATCH = RHRC / "closure_batch"
COUNTERMODELS = RHRC / "countermodels"
for path in (CLOSURE_BATCH, COUNTERMODELS):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

from first_crossing_generic_falsifiers import harvest as generic_harvest  # noqa: E402
from post204_pair_d_exact_geometry import certify_c1  # noqa: E402


def replay_controls() -> dict:
    generic = generic_harvest()
    if generic["claim_cap"] != "SYNTHETIC_GENERIC_COUNTERMODEL_ONLY":
        raise AssertionError("generic first-crossing claim cap drift")
    if generic["terminal_claim"] != "RH_OPEN":
        raise AssertionError("generic first-crossing control attempted RH promotion")

    pair_d = certify_c1()
    if pair_d["status"] != "PASS":
        raise AssertionError("Pair-D C1 control did not certify")
    if not pair_d["simultaneous_badness"]:
        raise AssertionError("Pair-D C1 no longer has simultaneous badness")
    if pair_d["canonical_realizability"] is not False:
        raise AssertionError("Pair-D C1 canonical-realizability firewall drift")

    return {
        "schema_version": "RHRC-CONTACT-QUOTIENT-COUNTERMODEL-CONTROLS-1.0",
        "status": "PASS",
        "claim_cap": "NEGATIVE_CONTROLS_ONLY",
        "generic_first_crossing": {
            "cubic_disposition": generic["cubic_contact"]["disposition"],
            "singular_disposition": generic["singular_coupling_contact"]["disposition"],
            "terminal_claim": generic["terminal_claim"],
        },
        "pair_d_c1": {
            "classification": pair_d["classification"],
            "reversal_symmetric": bool(pair_d["reversal_symmetric"]),
            "centered_index_commutator_zero": bool(pair_d["centered_index_commutator_zero"]),
            "simultaneous_badness": bool(pair_d["simultaneous_badness"]),
            "canonical_realizability": bool(pair_d["canonical_realizability"]),
        },
        "interpretation": (
            "The controls certify that generic Hermitian/contact and Pair-D parity "
            "geometry can support crossings/badness. They do not instantiate the "
            "canonical zeta source and are not RH counterexamples."
        ),
        "terminal_claim": "RH_OPEN",
        "theorem_promotion": False,
    }


if __name__ == "__main__":
    import json
    print(json.dumps(replay_controls(), indent=2, sort_keys=True))
