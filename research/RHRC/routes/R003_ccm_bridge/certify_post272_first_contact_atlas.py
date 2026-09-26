#!/usr/bin/env python3
"""Certify interpretation/firewall invariants of the post-#272 atlas output."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

ALLOWED = {
    "CERTIFIED_CURRENT_PRIME_GROUND_RESPONSE",
    "NO_CERTIFIED_CURRENT_PRIME_GROUND_RESPONSE",
    "CONTROL_FAILURE",
}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    raw = json.loads(Path(args.input).read_text(encoding="utf-8"))
    assert raw["claim_cap"] == "EXPERIMENTAL_SIGNAL_ONLY"
    assert raw["adaptive_search"] is False
    s = raw["summary"]
    assert s["classification"] in ALLOWED
    assert s["theorem_promotion"] is False
    assert s["rh_claim"] is False
    assert any("entering atom vanishes" in x for x in raw["nonclaims"])
    assert any("RH remains OPEN" in x for x in raw["nonclaims"])
    for case in raw["cases"]:
        assert case["claim_cap"] == "EXPERIMENTAL_SIGNAL_ONLY"
        if case["kind"] == "ZERO_VON_MANGOLDT_CONTROL":
            assert case["von_mangoldt_is_zero"]
            assert case["seam"]["current_q_atom_exact_zero"]
            assert all(x["right"]["current_q_atom_exact_zero"] for x in case["scales"])
        else:
            assert not case["von_mangoldt_is_zero"]
    cert = {
        "schema_version": "POST272_TRUE_GROUND_FIRST_CONTACT_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "classification": s["classification"],
        "summary": s,
        "atlas": raw,
        "theorem_promotion": False,
        "rh_claim": False,
        "terminal_claim": "RH_OPEN",
    }
    Path(args.output).write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({k: cert[k] for k in ("status", "classification", "terminal_claim")}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
