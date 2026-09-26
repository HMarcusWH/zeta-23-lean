#!/usr/bin/env python3
"""Fail-closed scope check for the post-#272 first-contact atlas."""
from __future__ import annotations

import json
from pathlib import Path

import canonical_source_arb as ca
from post272_first_contact_atlas import CLAIM_CAP, SCHEMA, validate_fixture

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post272_first_contact_atlas_v1.json"


def main() -> int:
    f = json.loads(FIXTURE.read_text(encoding="utf-8"))
    validate_fixture(f)
    assert f["schema_version"] == SCHEMA
    assert f["claim_cap"] == CLAIM_CAP
    assert f["adaptive_search"] is False
    assert [(x["q"], x["K"]) for x in f["primary_cases"]] == [
        (13, 3), (16, 3), (17, 3), (14, 3), (15, 3)
    ]
    assert [(x["q"], x["K"]) for x in f["replication_cases"]] == [(16, 4), (17, 4)]
    assert f["offset_powers"] == [8, 10, 12]
    assert f["planted_gamma"] == [10, 1]
    assert f["planted_off_line_delta"] == [1, 20]
    for x in f["primary_cases"] + f["replication_cases"]:
        zero = ca.von_mangoldt(x["q"]).is_zero()
        if x["kind"] == "ZERO_VON_MANGOLDT_CONTROL":
            assert zero
        else:
            assert not zero
    print("POST272 FIRST-CONTACT ATLAS SCOPE: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
