from __future__ import annotations

import argparse
import json
from pathlib import Path


EXPECTED = {"A", "B", "C", "D"}


class HarvestError(ValueError):
    pass


def harvest(paths: list[Path]) -> dict:
    rows = [json.loads(p.read_text()) for p in paths]
    ids = [str(r.get("track_id")) for r in rows]
    if len(ids) != len(set(ids)):
        raise HarvestError("duplicate track result")
    if set(ids) != EXPECTED:
        raise HarvestError(f"track coverage mismatch: {set(ids)}")
    for r in rows:
        if r.get("execution_status") != "SUCCESS":
            raise HarvestError(f"execution failure in track {r.get('track_id')}")
        if r.get("integrity_status") != "PASS":
            raise HarvestError(f"integrity failure in track {r.get('track_id')}")
        if r.get("terminal_claim") != "RH_OPEN":
            raise HarvestError("research lane attempted terminal promotion")
    closed = [r["track_id"] for r in rows if r.get("rh_closure") is True]
    disposition = (
        "TERMINAL_CLAIM_REQUIRES_SEPARATE_LEAN_VALIDATION"
        if closed else "NO_RH_CLOSURE_ALL_PARALLEL_TRACKS_HARVESTED"
    )
    return {
        "schema_version": "RHRC-CLOSURE-HARVEST-1.0",
        "execution_status": "SUCCESS",
        "integrity_status": "PASS",
        "research_disposition": disposition,
        "track_dispositions": {r["track_id"]: r["research_disposition"] for r in rows},
        "terminal_claim": "RH_OPEN"
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--results", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    root = Path(args.results)
    out = harvest(sorted(root.glob("track_*.json")))
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
