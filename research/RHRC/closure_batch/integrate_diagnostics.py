from __future__ import annotations

import argparse
import json
from pathlib import Path


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def save(path: Path, obj: dict) -> None:
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--results", required=True)
    args = ap.parse_args()
    root = Path(args.results)

    mapping = {
        "A": ("track_a.json", "diagnostic_a_small_aperture.json"),
        "B": ("track_b.json", "diagnostic_b_schur_arb.json"),
        "C": ("track_c.json", "diagnostic_c_characteristic.json"),
        "D": ("track_d.json", "diagnostic_d_r002.json"),
    }
    for track, (track_name, diagnostic_name) in mapping.items():
        tp, dp = root / track_name, root / diagnostic_name
        row, diag = load(tp), load(dp)
        if row.get("track_id") != track:
            raise SystemExit(f"{track}: track id drift")
        if diag.get("terminal_claim") != "RH_OPEN":
            raise SystemExit(f"{track}: diagnostic attempted terminal promotion")
        dclass = str(diag.get("classification", "UNCLASSIFIED"))
        base = str(row.get("research_disposition", "UNCLASSIFIED"))

        if track == "B" and int(diag.get("certified_bad_interval_count", 0)) > 0:
            disposition = (
                "RIGOROUS_BOUNDED_CANONICAL_SCHUR_COUNTEREVIDENCE_"
                "UNIVERSAL_DOMINATION_CANDIDATE_FALSIFIED_ON_FROZEN_SCOPE"
            )
        else:
            disposition = base + "__DIAGNOSTIC_" + dclass

        row["base_research_disposition"] = base
        row["diagnostic_classification"] = dclass
        row["research_disposition"] = disposition
        row["diagnostic_file"] = diagnostic_name
        row["theorem_authority"] = False
        row["rh_closure"] = False
        row["terminal_claim"] = "RH_OPEN"
        save(tp, row)

    print("CLOSURE DIAGNOSTIC INTEGRATION: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
