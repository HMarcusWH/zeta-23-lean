from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path


@dataclass(frozen=True)
class FFBBPControlSnapshot:
    qualified_reference_version: str
    qualified_profile: str
    v16_theory_version: str
    v16_inherits_qualification: bool


def load_ffbbp_snapshot(rhrc_root: Path) -> FFBBPControlSnapshot:
    old = json.loads((rhrc_root / "ffbbp" / "FFBBP_REFERENCE.json").read_text(encoding="utf-8"))
    v16 = json.loads((rhrc_root / "ffbbp" / "FFBBP_V16_ASSURANCE_REFERENCE.json").read_text(encoding="utf-8"))
    return FFBBPControlSnapshot(
        qualified_reference_version=str(old["reference_architecture_version"]),
        qualified_profile=str(old["qualified_profile"]["name"]),
        v16_theory_version=str(v16["theory_version"]),
        v16_inherits_qualification=bool(v16["inherits_run42c_qualification"]),
    )
