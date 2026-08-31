#!/usr/bin/env python3
"""Semantic regression firewall for the PR #71 source-normalization repair."""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]

manifest_path = ROOT / "research/RHRC/routes/R004_prolate_v2/CCM_FORMAL_PORT_MANIFEST.json"
registry_path = ROOT / "research/RHRC/CLAIM_REGISTRY.json"
finite_path = ROOT / "Zeta23/CCM/FiniteMatrix.lean"
repair_path = ROOT / "Zeta23/CCM/SourceNormalizationRepair.lean"

manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
registry = json.loads(registry_path.read_text(encoding="utf-8"))
finite_text = finite_path.read_text(encoding="utf-8")
repair_text = repair_path.read_text(encoding="utf-8")

errors: list[str] = []

params = manifest.get("parameter_conventions", {})
if params.get("formal_aperture_core") != "Zeta23.CCM.canonicalSourceMatrix":
    errors.append("R004 manifest must use canonicalSourceMatrix as formal_aperture_core.")
if params.get("legacy_printed_aperture_core") != "Zeta23.CCM.finiteMatrix":
    errors.append("R004 manifest must preserve finiteMatrix only as legacy_printed_aperture_core.")

mapping = manifest.get("mapping", {})
if mapping.get("canonical_source_matrix") != "Zeta23.CCM.canonicalSourceMatrix":
    errors.append("R004 manifest canonical_source_matrix binding is missing.")
if mapping.get("legacy_printed_matrix") != "Zeta23.CCM.legacyPrintedMatrix":
    errors.append("R004 manifest legacy_printed_matrix binding is missing.")

claim = next((c for c in registry.get("claims", [])
              if c.get("id") == "R004_CCM_DISPLACEMENT_FORMAL"), None)
if claim is None:
    errors.append("R004_CCM_DISPLACEMENT_FORMAL claim is missing.")
else:
    if claim.get("theorem") != "Zeta23.CCM.rank_canonicalSourceMatrix_displacement_le_two":
        errors.append("R004 displacement claim must bind the canonical-source theorem.")
    if "canonical direct-source" not in claim.get("statement", ""):
        errors.append("R004 displacement claim must say canonical direct-source.")

if "Historical printed-normalization finite matrix" not in finite_text:
    errors.append("FiniteMatrix.lean must retain the legacy printed-normalization label.")
if "Canonical finite CCM matrix" in finite_text:
    errors.append("FiniteMatrix.lean must not relabel finiteMatrix as canonical.")

required_repair_markers = [
    "def sourceEq411DerivedCorrection",
    "theorem sourceEq411_corrected_integrated_rewrite",
    "def canonicalSourceMatrix",
    "theorem canonicalSourceMatrix_eq_sourceEq44Matrix",
    "theorem canonicalSourceMatrix_eq_legacyPrintedMatrix_add_correction",
    "theorem canonicalSourceMatrix_displacement",
    "theorem rank_canonicalSourceMatrix_displacement_le_two",
]
for marker in required_repair_markers:
    if marker not in repair_text:
        errors.append(f"Missing normalization-repair marker: {marker}")

# Do not let the historical matrix become the ambient external QW restriction
# by a future wording-only edit.  The actual QW bridge must use the canonical
# source object and a separately theorem-locked correspondence.
for path in [finite_path, repair_path]:
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        compact = line.replace(" ", "")
        if "QW_lambda" in line and ("finiteMatrix=" in compact or "=finiteMatrix" in compact):
            errors.append(f"{path.relative_to(ROOT)}:{line_no}: direct QW_lambda/finiteMatrix identification forbidden.")

if errors:
    print("SOURCE NORMALIZATION FIREWALL: FAIL")
    for error in errors:
        print(f"- {error}")
    raise SystemExit(1)

print("SOURCE NORMALIZATION FIREWALL: PASS")
print("- canonical source matrix: Zeta23.CCM.canonicalSourceMatrix")
print("- legacy printed matrix: Zeta23.CCM.legacyPrintedMatrix")
print("- ambient QW_lambda finite restriction remains a separate bridge")
