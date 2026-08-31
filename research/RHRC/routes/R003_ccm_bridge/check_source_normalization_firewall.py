#!/usr/bin/env python3
"""Semantic regression firewall for the PR #71/#73 source-normalization repair.

This guard has two jobs:

1. Keep the executable/proof-object provenance split exact:
   - Python run_commutator_gauntlet_v2.py::build_ccm_matrix -> finiteMatrixOfLambda
     (legacy printed normalization).
   - canonical direct-source matrix -> canonicalSourceMatrix / cutoffFreeMatrix,
     with cutoffFreeMatrixOfLambda as its lambda wrapper.

2. Reject any future direct identification of the historical finiteMatrix with
   the ambient external QW_lambda finite restriction anywhere in the relevant
   CCM/R003/R004 claim/provenance surface.
"""

from __future__ import annotations

import json
import re
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
if params.get("formal_lambda_wrapper") != "Zeta23.CCM.cutoffFreeMatrixOfLambda":
    errors.append("R004 manifest must use cutoffFreeMatrixOfLambda as formal_lambda_wrapper.")
if params.get("legacy_printed_aperture_core") != "Zeta23.CCM.finiteMatrix":
    errors.append("R004 manifest must preserve finiteMatrix only as legacy_printed_aperture_core.")
if params.get("legacy_printed_lambda_wrapper") != "Zeta23.CCM.finiteMatrixOfLambda":
    errors.append("R004 manifest must preserve finiteMatrixOfLambda as legacy_printed_lambda_wrapper.")

mapping = manifest.get("mapping", {})
if mapping.get("build_ccm_matrix") != "Zeta23.CCM.finiteMatrixOfLambda":
    errors.append(
        "R004 manifest build_ccm_matrix must bind the Python executable to "
        "Zeta23.CCM.finiteMatrixOfLambda (legacy printed normalization)."
    )
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

# Broad relevant-surface scan.
#
# We intentionally scan code, claims, route docs, manifests, and source maps,
# not just the two files that originally carried the repair.  A future bridge
# is allowed to *mention* finiteMatrix and QW_lambda in the same file; what is
# forbidden is a direct equality/definition/equivalence that identifies them.
scan_roots = [
    ROOT / "Zeta23/CCM",
    ROOT / "research/RHRC/routes/R003_ccm_bridge",
    ROOT / "research/RHRC/routes/R004_prolate_v2",
]
scan_files = [
    ROOT / "Zeta23/CCM.lean",
    ROOT / "research/RHRC/CLAIM_REGISTRY.json",
    ROOT / "research/RHRC/routes/ROUTE_REGISTRY.json",
    ROOT / "research/RHRC/external/connes_cvs/SOURCE_MAP.md",
]
allowed_suffixes = {".lean", ".py", ".json", ".md", ".txt", ".yml", ".yaml"}

for root in scan_roots:
    if root.exists():
        scan_files.extend(
            p for p in root.rglob("*")
            if p.is_file() and p.suffix.lower() in allowed_suffixes
        )

# Match both directions, allowing common external spellings.
qw = r"(?:QW_lambda|QW_\\lambda|QWλ|QW\s*lambda)"
finite = r"(?:Zeta23\.CCM\.)?(?:legacyPrintedMatrix|finiteMatrix(?:OfLambda)?)"
relation = r"(?:=|:=|≡|↔|\bis\s+(?:exactly\s+)?(?:the\s+)?(?:finite\s+)?restriction\s+of\b)"

bad_patterns = [
    re.compile(rf"{finite}\s*{relation}[^\n]{{0,240}}{qw}", re.IGNORECASE),
    re.compile(rf"{qw}[^\n]{{0,240}}{relation}\s*{finite}", re.IGNORECASE),
]

seen: set[Path] = set()
for path in scan_files:
    if path in seen or not path.exists():
        continue
    seen.add(path)
    text = path.read_text(encoding="utf-8", errors="replace")
    for line_no, line in enumerate(text.splitlines(), 1):
        # Negative/meta statements are allowed: they document the firewall.
        lowered = line.lower()
        if any(token in lowered for token in (
            "forbid", "forbidden", "must not", "do not identify",
            "no theorem", "no source map", "remains a separate bridge",
        )):
            continue
        if any(pattern.search(line) for pattern in bad_patterns):
            errors.append(
                f"{path.relative_to(ROOT)}:{line_no}: direct legacy finiteMatrix/"
                "QW_lambda identification forbidden."
            )

if errors:
    print("SOURCE NORMALIZATION FIREWALL: FAIL")
    for error in errors:
        print(f"- {error}")
    raise SystemExit(1)

print("SOURCE NORMALIZATION FIREWALL: PASS")
print("- Python build_ccm_matrix -> Zeta23.CCM.finiteMatrixOfLambda (legacy)")
print("- canonical lambda wrapper -> Zeta23.CCM.cutoffFreeMatrixOfLambda")
print("- canonical source matrix -> Zeta23.CCM.canonicalSourceMatrix")
print(f"- scanned relevant files: {len(seen)}")
print("- ambient QW_lambda finite restriction remains a separate bridge")
