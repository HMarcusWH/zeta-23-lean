"""Shared, dependency-free provenance and exact-partition checks for certificates.

These checks validate evidence structure only; fresh Arb evaluation is still
required. A self-described PASS, a checksum, or a receipt is never positivity.
"""
from __future__ import annotations

import hashlib
import json
import subprocess
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[4]
BASE = "research/RHRC/routes/R003_ccm_bridge/"
LAYERS = {(q, p) for q in range(1, 16) for p in ("even", "odd")}
# Freeze transitive evaluator, basis, coordinate and acceptance dependencies.
# Some imported discovery utilities are deliberately included conservatively.
SOURCE_INPUTS = [BASE + p for p in (
    "canonical_source_arb.py", "canonical_source_numeric.py",
    "post150_selected_residual.py", "post166_fb05_cell_interval.py",
    "post167_fb05_threshold_jet.py", "post169_fb05_schur_visibility.py",
    "post173_fb05_q13_scalar_barrier.py", "post175_fb05_q13_fixed_unit_enclosure.py",
    "post177_fb05_q13_fixed_unit_derivative.py",
    "post194_fb05_q14_fixed_unit_second_derivative.py",
    "post247_remainder_budget_ratio_scout.py",
    "post285/post285_m51_k2_even_bottom_certificate.py",
    "fixtures/post175_fb05_q13_fixed_unit_enclosure_v1.json", "requirements.txt",
    "post287/certificate_integrity.py", "post287/wp2_k2_even_transcript.py",
    "post287/wp2_verify_transcript.py", "post287/wp2_wp4_normalization_gate.py",
    "post287/wp2_literature_form_arb_probe.py",
    "post287/wp4_k2_odd_prerequisite.py", "post287/wp4_k3_frozen_q14_gate.py",
    "post287/wp4_k3_fourth_order_fallback.py", "post287/wp4_fourth_order_validate.py",
    "post287/wp4_k3_full_continuum.py", "post287/wp4_k3_verify_full_transcript.py",
    "post287/wp4_k3_assemble_shards.py",
)] + ["research/RHRC/routes/R004_prolate_v2/run_commutator_gauntlet_v2.py"]


def source_input_digests() -> dict[str, str]:
    return {p: hashlib.sha256((REPO_ROOT / p).read_bytes()).hexdigest()
            for p in SOURCE_INPUTS}


def source_commit() -> str:
    return subprocess.check_output(["git", "rev-parse", "HEAD"],
                                   cwd=REPO_ROOT, text=True).strip()


def assert_source_unchanged(initial: dict) -> dict:
    if source_input_digests() != initial:
        raise RuntimeError('certificate source files changed while computation was running')
    return initial


def rational(pair) -> Fraction:
    if (not isinstance(pair, list) or len(pair) != 2 or
            any(type(v) is not int for v in pair) or pair[1] <= 0):
        raise ValueError("expected two exact integers with positive denominator")
    return Fraction(*pair)


def record_path(directory: Path, name: str) -> Path:
    if not isinstance(name, str) or Path(name).name != name or "\\" in name:
        raise ValueError("certificate record must be a local basename")
    result = directory / name
    if result.resolve().parent != directory.resolve():
        raise ValueError("certificate record escapes its directory")
    return result


def validate_layer(spec: dict, data: dict, method: str,
                   expected_bounds=None) -> bool:
    """Validate counts, labels and a full accepted+unresolved rational partition.

    Return whether the entire layer is certified according to its structure.
    No numerical bound is accepted here; the verifier recomputes every tile.
    """
    cell, parity = spec["cell"], spec["parity"]
    if (cell, parity) not in LAYERS or type(cell) is not int:
        raise AssertionError(("invalid layer", cell, parity))
    if spec["file"] != f"k3_Q{cell:02d}_{parity}.json":
        raise AssertionError("noncanonical layer filename")
    if data["Q"] != cell or data["parity"] != parity:
        raise AssertionError("manifest/payload layer mismatch")
    accepted, unresolved = data["accepted"], data["unresolved"]
    if (type(spec["intervals"]) is not int or
            type(spec["unresolved_count"]) is not int or
            spec["intervals"] != len(accepted) or
            spec["unresolved_count"] != len(unresolved)):
        raise AssertionError("manifest/payload counts disagree")
    complete = not unresolved
    expected_status = "PASS" if complete else "UNRESOLVED"
    if spec["status"] != expected_status or data["status"] != expected_status:
        raise AssertionError("manifest/payload disposition disagrees with unresolved set")
    left, right = rational(data["left"]), rational(data["right"])
    if not left < right or (expected_bounds is not None and
                            (left, right) != expected_bounds):
        raise AssertionError("incorrect layer target")
    previous = left
    for tile in accepted:
        lo, hi = rational(tile["left"]), rational(tile["right"])
        if lo < previous or not left <= lo < hi <= right:
            raise AssertionError("accepted tiles overlap or are out of range")
        if tile.get("accepted") is not True or tile.get("method") != method:
            raise AssertionError("tile method/disposition differs from producer")
        previous = hi
    pieces = sorted((rational(t["left"]), rational(t["right"]))
                    for t in accepted + unresolved)
    cursor = left
    for lo, hi in pieces:
        if lo != cursor or not left <= lo < hi <= right:
            raise AssertionError("accepted plus unresolved set has a gap or overlap")
        cursor = hi
    if cursor != right:
        raise AssertionError("partition does not reach target endpoint")
    return complete


def validate_gate(path: Path, method: str) -> dict:
    gate = json.loads(path.read_text())
    schema = ("post287.wp4.k3-frozen-gate.v1" if method == "SECOND"
              else "post287.wp4.fourth_order.v1")
    fixture = json.loads((REPO_ROOT / BASE / "fixtures/"
                          "post175_fb05_q13_fixed_unit_enclosure_v1.json").read_text())
    expected=frozen_box_keys(fixture)
    required=len(expected)
    if (gate.get("schema") != schema or gate.get("terminal_claim") != "RH_OPEN" or
            gate.get("source_digests") != source_input_digests() or
            gate.get("gate") != "PASS" or gate.get("precision_bits") != 384 or
            gate.get("tested_boxes") != required or gate.get("frozen_boxes") != required or
            len(gate.get("boxes", [])) != required or
            any(b.get("verdict") != "PASS" for b in gate["boxes"]) or
            gate.get('certified_negative_stop') is not False or
            {box_key(b,method) for b in gate['boxes']} != expected):
        raise ValueError("gate must be a complete source-bound 384-bit frozen PASS")
    if method == "SECOND" and not 0 <= gate["max_depth"] <= 40:
        raise ValueError("second-order gate exceeded frozen depth cap")
    return gate


def validate_second_failure(path: Path) -> dict:
    gate=json.loads(path.read_text())
    fixture=json.loads((REPO_ROOT / BASE / 'fixtures/'
                        'post175_fb05_q13_fixed_unit_enclosure_v1.json').read_text())
    expected=frozen_box_keys(fixture)
    actual=[box_key(b,'SECOND') for b in gate.get('boxes',[])]
    if (gate.get("schema") != "post287.wp4.k3-frozen-gate.v1" or
            gate.get("terminal_claim") != "RH_OPEN" or
            gate.get("source_digests") != source_input_digests() or
            gate.get("precision_bits") != 384 or gate.get("gate") != "UNRESOLVED" or
            gate.get('certified_negative_stop') is not False or
            gate.get('tested_boxes') != len(actual) or
            gate.get('frozen_boxes') != len(expected) or
            len(actual) != len(set(actual)) or not set(actual) <= expected or
            not 0 <= gate.get('max_depth',-1) <= 40 or
            (set(actual)==expected and all(b.get('verdict')=='PASS' for b in gate['boxes']))):
        raise ValueError("FOURTH requires a recorded source-bound SECOND failure")
    return gate


def frozen_box_keys(fixture: dict) -> set:
    expected={(14,Fraction(str(b['t'])),Fraction(1,2**k),parity,'primary')
              for b in fixture['primary_Q14_centers']
              for k in fixture['primary_radius_bits'] for parity in ('even','odd')}
    expected.update((b['Q'],Fraction(str(b['t'])),Fraction(1,2**b['radius_bit']),
                     parity,'control') for b in fixture['control_boxes']
                    for parity in ('even','odd'))
    return expected


def box_key(box: dict, method: str) -> tuple:
    t=Fraction(box['t']) if method=='SECOND' else rational(box['t'])
    radius=Fraction(box['radius']) if method=='SECOND' else rational(box['halfwidth'])
    return box['Q'],t,radius,box['parity'],box['kind']
