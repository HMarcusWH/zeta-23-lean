#!/usr/bin/env python3
"""Read-only, byte-exact numerical-source bridge from approved D2 to PR292.

This checks INPUT identity, not D2 positivity, Lean proof validity, or
completion of the 460-child campaign. A changed mathematical input fails
closed; there is no metadata-only override or silent source repair.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[5]
D2_RUN_ID = 38569316691
D2_PRODUCER_HEAD = "a55fbeeed6500bffe2ccac3960258ca5c590c7ee"
D2_PRODUCER_TREE = "7ffdf5095db2d54ef97897c19797886d145b65d2"
SEAM_SOURCE_PATHS = (
    "Zeta23/CCM/KernelAnalysis.lean",
    "Zeta23/CCM/CanonicalPrimeSeamTaylor.lean",
    "Zeta23/CCM/SourceMatrix.lean",
)
POST287 = REPO / "research/RHRC/routes/R003_ccm_bridge/post287"
sys.path.insert(0, str(POST287))
from certificate_integrity import SOURCE_INPUTS  # Frozen canonical evaluator inputs.


def git(*args: str) -> bytes:
    return subprocess.check_output(("git", *args), cwd=REPO)


def hex40(value: object) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value) is not None


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def exact_numeric_source(proof_head: str | None = None, proof_tree: str | None = None) -> dict:
    """Compare BOTH Git trees and every frozen evaluator/seam input byte."""
    head = proof_head or git("rev-parse", "HEAD").decode().strip()
    tree = proof_tree or git("rev-parse", "HEAD^{tree}").decode().strip()
    if not hex40(head) or not hex40(tree):
        raise ValueError("invalid proof Git identity")
    if head != git("rev-parse", "HEAD").decode().strip():
        raise ValueError("not checking the current exact proof checkout")
    if tree != git("rev-parse", head + "^{tree}").decode().strip():
        raise ValueError("proof Git commit/tree mismatch")
    if git("rev-parse", D2_PRODUCER_HEAD + "^{tree}").decode().strip() != D2_PRODUCER_TREE:
        raise ValueError("approved D2 producer Git tree changed or missing")
    source_paths = tuple(dict.fromkeys((*SOURCE_INPUTS, *SEAM_SOURCE_PATHS)))
    if len(source_paths) < 25:
        raise ValueError("canonical numerical dependency inventory unexpectedly small")
    checked = {}
    for path in source_paths:
        if path.startswith("/") or ".." in Path(path).parts:
            raise ValueError("unsafe source path")
        producer = git("show", D2_PRODUCER_HEAD + ":" + path)
        final = git("show", head + ":" + path)
        p_hash, f_hash = sha256(producer), sha256(final)
        if p_hash != f_hash:
            raise ValueError("D2 mathematical source changed: " + path)
        checked[path] = p_hash
    return {
        "schema": "RH_POST292_D2_SOURCE_EQUIVALENCE_1.0",
        "execution_status": "SUCCESS",
        "integrity_status": "PASS",
        "source_identity_method": "EXACT_GIT_BLOB_BYTES_SHA256",
        "d2_run_id": D2_RUN_ID,
        "d2_producer_head": D2_PRODUCER_HEAD,
        "d2_producer_tree": D2_PRODUCER_TREE,
        "proof_head": head,
        "proof_tree": tree,
        "compared_file_count": len(checked),
        "canonical_inputs": {path: checked[path] for path in SOURCE_INPUTS},
        "seam_sources": {path: checked[path] for path in SEAM_SOURCE_PATHS},
        "scope": "SOURCE_IDENTITY_ONLY; independent 768-bit D2 nonpartial checker still required",
        "terminal_claim": "RH_OPEN",
        "not_a_lean_proof": True,
    }


def verify_d2_receipt(d2: dict, equivalence: dict, run_id: int = D2_RUN_ID) -> None:
    """Additional provenance check; NEVER infer mathematical coverage from it."""
    if type(run_id) is not int or run_id != D2_RUN_ID:
        raise ValueError("not the single approved D2 execution")
    if equivalence.get("integrity_status") != "PASS" or \
            equivalence.get("d2_run_id") != run_id:
        raise ValueError("missing verified source identity")
    if d2.get("source_tree") != D2_PRODUCER_TREE:
        raise ValueError("D2 checker did not use approved producer source tree")
    original = d2.get("current_source", {})
    if original.get("commit") != D2_PRODUCER_HEAD or original.get("tree") != D2_PRODUCER_TREE:
        raise ValueError("D2 receipt is not from the approved producer")
    if original.get("source_digests") != equivalence.get("canonical_inputs"):
        raise ValueError("D2 receipt's exact evaluator source digest map differs")
    seams = original.get("seam_source_bindings", {}).get("bindings", {})
    for item in seams.values():
        if not isinstance(item, dict) or \
                item.get("sha256") != equivalence["seam_sources"].get(item.get("path")):
            raise ValueError("D2 physical-seam mathematical source differs")
    if d2.get("terminal_claim") != "RH_OPEN" or d2.get("not_a_lean_proof") is not True:
        raise ValueError("D2 claim boundary altered")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--d2", type=Path)
    ap.add_argument("--d2-run-id", type=int, default=D2_RUN_ID)
    args = ap.parse_args()
    equivalence = exact_numeric_source()
    if args.d2:
        verify_d2_receipt(json.loads(args.d2.read_text()), equivalence, args.d2_run_id)
        equivalence["d2_receipt_sha256"] = sha256(args.d2.read_bytes())
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(equivalence, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"integrity_status": "PASS", "compared_files": equivalence["compared_file_count"],
                      "d2_checked": args.d2 is not None, "not_a_lean_proof": True}))


if __name__ == "__main__":
    main()
