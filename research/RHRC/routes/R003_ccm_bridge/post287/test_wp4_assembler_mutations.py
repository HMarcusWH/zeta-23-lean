#!/usr/bin/env python3
"""Synthetic, adversarial controls for the WP4 hashchecked shard assembler.

No synthetic shard in this test is a proof or a numerical certificate.
"""
from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from wp4_k3_assemble_shards import local_source_digests

HERE = Path(__file__).resolve().parent
ASSEMBLER = HERE / "wp4_k3_assemble_shards.py"
HEAD = "TEST_SYNTHETIC_COMMIT"
DIGESTS = local_source_digests()

def dump(path: Path, obj: dict) -> bytes:
    raw = (json.dumps(obj, sort_keys=True, indent=2) + "\n").encode()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return raw

def one_shard(root: Path) -> dict:
    folder = root / "Q01-even"
    layer = {"Q": 1, "parity": "even", "status": "UNRESOLVED",
             "accepted": [], "unresolved": [{"reason": "SYNTHETIC_ONLY"}]}
    raw = dump(folder / "k3_Q01_even.json", layer)
    spec = {"cell": 1, "parity": "even", "file": "k3_Q01_even.json",
            "sha256": hashlib.sha256(raw).hexdigest(), "status": "UNRESOLVED",
            "intervals": 0, "unresolved_count": 1}
    manifest = {"schema": "post287.wp4.k3-full-continuum.v1",
                "terminal_claim": "RH_OPEN", "source_commit": HEAD,
                "source_digests": DIGESTS, "precision_bits": 192,
                "method": "SECOND", "records": [spec]}
    mbytes = dump(folder / "manifest.json", manifest)
    receipt = {"schema": "post287.wp4.checker.v1", "status": "PARTIAL_ACCEPTED_ONLY",
               "claimed_scope": "PARTIAL_ONLY", "verified_tiles": 0, "layers": 1,
               "precision_bits": 256,
               "manifest_sha256": hashlib.sha256(mbytes).hexdigest(),
               "source_digests": DIGESTS, "producer_commit": HEAD}
    dump(folder / "checker_receipt.json", receipt)
    return {"folder": folder, "manifest": manifest, "receipt": receipt}

def run(root: Path, target: Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(ASSEMBLER),
                           "--input", str(root), "--output", str(target)],
                          capture_output=True, text=True)

def check() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp)
        x = p / "shards"
        good = one_shard(x)
        accepted = run(x, p / "output-good")
        assert accepted.returncode == 0, accepted.stderr
        report = json.loads((p / "output-good" / "manifest.json").read_text())
        assert report["status"] == "UNRESOLVED"
        assert len(report["missing_layers"]) == 29
        assert report["all_L_positivity_certified"] is False

        layerfile = good["folder"] / "k3_Q01_even.json"
        layerfile.write_bytes(layerfile.read_bytes() + b" ")
        assert run(x, p / "out-tampered-tile").returncode != 0

        one_shard(x)
        receiptfile = good["folder"] / "checker_receipt.json"
        receipt = copy.deepcopy(good["receipt"])
        receipt["manifest_sha256"] = "0" * 64
        dump(receiptfile, receipt)
        assert run(x, p / "out-forged-receipt").returncode != 0

        one_shard(x)
        manifest = copy.deepcopy(good["manifest"])
        manifest["records"][0]["status"] = "PASS"
        manifest["records"][0]["unresolved_count"] = 0
        mbytes = dump(good["folder"] / "manifest.json", manifest)
        receipt = copy.deepcopy(good["receipt"])
        receipt["manifest_sha256"] = hashlib.sha256(mbytes).hexdigest()
        dump(receiptfile, receipt)
        assert run(x, p / "out-forged-pass").returncode != 0

        one_shard(x)
        manifest = copy.deepcopy(good["manifest"])
        manifest["source_digests"]["research/RHRC/routes/R003_ccm_bridge/post287/wp4_k3_full_continuum.py"] = "1" * 64
        mbytes = dump(good["folder"] / "manifest.json", manifest)
        receipt = copy.deepcopy(good["receipt"])
        receipt["manifest_sha256"] = hashlib.sha256(mbytes).hexdigest()
        dump(receiptfile, receipt)
        assert run(x, p / "out-source-mismatch").returncode != 0

        one_shard(x)
        import shutil
        shutil.copytree(good["folder"], x / "duplicate-layer")
        assert run(x, p / "out-duplicate").returncode != 0

    print("WP4 ASSEMBLER MUTATION CHECK: PASS (honest partial + 5 negative controls)")

if __name__ == "__main__":
    check()
