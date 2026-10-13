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
from certificate_integrity import (frozen_box_keys,validate_gate,
                                   validate_second_failure,REPO_ROOT,BASE)

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
             "left":[1,512],"right":[1,2],
             "accepted": [], "unresolved": [{"reason": "SYNTHETIC_ONLY",
                 "left":[1,512],"right":[1,2]}]}
    raw = dump(folder / "k3_Q01_even.json", layer)
    spec = {"cell": 1, "parity": "even", "file": "k3_Q01_even.json",
            "sha256": hashlib.sha256(raw).hexdigest(), "status": "UNRESOLVED",
            "intervals": 0, "unresolved_count": 1}
    manifest = {"schema": "post287.wp4.k3-full-continuum.v1",
                "terminal_claim": "RH_OPEN", "source_commit": HEAD,
                "source_digests": DIGESTS, "precision_bits": 192,
                "method": "SECOND", "second_gate_sha256":"f"*64,
                "records": [spec]}
    mbytes = dump(folder / "manifest.json", manifest)
    receipt = {"schema": "post287.wp4.checker.v1", "status": "PARTIAL_ACCEPTED_ONLY",
               "claimed_scope": "PARTIAL_ONLY", "verified_tiles": 0, "layers": 1,
               "complete_layers":0,"terminal_claim":"RH_OPEN",
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

        # Even a matching forged manifest + receipt cannot hide unresolved data.
        one_shard(x)
        import shutil
        shutil.rmtree(x / "duplicate-layer")
        manifest = copy.deepcopy(good["manifest"])
        manifest["records"][0]["status"] = "PASS"
        manifest["records"][0]["unresolved_count"] = 0
        mbytes = dump(good["folder"] / "manifest.json", manifest)
        receipt = copy.deepcopy(good["receipt"])
        receipt.update(status="PASS", complete_layers=1,
                       manifest_sha256=hashlib.sha256(mbytes).hexdigest())
        dump(receiptfile,receipt)
        assert run(x,p / "out-hidden-unresolved").returncode != 0

        one_shard(x)
        data=json.loads(layerfile.read_text())
        data["unresolved"][0]["left"]=[1,4]
        raw=dump(layerfile,data)
        manifest=copy.deepcopy(good["manifest"])
        manifest["records"][0]["sha256"]=hashlib.sha256(raw).hexdigest()
        mbytes=dump(good["folder"] / "manifest.json",manifest)
        receipt=copy.deepcopy(good["receipt"])
        receipt["manifest_sha256"]=hashlib.sha256(mbytes).hexdigest()
        dump(receiptfile,receipt)
        assert run(x,p / "out-hidden-partition-gap").returncode != 0

        # Missing receipt is honest unchecked evidence, never accepted positivity.
        one_shard(x)
        receiptfile.unlink()
        unchecked=run(x,p/'out-honest-unchecked')
        assert unchecked.returncode==0,unchecked.stderr
        report=json.loads((p/'out-honest-unchecked'/'manifest.json').read_text())
        assert report['status']=='UNRESOLVED' and not report['all_L_positivity_certified']
        assert report['records']==[] and len(report['missing_layers'])==30
        assert len(report['unverified_layers'])==1
        candidate=report['unverified_layers'][0]
        assert candidate['accepted_as_evidence'] is False
        assert (p/'out-honest-unchecked'/candidate['candidate_file']).read_bytes()==layerfile.read_bytes()
        one_shard(x)

        # Pure schema controls: synthetic gate rows never claim numerical evidence.
        fixture=json.loads((REPO_ROOT / BASE / 'fixtures/'
                            'post175_fb05_q13_fixed_unit_enclosure_v1.json').read_text())
        rows=[{'Q':q,'t':str(t),'radius':str(r),'parity':parity,'kind':kind,
               'verdict':'PASS'} for q,t,r,parity,kind in sorted(frozen_box_keys(fixture))]
        gate={'schema':'post287.wp4.k3-frozen-gate.v1','gate':'PASS',
              'terminal_claim':'RH_OPEN','source_digests':DIGESTS,
              'precision_bits':384,'max_depth':40,'frozen_boxes':len(rows),
              'tested_boxes':len(rows),'boxes':rows,'certified_negative_stop':False}
        gatefile=p / 'synthetic-gate.json'
        dump(gatefile,gate)
        validate_gate(gatefile,'SECOND')
        def reject_gate(obj):
            dump(gatefile,obj)
            try:
                validate_gate(gatefile,'SECOND')
            except (ValueError,AssertionError):
                return
            raise AssertionError('mutated frozen gate accepted')
        duplicated=copy.deepcopy(gate)
        duplicated['boxes'][-1]=duplicated['boxes'][0]
        reject_gate(duplicated)
        reject_gate({**gate,'precision_bits':192})
        reject_gate({**gate,'certified_negative_stop':True})
        dump(gatefile,gate)
        try:
            validate_second_failure(gatefile)
        except ValueError:
            pass
        else:
            raise AssertionError('PASS misrepresented as required method failure')

    print("WP4 ASSEMBLER MUTATION CHECK: PASS (honest partial + honest unchecked + 11 negative controls)")

if __name__ == "__main__":
    check()
