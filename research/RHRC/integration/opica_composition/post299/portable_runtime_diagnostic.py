"""Diagnostic-only comparison of a sealed historical producer and current runner.

No V1 or V2 acceptance can be granted by this script. The archive is a
fixed, single exact-run input; neither command success nor apparent
fingerprint compatibility certifies the numerical evidence or RH.
"""
from __future__ import annotations
import hashlib
import json
import sys
from io import BytesIO
from pathlib import Path
from zipfile import ZipFile
from .portable_runtime import compare_runtime, require_compatible, RuntimeMismatch
from .source_checker_v2 import E

SOURCE_HEAD = "df914f38f26bdc4109aeaa13f48b3896c3bc61b1"
SOURCE_TREE = "5fc2aa4793b658c58dd89c1d36b0ceee756d400d"
RUN_ID = "43700869719"
ATTEMPT = 1
# SHA256 of the original INNER bundle.zip, read from GitHub's transport receipt.
INNER_SHA256 = "d38c2eeeab0d14033e93ce9fcb6e370ee19456728fde695687d378af9898beb7"


def report(archive: Path) -> dict:
    with ZipFile(archive) as outer:
        if set(outer.namelist()) != {"transport.json", "bundle.zip"}:
            raise RuntimeError("Unexpected historical transport envelope files")
        envelope = json.loads(outer.read("transport.json"))
        exp = envelope["experiment"]
        if not (
            envelope["schema"] == "OPICA_EVIDENCE_TRANSPORT_V1"
            and envelope["lane_id"] == "SOURCE_NUMERICS"
            and exp["run_id"] == RUN_ID
            and type(exp["attempt"]) is int and exp["attempt"] == ATTEMPT
            and exp["requested_commit"] == SOURCE_HEAD
            and exp["requested_tree"] == SOURCE_TREE
        ):
            raise RuntimeError("Original transport provenance mismatch")
        inner = outer.read("bundle.zip")
        inner_hash = hashlib.sha256(inner).hexdigest()
        if inner_hash != INNER_SHA256 or envelope["container"] != {"bytes":len(inner),"sha256":inner_hash}:
            raise RuntimeError("Transport bundle not original SHA256-pinned artifact")
    rows = {}
    with ZipFile(BytesIO(inner)) as bundle:
        for optimized,mode in [(False,"normal"),(True,"optimized")]:
            raw = bundle.read("source-producer/"+mode+"/result.json")
            doc = json.loads(raw)
            if not (
                doc["schema"] == "OPICA4_FINITE_SOURCE_EVALUATOR_V1"
                and doc["status"] == "PASS_FINITE_SOURCE_ENCLOSURES"
                and doc["source_identity"]["head"] == SOURCE_HEAD
                and doc["source_identity"]["tree"] == SOURCE_TREE
                and doc["checked_commit"] == SOURCE_HEAD
                and doc["checked_tree"] == SOURCE_TREE
                and type(doc["precision_bits"]) is int
                and doc["precision_bits"] in (256,512)
                and doc["runtime"]["python_optimized"] is optimized
            ):
                raise RuntimeError("Original numerical source scope/precision mismatch")
            current = E.runtime_identity()
            current["python_optimized"] = optimized
            difference = compare_runtime(doc["runtime"], current)
            rows[mode] = {
                "status": "DIAGNOSTIC_COMPATIBLE" if difference["candidate_portable_match"] else "DIAGNOSTIC_DIVERGED",
                "producer_report_sha256": hashlib.sha256(raw).hexdigest(),
                "precision_bits": doc["precision_bits"],
                "diagnostic_portable_comparison": difference,
            }
    return {
        "schema": "OPICA4_V2_CROSS_RUN_DIAGNOSTICS_V1",
        "authority": "DIAGNOSTIC_ONLY_NOT_RELEASE_NOT_V1_ACCEPTANCE",
        "producer_run_id":RUN_ID,
        "attempt":ATTEMPT,
        "source_head":SOURCE_HEAD,
        "source_tree":SOURCE_TREE,
        "producer_inner_bundle_sha256":INNER_SHA256,
        "modes":rows,
        "all_candidate_portable":all(x["diagnostic_portable_comparison"]["candidate_portable_match"] for x in rows.values()),
        "RH":"OPEN",
        "Step4":"OPEN",
    }


def main() -> int:
    if len(sys.argv) != 3:
        raise SystemExit("Usage: python -m ...portable_runtime_diagnostic <archive.zip> <report.json>")
    source = Path(sys.argv[1]); out = Path(sys.argv[2])
    result = report(source)
    out.write_text(json.dumps(result, sort_keys=True, indent=2)+"\n")
    print(json.dumps(result, sort_keys=True))
    if not result["all_candidate_portable"]:
        print("DIAGNOSTIC_FINDING: non-host runtime mismatch; NOT APPROVED",file=sys.stderr)
        return 1
    print("DIAGNOSTIC_ONLY: candidate runtime-compatible; V1 and V2 release NOT APPROVED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
