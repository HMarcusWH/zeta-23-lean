"""No-dependency, adversarial tests for the candidate V2 runtime identity boundary."""
import hashlib
from pathlib import Path
import unittest

from research.RHRC.integration.opica_composition.post299.portable_runtime import (
    RuntimeMismatch, compare_runtime, require_compatible,
)

ROOT = Path(__file__).resolve().parents[5]
V1 = ROOT / "research/RHRC/integration/opica_round4/source_checker.py"
V1_BLOB = "0dcfad9ebf16b342d6f31570ead0e8f69371974e"


def identity(platform="Linux-7.0.0-1017-azure-x86_64-with-glibc2.39", optimized=False):
    # Official source-producer runtime shape from PR300 run #43641812084.
    return {
        "python_executable": "/opt/hostedtoolcache/Python/3.13.5/x64/bin/python3.13",
        "python_executable_sha256": "9cf89c50189de85411dd34b0f0ec5daaab41bf6cd447628572defe3b3ffd0a04",
        "python_version": "3.13.5",
        "python_optimized": optimized,
        "python_flint_version": "0.9.0",
        "python_flint_module_sha256": "2e5f8f1768d14eccd7961353c635195bd557f297edff8b8de09e2d211f03ec2d",
        "flint_version": "3.6.0",
        "native_library_sha256": {
            "/opt/hostedtoolcache/Python/3.13.5/x64/lib/python3.13/site-packages/flint/pyflint.abi3.so":
                "1f7ef1f52024937f542772ff9190e2f74449228cd69a6746b6608fbbd449d138",
            "/opt/hostedtoolcache/Python/3.13.5/x64/lib/python3.13/site-packages/python_flint.libs/libflint-6839011d.so.24.0.0":
                "871a4132fd1e9f3638391b2208e07088f8e3e72a10e41d45f58b150a60c2a1a9",
            "/opt/hostedtoolcache/Python/3.13.5/x64/lib/python3.13/site-packages/python_flint.libs/libgmp-e0c82b6b.so.10.5.0":
                "33d24e675b10f8b1ab93a8ad3fa2ed5012e1b0d89dcdb97273877c6c6b9450d8",
            "/opt/hostedtoolcache/Python/3.13.5/x64/lib/python3.13/site-packages/python_flint.libs/libmpfr-be332c05.so.6.2.2":
                "c4dfcfc7c5c7ab71d427e15f2f9fae4ace88592a81d4596a918dcc02eadfc6e3",
        },
        "platform": platform,
    }


AWS = "Linux-6.14.0-1034-aws-x86_64-with-glibc2.39"


class PortableRuntimeContractTest(unittest.TestCase):
    def test_frozen_v1_source_unchanged(self):
        data = V1.read_bytes()
        sha = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\x00" + data).hexdigest()
        self.assertEqual(sha, V1_BLOB)

    def test_producer_artifact_shape(self):
        self.assertTrue(require_compatible(identity(), identity())["candidate_portable_match"])

    def test_cross_runner_platform_only(self):
        a = require_compatible(identity(), identity(AWS))
        self.assertEqual(a["different_fields"], ["platform"])
        self.assertTrue(a["allowed_platform_drift_only"])
        self.assertEqual(a["authority"], "CANDIDATE_ONLY_NOT_RELEASE_APPROVAL")

    def test_optimized_mode_accepts_only_same_mode(self):
        self.assertTrue(require_compatible(identity(optimized=True), identity(AWS, optimized=True))
                        ["candidate_portable_match"])
        with self.assertRaises(RuntimeMismatch):
            require_compatible(identity(optimized=False), identity(AWS, optimized=True))

    def test_binary_and_executable_sha_must_match(self):
        for field in ("python_executable_sha256", "python_flint_module_sha256"):
            bad = identity(AWS)
            bad[field] = "0"*64
            with self.subTest(field=field), self.assertRaises(RuntimeMismatch):
                require_compatible(identity(), bad)

    def test_any_native_library_mutation_rejected(self):
        good = identity()
        for key in good["native_library_sha256"]:
            bad = identity(AWS)
            bad["native_library_sha256"][key] = "0"*64
            with self.subTest(path=key), self.assertRaises(RuntimeMismatch):
                require_compatible(good,bad)

    def test_exact_paths_and_versions_required(self):
        for field,value in (
            ("python_executable", "/home/attacker/python"),
            ("python_version", "3.13.6"),
            ("python_flint_version", "0.9.1"),
            ("flint_version", "3.6.1"),
        ):
            bad = identity(AWS);bad[field]=value
            with self.subTest(field=field), self.assertRaises(RuntimeMismatch):
                require_compatible(identity(),bad)

    def test_architecture_abi_and_os_are_not_portable(self):
        for other in (
            "Linux-6.14.0-1034-aws-aarch64-with-glibc2.39",
            "Linux-6.14.0-1034-aws-x86_64-with-glibc2.40",
            "Darwin-26.0.0-arm64",
            "Linux-x-aws-x86_64-with-glibc2.39",
            "Linux-6.14.0-x86_64-with-musl1.2",
        ):
            with self.subTest(other=other), self.assertRaises(RuntimeMismatch):
                require_compatible(identity(),identity(other))

    def test_missing_extra_fields_and_type_mismatch_fail(self):
        for mutation in ("missing", "extra", "wrong-type"):
            bad=identity(AWS)
            if mutation=="missing":del bad["python_version"]
            elif mutation=="extra":bad["secret_override"]="PASS"
            else:bad["python_optimized"]=0
            with self.subTest(mutation=mutation), self.assertRaises(RuntimeMismatch):
                require_compatible(identity(),bad)

    def test_invalid_digest_and_paths_fail_closed(self):
        for field,value in (
            ("python_executable_sha256", "xyz"),
            ("python_executable", "../../bad"),
        ):
            bad=identity(AWS);bad[field]=value
            with self.subTest(field=field), self.assertRaises(RuntimeMismatch):
                require_compatible(identity(),bad)

    def test_report_cannot_claim_acceptance(self):
        x=compare_runtime(identity(),identity(AWS))
        self.assertNotIn("acceptance_eligible",x)
        self.assertNotIn("full_round4_accepted",x)
        self.assertNotIn("RH",x)


if __name__ == "__main__":
    unittest.main()
