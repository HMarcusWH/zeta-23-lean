"""Exercise the V2 checker worker binding itself (never invoke release acceptance)."""
from copy import deepcopy
from unittest import TestCase, mock
import uuid

from research.RHRC.integration.opica_composition.post299 import source_checker_v2 as C
from research.RHRC.integration.opica_composition.post299.test_portable_runtime import (
    identity, AWS,
)


def receipt(producer, case, source, *, kind="UNIT_PRODUCER"):
    return {
        "execution": {
            "run_id": str(uuid.uuid4()),
            "started_utc": "2026-11-15T00:00:00+00:00",
            "finished_utc": "2026-11-15T00:00:01+00:00",
            "source_identity": source,
            "runtime": deepcopy(producer),
            "argv": [
                str(C.HERE / "source_evaluator.py"),
                "--_verify-worker" if kind == "DIRECT_CHECKER" else "--_worker",
                case["id"],
                "--precision-bits",
                "256",
                "--worker-output",
                "/tmp/" + case["id"] + ".json",
            ],
            "producer_kind": kind,
        }
    }


class V2WorkerBindingTest(TestCase):
    def setUp(self):
        self.case = {"id": "K4_Q3_FIVE_FOURTHS"}
        self.source = {"head": "PR299_FROZEN", "tree": "PR299_TREE"}
        self.azure = identity()
        self.aws = identity(AWS)

    def test_live_import_uses_original_round4_evaluator(self):
        self.assertEqual(C.HERE.name, "opica_round4")
        self.assertEqual(C.PASS_STATUS, "CANDIDATE_V2_RECOMPUTED_FINITE_SOURCE_NOT_RELEASE")
        self.assertEqual(C.HERE / "source_evaluator.py", C.HERE / "source_evaluator.py")

    def test_original_producer_worker_is_exact_and_cross_host_compatible(self):
        value=receipt(self.azure,self.case,self.source)
        with mock.patch.object(C.E, "runtime_identity", return_value=deepcopy(self.aws)):
            C.execution(value,self.source,self.case,256,
                        optimized=False,producer_runtime=deepcopy(self.azure))

    def test_mutated_producer_worker_runtime_is_rejected(self):
        value=receipt(self.azure,self.case,self.source)
        value["execution"]["runtime"]["python_executable_sha256"]="0"*64
        with mock.patch.object(C.E,"runtime_identity",return_value=deepcopy(self.aws)):
            with self.assertRaises(C.B.InvalidRequest):
                C.execution(value,self.source,self.case,256,
                            optimized=False,producer_runtime=deepcopy(self.azure))

    def test_binary_mismatch_between_producer_and_verifier_is_rejected(self):
        bad_aws=deepcopy(self.aws)
        bad_aws["native_library_sha256"][next(iter(bad_aws["native_library_sha256"]))]="0"*64
        value=receipt(self.azure,self.case,self.source)
        with mock.patch.object(C.E,"runtime_identity",return_value=bad_aws):
            with self.assertRaises(ValueError):
                C.execution(value,self.source,self.case,256,
                            optimized=False,producer_runtime=deepcopy(self.azure))

    def test_producer_platform_not_accepted_for_direct_checker(self):
        value=receipt(self.azure,self.case,self.source,kind="DIRECT_CHECKER")
        with mock.patch.object(C.E,"runtime_identity",return_value=deepcopy(self.aws)):
            with self.assertRaises(C.B.InvalidRequest):
                C.execution(value,self.source,self.case,256,
                            direct=True,producer_runtime=deepcopy(self.azure))

    def test_independent_direct_checker_uses_local_exact_runtime(self):
        value=receipt(self.aws,self.case,self.source,kind="DIRECT_CHECKER")
        with mock.patch.object(C.E,"runtime_identity",return_value=deepcopy(self.aws)):
            C.execution(value,self.source,self.case,256,direct=True)

    def test_direct_checker_misrepresented_platform_rejected(self):
        value=receipt(self.azure,self.case,self.source,kind="DIRECT_CHECKER")
        with mock.patch.object(C.E,"runtime_identity",return_value=deepcopy(self.aws)):
            with self.assertRaises(C.B.InvalidRequest):
                C.execution(value,self.source,self.case,256,direct=True)
