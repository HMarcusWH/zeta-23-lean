#!/usr/bin/env python3
"""Synthetic RHKG receipt integrity mutations. This does not invoke Lean."""
import copy
import tempfile
import unittest
from pathlib import Path
from graph_precheck_receipt import GENERATED_ROOTS,CHECK_PROGRAMS,build_receipt,validate_receipt

H="a"*40
T="b"*40
RUN="42"

class GraphReceiptTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo=Path(self.tmp.name)
        for i,folder in enumerate(GENERATED_ROOTS):
            path=self.repo / folder / f"generated_{i}.json"
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text('{"origin":"synthetic"}\n')
        for file in CHECK_PROGRAMS:
            path=self.repo / file
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text("SYNTHETIC_SOURCE_ONLY\n")
        self.receipt=build_receipt(self.repo,H,T,RUN)

    def test_synthetic_exact_receipt(self):
        self.assertTrue(validate_receipt(self.receipt,self.repo,H,T,RUN))
    def test_stale_tree(self):
        with self.assertRaisesRegex(ValueError,"exact CI"):
            validate_receipt(self.receipt,self.repo,H,"c"*40,RUN)
    def test_other_run(self):
        with self.assertRaisesRegex(ValueError,"exact CI"):
            validate_receipt(self.receipt,self.repo,H,T,"wrong")
    def test_missing_root_product(self):
        file=self.repo / GENERATED_ROOTS[0] / "generated_0.json"
        file.unlink()
        with self.assertRaisesRegex(ValueError,"empty"):
            validate_receipt(self.receipt,self.repo,H,T,RUN)
    def test_changed_output_byte(self):
        file=self.repo / GENERATED_ROOTS[0] / "generated_0.json"
        file.write_text('{"origin":"mutated"}\n')
        with self.assertRaisesRegex(ValueError,"drift"):
            validate_receipt(self.receipt,self.repo,H,T,RUN)
    def test_changed_checker(self):
        file=self.repo / CHECK_PROGRAMS[0]
        file.write_text("UNREVIEWED_TEST_EDIT\n")
        with self.assertRaisesRegex(ValueError,"drift"):
            validate_receipt(self.receipt,self.repo,H,T,RUN)
    def test_fabricated_pass_flag(self):
        record=copy.deepcopy(self.receipt)
        record.pop("generated_files")
        with self.assertRaisesRegex(ValueError,"drift"):
            validate_receipt(record,self.repo,H,T,RUN)
    def test_unknown_schema(self):
        record=copy.deepcopy(self.receipt)
        record["schema"]="FALSE_GREEN"
        with self.assertRaisesRegex(ValueError,"exact CI"):
            validate_receipt(record,self.repo,H,T,RUN)
if __name__=="__main__":
    unittest.main()
