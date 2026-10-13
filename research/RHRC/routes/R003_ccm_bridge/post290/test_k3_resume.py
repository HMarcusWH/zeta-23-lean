#!/usr/bin/env python3
"""Exact ancestry, partition and fail-closed controls for the D2 continuation."""
import copy
import json
import tempfile
import unittest
from unittest.mock import patch
from fractions import Fraction
from pathlib import Path
from k3_resume_partition import coalesce, split, pair, intake, LAYERS
from certificate_integrity import validate_layer
from k3_assemble_complete import final
from k3_resume_partition import digest, write, seam_source_bindings


class FinalCheckerMutations(unittest.TestCase):
    """Format/provenance fixtures only; these synthetic files are not native data."""
    def fixture(self,root):
        from flint import ctx
        from wp4_k3_full_continuum import interval_bounds
        ctx.prec=768
        candidate=root/"candidate"
        replay=root/"full-checker.json"
        specs=[]
        receipts=[]
        for q,parity in sorted(LAYERS):
            left,right=map(pair,interval_bounds(q))
            tile={"left":left,"right":right,"method":"SECOND","accepted":True}
            data={"Q":q,"parity":parity,"left":left,"right":right,"accepted":[tile],"unresolved":[],"status":"PASS","evidence_type":"VALIDATOR_CONTROL"}
            filename=f"k3_Q{q:02d}_{parity}.json"
            write(candidate/filename,data)
            spec={"cell":q,"parity":parity,"file":filename,"sha256":digest(candidate/filename),"status":"PASS","intervals":1,"unresolved_count":0}
            specs.append(spec)
            checkname=f"replay_Q{q:02d}_{parity}.json"
            positive={"lower":[1,10],"upper":[1,5],"finite":True}
            payload={"Q":q,"parity":parity,"candidate_sha256":spec["sha256"],"precision_bits":768,"complete":True,"seams_verified":True,
                     "seam_source_bindings":seam_source_bindings(),
                     "verified":[{"index":0,"left":left,"right":right,"accepted":True,"a_interval":positive,"delta_interval":positive}],"failed":[],"unverified":[],"unresolved":[],"evidence_type":"VALIDATOR_CONTROL"}
            path=root/"replay-layers"/checkname
            write(path,payload)
            receipts.append({"Q":q,"parity":parity,"file":checkname,"sha256":digest(path),"complete":True})
        manifest={"schema":"post290.k3-candidate.v1","status":"CANDIDATE_COMPLETE","current_source":{"test":"synthetic-integrity-fixture"},"historical_source":{"test":"synthetic-integrity-fixture"},"records":specs}
        write(candidate/"manifest.json",manifest)
        aggregate={"candidate_manifest_sha256":digest(candidate/"manifest.json"),"current_source":manifest["current_source"],"layers":30,"complete_layers":30,"verified_tiles":30,"failed_tiles":0,"unverified_tiles":0,"unresolved_tiles":0,"claimed_scope":"K3_FULL","status":"PASS","precision_bits":768,"seams_verified":True,"layer_receipts":receipts}
        write(replay,aggregate)
        return candidate,replay,aggregate

    def mutate_payload(self,root,aggregate,mutator):
        entry=aggregate["layer_receipts"][0]
        path=root/"replay-layers"/entry["file"]
        data=json.loads(path.read_text())
        mutator(data)
        write(path,data)
        entry["sha256"]=digest(path)
        write(root/"full-checker.json",aggregate)

    def run_final(self,candidate,replay,out):
        # Mock only host identity for the synthetic integrity fixture.
        # No numerical evaluator is mocked or exercised by these format controls.
        with patch("k3_assemble_complete.require_current"):
            return final(candidate,replay,out)

    def test_consistent_exact_positive_integrity_fixture(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,replay,_=self.fixture(root)
            self.assertEqual(self.run_final(candidate,replay,root/"out.json")["status"],"D2_COMPLETE")

    def test_false_layer_aggregate_complete_rejected(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,replay,aggregate=self.fixture(root)
            self.mutate_payload(root,aggregate,lambda d:d.update(complete=False))
            with self.assertRaisesRegex(ValueError,"layer summary contradicts"):
                self.run_final(candidate,replay,root/"out.json")

    def test_false_global_aggregate_complete_rejected(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,replay,aggregate=self.fixture(root)
            self.mutate_payload(root,aggregate,lambda d:d.update(complete=False))
            aggregate["layer_receipts"][0]["complete"]=False
            write(replay,aggregate)
            with self.assertRaisesRegex(ValueError,"checker summary disagrees.*complete_layers"):
                self.run_final(candidate,replay,root/"out.json")

    def test_nan_display_without_exact_bounds_rejected(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,replay,aggregate=self.fixture(root)
            def mutation(data):
                tile=data["verified"][0]
                tile.pop("a_interval")
                tile["a"]={"repr":"nan","lower":"nan","upper":"nan"}
            self.mutate_payload(root,aggregate,mutation)
            with self.assertRaisesRegex(ValueError,"missing or nonfinite exact fresh bound"):
                self.run_final(candidate,replay,root/"out.json")

    def test_nonfinite_exact_bound_rejected(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,replay,aggregate=self.fixture(root)
            self.mutate_payload(root,aggregate,lambda d:d["verified"][0]["a_interval"].update(finite=False))
            with self.assertRaisesRegex(ValueError,"missing or nonfinite exact fresh bound"):
                self.run_final(candidate,replay,root/"out.json")

    def test_nan_display_cannot_render_finite_exact_evidence(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,replay,aggregate=self.fixture(root)
            self.mutate_payload(root,aggregate,lambda d:d["verified"][0].update(a={"ball":"nan","lower":"nan","upper":"nan"}))
            with self.assertRaisesRegex(ValueError,"nonfinite fresh-bound display"):
                self.run_final(candidate,replay,root/"out.json")

    def test_unordered_or_nonpositive_exact_bound_rejected(self):
        for lower,upper in (([1,1],[1,2]),([0,1],[1,2]),([-1,1],[1,2])):
            with self.subTest(lower=lower,upper=upper),tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
                root=Path(td);candidate,replay,aggregate=self.fixture(root)
                self.mutate_payload(root,aggregate,lambda d:d["verified"][0]["delta_interval"].update(lower=lower,upper=upper))
                with self.assertRaisesRegex(ValueError,"unordered or nonpositive"):
                    self.run_final(candidate,replay,root/"out.json")

    def test_unverified_leaf_relabelled_complete_rejected(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,replay,aggregate=self.fixture(root)
            self.mutate_payload(root,aggregate,lambda d:d["unverified"].append({"index":0,"left":[0,1],"right":[1,1]}))
            with self.assertRaisesRegex(ValueError,"unchecked/unresolved leaf relabelled"):
                self.run_final(candidate,replay,root/"out.json")

    def test_wrong_checker_payload_layer_rejected(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,replay,aggregate=self.fixture(root)
            self.mutate_payload(root,aggregate,lambda d:d.update(Q=2,parity="odd"))
            with self.assertRaisesRegex(ValueError,"wrong Q/parity"):
                self.run_final(candidate,replay,root/"out.json")

    def test_wrong_endpoint_source_coordinate_rejected(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,replay,aggregate=self.fixture(root)
            self.mutate_payload(root,aggregate,lambda d:d["seam_source_bindings"].update(entering_source_coordinate="omega=1"))
            with self.assertRaisesRegex(ValueError,"stale physical-seam theorem"):
                self.run_final(candidate,replay,root/"out.json")

    def test_nonboolean_complete_rejected(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,replay,aggregate=self.fixture(root)
            self.mutate_payload(root,aggregate,lambda d:d.update(complete=1))
            aggregate["layer_receipts"][0]["complete"]=1
            write(replay,aggregate)
            with self.assertRaisesRegex(ValueError,"must be Boolean"):
                self.run_final(candidate,replay,root/"out.json")

    def test_wrong_physical_cell_target_rejected(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            root=Path(td);candidate,replay,aggregate=self.fixture(root)
            entry=aggregate["layer_receipts"][0]
            name=f"k3_Q{entry['Q']:02d}_{entry['parity']}.json"
            raw=candidate/name
            data=json.loads(raw.read_text())
            data["left"]=[0,1]
            data["accepted"][0]["left"]=[0,1]
            write(raw,data)
            manifest=json.loads((candidate/"manifest.json").read_text())
            manifest["records"][0]["sha256"]=digest(raw)
            write(candidate/"manifest.json",manifest)
            aggregate["candidate_manifest_sha256"]=digest(candidate/"manifest.json")
            self.mutate_payload(root,aggregate,lambda d:d.update(candidate_sha256=digest(raw)))
            with self.assertRaisesRegex(AssertionError,"incorrect layer target"):
                self.run_final(candidate,replay,root/"out.json")


class PartitionControls(unittest.TestCase):
    def test_coalesce_only_adjacent_preserves_original_ids(self):
        raw=[{"left":[3,4],"right":[1,1]},{"left":[0,1],"right":[1,4]},{"left":[1,4],"right":[1,2]}]
        got=coalesce(raw)
        self.assertEqual([(c["left"],c["right"],c["parents"]) for c in got],[(Fraction(0),Fraction(1,2),[1,2]),(Fraction(3,4),Fraction(1),[0])])

    def test_exact_eighths_and_fourths(self):
        lo,hi=Fraction(379,1000),Fraction(498,1000)
        pieces=split(lo,hi,8)
        self.assertEqual(pieces[0][0],lo);self.assertEqual(pieces[-1][1],hi)
        self.assertTrue(all(b==c for (_,b),(c,_) in zip(pieces,pieces[1:])))
        self.assertTrue(all(b-a==(hi-lo)/8 for a,b in pieces))
        children=split(*pieces[3],4)
        self.assertEqual(sum(b-a for a,b in children),pieces[3][1]-pieces[3][0])

    def test_overlap_and_unordered_rejected(self):
        for raw in ([{"left":[0,1],"right":[2,1]},{"left":[1,1],"right":[3,1]}],[{"left":[2,1],"right":[1,1]}]):
            with self.assertRaises(ValueError):coalesce(raw)

    def test_continuous_cover_cannot_be_point_samples(self):
        s={"cell":9,"parity":"even","file":"k3_Q09_even.json","status":"PASS","intervals":1,"unresolved_count":0}
        r={"Q":9,"parity":"even","status":"PASS","left":[0,1],"right":[1,1],"accepted":[{"left":[1,2],"right":[1,2],"accepted":True,"method":"SECOND"}],"unresolved":[]}
        with self.assertRaises(AssertionError):validate_layer(s,r,"SECOND")

    def test_missing_interval_not_accepted(self):
        s={"cell":9,"parity":"even","file":"k3_Q09_even.json","status":"PASS","intervals":1,"unresolved_count":0}
        r={"Q":9,"parity":"even","status":"PASS","left":[0,1],"right":[1,1],"accepted":[{"left":[0,1],"right":[1,2],"accepted":True,"method":"SECOND"}],"unresolved":[]}
        with self.assertRaises(AssertionError):validate_layer(s,r,"SECOND")

    def test_historical_source_and_layer_mutations(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as td:
            p=Path(td)
            base={"source_commit":"forged-current-source","method":"SECOND","terminal_claim":"RH_OPEN","records":[]}
            (p/"manifest.json").write_text(json.dumps(base))
            with self.assertRaises(ValueError):intake(p)
            base["source_commit"]="31512dbb698dd59b90cfa32549f0e9273a5163f9"
            (p/"manifest.json").write_text(json.dumps(base))
            with self.assertRaises(ValueError):intake(p)


if __name__=="__main__":
    unittest.main()
