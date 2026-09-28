from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest

from harvest import HarvestError, harvest


def row(track: str) -> dict:
    return {
        "schema_version": "RHRC-CLOSURE-TRACK-1.0",
        "track_id": track,
        "execution_status": "SUCCESS",
        "integrity_status": "PASS",
        "research_disposition": f"{track}_OPEN",
        "rh_closure": False,
        "terminal_claim": "RH_OPEN"
    }


class HarvestTests(unittest.TestCase):
    def write_rows(self, ids):
        tmp = tempfile.TemporaryDirectory()
        root = Path(tmp.name)
        paths = []
        for n, i in enumerate(ids):
            p = root / f"r{n}.json"
            p.write_text(json.dumps(row(i)))
            paths.append(p)
        return tmp, paths

    def test_complete(self):
        tmp, paths = self.write_rows(["A", "B", "C", "D"])
        try:
            self.assertEqual(harvest(paths)["terminal_claim"], "RH_OPEN")
        finally:
            tmp.cleanup()

    def test_missing_rejected(self):
        tmp, paths = self.write_rows(["A", "B", "C"])
        try:
            with self.assertRaises(HarvestError):
                harvest(paths)
        finally:
            tmp.cleanup()

    def test_duplicate_rejected(self):
        tmp, paths = self.write_rows(["A", "B", "C", "D", "D"])
        try:
            with self.assertRaises(HarvestError):
                harvest(paths)
        finally:
            tmp.cleanup()

    def test_terminal_promotion_rejected(self):
        tmp, paths = self.write_rows(["A", "B", "C", "D"])
        try:
            data = json.loads(paths[0].read_text())
            data["terminal_claim"] = "RH_PROVED"
            paths[0].write_text(json.dumps(data))
            with self.assertRaises(HarvestError):
                harvest(paths)
        finally:
            tmp.cleanup()


if __name__ == "__main__":
    unittest.main()
