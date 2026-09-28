from __future__ import annotations

import json
from pathlib import Path
import unittest

import canonical_characteristic_scout as cscope
import canonical_schur_arb as bscope
import r002_visibility_audit as dscope
import small_aperture_arb_audit as ascope

HERE = Path(__file__).resolve().parent


class PlanScopeTests(unittest.TestCase):
    def setUp(self):
        self.plan = json.loads((HERE / "PLAN.json").read_text(encoding="utf-8"))
        self.scope = self.plan["research_scope"]

    def test_a_scope(self):
        a = self.scope["A"]
        self.assertEqual(a["L"], f"{ascope.FROZEN_L_NUM}/{ascope.FROZEN_L_DEN}")
        self.assertEqual(a["K"], list(ascope.FROZEN_K))
        self.assertEqual(a["precision_bits"], ascope.PREC)

    def test_b_scope(self):
        b = self.scope["B"]
        self.assertEqual(b["physical_Q"], list(bscope.PHYSICAL_Q))
        self.assertEqual(b["true_von_mangoldt_thresholds"], list(bscope.TRUE_VM_THRESHOLDS))
        self.assertEqual(b["zero_weight_controls"], list(bscope.ZERO_WEIGHT_CONTROLS))
        self.assertEqual(b["successor_K"], list(bscope.SUCCESSOR_K))
        self.assertEqual(b["predecessor_N"], [k - 1 for k in bscope.SUCCESSOR_K])
        self.assertEqual(b["parities"], list(bscope.PARITIES))
        self.assertEqual(b["segments_per_cell"], bscope.DEN)
        self.assertEqual(b["precision_bits"], bscope.PREC)
        self.assertEqual(b["backend"], "FIXED_UNIT_MVT_CANONICAL_ARB")

    def test_c_scope(self):
        c = self.scope["C"]
        self.assertEqual(c["L"], list(cscope.FROZEN_L))
        self.assertEqual(c["physical_Q"], list(cscope.FROZEN_Q))
        self.assertEqual(c["K"], list(cscope.FROZEN_K))
        self.assertEqual(c["z"], cscope.z_scope_records())
        self.assertEqual(c["precision_bits"], cscope.PREC)

    def test_d_scope(self):
        d = self.scope["D"]
        self.assertEqual(d["specialization_L"], dscope.SPECIALIZATION_L)
        self.assertEqual(d["taper_width_fractions"], list(dscope.TAPER_WIDTH_FRACTIONS))
        self.assertEqual(d["masking_log_height"], dscope.MASKING_LOG_HEIGHT)
        self.assertEqual(d["masking_lambdas"], list(dscope.MASKING_LAMBDAS))
        self.assertEqual(d["masking_deltas"], list(dscope.MASKING_DELTAS))
        self.assertEqual(d["production_lambda_max"], dscope.PRODUCTION_LAMBDA_MAX)
        self.assertEqual(d["synthetic_seed"], dscope.SYNTHETIC_SEED)


if __name__ == "__main__":
    unittest.main()
