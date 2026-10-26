from copy import deepcopy
from fractions import Fraction
from pathlib import Path
import sys
import unittest

HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(HERE));sys.path.insert(0,str(Path(__file__).resolve().parent))
import primal_certifier as primal
from certificate_io import InvalidCertificate,UnsupportedCertification,validate_certificate
from test_native_evaluation import request_fixture

REGION={"delta_lower":"1/4","delta_upper":"3/8","abs_tau_lower":"1","abs_tau_upper":"2"}
NONAUTHORITY_DEPENDENCY=[{"declaration":"Zeta23.OPICARound2.native_source_prefix_error",
                         "type_sha256":"a"*64,"compiler_receipt_sha256":"b"*64}]


class PrimalTests(unittest.TestCase):
    def test_actual_regional_formula_both_guards(self):
        small=primal.regional_margin(REGION,cut_M=0)
        split=primal.regional_margin(REGION,cut_M=1)
        self.assertGreater(Fraction(small["lower_square"]),0)
        self.assertGreater(Fraction(split["lower_square"]),0)
        self.assertEqual(small["source_product_copies"],1)
        self.assertEqual(small["scope"],"bounded right-hand parameter rectangle; no global approximation claim")

    def test_unguarded_cut_and_critical_boundary_rejected(self):
        far={**REGION,"abs_tau_upper":"100000"}
        with self.assertRaises(InvalidCertificate): primal.regional_margin(far,cut_M=0)
        with self.assertRaises(InvalidCertificate): primal.regional_margin(far,cut_M=1)
        with self.assertRaises(InvalidCertificate): primal.regional_margin({**REGION,"delta_lower":"0"})
        with self.assertRaises(InvalidCertificate): primal.regional_margin({**REGION,"delta_upper":"1/2"})

    def test_missing_analytic_metadata_remains_unresolved(self):
        req=request_fixture()
        with self.assertRaises(UnsupportedCertification): primal.produce_primal(req,REGION,expected_source=req["source"])

    def test_literal_small_trial_gets_no_certificate_with_all_error_terms(self):
        req=request_fixture()
        out=primal.produce_primal(req,REGION,expected_source=req["source"],analytic_dependencies=NONAUTHORITY_DEPENDENCY)
        c=out["certificate"]
        self.assertEqual(c["outcome"],"NO_CERTIFICATE")
        self.assertEqual(out["validation"]["authority"],"VALIDATED_INPUT_ONLY_NO_ANALYTIC_AUTHORITY")
        self.assertFalse(out["independent_recomputation"])
        self.assertEqual(c["RH"],"OPEN")
        self.assertGreater(Fraction(c["error_budget"]["source_norm_error"]),0)
        self.assertGreater(Fraction(c["error_budget"]["kernel_lag_norm_error"]),0)
        self.assertGreater(Fraction(c["error_budget"]["output_target_tail_norm_error"]),0)

    def test_independent_recompute_binds_coefficients_and_every_error(self):
        req=request_fixture()
        out=primal.produce_primal(req,REGION,expected_source=req["source"],analytic_dependencies=NONAUTHORITY_DEPENDENCY)
        c=out["certificate"]
        checker=primal.independent_primal_checker(req,expected_source=req["source"],expected_region=REGION)
        self.assertEqual(checker(c)["upper_square"],c["upper_square"])
        for field in ("source_norm_error","kernel_lag_norm_error","output_target_tail_norm_error"):
            bad=deepcopy(c);bad["error_budget"][field]="0"
            with self.assertRaises(InvalidCertificate): checker(bad)
        bad=deepcopy(c);bad["coefficients"][0]["re"]="1"
        with self.assertRaises(InvalidCertificate): checker(bad)
        bad=deepcopy(c);bad["region"]["abs_tau_upper"]="3"
        with self.assertRaises(InvalidCertificate): checker(bad)

    def test_runtime_cannot_supply_its_own_analytic_authority(self):
        req=request_fixture()
        out=primal.produce_primal(req,REGION,expected_source=req["source"],analytic_dependencies=NONAUTHORITY_DEPENDENCY)
        c=deepcopy(out["certificate"]);c["outcome"]="CERTIFIED_FINITE"
        with self.assertRaises(UnsupportedCertification): validate_certificate(c,req["source"])
        with self.assertRaises(InvalidCertificate): primal.accept_primal(c,req,expected_source=req["source"],
            expected_region=REGION,expected_checker_sha256="0"*64,approved_analytic_dependencies={})

    def test_scaled_target_does_not_reuse_native_margin(self):
        req=request_fixture();req["target_coefficient"]={"re":"0","im":"0"}
        with self.assertRaises(InvalidCertificate): primal.produce_primal(req,REGION,
            expected_source=req["source"],analytic_dependencies=NONAUTHORITY_DEPENDENCY)


if __name__=="__main__": unittest.main()
