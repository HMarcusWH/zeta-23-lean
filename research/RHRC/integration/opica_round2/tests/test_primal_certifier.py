from copy import deepcopy
from fractions import Fraction
from pathlib import Path
import sys
import unittest

HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(HERE));sys.path.insert(0,str(Path(__file__).resolve().parent))
import primal_certifier as primal
from certificate_io import (InvalidCertificate,UnsupportedCertification,canonical_bytes,loads_strict_json,
                            parse_endpoint_rational,validate_certificate)
from test_native_evaluation import request_fixture

REGION={"delta_lower":"1/4","delta_upper":"3/8","abs_tau_lower":"1","abs_tau_upper":"2"}
NONAUTHORITY_DEPENDENCY=[{"declaration":"Zeta23.OPICARound2.native_source_prefix_error",
                         "type_sha256":"a"*64,"compiler_receipt_sha256":"b"*64}]


class PrimalTests(unittest.TestCase):
    def test_real_high_precision_producer_checker_and_certificate_roundtrip(self):
        # Metadata selects the actual evaluator; these fixtures grant no theorem authority.
        declarations = ("native_source_prefix_error", "native_probe_adaptive_error_budgets",
                        "native_product_box_margin", "zero_region_of_finite_probe_certificate")
        dependencies = [{**NONAUTHORITY_DEPENDENCY[0], "declaration":"Zeta23.OPICARound2."+name}
                        for name in declarations]
        approved = {row["declaration"]:{key:row[key] for key in ("type_sha256","compiler_receipt_sha256")}
                    for row in dependencies}
        for bits in (256,512):
            with self.subTest(bits=bits):
                request = request_fixture()
                request["precision_bits"] = bits
                before = deepcopy(request)
                out = primal.produce_primal(request,REGION,expected_source=request["source"],
                                            analytic_dependencies=dependencies)
                certificate = loads_strict_json(canonical_bytes(out["certificate"]))
                self.assertEqual(request,before)
                self.assertEqual(certificate,out["certificate"])
                self.assertEqual(certificate["outcome"],"NO_CERTIFICATE")
                self.assertGreater(len(certificate["error_budget"]["total_norm_error"]),180)
                if bits == 512:
                    self.assertGreater(len(certificate["upper_square"]),180)
                    self.assertGreater(len(certificate["witness_lower_square"]),180)
                self.assertGreaterEqual(parse_endpoint_rational(certificate["upper_square"]),
                                        parse_endpoint_rational(certificate["witness_lower_square"]))
                checker = primal.independent_primal_checker(request,expected_source=request["source"],expected_region=REGION)
                self.assertEqual(checker(certificate)["upper_square"],certificate["upper_square"])
                accepted = primal.accept_primal(certificate,request,expected_source=request["source"],
                    expected_region=REGION,expected_checker_sha256=primal.checker_digest(),
                    approved_analytic_dependencies=approved)
                self.assertEqual(accepted["claimed_outcome"],"NO_CERTIFICATE")
                self.assertEqual(accepted["authority"],"VALIDATED_INPUT_ONLY_NO_ANALYTIC_AUTHORITY")
                self.assertEqual(accepted["RH"],"OPEN")
                forged = deepcopy(certificate)
                forged.update(upper_square="0",outcome="UNRESOLVED")
                with self.assertRaises(InvalidCertificate):
                    primal.accept_primal(forged,request,expected_source=request["source"],
                        expected_region=REGION,expected_checker_sha256=primal.checker_digest(),
                        approved_analytic_dependencies=approved)

    def test_high_precision_does_not_relax_native_input_limits(self):
        from native_evaluation import evaluate_native
        long_input = str(Fraction(1,2**700))
        request = request_fixture()
        request["precision_bits"] = 512
        for key in ("coefficient", "kernel_lag_horizon", "absolute_output_horizon"):
            bad = deepcopy(request)
            if key == "coefficient":
                bad["coefficients"][0]["re"] = long_input
            else:
                bad[key] = long_input
            with self.subTest(key=key), self.assertRaises(InvalidCertificate) as caught:
                evaluate_native(bad,expected_source=request["source"])
            self.assertEqual(caught.exception.code,"rational")
        with self.assertRaises(InvalidCertificate):
            primal.regional_margin({**REGION,"delta_lower":long_input},precision_bits=512)

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
