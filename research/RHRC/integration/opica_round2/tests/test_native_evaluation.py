from copy import deepcopy
from fractions import Fraction
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import native_evaluation as native
from certificate_io import InvalidCertificate, canonical_sha256
from flint import arb, ctx


def request_fixture():
    """Synthetic identity selects the real evaluator, without theorem authority."""
    source = {"commit":"1"*40,"tree":"2"*40,"source_definition_sha256":"3"*64,
              "kernel_definition_sha256":"4"*64,"filter_definition_sha256":native.RAW_FILTER_DEFINITION_SHA256,
              "sigma":"1/4096","delay":"1/4096","source_product_copies":1}
    request = {"schema":native.SCHEMA,"source":source,"coefficients":[{"re":"1/3","im":"-1/4"}],
               "dictionary_indices":["1"],"target_coefficient":{"re":"1","im":"0"},
               "source_prefix_M":12,"kernel_lag_horizon":"1","absolute_output_horizon":"2",
               "precision_bits":96,"quadrature":{"frequency_cutoff":"1000000","frequency_cells":4,
                 "source_cells":2,"lag_cells":2,"output_cells":2}}
    request["coefficient_sha256"] = native.coefficient_digest(request["coefficients"],
        request["dictionary_indices"],request["target_coefficient"])
    return request


class OutwardArithmeticTests(unittest.TestCase):
    def test_exact_dyadic_endpoint_and_outward_rational_ball(self):
        with ctx.workprec(128):
            ball = native.interval(Fraction(1,3),Fraction(2,3))
            lo,hi = native.bounds(ball)
            self.assertLessEqual(lo,Fraction(1,3))
            self.assertGreaterEqual(hi,Fraction(2,3))
            self.assertEqual(native._fraction_dyadic(arb((7,-12))),Fraction(7,4096))
            self.assertEqual(native._fraction_dyadic(arb((-3,9))),Fraction(-1536))

    def test_square_and_integer_power_cross_zero_without_nan(self):
        with ctx.workprec(96):
            ball = native.interval(-2,3)
            lo,hi = native.bounds(native._square(ball))
            self.assertLessEqual(lo,0)
            self.assertGreaterEqual(hi,9)
            for x in (-2,-1,0,1,3):
                self.assertTrue(native._pow(ball,4).contains(x**4))

    def test_one_copy_finite_fourier_is_literal_product(self):
        with ctx.workprec(128):
            evaluator = native.NativeEvaluator(12,Fraction(10**6),[4,2,2,2])
            self.assertTrue(evaluator.fourier(arb(0)).contains(arb("1/16")))
            tau = arb(1024)
            exact = (tau*tau+arb("1/4"))*(tau*tau+arb("1/4"))
            for n in range(12):
                u = tau*arb(str(native.SIGMA/((n+1)*(n+2))))
                exact *= u.sin()/u
            self.assertTrue(evaluator.fourier(tau).overlaps(exact))
            duplicate = (tau*tau+arb("1/4"))*(tau*tau+arb("1/4"))
            for n in range(12):
                u = tau*arb(str(native.SIGMA/((n+1)*(n+2))))
                factor = u.sin()/u
                duplicate *= factor*factor
            self.assertFalse(evaluator.fourier(tau).overlaps(duplicate))

    def test_actual_causal_kernel_sign_and_floor_seams(self):
        with ctx.workprec(128):
            evaluator = native.NativeEvaluator(12,Fraction(10**6),[4,2,2,2])
            self.assertTrue(evaluator.kernel_c(arb(-1)).is_zero())
            self.assertTrue(evaluator.kernel_c(arb(0)).contains(1))
            s = arb(1)
            actual = (-3*s/2).exp()*2*(3-s.exp())
            self.assertTrue(evaluator.kernel_a(s).overlaps(actual))
            seam = evaluator.kernel_a(native.interval(Fraction(69,100),Fraction(70,100)))
            self.assertTrue(seam.contains(0))
            self.assertTrue(seam.contains(1/arb(2).sqrt()))
            self.assertGreater(evaluator.seam_cells,0)

    def test_prefix_compact_support_and_all_derivative_bounds(self):
        with ctx.workprec(96):
            evaluator = native.NativeEvaluator(12,Fraction(10**6),[4,2,2,2])
            self.assertTrue(evaluator.source(arb(-1)).is_zero())
            self.assertTrue(evaluator.source(arb(1)).is_zero())
            for k in (0,1,2,4):
                lo,hi = native.bounds(evaluator.derivative_norm(k))
                self.assertGreater(hi,0)
                self.assertGreaterEqual(lo,0)
            self.assertGreater(native.bounds(evaluator.source_error())[1],0)
            with self.assertRaises(InvalidCertificate):
                evaluator.derivative_norm(3)


class NativeRequestTests(unittest.TestCase):
    def evaluate(self, request):
        return native.evaluate_native(request,expected_source=request_fixture()["source"])

    def test_actual_finite_output_and_authority_firewall(self):
        request = request_fixture()
        result = self.evaluate(request)
        self.assertEqual(result["request_sha256"],canonical_sha256(request))
        self.assertEqual(result["coefficient_sha256"],request["coefficient_sha256"])
        self.assertGreater(Fraction(result["upper_square"]),0)
        self.assertGreaterEqual(Fraction(result["lower_square"]),0)
        self.assertLessEqual(Fraction(result["lower_square"]),Fraction(result["upper_square"]))
        self.assertGreater(Fraction(result["error_budget"]["source_norm_error"]),0)
        self.assertGreater(Fraction(result["error_budget"]["kernel_lag_norm_error"]),0)
        self.assertGreater(Fraction(result["error_budget"]["output_target_tail_norm_error"]),0)
        self.assertEqual(Fraction(result["error_budget"]["total_norm_error"]),
            sum((Fraction(result["error_budget"][k]) for k in ("source_norm_error",
                 "kernel_lag_norm_error","output_target_tail_norm_error",
                 "quadrature_norm_error","rounding_norm_error")),Fraction()))
        self.assertEqual(result["authority"],native.AUTHORITY)
        self.assertEqual(result["RH"],"OPEN")
        self.assertEqual(result["Step4"],"OPEN")
        self.assertNotIn("CERTIFIED_FINITE",str(result))
        self.assertNotIn("theorem",result)
        self.assertEqual(result,self.evaluate(request))

    def test_zero_trial_and_target_scaling(self):
        request = request_fixture()
        request["coefficients"] = []
        request["dictionary_indices"] = []
        request["target_coefficient"] = {"re":"0","im":"0"}
        request["coefficient_sha256"] = native.coefficient_digest([],[],request["target_coefficient"])
        zero = self.evaluate(request)
        self.assertEqual(Fraction(zero["upper_square"]),0)
        self.assertEqual(Fraction(zero["lower_square"]),0)
        request["target_coefficient"] = {"re":"2","im":"-1"}
        request["coefficient_sha256"] = native.coefficient_digest([],[],request["target_coefficient"])
        result = self.evaluate(request)
        self.assertGreater(Fraction(result["upper_square"]),0)

    def test_second_order_actual_variance_remainder(self):
        request = request_fixture()
        request["source_correction"] = "SECOND_ORDER"
        request["variance_terms"] = 3
        result = self.evaluate(request)
        self.assertGreater(Fraction(result["actualobjects"]["variance_partial"]),0)
        self.assertGreater(Fraction(result["actualobjects"]["variance_remainder_upper"]),0)
        self.assertIn("4",result["derivative_norm_square_intervals"])
        self.assertGreater(Fraction(result["source_input_norm_error"]),0)

    def test_large_finite_zero_dictionaries_remain_bound_without_convolution_work(self):
        for count in (33,2047):
            with self.subTest(count=count):
                request = request_fixture()
                request["dictionary_indices"] = [str(n) for n in range(1,count+1)]
                request["coefficients"] = [{"re":"0","im":"0"} for _ in range(count)]
                request["absolute_output_horizon"] = "20"
                request["coefficient_sha256"] = native.coefficient_digest(request["coefficients"],
                    request["dictionary_indices"],request["target_coefficient"])
                result = self.evaluate(request)
                self.assertEqual(result["coefficient_sha256"],request["coefficient_sha256"])
                self.assertEqual(result["dictionary_indices"],request["dictionary_indices"])
                self.assertEqual(result["coefficients"],request["coefficients"])
                self.assertEqual(result["actualobjects"]["listed_columns"],count)
                self.assertEqual(result["actualobjects"]["nonzero_columns"],0)
                self.assertEqual(result["actualobjects"]["source_value_calls"],2)
                self.assertGreater(Fraction(result["upper_square"]),0)
                self.assertEqual(result["authority"],native.AUTHORITY)

    def test_nonzero_dictionary_work_is_still_bounded(self):
        coarse = request_fixture()
        coarse["dictionary_indices"] = [str(n) for n in range(1,34)]
        coarse["coefficients"] = [{"re":"1","im":"0"} for _ in range(33)]
        coarse["absolute_output_horizon"] = "20"
        coarse["quadrature"].update(frequency_cells=1,source_cells=1,output_cells=1,lag_cells=1)
        coarse["coefficient_sha256"] = native.coefficient_digest(coarse["coefficients"],
            coarse["dictionary_indices"],coarse["target_coefficient"])
        finite = self.evaluate(coarse)
        self.assertEqual(finite["actualobjects"]["nonzero_columns"],33)
        self.assertGreater(Fraction(finite["upper_square"]),0)
        request = request_fixture()
        request["dictionary_indices"] = [str(n) for n in range(1,2048)]
        request["coefficients"] = [{"re":"1","im":"0"} for _ in range(2047)]
        request["absolute_output_horizon"] = "20"
        request["quadrature"].update(frequency_cells=64,output_cells=8,lag_cells=8)
        request["coefficient_sha256"] = native.coefficient_digest(request["coefficients"],
            request["dictionary_indices"],request["target_coefficient"])
        with self.assertRaises(InvalidCertificate) as caught:
            self.evaluate(request)
        self.assertEqual(caught.exception.code,"resource_limit")

    def test_source_copy_delay_and_trusted_configuration(self):
        for key,value in (("source_product_copies",2),("source_product_copies",True),
                          ("delay","0"),("sigma","1/2048"),("filter_definition_sha256","5"*64)):
            request = request_fixture()
            request["source"][key] = value
            with self.subTest(key=key,value=value),self.assertRaises(InvalidCertificate):
                native.evaluate_native(request,expected_source=request["source"])
        request = request_fixture()
        source = deepcopy(request["source"])
        source["tree"] = "0"*40
        with self.assertRaises(InvalidCertificate):
            native.evaluate_native(request,expected_source=source)

    def test_stale_coefficients_wrong_horizons_missing_settings(self):
        changes = [("coefficient_sha256","0"*64),("kernel_lag_horizon","0"),
                   ("absolute_output_horizon","1"),("source_prefix_M",11),
                   ("source_prefix_M",True),("precision_bits",True),("source_correction","SYNTHETIC")]
        for key,value in changes:
            request = request_fixture()
            request[key] = value
            with self.subTest(key=key,value=value),self.assertRaises(InvalidCertificate):
                self.evaluate(request)
        request = request_fixture()
        del request["absolute_output_horizon"]
        with self.assertRaises(InvalidCertificate):
            self.evaluate(request)
        request = request_fixture()
        request["coefficients"][0]["re"] = "2/3"
        with self.assertRaises(InvalidCertificate):
            self.evaluate(request)

    def test_bounded_aggregate_work_and_strict_scalar_types(self):
        for key,value in (("frequency_cells",4096),("frequency_cells",True),("frequency_cutoff",1.0)):
            request = request_fixture()
            request["quadrature"][key] = value
            if value == 4096:
                request["quadrature"]["output_cells"] = 4096
            with self.subTest(key=key),self.assertRaises(InvalidCertificate):
                self.evaluate(request)
        request = request_fixture()
        request["forged_tail_zero"] = True
        with self.assertRaises(InvalidCertificate):
            self.evaluate(request)


if __name__ == "__main__":
    unittest.main()
