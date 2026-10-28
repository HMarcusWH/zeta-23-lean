from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import certificate_io as io


def example_certificate():
    """Synthetic parser fixture; it is not an actual native analytic certificate."""
    return {
        "schema": "OPICA2_PRIMAL_CERTIFICATE_V1",
        "source": {"commit": "1"*40, "tree": "2"*40,
                   "source_definition_sha256": "3"*64, "kernel_definition_sha256": "4"*64,
                   "filter_definition_sha256": "5"*64, "sigma": "1/4096", "delay": "1/4096",
                   "source_product_copies": 1},
        "coefficients": [{"re": "1", "im": "0"}], "dictionary_indices": ["1"],
        "region": {"delta_lower": "1/4", "delta_upper": "3/8",
                   "abs_tau_lower": "1", "abs_tau_upper": "2"},
        "source_prefix_M": 12, "kernel_lag_horizon": "8", "absolute_output_horizon": "12",
        "precision_bits": 128, "backend": {"name": "SYNTHETIC_PARSER_CONTROL",
                                           "version": "1", "lock_sha256": "6"*64},
        "error_budget": {"source_norm_error": "1/1000", "kernel_lag_norm_error": "1/1000",
                         "output_target_tail_norm_error": "1/1000", "quadrature_norm_error": "1/1000",
                         "rounding_norm_error": "1/1000", "filter_operator_norm_upper": "1",
                         "total_norm_error": "1/100"},
        "upper_square": "1/4", "witness_lower_square": "1",
        "analytic_dependencies": [{"declaration": "SyntheticControl.only",
                                   "type_sha256": "7"*64, "compiler_receipt_sha256": "8"*64}],
        "producer_sha256": "9"*64, "checker_sha256": "a"*64,
        "outcome": "EXPERIMENTAL_SIGNAL", "RH": "OPEN",
    }


class StrictInputTests(unittest.TestCase):
    def test_json_refusals(self):
        for text in ('{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}',
                     '{"x":1.5}', '{"x":1e5}', '{"x":-Infinity}', '{"x":-0}'):
            with self.subTest(text=text), self.assertRaises(io.InvalidCertificate):
                io.loads_strict_json(text)

    def test_bounded_input_and_utf8(self):
        with self.assertRaises(io.InvalidCertificate):
            io.loads_strict_json(b"\xff")
        with self.assertRaises(io.InvalidCertificate):
            io.loads_strict_json("[]", 1)
        with self.assertRaises(io.InvalidCertificate):
            io.loads_strict_json("["*70 + "]"*70)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/"file.json"
            path.write_text('{"x":1}', encoding="utf-8")
            self.assertEqual(io.load_strict_json(path), {"x": 1})
            with self.assertRaises(io.InvalidCertificate):
                io.load_strict_json(path, 3)

    def test_integer_canonical_and_bool(self):
        self.assertEqual(io.parse_integer("-12"), -12)
        for x in (True, 1, 1.0, "01", "-0", "+1", "1/1", " 1"):
            with self.subTest(value=x), self.assertRaises(io.InvalidCertificate):
                io.parse_integer(x)
        with self.assertRaises(io.InvalidCertificate):
            io.parse_integer("0", minimum=1)

    def test_rational_canonical(self):
        self.assertEqual(io.parse_rational("-2/3"), Fraction(-2, 3))
        for x in (False, 2, "1/0", "2/2", "0/2", "-0", "1/1", "1.0", "1/-2", "1\n"):
            with self.subTest(value=x), self.assertRaises(io.InvalidCertificate):
                io.parse_rational(x)
        with self.assertRaises(io.InvalidCertificate):
            io.parse_rational("-1/2", nonnegative=True)
        self.assertEqual(io.parse_complex({"re": "1/2", "im": "-1"}).re, Fraction(1, 2))
        with self.assertRaises(io.InvalidCertificate):
            io.parse_complex({"re": "1/2", "im": "0", "ignored": 1})

    def test_generated_endpoint_budget_is_separate_from_user_input(self):
        endpoint = str(Fraction(1, 2**700))
        self.assertGreater(len(endpoint), io.MAX_INPUT_RATIONAL_CHARS)
        self.assertEqual(io.parse_endpoint_rational(endpoint), Fraction(1, 2**700))
        for call in (lambda: io.parse_rational(endpoint),
                     lambda: io.parse_complex({"re": endpoint, "im": "0"})):
            with self.assertRaises(io.InvalidCertificate):
                call()
        boundary = "1/" + "9" * (io.MAX_ENDPOINT_RATIONAL_CHARS-2)
        self.assertEqual(str(io.parse_endpoint_rational(boundary)), boundary)
        with patch.object(io, "Fraction") as constructor:
            with self.assertRaises(io.InvalidCertificate):
                io.parse_endpoint_rational(boundary + "9")
            constructor.assert_not_called()

    def test_generated_endpoints_keep_canonical_and_nonnegative_guards(self):
        for value in (False, True, 1, Fraction(1), "01", "-0", "2/2", "0/2", "1/0",
                      "1/-2", "1.0", "NaN", "Infinity", "+1", "1\n"):
            with self.subTest(value=value), self.assertRaises(io.InvalidCertificate):
                io.parse_endpoint_rational(value)
        self.assertEqual(io.parse_endpoint_rational("-1/2"), Fraction(-1, 2))
        with self.assertRaises(io.InvalidCertificate):
            io.parse_endpoint_rational("-1/2", nonnegative=True)

    def test_schema_endpoint_and_input_budgets_match_their_runtime_parsers(self):
        properties = io.load_strict_json(HERE/"schemas/certificate.schema.json")["properties"]
        endpoints = [properties["upper_square"], properties["witness_lower_square"],
                     *properties["error_budget"]["properties"].values()]
        self.assertEqual(len(endpoints), 9)
        boundary = "1/" + "9" * (io.MAX_ENDPOINT_RATIONAL_CHARS-2)
        for rule in endpoints:
            self.assertEqual(rule["maxLength"], io.MAX_ENDPOINT_RATIONAL_CHARS)
            io.validate_schema(boundary, rule)
            with self.assertRaises(io.InvalidCertificate):
                io.validate_schema(boundary + "9", rule)
        inputs = [*properties["coefficients"]["items"]["properties"].values(),
                  *properties["region"]["properties"].values(),
                  properties["kernel_lag_horizon"], properties["absolute_output_horizon"]]
        for rule in inputs:
            self.assertEqual(rule["maxLength"], 180)
            with self.assertRaises(io.InvalidCertificate):
                io.validate_schema("1/" + "9"*179, rule)

    def test_closed_schema_definition(self):
        for schema in ({"type": "object", "required": ["missing"]},
                       {"type": "object", "evilKeyword": True},
                       {"type": "string", "pattern": "["},
                       {"type": "array", "uniqueItems": 1},
                       {"type": "array", "minItems": 2, "maxItems": 1}):
            with self.subTest(schema=schema), self.assertRaises(io.SchemaDefinitionError):
                io.validate_schema_definition(schema)
        for path in (HERE/"schemas").glob("*.json"):
            io.validate_schema_definition(io.load_strict_json(path))

    def test_schema_boolean_is_not_integer_or_numeric_const(self):
        with self.assertRaises(io.InvalidCertificate):
            io.validate_schema(True, {"type": "integer"})
        with self.assertRaises(io.InvalidCertificate):
            io.validate_schema(True, {"const": 1})
        with self.assertRaises(io.InvalidCertificate):
            io.validate_schema({"nested": [True]}, {"const": {"nested": [1]}})
        with self.assertRaises(io.InvalidCertificate):
            io.validate_schema("a"*64 + "\n", {"type": "string", "pattern": "^[0-9a-f]{64}$"})


class CertificateBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.obj = example_certificate()
        self.source = deepcopy(self.obj["source"])

    def check(self, obj=None, **kwargs):
        return io.validate_certificate(self.obj if obj is None else obj, self.source, **kwargs)

    def test_valid_input_retains_nonproof_authority(self):
        result = self.check()
        self.assertEqual(result["authority"], "VALIDATED_INPUT_ONLY_NO_ANALYTIC_AUTHORITY")
        self.assertEqual(result["RH"], "OPEN")

    def test_configured_source_is_required(self):
        with self.assertRaises(io.InvalidCertificate):
            io.validate_certificate(self.obj)
        wrong = deepcopy(self.obj)
        wrong["source"]["source_product_copies"] = 2
        with self.assertRaises(io.InvalidCertificate):
            self.check(wrong)
        wrong = deepcopy(self.obj)
        wrong["source"]["source_product_copies"] = True
        with self.assertRaises(io.InvalidCertificate):
            self.check(wrong)

    def test_source_delay_filter_and_hash_identity(self):
        for key, value in [("delay", "0"), ("sigma", "1/2048"),
                           ("tree", "0"*40), ("filter_definition_sha256", "0"*64)]:
            wrong = deepcopy(self.obj)
            wrong["source"][key] = value
            with self.subTest(key=key), self.assertRaises(io.InvalidCertificate):
                self.check(wrong)

    def test_unknown_fields_and_outcomes(self):
        for key, value in [("outcome", "RH_PROVED"), ("RH", "PROVED"), ("ignored", 1)]:
            wrong = deepcopy(self.obj)
            wrong[key] = value
            with self.subTest(key=key), self.assertRaises(io.InvalidCertificate):
                self.check(wrong)

    def test_dictionary_count_zero_and_duplicates(self):
        for indices in (["0"], ["1", "1"], ["2", "1"], ["1", "2"]):
            wrong = deepcopy(self.obj)
            wrong["dictionary_indices"] = indices
            with self.subTest(indices=indices), self.assertRaises(io.InvalidCertificate):
                self.check(wrong)

    def test_regions_and_distinct_cutoffs(self):
        for key, value in [("delta_lower", "0"), ("delta_upper", "1/2"),
                           ("delta_lower", "2/5"), ("abs_tau_lower", "3")]:
            wrong = deepcopy(self.obj)
            wrong["region"][key] = value
            with self.subTest(key=key), self.assertRaises(io.InvalidCertificate):
                self.check(wrong)
        for key, value in [("source_prefix_M", True), ("source_prefix_M", 11),
                           ("source_prefix_M", 1_000_001), ("absolute_output_horizon", "8")]:
            wrong = deepcopy(self.obj)
            wrong[key] = value
            with self.subTest(key=key), self.assertRaises(io.InvalidCertificate):
                self.check(wrong)

    def test_error_terms_are_complete_nonnegative_and_normed(self):
        for key in ("source_norm_error", "kernel_lag_norm_error", "output_target_tail_norm_error"):
            wrong = deepcopy(self.obj)
            del wrong["error_budget"][key]
            with self.subTest(key=key), self.assertRaises(io.InvalidCertificate):
                self.check(wrong)
        for key, value in [("quadrature_norm_error", "-1/100"),
                           ("total_norm_error", "1/10000"), ("filter_operator_norm_upper", "0")]:
            wrong = deepcopy(self.obj)
            wrong["error_budget"][key] = value
            with self.subTest(key=key), self.assertRaises(io.InvalidCertificate):
                self.check(wrong)

    def test_no_python_theorem_or_unchecked_finite_promotion(self):
        for outcome in ("KERNEL_CHECKED_THEOREM", "EXACT_FINITE_ARITHMETIC", "CERTIFIED_FINITE"):
            wrong = deepcopy(self.obj)
            wrong["outcome"] = outcome
            with self.subTest(outcome=outcome), self.assertRaises(io.UnsupportedCertification):
                self.check(wrong)

    def synthetic_checker(self, obj):
        return {"certificate_sha256": io.canonical_sha256(obj), "upper_square": "1/4",
                "witness_lower_square": "1", "total_norm_error": "1/100"}

    def checker_config(self):
        return {"independent_checker": self.synthetic_checker, "expected_checker_sha256": "a"*64,
                "approved_analytic_dependencies": {"SyntheticControl.only":
                    {"type_sha256": "7"*64, "compiler_receipt_sha256": "8"*64}}}

    def test_synthetic_recomputation_protocol_is_finite_only(self):
        self.obj["outcome"] = "CERTIFIED_FINITE"
        result = self.check(**self.checker_config())
        self.assertEqual(result["authority"], "CERTIFIED_FINITE_NOT_LEAN")

    def test_synthetic_recomputation_protocol_roundtrips_large_endpoints(self):
        # A parser/checker protocol fixture, not an actual analytic certificate.
        upper, lower, total = (str(Fraction(1, 2**k)) for k in (700, 699, 701))
        self.obj.update(outcome="CERTIFIED_FINITE", upper_square=upper, witness_lower_square=lower)
        self.obj["error_budget"] = {key: "0" for key in self.obj["error_budget"]}
        self.obj["error_budget"].update(filter_operator_norm_upper="1", total_norm_error=total)
        config = self.checker_config()
        config["independent_checker"] = lambda obj: {"certificate_sha256": io.canonical_sha256(obj),
            "upper_square": upper, "witness_lower_square": lower, "total_norm_error": total}
        encoded = io.canonical_bytes(self.obj)
        result = self.check(io.loads_strict_json(encoded), **config)
        self.assertEqual(result["authority"], "CERTIFIED_FINITE_NOT_LEAN")
        self.assertEqual(result["upper_square"], upper)
        for field in ("upper_square", "witness_lower_square", "total_norm_error"):
            def oversized(obj, field=field):
                record = {"certificate_sha256": io.canonical_sha256(obj),
                          "upper_square": upper, "witness_lower_square": lower, "total_norm_error": total}
                record[field] = "9" * (io.MAX_ENDPOINT_RATIONAL_CHARS+1)
                return record
            config["independent_checker"] = oversized
            with self.subTest(field=field), self.assertRaises(io.InvalidCertificate):
                self.check(**config)

    def test_stale_or_forged_checker_and_analytic_identity_rejected(self):
        self.obj["outcome"] = "CERTIFIED_FINITE"
        for change in ("digest", "upper", "analytic", "checker"):
            obj = deepcopy(self.obj)
            config = self.checker_config()
            if change == "digest":
                config["independent_checker"] = lambda _: {
                    "certificate_sha256": "0"*64, "upper_square": "1/4",
                    "witness_lower_square": "1", "total_norm_error": "1/100"}
            elif change == "upper":
                obj["upper_square"] = "0"
            elif change == "analytic":
                obj["analytic_dependencies"][0]["type_sha256"] = "0"*64
            else:
                obj["checker_sha256"] = "0"*64
            with self.subTest(change=change), self.assertRaises(io.InvalidCertificate):
                self.check(obj, **config)

    def test_no_certificate_outcome_is_distinct(self):
        self.obj["outcome"] = "NO_CERTIFICATE"
        with self.assertRaises(io.InvalidCertificate):
            self.check()
        self.obj["upper_square"] = "1"
        self.assertEqual(self.check()["claimed_outcome"], "NO_CERTIFICATE")

    def test_independent_checker_cannot_mutate_coefficients(self):
        self.obj["outcome"] = "CERTIFIED_FINITE"
        config = self.checker_config()
        def mutating_checker(obj):
            obj["coefficients"][0]["re"] = "2"
            return self.synthetic_checker(obj)
        config["independent_checker"] = mutating_checker
        with self.assertRaises(io.InvalidCertificate):
            self.check(**config)
        self.assertEqual(self.obj["coefficients"][0]["re"], "1")

    def test_failure_envelope_needs_no_fake_compiler_objects(self):
        result = io.failure_envelope("analytic", io.UnsupportedCertification("not_available", "No verified enclosure"))
        self.assertEqual(result["outcome"], "UNRESOLVED")
        self.assertIsNone(result["source_identity"])
        self.assertEqual(result["artifact_hashes"], [])
        for key, value in [("has_proof_authority", True), ("full_release_accepted", True),
                           ("RH", "PROVED"), ("exporter_sha256", "0"*64)]:
            wrong = deepcopy(result)
            wrong[key] = value
            with self.subTest(key=key), self.assertRaises(io.InvalidCertificate):
                io.validate_failure_envelope(wrong)
        wrong = deepcopy(result)
        wrong["observed_at_utc"] = "not-a-date"
        with self.assertRaises(io.InvalidCertificate):
            io.validate_failure_envelope(wrong)
        io.validate_failure_envelope(io.failure_envelope("early", Exception()))


if __name__ == "__main__":
    unittest.main()

