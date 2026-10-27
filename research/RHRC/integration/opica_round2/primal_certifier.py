"""Source-bound finite primal witnesses; no matrix inverse is used.

The producer, independent recomputation and accepted analytic dependencies are
separate inputs. A finite exclusion never establishes a terminal restriction.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from typing import Any, Callable, Mapping

try:
    from .certificate_io import (InvalidCertificate, UnsupportedCertification, canonical_sha256,
        failure_envelope, load_strict_json, parse_endpoint_rational, parse_rational, require, validate_certificate)
except ImportError:
    from certificate_io import (InvalidCertificate, UnsupportedCertification, canonical_sha256,
        failure_envelope, load_strict_json, parse_endpoint_rational, parse_rational, require, validate_certificate)

HERE = Path(__file__).resolve().parent
SIGMA = Fraction(1,4096)


def checker_digest() -> str:
    """All executable numeric/parser inputs, not a digest selected by a certificate."""
    paths = [HERE/name for name in ("certificate_io.py","native_evaluation.py",
             "primal_certifier.py","gram_diagnostics.py","python-checks.lock")]
    require(all(p.is_file() and not p.is_symlink() for p in paths), "checker_source", "Complete numeric checker source required")
    return canonical_sha256([{ "path":p.name,"sha256":hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths])


def _fraction_exact(ball) -> Fraction:
    require(ball.is_finite() and ball.is_exact(), "interval_endpoint", "Finite exact binary endpoint required")
    mantissa, exponent = ball.man_exp()
    exponent = int(exponent)
    require(abs(exponent) <= 100_000, "endpoint_limit", "Interval exponent exceeds resource limit")
    return Fraction(int(mantissa))*Fraction(2)**exponent


def regional_margin(region: Mapping[str, Any], *, cut_M: int | None = None,
                    precision_bits: int = 128) -> dict[str, Any]:
    """Outward lower for the literal P21 probeBoxMargin, using its guarded cut."""
    fields = {"delta_lower","delta_upper","abs_tau_lower","abs_tau_upper"}
    require(type(region) is dict and set(region) == fields, "region", "Complete bounded region required")
    delta0,delta1,tau0,tau1 = [parse_rational(region[k]) for k in
                              ("delta_lower","delta_upper","abs_tau_lower","abs_tau_upper")]
    require(0 < delta0 <= delta1 < Fraction(1,2) and 0 <= tau0 <= tau1,
            "region", "Strict off-line bounded region required")
    require(type(precision_bits) is int and 64 <= precision_bits <= 512,
            "precision", "Precision must be 64..512 bits")
    L = delta1+tau1  # |delta+i tau| <= delta+|tau|, so this covers the requested rectangle.
    require(L <= 10**8,"region_limit","Bounded margin resource limit exceeded")
    if cut_M is None:
        cut_M = 0
        while (SIGMA*L>1 if cut_M == 0 else SIGMA*L>Fraction((cut_M+1)*(cut_M+2),2)):
            cut_M += 1
            require(cut_M <= 10_000, "cut_limit", "Product split resource limit exceeded")
    require(type(cut_M) is int and 0 <= cut_M <= 10_000, "cut", "Bounded integer product cut required")
    require((cut_M == 0 and SIGMA*L <= 1) or
            (cut_M >= 1 and SIGMA*L/Fraction((cut_M+1)*(cut_M+2)) <= Fraction(1,2)),
            "cut_guard", "P21 cut hypothesis failed")
    try:
        import flint
        from flint import arb,ctx
    except ImportError as exc:
        raise UnsupportedCertification("backend_unavailable","Locked rigorous interval backend is unavailable") from exc
    require(flint.__version__ == "0.9.0","backend_version","Pinned python-flint 0.9.0 required")
    def A(q): return arb(str(q.numerator))/arb(str(q.denominator))
    with ctx.workprec(precision_bits):
        if cut_M == 0:
            product = (-A(SIGMA**2*L**2/Fraction(3))).exp()
        else:
            product = A(delta0/L)**cut_M * (-A(Fraction(2)*SIGMA**2*L**2/Fraction(9*cut_M**3))).exp()
        rational = (Fraction(1,2)-delta1)**3*(Fraction(1,2)+delta0)/(L+Fraction(3,2))
        square = A(2*delta0)*(-A(2*SIGMA*delta1)).exp()*A(rational**2)*product**2
        lower = _fraction_exact(square.lower())
    require(lower > 0,"positive_margin","No strictly positive outward lower was resolved")
    return {"schema":"OPICA2_REGIONAL_MARGIN_V1","region":dict(region),"delta0":str(delta0),
            "delta1":str(delta1),"L":str(L),"cut_M":cut_M,"lower_square":str(lower),
            "source_product_copies":1,"sigma":"1/4096","delay":"1/4096",
            "formula":"2*delta0*exp(-2*sigma*delta1)*((1/2-delta1)^3*(1/2+delta0)/(L+3/2))^2*BQ^2",
            "analytic_declaration":"Zeta23.OPICARound2.native_product_box_margin",
            "scope":"bounded right-hand parameter rectangle; no global approximation claim",
            "authority":"RIGOROUS_NUMERICAL_ENCLOSURE_NOT_LEAN","RH":"OPEN","Step4":"OPEN"}


def produce_primal(request: dict, region: dict, *, expected_source: Mapping[str, Any],
                   analytic_dependencies: list[dict] | None = None,
                   cut_M: int | None = None, evaluator: Callable | None = None) -> dict:
    try:
        from .native_evaluation import evaluate_native
    except ImportError:
        from native_evaluation import evaluate_native
    if not analytic_dependencies:
        raise UnsupportedCertification("analytic_dependencies_required",
            "Supply explicit source-bound analytic declaration references; the standalone evaluator needs no theorem-authority metadata")
    require(request.get("target_coefficient",{"re":"1","im":"0"}) == {"re":"1","im":"0"},
            "target_scale","Regional exclusion uses the literal unscaled target")
    before = canonical_sha256(request)
    evaluation = (evaluator or evaluate_native)(deepcopy(request),expected_source=expected_source)
    require(evaluation.get("request_sha256") == before and evaluation.get("source_identity") == dict(expected_source),
            "native_binding","Native enclosure differs from the requested original source")
    margin = regional_margin(region,cut_M=cut_M,precision_bits=request["precision_bits"])
    upper = parse_endpoint_rational(evaluation["upper_square"],nonnegative=True)
    lower = parse_endpoint_rational(margin["lower_square"],nonnegative=True)
    implementation = checker_digest()
    require(type(evaluation.get("backend")) is dict,"backend_identity","Native backend identity is required")
    certificate = {"schema":"OPICA2_PRIMAL_CERTIFICATE_V1","source":dict(expected_source),
        "coefficients":deepcopy(request["coefficients"]),"dictionary_indices":list(request["dictionary_indices"]),
        "region":dict(region),"source_prefix_M":request["source_prefix_M"],
        "kernel_lag_horizon":request["kernel_lag_horizon"],
        "absolute_output_horizon":request["absolute_output_horizon"],"precision_bits":request["precision_bits"],
        "backend":deepcopy(evaluation["backend"]),"error_budget":deepcopy(evaluation["error_budget"]),
        "upper_square":str(upper),"witness_lower_square":str(lower),
        "analytic_dependencies":deepcopy(analytic_dependencies or []),
        "producer_sha256":implementation,"checker_sha256":implementation,
        "outcome":"NO_CERTIFICATE" if upper >= lower else "UNRESOLVED","RH":"OPEN"}
    shape = validate_certificate(certificate,expected_source)
    require(canonical_sha256(request) == before,"request_mutation","Producer changed its trial")
    return {"certificate":certificate,"evaluation_request":deepcopy(request),"evaluation":evaluation,
            "margin":margin,"validation":shape,"independent_recomputation":False,
            "full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}


def independent_primal_checker(request: dict, *, expected_source: Mapping[str, Any],
                               expected_region: Mapping[str, Any],cut_M: int | None = None,
                               evaluator: Callable | None = None) -> Callable[[dict],dict]:
    """Recompute the analytic primitive, then independently bind all finite certificate fields.

    The caller still authenticates this checker and every analytic dependency in
    certificate_io. This closure cannot confer its own approval or theorem status.
    """
    fixed_request, fixed_region = deepcopy(request),dict(expected_region)
    fixed_hash = canonical_sha256(fixed_request)
    def check(certificate):
        try:
            from .native_evaluation import evaluate_native
        except ImportError:
            from native_evaluation import evaluate_native
        require(certificate["source"] == dict(expected_source) and certificate["region"] == fixed_region,
                "checker_scope","Wrong native source or bounded region")
        keys = ("coefficients","dictionary_indices","source_prefix_M","kernel_lag_horizon",
                "absolute_output_horizon","precision_bits")
        require(all(certificate[k] == fixed_request[k] for k in keys),"stale_trial","Certificate changed the configured finite trial")
        require(fixed_request.get("target_coefficient",{"re":"1","im":"0"}) == {"re":"1","im":"0"},
                "target_scale","Native regional checker requires the unscaled target")
        fresh = (evaluator or evaluate_native)(deepcopy(fixed_request),expected_source=expected_source)
        require(fresh.get("request_sha256") == fixed_hash and fresh.get("source_identity") == dict(expected_source),
                "recompute_binding","Independent enclosure is not for the exact configured request")
        margin = regional_margin(fixed_region,cut_M=cut_M,precision_bits=fixed_request["precision_bits"])
        require(certificate["backend"] == fresh["backend"] and certificate["error_budget"] == fresh["error_budget"],
                "recompute_budget","Missing, stale or forged absolute error component")
        total = parse_endpoint_rational(fresh["error_budget"]["total_norm_error"],nonnegative=True)
        components = ("source_norm_error","kernel_lag_norm_error","output_target_tail_norm_error",
                      "quadrature_norm_error","rounding_norm_error")
        require(total >= sum((parse_endpoint_rational(fresh["error_budget"][k],nonnegative=True) for k in components),Fraction()),
                "incomplete_budget","Recomputed total omits an absolute norm error")
        require(certificate["upper_square"] == fresh["upper_square"] and
                certificate["witness_lower_square"] == margin["lower_square"],
                "forged_bounds","Certificate bounds differ from the independent native computation")
        return {"certificate_sha256":canonical_sha256(certificate),"upper_square":fresh["upper_square"],
                "witness_lower_square":margin["lower_square"],"total_norm_error":str(total)}
    return check


def accept_primal(certificate: dict, request: dict, *, expected_source: Mapping[str, Any],
                  expected_region: Mapping[str, Any],expected_checker_sha256: str,
                  approved_analytic_dependencies: Mapping[str, Mapping[str,str]],
                  cut_M: int | None = None) -> dict:
    require(expected_checker_sha256 == checker_digest(),"checker_source","Configured checker digest differs from installed exact source")
    required = {"Zeta23.OPICARound2.native_source_prefix_error",
                "Zeta23.OPICARound2.native_probe_adaptive_error_budgets",
                "Zeta23.OPICARound2.native_product_box_margin",
                "Zeta23.OPICARound2.zero_region_of_finite_probe_certificate"}
    require(required <= {row["declaration"] for row in certificate["analytic_dependencies"]},
            "missing_analytic_dependency","Native certificate omits an actual source, budget or regional theorem")
    proposed = deepcopy(certificate)
    if parse_endpoint_rational(proposed["upper_square"],nonnegative=True) < parse_endpoint_rational(proposed["witness_lower_square"],nonnegative=True):
        require(proposed["outcome"] in {"UNRESOLVED","CERTIFIED_FINITE"},"promotion_scope","Unexpected finite candidate outcome")
        proposed["outcome"] = "CERTIFIED_FINITE"
    return validate_certificate(proposed,expected_source,
        independent_checker=independent_primal_checker(request,expected_source=expected_source,
            expected_region=expected_region,cut_M=cut_M),expected_checker_sha256=expected_checker_sha256,
        approved_analytic_dependencies=approved_analytic_dependencies)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request",required=True,type=Path)
    parser.add_argument("--source-config",required=True,type=Path)
    parser.add_argument("--region",required=True,type=Path)
    parser.add_argument("--analytic-dependencies",required=True,type=Path)
    parser.add_argument("--product-cut",type=int)
    args = parser.parse_args()
    try:
        result=produce_primal(load_strict_json(args.request),load_strict_json(args.region),
            expected_source=load_strict_json(args.source_config),cut_M=args.product_cut,
            analytic_dependencies=load_strict_json(args.analytic_dependencies))
    except (InvalidCertificate,ValueError,TypeError,KeyError) as exc:
        print(json.dumps(failure_envelope("native-primal",exc),sort_keys=True))
        return 1
    print(json.dumps(result,sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
