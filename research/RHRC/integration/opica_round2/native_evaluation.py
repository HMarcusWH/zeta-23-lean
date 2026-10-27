"""Outward Arb enclosures for the literal one-copy native finite trial.

The source is evaluated by the proved finite-prefix inverse Fourier identity,
with an explicit improper-integral tail. Interval Riemann sums enclose every
finite integral, including integer floor seams. This numerical layer creates
neither a Lean theorem nor CERTIFIED_FINITE authority; certificate_io owns that
independently configured boundary.
"""
from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
import hashlib
from importlib.metadata import version
from pathlib import Path
from typing import Any, Mapping

try:
    from .certificate_io import canonical_sha256, parse_complex, parse_integer, parse_rational, require
except ImportError:
    from certificate_io import canonical_sha256, parse_complex, parse_integer, parse_rational, require

SIGMA = Fraction(1, 4096)
SCHEMA = "OPICA2_NATIVE_EVALUATION_REQUEST_V1"
AUTHORITY = "RIGOROUS_NUMERICAL_ENCLOSURE_NOT_LEAN"
MAX_WORK = 5_000_000
MAX_COLUMNS = 100_000
RAW_FILTER_DEFINITION = "OPICA2_RAW_IDENTITY_FILTER_V1: B(f)=f"
RAW_FILTER_DEFINITION_SHA256 = hashlib.sha256(RAW_FILTER_DEFINITION.encode("utf-8")).hexdigest()


def _pow(value, n: int):
    """Integer multiplication, avoiding Arb's real-power branch at zero."""
    arb, _ = _backend()
    result = arb(1)
    while n:
        if n & 1:
            result *= value
        n //= 2
        if n:
            value *= value
    return result


def _square(value):
    lo, hi = bounds(value)
    lower = 0 if lo <= 0 <= hi else min(lo*lo, hi*hi)
    return interval(lower, max(lo*lo,hi*hi))


@lru_cache(maxsize=1)
def _backend():
    try:
        from flint import arb, ctx
    except ImportError as exc:
        raise RuntimeError("Pinned python-flint 0.9.0 is required") from exc
    require(version("python-flint") == "0.9.0", "backend_version", "Pinned python-flint 0.9.0 required")
    return arb, ctx


def _fraction_dyadic(value) -> Fraction:
    """Read an exact Arb endpoint without decimal or binary-float conversion."""
    require(value.is_finite() and value.is_exact(), "nonfinite_ball", "Finite exact Arb endpoint required")
    mantissa, exponent = value.man_exp()
    m, e = int(mantissa), int(exponent)
    return Fraction(m * 2**e) if e >= 0 else Fraction(m, 2**(-e))


def bounds(value) -> tuple[Fraction, Fraction]:
    require(value.is_finite(), "nonfinite_ball", "Numerical enclosure is not finite")
    return _fraction_dyadic(value.lower()), _fraction_dyadic(value.upper())


def interval(lower: Fraction | int, upper: Fraction | int):
    arb, _ = _backend()
    lower, upper = Fraction(lower), Fraction(upper)
    require(lower <= upper, "interval_order", "Reversed interval")
    return arb(str((lower + upper) / 2), str((upper - lower) / 2))


def coefficient_digest(coefficients, dictionary_indices, target_coefficient=None) -> str:
    target = {"re": "1", "im": "0"} if target_coefficient is None else target_coefficient
    return canonical_sha256({"coefficients": coefficients, "dictionary_indices": dictionary_indices,
                             "target_coefficient": target})


def _positive_int(value: Any, name: str, maximum: int = 4096) -> int:
    require(type(value) is int and 1 <= value <= maximum, "resource_limit", name + " out of range")
    return value


def _prepare(request: Any, expected_source: Mapping[str, Any]):
    required = {"schema", "source", "coefficients", "dictionary_indices", "coefficient_sha256",
                "source_prefix_M", "kernel_lag_horizon", "absolute_output_horizon", "precision_bits", "quadrature"}
    optional = {"target_coefficient", "source_correction", "variance_terms"}
    require(type(request) is dict and required <= set(request) <= required | optional,
            "request_fields", "Unknown or missing native evaluation fields")
    require(request["schema"] == SCHEMA, "request_schema", "Unknown native evaluation schema")
    require(isinstance(expected_source, Mapping) and type(request["source"]) is dict,
            "source_identity", "Configured source identity required")
    require(request["source"] == dict(expected_source), "source_identity", "Source identity mismatch")
    source = request["source"]
    require(type(source.get("source_product_copies")) is int and source["source_product_copies"] == 1
            and source.get("sigma") == str(SIGMA) and source.get("delay") == str(SIGMA),
            "native_source", "The literal one-copy source and delay sigma=1/4096 are required")
    require(source.get("filter_definition_sha256") == RAW_FILTER_DEFINITION_SHA256,
            "filter_identity", "Raw native evaluation requires the explicit identity filter digest")
    require(type(request["coefficients"]) is list and type(request["dictionary_indices"]) is list
            and len(request["coefficients"]) == len(request["dictionary_indices"])
            and len(request["coefficients"]) <= MAX_COLUMNS, "dictionary_count", "At most 100000 matched columns required")
    coefficients = [parse_complex(x) for x in request["coefficients"]]
    indices = [parse_integer(n, minimum=1, maximum=10**12) for n in request["dictionary_indices"]]
    require(indices == sorted(set(indices)), "dictionary_indices", "Distinct ascending positive indices required")
    target_obj = request.get("target_coefficient", {"re": "1", "im": "0"})
    target = parse_complex(target_obj)
    digest = coefficient_digest(request["coefficients"], request["dictionary_indices"], target_obj)
    require(request["coefficient_sha256"] == digest, "coefficient_hash", "Stale coefficient binding")
    M = request["source_prefix_M"]
    require(type(M) is int and 12 <= M <= 256, "source_prefix", "Finite prefix M must be in 12..256")
    T = parse_rational(request["kernel_lag_horizon"], nonnegative=True)
    S = parse_rational(request["absolute_output_horizon"], nonnegative=True)
    require(0 < T <= 64 and 0 < S <= 128, "horizon", "Positive bounded, distinct lag/output horizons required")
    bits = request["precision_bits"]
    require(type(bits) is int and 64 <= bits <= 512, "precision", "Precision must be in 64..512 bits")
    quad = request["quadrature"]
    require(type(quad) is dict and set(quad) == {"frequency_cutoff", "frequency_cells", "source_cells",
            "lag_cells", "output_cells"}, "quadrature_fields", "Complete closed quadrature settings required")
    R = parse_rational(quad["frequency_cutoff"], nonnegative=True)
    require(1 <= R <= 10**9, "frequency_cutoff", "Frequency cutoff must be in 1..10^9")
    grids = [_positive_int(quad[k], k) for k in ("frequency_cells", "source_cells", "lag_cells", "output_cells")]
    F, U, L, O = grids
    active_columns = sum(c.re != 0 or c.im != 0 for c in coefficients)
    work = (U + O * L * active_columns + 4) * F * M + O * U + len(indices)
    require(work <= MAX_WORK,
            "resource_limit", "Aggregate frequency/source/lag/output work exceeds limit")
    correction = request.get("source_correction", "RAW")
    require(correction in ("RAW", "SECOND_ORDER"), "source_correction", "Unknown source approximation")
    terms = request.get("variance_terms", 32)
    require(type(terms) is int and 0 <= terms <= 4096, "variance_terms", "Finite variance refinement required")
    canonical_sha256(request)  # Reject floats and other unsupported canonical data.
    return coefficients, indices, target, digest, M, T, S, bits, R, grids, correction, terms


class NativeEvaluator:
    """One bounded evaluation context; all inputs are exact rationals."""
    def __init__(self, M: int, R: Fraction, grids: list[int], correction="RAW", variance_terms=32):
        self.arb, _ = _backend()
        self.M, self.R = M, R
        self.F, self.U, self.L, self.O = grids
        self.widths = [SIGMA / ((n+1)*(n+2)) for n in range(M)]
        self.C = Fraction(1)
        for a in self.widths:
            self.C /= a
        self.variance_upper = SIGMA**2 / (3*(M+1)**2*(M+2))
        self.variance_hat = sum((SIGMA**2 / (3*(n+1)**2*(n+2)**2)
                                 for n in range(M, M+variance_terms)), Fraction())
        N = M + variance_terms
        self.variance_remainder = SIGMA**2 / (3*(N+1)**2*(N+2))
        self.correction = correction
        self.seam_cells = 0
        self.source_calls = 0
        self.norm_squares = {}

    def _a(self, q):
        return self.arb(str(q))

    def fourier(self, tau):
        product = self.arb(1)
        for a in self.widths:
            product *= (self._a(a) * tau).sinc()
        return _square(_pow(tau,2) + self._a(Fraction(1,4))) * product

    def integrate(self, function, end: Fraction, cells: int):
        step = end / cells
        total = self.arb(0)
        for k in range(cells):
            total += function(interval(k*step, (k+1)*step)) * self._a(step)
        require(total.is_finite(), "nonfinite_ball", "Integral enclosure is not finite")
        return total

    def source(self, t):
        """Actual j_M (or its explicit second-order correction), not a spline surrogate."""
        self.source_calls += 1
        lo, hi = bounds(t)
        if hi < 0 or lo > 2*SIGMA:
            return self.arb(0)
        def integrand(tau):
            value = ((t-self._a(SIGMA))*tau).cos() * self.fourier(tau)
            if self.correction == "SECOND_ORDER":
                value *= 1 - self._a(self.variance_hat/2)*_pow(tau,2)
            return value
        finite = self.integrate(integrand, self.R, self.F) / self.arb.pi()
        tail = self._a(Fraction(25,16)*self.C/(self.M-5) * self.R**(5-self.M)) / self.arb.pi()
        if self.correction == "SECOND_ORDER":
            tail += self._a(Fraction(25,32)*self.C*self.variance_hat/(self.M-7)
                            * self.R**(7-self.M)) / self.arb.pi()
        return finite + interval(-bounds(tail)[1], bounds(tail)[1])

    def derivative_norm(self, k: int):
        require(type(k) is int and k in (0,1,2,4), "derivative_order", "Supported source derivative orders are 0,1,2,4")
        if k not in self.norm_squares:
            finite = self.integrate(lambda tau: _pow(tau,2*k)*_square(self.fourier(tau)), self.R, self.F)/self.arb.pi()
            exponent = 2*self.M-2*k-9
            tail = self._a(Fraction(5,4)**4*self.C**2/exponent*self.R**(-exponent))/self.arb.pi()
            lower, upper = bounds(finite)
            upper += bounds(tail)[1]
            self.norm_squares[k] = interval(max(Fraction(),lower), upper)
        # Only the upper norm is used in the error transport. Taking sqrt of a
        # rounded [0,U] ball would incorrectly invoke Arb at a negative endpoint.
        return self._a(bounds(self.norm_squares[k])[1]).sqrt()

    def source_error(self):
        D2 = self.derivative_norm(2)
        if self.correction == "SECOND_ORDER":
            return (self._a(self.variance_upper**2/8)*self.derivative_norm(4)
                    + self._a(self.variance_remainder/2)*D2)
        first = self._a(SIGMA/(self.M+1))*self.derivative_norm(1)
        second = self._a(self.variance_upper/2)*D2
        return self._a(min(bounds(first)[1], bounds(second)[1]))

    def kernel_a(self, s):
        lo, hi = bounds(s)
        if hi < 0:
            return self.arb(0)
        envelope = (-s/2).exp()
        if lo < 0:
            self.seam_cells += 1
            return interval(0, max(Fraction(1), bounds(envelope)[1]))
        e = s.exp()
        elo,ehi = bounds(e)
        nlo,nhi = elo.numerator//elo.denominator, ehi.numerator//ehi.denominator
        if nlo != nhi:
            self.seam_cells += 1
            return interval(0, bounds(envelope)[1])
        return (-3*s/2).exp()*nlo*(nlo+1-e)

    def kernel_c(self, s):
        lo,hi = bounds(s)
        if hi < 0:
            return self.arb(0)
        if lo < 0:
            return interval(-1, 2)  # literal causal signed kernel envelope
        return -(-s/2).exp()+2*(-3*s/2).exp()


def evaluate_native(request: Any, *, expected_source: Mapping[str, Any]) -> dict[str, Any]:
    coefficients,indices,target,digest,M,T,S,bits,R,grids,correction,terms = _prepare(request,expected_source)
    arb,ctx = _backend()
    with ctx.workprec(bits):
        ev = NativeEvaluator(M,R,grids,correction,terms)
        largest = max(indices,default=1)
        require(S >= bounds(arb(largest).log()+arb(str(T+2*SIGMA)))[1],
                "output_horizon", "Output horizon must cover lag horizon plus log(max index) plus 2 sigma")
        def complex_abs(z):
            return arb(str(z.re*z.re+z.im*z.im)).sqrt()
        abs_target = complex_abs(target)
        active = [(n,x) for n,x in zip(indices,coefficients) if x.re != 0 or x.im != 0]
        Ax = sum((complex_abs(x)/arb(n).sqrt() for n,x in active), arb(0))
        ustep = 2*SIGMA/ev.U
        source_cells = [(interval(k*ustep,(k+1)*ustep), None) for k in range(ev.U)]
        source_cells = [(u,ev.source(u)) for u,_ in source_cells]
        active_with_logs = [(n,x,arb(n).log()) for n,x in active]
        def head_energy(t):
            V = sum((ev.kernel_c(t-u)*g*arb(str(ustep)) for u,g in source_cells),arb(0))
            re,im = arb(str(target.re))*V,arb(str(target.im))*V
            for n,x,logn in active_with_logs:
                W = ev.integrate(lambda s: ev.kernel_a(s)*ev.source(t-logn-s),T,ev.L)/arb(n).sqrt()
                re -= arb(str(x.re))*W
                im -= arb(str(x.im))*W
            return _square(re)+_square(im)
        head = ev.integrate(head_energy,S,ev.O)
        head_lo,head_hi = bounds(head)
        head_lo,head_hi = max(Fraction(),head_lo),max(Fraction(),head_hi)
        eps = ev.source_error()
        source_error = eps*(abs_target*arb("10/3")+2*Ax)
        gnorm = ev.derivative_norm(0)
        if correction == "SECOND_ORDER":
            gnorm += arb(str(ev.variance_hat/2))*ev.derivative_norm(2)
        Jnorm = gnorm+eps
        lag_error = 2*(-arb(str(T))/2).exp()*Jnorm*Ax
        # Canonical target tail, never a killed-tail assertion for g.
        target_tail = abs_target*8/arb(3).sqrt()*(arb(str(3*SIGMA-3*S/2))).exp()
        source_upper = bounds(source_error)[1]
        lag_upper = bounds(lag_error)[1]
        target_upper = bounds(target_tail)[1]
        # Sum the emitted endpoint rationals, so the serialized total also
        # covers every serialized component, independently of ball rounding.
        error_upper = source_upper+lag_upper+target_upper
        upper_norm = arb(str(head_hi)).sqrt()+arb(str(error_upper))
        upper_square = bounds(_square(upper_norm))[1]
        lower_norm = max(Fraction(),bounds(arb(str(head_lo)).sqrt()-arb(str(error_upper)))[0])
        lower_square = lower_norm**2
        budget = {"source_norm_error":str(source_upper),
                  "kernel_lag_norm_error":str(lag_upper),
                  "output_target_tail_norm_error":str(target_upper),
                  "quadrature_norm_error":"0","rounding_norm_error":"0",
                  "filter_operator_norm_upper":"1","total_norm_error":str(error_upper)}
        return {"schema":"OPICA2_NATIVE_EVALUATION_V1","request_sha256":canonical_sha256(request),
                "source_identity":dict(expected_source),"coefficients":request["coefficients"],
                "dictionary_indices":request["dictionary_indices"],
                "target_coefficient":request.get("target_coefficient",{"re":"1","im":"0"}),
                "coefficient_sha256":digest,"lower_square":str(lower_square),"upper_square":str(upper_square),
                "head_energy_interval":{"lower":str(head_lo),"upper":str(head_hi)},
                "source_input_norm_error":str(bounds(eps)[1]),"error_budget":budget,
                "derivative_norm_square_intervals":{str(k):{"lower":str(bounds(v)[0]),"upper":str(bounds(v)[1])}
                                                     for k,v in ev.norm_squares.items()},
                "actualobjects":{"source":"one-copy first-M sinc product inverse Fourier; P^2 multiplier",
                    "delay":str(SIGMA),"source_product_copies":1,"prefix_M":M,"source_correction":correction,
                    "variance_partial":str(ev.variance_hat),"variance_remainder_upper":str(ev.variance_remainder),
                    "kernel_c":"-exp(-s/2)+2exp(-3s/2), causal",
                    "kernel_a":"exp(-3s/2)floor(exp(s))(floor(exp(s))+1-exp(s)), causal",
                    "final_filter":"identity (raw native residual)",
                    "filter_definition_preimage":RAW_FILTER_DEFINITION,
                    "filter_definition_sha256":RAW_FILTER_DEFINITION_SHA256,
                    "floor_seam_cells":ev.seam_cells,"source_value_calls":ev.source_calls,
                    "listed_columns":len(indices),"nonzero_columns":len(active),
                    "quadrature":"interval range Riemann sums plus explicit frequency tails",
                    "quadrature_rounding_location":"included in head_energy_interval",
                    "output_tail":"canonical target only; no killed-tail assumption for finite source"},
                "backend":{"name":"python-flint/Arb","version":version("python-flint"),
                           "lock_sha256":hashlib.sha256(Path(__file__).with_name("python-checks.lock").read_bytes()).hexdigest()},
                "authority":AUTHORITY,"RH":"OPEN","Step4":"OPEN"}
