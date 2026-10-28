"""Finite native w-shift Gram enclosures reconstructed by polarization.

Every energy is recomputed on the configured original source. Gershgorin
conditioning and a finite Schur gap are diagnostics, never limit estimates.
"""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
from fractions import Fraction
import math
from typing import Any, Callable, Mapping

try:
    from .certificate_io import canonical_sha256, parse_complex, parse_endpoint_rational, parse_integer, parse_rational, require
except ImportError:
    from certificate_io import canonical_sha256, parse_complex, parse_endpoint_rational, parse_integer, parse_rational, require


def _q(value: Any) -> Fraction:
    return value if type(value) is Fraction else parse_rational(value)


@dataclass(frozen=True)
class Interval:
    lower: Fraction
    upper: Fraction

    def __post_init__(self):
        require(type(self.lower) is Fraction and type(self.upper) is Fraction
                and self.lower <= self.upper, "interval", "Ordered exact rational endpoints required")

    @classmethod
    def point(cls, x):
        x = _q(x)
        return cls(x, x)

    @classmethod
    def read(cls, obj):
        require(type(obj) is dict and set(obj) == {"lower", "upper"}, "interval", "Exact interval fields required")
        def endpoint(value):
            return value if type(value) is Fraction else parse_endpoint_rational(value)
        return cls(endpoint(obj["lower"]), endpoint(obj["upper"]))

    def json(self):
        return {"lower": str(self.lower), "upper": str(self.upper)}

    def __add__(self, other):
        other = other if isinstance(other, Interval) else Interval.point(other)
        return Interval(self.lower+other.lower, self.upper+other.upper)

    def __neg__(self):
        return Interval(-self.upper, -self.lower)

    def __sub__(self, other):
        return self + -other

    def __mul__(self, other):
        other = other if isinstance(other, Interval) else Interval.point(other)
        products = [a*b for a in (self.lower, self.upper) for b in (other.lower, other.upper)]
        return Interval(min(products), max(products))

    def scale(self, x):
        return self*Interval.point(x)

    def square(self):
        return Interval(Fraction() if self.lower <= 0 <= self.upper else
                        min(self.lower**2, self.upper**2), max(self.lower**2, self.upper**2))


@dataclass(frozen=True)
class ComplexInterval:
    re: Interval
    im: Interval

    @classmethod
    def point(cls, obj):
        z = parse_complex(obj)
        return cls(Interval.point(z.re), Interval.point(z.im))

    @classmethod
    def read(cls, obj):
        require(type(obj) is dict and set(obj) == {"re", "im"}, "complex_interval", "Real and imaginary intervals required")
        return cls(Interval.read(obj["re"]), Interval.read(obj["im"]))

    def json(self):
        return {"re": self.re.json(), "im": self.im.json()}

    def conj(self):
        return ComplexInterval(self.re, -self.im)

    def __add__(self, other):
        return ComplexInterval(self.re+other.re, self.im+other.im)

    def __neg__(self):
        return ComplexInterval(-self.re, -self.im)

    def __sub__(self, other):
        return self + -other

    def __mul__(self, other):
        return ComplexInterval(self.re*other.re-self.im*other.im,
                               self.re*other.im+self.im*other.re)

    def norm_square_upper(self):
        return self.re.square().upper+self.im.square().upper


ZERO = {"re":"0", "im":"0"}
ONE = {"re":"1", "im":"0"}
I = {"re":"0", "im":"1"}
MINUS_ONE = {"re":"-1", "im":"0"}


def sqrt_upper(q: Fraction, bits: int = 80) -> Fraction:
    require(type(q) is Fraction and q >= 0 and type(bits) is int and 1 <= bits <= 512,
            "sqrt", "Nonnegative rational and bounded precision required")
    unit = 1 << bits
    scaled = (q.numerator*unit*unit)//q.denominator
    root = math.isqrt(scaled)
    if Fraction(root*root, unit*unit) < q:
        root += 1
    return Fraction(root, unit)


def gershgorin_lower(matrix: list[list[ComplexInterval]]) -> Fraction | None:
    n = len(matrix)
    require(all(len(row) == n for row in matrix), "matrix_shape", "Square Gram required")
    if n == 0:
        return None
    require(all(matrix[i][j] == matrix[j][i].conj() for i in range(n) for j in range(n)),
            "hermitian", "Hermitian interval symmetry required")
    require(all(matrix[i][i].im == Interval.point("0") for i in range(n)),
            "diagonal", "Native Gram diagonal must be real")
    return min(matrix[i][i].re.lower-sum(
        (sqrt_upper(matrix[i][j].norm_square_upper()) for j in range(n) if i != j), Fraction())
        for i in range(n))


def evaluate_gram(base_request: Mapping[str, Any], *, expected_source: Mapping[str, Any],
                  evaluator: Callable | None = None) -> dict[str, Any]:
    """Use actual native energies, including the target, with an independent source configuration."""
    try:
        from .native_evaluation import coefficient_digest, evaluate_native
    except ImportError:
        from native_evaluation import coefficient_digest, evaluate_native
    evaluator = evaluator or evaluate_native
    require(type(base_request) is dict, "gram_request", "Native request required")
    indices = base_request.get("dictionary_indices")
    require(type(indices) is list and 1 <= len(indices) <= 8,
            "gram_size", "Diagnostic Gram supports one to eight literal columns")
    parsed = [parse_integer(x, minimum=1, maximum=10**12) for x in indices]
    require(parsed == sorted(set(parsed)), "gram_indices", "Distinct ascending positive columns required")
    require(base_request.get("source") == dict(expected_source), "source_identity", "Configured original source required")
    original = canonical_sha256(base_request)
    observations = []
    n = len(indices)

    def energy(target, entries):
        request = deepcopy(base_request)
        request["target_coefficient"] = target
        request["coefficients"] = [deepcopy(entries.get(i, ZERO)) for i in range(n)]
        request["coefficient_sha256"] = coefficient_digest(request["coefficients"], indices, target)
        wanted = canonical_sha256(request)
        result = evaluator(request, expected_source=expected_source)
        require(type(result) is dict and result.get("request_sha256") == wanted
                and result.get("source_identity") == dict(expected_source)
                and result.get("coefficient_sha256") == request["coefficient_sha256"],
                "gram_energy_binding", "Native energy does not match exact source and trial")
        value = Interval(parse_endpoint_rational(result["lower_square"], nonnegative=True),
                         parse_endpoint_rational(result["upper_square"], nonnegative=True))
        observations.append({"request_sha256": wanted,"coefficient_sha256":request["coefficient_sha256"],
                             "energy":value.json()})
        return value

    q = energy(ONE, {})
    diagonal = [energy(ZERO,{i:ONE}) for i in range(n)]
    zero = Interval.point("0")
    matrix = [[ComplexInterval(zero,zero) for _ in range(n)] for _ in range(n)]
    cross = []
    for i in range(n):
        matrix[i][i] = ComplexInterval(diagonal[i],zero)
        real = (q+diagonal[i]-energy(ONE,{i:ONE})).scale(Fraction(1,2))
        imag = (q+diagonal[i]-energy(ONE,{i:I})).scale(Fraction(1,2))
        cross.append(ComplexInterval(real,imag))
        for j in range(i):
            real = (diagonal[j]+diagonal[i]-energy(ZERO,{j:ONE,i:MINUS_ONE})).scale(Fraction(1,2))
            imag = (diagonal[j]+diagonal[i]-energy(ZERO,{j:ONE,i:I})).scale(Fraction(1,2))
            matrix[j][i] = ComplexInterval(real,imag)
            matrix[i][j] = matrix[j][i].conj()
    lower = gershgorin_lower(matrix)
    require(canonical_sha256(base_request) == original, "request_mutation", "Gram evaluation changed its input")
    return {"schema":"OPICA2_NATIVE_GRAM_ENCLOSURE_V1","source_identity":dict(expected_source),
            "request_sha256":original,"dictionary_indices":indices,
            "target":"probeTarget","dictionary":"probeColumn(n): actual completed w shifts",
            "inner_product":"conjugate first argument; b_i=<column_i,target>",
            "q":q.json(),"b":[v.json() for v in cross],"G":[[v.json() for v in row] for row in matrix],
            "verified_gram_lower":None if lower is None else str(lower),
            "strict_conditioning_established":lower is not None and lower>0,
            "observations":observations,"authority":"NUMERICAL_ENCLOSURE_NOT_LEAN",
            "asymptotic_claim":False,"full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}


def primal_interval(q: Interval, cross: list[ComplexInterval], matrix: list[list[ComplexInterval]],
                    coefficients: list[dict]) -> Interval:
    """q-2 Re(x*b)+x*Gx, with the native conjugate-first convention."""
    x = [ComplexInterval.point(z) for z in coefficients]
    n = len(x)
    require(len(cross) == n and len(matrix) == n and all(len(row) == n for row in matrix),
            "column_count", "Exact coefficient, cross and Gram dimensions required")
    result = q
    for i in range(n):
        result = result-(x[i].conj()*cross[i]).re.scale(Fraction(2))
        for j in range(n):
            result = result+(x[i].conj()*matrix[i][j]*x[j]).re
    return result


def conditioned_gap(gram: dict, coefficients: list[dict]) -> dict:
    require(gram.get("target") == "probeTarget" and
            gram.get("dictionary") == "probeColumn(n): actual completed w shifts",
            "gram_objects", "Target/v-Gram cannot replace the actual completed dictionary Gram")
    q = Interval.read(gram["q"])
    b = [ComplexInterval.read(v) for v in gram["b"]]
    matrix = [[ComplexInterval.read(v) for v in row] for row in gram["G"]]
    energy = primal_interval(q,b,matrix,coefficients)
    ell = gershgorin_lower(matrix)
    result = {"energy":energy.json(),"ell":None if ell is None else str(ell),
              "distance_square_lower":"0","conditioned":False,
              "projection_space":"span of exactly the listed actual dictionary indices; no lower bound for a larger prefix",
              "dictionary_indices":gram.get("dictionary_indices"),
              "authority":"FINITE_NUMERICAL_DIAGNOSTIC_NOT_LIMIT_PROOF","RH":"OPEN","Step4":"OPEN"}
    if ell is None or ell <= 0:
        return result
    x = [ComplexInterval.point(v) for v in coefficients]
    gradient_upper = Fraction()
    for i in range(len(x)):
        residual = b[i]
        for j in range(len(x)):
            residual = residual-matrix[i][j]*x[j]
        gradient_upper += residual.norm_square_upper()
    result.update(conditioned=True,gradient_square_upper=str(gradient_upper),
                  distance_square_lower=str(max(Fraction(),energy.lower-gradient_upper/ell)))
    return result
