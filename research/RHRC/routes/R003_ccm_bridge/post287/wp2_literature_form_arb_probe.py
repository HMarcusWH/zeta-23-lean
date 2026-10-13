#!/usr/bin/env python3
"""Rev4 section 14.4: tail-free Arb check of the literature functional.

Source: ExplicitFormula.lean, literatureRHS and gammaBracket; the finite
physical arch representation is supported by DictionaryArchPhysical.lean.
For real coefficients, H(t)=Re integral f(v+t) conj(f(v)) dv. Orthonormal
modes on [0,L] give H(0)=sum u_n^2. The digamma integral, with x=2t, gives

 A=-(gamma+log(pi)+log(1-exp(-2L)))H(0)
   +2 integral_0^L exp(-t/2)/(1-exp(-2t))
        ((exp(-3t/2)-1)H(0)+H(0)-H(t)) dt.

The term beyond L is integrated exactly, since H vanishes there. Sinc
and exponential slopes remove the origin singularity before Arb integration.
This independently constructs H, the pole, primes and arch scalar, without
using matrix entries to construct the literature-side answer. The matrix
backend is used only for comparison. No heuristic frequency tail is dropped.

The reading of this functional as the external papers' form is DERIVED,
not a new Lean theorem or validation of any paper's coercivity certificate.
PASS covers exactly the two real rational vectors below. RH_OPEN.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

from flint import acb, arb, ctx, fmpq

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import canonical_source_arb as C


def exact(value: Fraction | int) -> arb:
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))


def integrate_real(function, aperture: arb) -> arb:
    value = acb.integral(lambda t, analytic: function(t), acb(0), acb(aperture))
    if not value.imag.contains(0):
        raise ArithmeticError("literature scalar acquired a non-real enclosure")
    return value.real


def exp_slope(t: acb) -> acb:
    """Entire (exp(t)-1)/t, including its removable value at zero."""
    return (t / 2).exp() * (acb(0, 1) * t / 2).sinc()


def compare_vector(coefficients: list[Fraction], precision_bits: int) -> dict:
    aperture = exact(Fraction(8, 5))
    indices = list(range(-2, 3))
    weights = [exact(u) for u in coefficients]
    mass = sum((u * u for u in weights), arb(0))

    def deficit_slope(t: acb) -> acb:
        """Entire (H(0)-H(t))/t for the finite real coefficient vector."""
        value = acb(0)
        for n, u in zip(indices, weights):
            frequency = acb(2 * arb.pi() * n / aperture)
            value += u * u * (
                frequency ** 2 * t / 2 * (frequency * t / 2).sinc() ** 2
                + (frequency * t).cos() / aperture)
        for i, n in enumerate(indices):
            for j in range(i + 1, len(indices)):
                m = indices[j]
                value += 2 * weights[i] * weights[j] * (
                    m * (2 * arb.pi() * m * t / aperture).sinc()
                    - n * (2 * arb.pi() * n * t / aperture).sinc()
                ) / (aperture * (m - n))
        return value

    def correlation(t: acb) -> acb:
        return mass - t * deficit_slope(t)

    pole = integrate_real(lambda t: 2 * correlation(t) * (
        (t / 2).exp() + (-t / 2).exp()), aperture)
    # Exactly the prime powers below exp(8/5): 2,3,4; Lambda(4)=log(2).
    prime_weights = {2: arb(2).log(), 3: arb(3).log(), 4: arb(2).log()}
    prime = sum((2 * prime_weights[q] / arb(q).sqrt()
                 * correlation(acb(arb(q).log())).real
                 for q in (2, 3, 4)), arb(0))

    def arch_integrand(t: acb) -> acb:
        # t*exp(-t/2)/(1-exp(-2t)) = exp(t/2)/(2*sinh(t)/t).
        regularized_scale = (t / 2).exp() / (2 * (acb(0, 1) * t).sinc())
        return 2 * regularized_scale * (
            -arb(3) / 2 * exp_slope(-arb(3) * t / 2) * mass
            + deficit_slope(t))

    arch = -(arb.const_euler() + arb.pi().log()
             + (1 - (-2 * aperture).exp()).log()) * mass
    arch += integrate_real(arch_integrand, aperture)
    direct = pole - prime + arch
    matrix = C.canonical_source_matrix(aperture, 2, 4)
    energy = sum((weights[i] * matrix[i, j] * weights[j]
                  for i in range(5) for j in range(5)), arb(0))
    difference = direct - energy
    C.require_finite(mass,pole,prime,arch,direct,energy,difference)
    tolerance = arb(2) ** -(precision_bits // 2)
    if not difference.contains(0) or not bool(abs(difference) < tolerance):
        raise AssertionError("independent literature/canonical normalization mismatch")
    ratio = direct / energy
    C.require_finite(ratio)
    if not ratio.contains(1):
        raise AssertionError("normalization ratio does not enclose one")
    coth = ((aperture / 2).exp() + (-aperture / 2).exp()) / (
        (aperture / 2).exp() - (-aperture / 2).exp())
    extra_arch_correction = (arb.const_euler() + (4 * arb.pi()).log()
                             - coth.log()) * mass
    C.require_finite(coth,extra_arch_correction)
    controls = {
        "factor_two_rejected": not (2 * direct - energy).contains(0),
        "second_arch_correction_rejected": not (
            direct - extra_arch_correction - energy).contains(0),
    }
    if not all(controls.values()):
        raise AssertionError("normalization control was not discriminated")
    return {
        "coefficients": [[u.numerator, u.denominator] for u in coefficients],
        "aperture": [8, 5], "K": 2, "cutoff_Q": 4,
        "mass": C.ball_record(mass, 35),
        "pole": C.ball_record(pole, 35), "prime_subtracted": C.ball_record(prime, 35),
        "arch_added": C.ball_record(arch, 35),
        "canonical_energy": C.ball_record(energy, 35),
        "literature_energy": C.ball_record(direct, 35),
        "difference": C.ball_record(difference, 35),
        "ratio": C.ball_record(ratio, 35), "controls": controls,
    }


def run_probe(precision_bits: int = 256) -> dict:
    if precision_bits < 128:
        raise ValueError("require at least 128 bits for this normalization gate")
    ctx.prec = precision_bits
    vectors = [[Fraction(x) for x in row] for row in (
        ("0.3", "-1", "0.5", "0.7", "-0.2"),
        ("1", "0.25", "-2", "0.6", "0.15"),
    )]
    return {
        "schema": "post287.wp2.literature_scalar_probe.v1",
        "status": "PASS_FINITE_LITERATURE_NORMALIZATION", "terminal_claim": "RH_OPEN",
        "precision_bits": precision_bits,
        "representation": "DERIVED exact digamma x-space transform; no frequency tail approximation",
        "results": [compare_vector(u, precision_bits) for u in vectors],
        "does_not_prove": ["all-vector Lean/Python equivalence", "ambient domain transfer",
                           "external coercivity theorem", "RH"],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--precision-bits", type=int, default=256)
    args = parser.parse_args()
    result = run_probe(args.precision_bits)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "vectors": len(result["results"])}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
