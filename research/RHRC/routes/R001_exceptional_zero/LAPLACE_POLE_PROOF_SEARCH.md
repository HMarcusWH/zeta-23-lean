# R001 Laplace-pole proof search

Status: **proof-search note; no RH claim**.

## Zero-side target

For `s = 1/2 + i xi`, write the R6 zero mode associated to a zero `rho` as

`exp(2 a (rho-s)) / (rho-s)`.

Laplace transformation in `a` gives, initially to the right of the exponential mode,

`1 / ((rho-s) * (z - 2 (rho-s)))`.

With `w = rho-s`,

`1/(w(z-2w)) = (1/z) * (1/w - 1/(w-z/2))`.

Thus a zero with `Re rho > 1/2` produces a candidate pole at

`z_rho = 2 (rho-s)`, with `Re z_rho > 0`.

The intended contradiction mechanism is:

1. a subexponential aperture residual has a holomorphic one-sided Laplace transform on `Re z > 0`;
2. the Laplace-transformed symmetric zero family converges with an additional inverse denominator;
3. after isolating any off-line zero, its transformed term has a genuine right-half-plane pole;
4. the remaining transformed zero family is locally holomorphic near that pole;
5. therefore permanent cancellation cannot make the full aperture residual subexponential if an off-line zero exists.

This replaces a fragile monotone-slope claim by a pole/limsup invariant.

## Existing formal substrate

Anthropic's `Zeta23.XiPrime.ExplicitFormula.ZeroFree` already proves:

- `exists_normSq_sub_ge`: for a point where `xi` is nonzero, distance to every zeta zero has a uniform inverse-square lower comparison;
- `summable_mult_mul`: any zero weight bounded by `C/(1+|gamma_rho|^2)` is absolutely summable with multiplicity;
- `zero_sum_limit_gen`: finite symmetric zero windows converge to that absolutely convergent `tsum`;
- `logDeriv_xi_sub_reflect`: a completed-zeta logarithmic-derivative difference is represented by such an absolutely convergent zero sum.

The Laplace transform adds exactly the second zero-distance denominator needed for the same inverse-square summability mechanism.

## Formal decomposition

- Z0: one-mode Laplace identity — being formalized in `LaplacePole.lean`.
- Z1: absolute summability of the transformed full zero family away from its poles.
- Z2: local holomorphy of the remainder after removing one zero.
- Z3: simple-pole nonremovability at `z = 2(rho-s)` with multiplicity folded into the residue.
- Z4: subexponential residual => holomorphic Laplace transform on the right half-plane.
- Z5: bridge the symmetric R6 residual to the transformed zero family.
- Z6: conclude `Subexponential residual -> no zero with Re rho > 1/2`; functional symmetry then excludes the left half as well.

`R001_ZERO_GROWTH` remains OPEN until Z0-Z6 close without conditional ancestry.

## Prime-side wall

Kim et al. R6 uses the truncated von Mangoldt symbol and subtracts the analytic PNT/log-derivative background. The residual is the classical explicit-formula zero term. A generic pointwise/subexponential bound at the critical line would therefore encode the same zero-free information we seek; PNT alone is insufficient.

`R001_PRIME_UPPER` must therefore obtain a genuinely new bound from additional averaged/operator/probe structure. Rephrasing the classical explicit formula is not progress and is recorded as a dead-route condition.

## Claim discipline

Finite R001 numerics and the Laplace-pole architecture are research guidance only. Mathematical promotion remains Lean/comparator-only.
