# Astra post-#155 RH path assessment — external review provenance

Date recorded: 2026-09-13

> **Evidence class:** EXTERNAL DERIVED / REVIEW EVIDENCE. This file preserves an external assessment supplied to the project after merged PR #155. It does not become Lean theorem authority by being stored in the repository. Compiler/CI evidence wins. **RH remains OPEN.**

## Central assessment

The review independently checked PRs #151-#155 and agreed with the core post-green correction:

> PR #155 solves the analytic legality of smoothing, not the production jet instantiation and not the arithmetic sign problem.

At the reviewed state, merged `main` was

```text
7bd3f1028d42272fcadc347c43371b992d9c0bd7
```

and the theorem inventory distinguished:

```text
generic smoothing engine: PROVED
production order-6/order-8 specialization: DERIVED / OPEN IN LEAN
arithmetic sign of the complete transformed residual: OPEN.
```

## Source-coordinate D-transport composition

The review derives the entrywise matrix relation

```text
A'' + (2*pi)^2 D A D
  = -4*pi * (rank-at-most-two correction)
```

where the correction is built from the all-ones vector and the sine profile.

For complex coefficients `u`, if

```text
sum u_n = 0,
```

the correction's Hermitian quadratic form vanishes because every correction term contains `sum u` or its conjugate. Hence the review derives

```text
g_u''(omega)=-(2*pi)^2 g_(D u)(omega).
```

**Status in this file: EXTERNAL DERIVED.**

## Recommended stronger theorem composition

Rather than making the full arbitrary Taylor convolution the primary implementation target, the review recommends the moment-prefix recursion.

Using the already-existing moment shift

```text
M_k(Du)=M_(k+1)(u),
```

the proposed theorem is

```text
M0=...=M(r-1)=0
  -> g_u^(2r)(omega)=(-1)^r*(2*pi)^(2r)*g_(D^r u)(omega)
```

and therefore

```text
g_u^(2r+1)(0)=2*(-1)^r*(2*pi)^(2r)*|M_r(u)|^2.
```

Expected consequences:

```text
M0=M1=M2=0
  -> g^(1)(0)=g^(3)(0)=g^(5)(0)=0
  -> g^(7)(0)=-2*(2*pi)^6*|M3|^2

even parity + M3=0
  -> g^(7)(0)=0
  -> g^(9)(0)=2*(2*pi)^8*|M4|^2.
```

These remain unproved until Lean validates them.

## Complex-production implementation warning

The review explicitly warns that existing contraction-level second-derivative lemmas are for real coefficient vectors, while production `sourceAtomRealEnergy` is the real part of a genuinely complex sesquilinear quadratic form.

Recommended safe implementation:

```text
1. prove the entrywise rank-two identity with sourceEntrySecondDerivative;
2. include the diagonal case;
3. coerce the identity to the complex source matrix;
4. sum against conj(u_i)*u_j;
5. explicitly kill the correction from sum u=0;
6. identify D A D with source energy of indexMatrix *ᵥ u.
```

A theorem only for `sourceContractReal` must not be silently promoted to the complex production trial.

## Exact falsification of pointwise positivity shortcut

The review supplies exact boundary-flat `K=2` fixtures

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

and reports that the relevant seventh/ninth derivatives change sign even though the discrepancy primitives can be positive in the prime-free aperture.

Therefore the proposed mechanism

```text
positive Riesz primitive + boundary flatness
  -> pointwise nonnegative smoothed integrand
```

is false as a universal route.

This does not refute the exact Riesz representation. It redirects the sign problem to the complete integrated discrepancy minus archimedean/scalar residual.

## Downstream assessment

If the D-transport / production-jet theorem is formalized, the review expects the off-line-zero chain to sharpen to

```text
off-line zero
  -> retained regular first-bad certificate
  -> exact canonical source-channel energy < 0
  -> exact order-6 transformed negative residual
```

or exact order 8 in the even sector.

At that point the remaining contradiction-producing step is an independent signed arithmetic estimate or transfer mechanism for the complete transformed residual.

## Combined-parity lead

The review notes that the first surviving local cutoff effects have opposite parity signs and proposes testing quantities such as

```text
S_even + S_odd
S_even * S_odd
```

across prime-power thresholds and within fixed cells.

**Status: LEAD / HYPOTHESIS.** The recommendation is to falsify numerically before Lean investment.

## Recommended next theorem PR

```text
CCM: prove source-coordinate D transport and close production Riesz jets
```

Proposed theorem-bearing core:

```text
CanonicalSourceDerivativeTransport.lean
CanonicalSourceEnergyJets.lean
CanonicalPolePrimeRiesz.lean
RegularFirstBadRieszEnergy.lean
ExceptionalZero/RegularFirstBadClosure.lean
```

The external review recommends leaving the #152 observable unchanged until the exact Lean transformed residual exists.

## Claim boundary

The review explicitly does **not** claim:

```text
complete transformed-residual nonnegativity
negative-root exclusion
RiemannHypothesis.
```

**RH remains OPEN.**
