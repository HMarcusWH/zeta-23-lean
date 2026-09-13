# RHRC post-#159 delta — Riesz boundary × cross-parity source frontier

Date: 2026-09-13

> **Claim firewall: RH remains OPEN.**

## Exact authority

```text
merged theorem-bearing main = 63862cd80501754c6c6599ffea09b874a327dae4
validated #159 theorem head = b2a064ad5d1f0acbd93309a9257c5661cfa3ec28
validated theorem tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233
RHRC #1021 / run 34736245287 = SUCCESS
Permansson #794 / run 34736245311 = SUCCESS
control-plane semantic anchor = PR #117
```

## What became formally true

PR #159 theoremizes:

```text
iteratedDeriv_one_sourceAtomRealEnergy_eq_two_normSq_sum
iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix
iteratedDeriv_seven_sourceAtomRealEnergy_eq_moment_three
iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
canonicalPolePrimeRieszEndpointScalar
canonicalPolePrimeRieszBoundaryTerm
canonicalPolePrimeRieszEnergy_eq_succ_add_boundary
canonicalRieszSourceChannelEnergy_eq_succ_add_boundary
```

and attaches the exact boundary recurrence to the retained first-bad certificate.

For boundary-flat production carriers:

```text
g^(7)(0) = -2*(2*pi)^6*normSq(M3).
```

For even boundary-flat carriers:

```text
g^(9)(0) = 2*(2*pi)^8*normSq(M4).
```

The complete transformed channel obeys an exact signed recurrence

```text
C_r = C_(r+1) + B_r
```

with no sign assumed for the endpoint scalar.

On retained states this gives exact R6->R7 and, under even parity, R8->R9 moment-square boundary decompositions.

## What changed

The boundary-term sublead is no longer open. The vector dependence of the first surviving even boundary correction is theoremically compressed to one centered-moment square.

Because source energy is odd, all even endpoint jets vanish. Hence odd Riesz-order boundary steps are zero and the natural transformed order flow can be viewed in two-step even increments. This is a DERIVED consequence unless separately theorem-packaged.

Scalar endpoint positivity by itself is not a contradiction: depending on order/sign it may explain or propagate transformed negativity.

## Repo-wide composition discovered after green

The existing negative-shift cross-parity theorem already proves, at an even secular root,

```text
F_odd(lam)
  = overlap(lam) * evenQuadraticSourceMoment L (N+1) u_even(lam).
```

The source moment is already theorem-backed as

```text
evenQuadraticSourceMoment
  = explicitCanonicalSourceMoment
  = pole
    - reduced arch diagonal
    - reduced arch offdiagonal
    - finite von-Mangoldt weighted source atoms.
```

Global first-bad minimality already gives predecessor nonnegativity for either parity at every smaller size.

Therefore the highest-information post-#159 move is not isolated endpoint-scalar scanning. It is to align these existing source/parity interfaces with #159 on the **same negative secular trial**.

## Next theorem package — LEAD

Target:

```text
negative eigenmode -> ParityBad
first-bad predecessor nonnegative for arbitrary parity
negative even secular root -> exact negative complete Riesz-8 state
same root -> exact Riesz-9 / M4 boundary inequality
same root -> odd secular scalar = overlap * explicitCanonicalSourceMoment
```

Then derive the fail-closed fork

```text
odd successor ParityBad
OR
explicitCanonicalSourceMoment(even negative secular trial) != 0.
```

If the odd successor is good, its secular scalar cannot vanish at the same negative shift, so the product on the right is nonzero. No division by overlap/Gamma/source moment is needed.

## New mixed-jet clue — DERIVED / OPEN IN LEAN

Let

```text
h_v(omega)
  = <centeredQuadraticNormal, sourceMatrix(omega) v>
    / <centeredQuadraticNormal, centeredQuadraticNormal>.
```

For even boundary-flat `v`, the exact source-entry expansion suggests

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v).
```

This survived a direct K=2 symbolic sanity check but is **not** Lean theorem authority.

If proved, it would connect the linear cross-parity source-defect channel to the quadratic #159 Riesz boundary:

```text
R8 boundary defect ~ endpointScalar * |M4|^2
                  ~ endpointScalar * |h_v^(7)(0)|^2.
```

This is the strongest new composition clue after #159.

## Falsification checks

Before building around the clue:

- theoremize or independently falsify the mixed source-pairing jet;
- test simultaneous both-parity badness rather than assuming opposite-parity goodness;
- do not infer `explicitCanonicalSourceMoment != 0 -> M4 != 0`;
- do not divide by overlap/Gamma/source moment without theorem-backed nonzeroness;
- preserve exact pole/prime/archimedean cancellation;
- test fixed-cell / prime-power-threshold canonical states with exact/Arb tooling;
- retain modified-source controls to detect structure-only arguments.

DR-024 remains dead: none of this uses pointwise fixed-sign Riesz-integrand positivity.

## Highest-leverage next moves

1. Synchronize living docs/control to theorem authority #159.
2. Theoremize the same-state shifted Riesz × cross-parity source composition.
3. Perform the required post-green pass on the resulting parity/source dichotomy.
4. If promising, theoremize the mixed quadratic-normal source-pairing seventh jet.
5. Retarget the interval harness to the composed mechanism before attempting an opposing sign theorem.

## Status firewall

**PROVED:** #159 self-energy moment jets and signed Riesz boundary recurrence; existing cross-parity source transfer; exact explicit source-moment decomposition.

**DERIVED:** two-step even Riesz-order viewpoint; mixed source-pairing seventh-jet formula; expected opposite-parity-good -> source-moment-nonzero consequence once same-state proof arguments are aligned.

**LEAD / HYPOTHESIS:** linear source-defect + quadratic Riesz-defect composition as an arithmetic rigidity mechanism.

**OPEN:** independent contradiction-producing arithmetic restriction, negative-root exclusion, terminal RH seam, RH.

**RH remains OPEN.**
