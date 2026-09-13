# RHRC formal audit — theorem authority through PR #159; same-state arithmetic frontier

> **RH remains OPEN.**

## Current authority split

```text
live main after merged PR #159 = 63862cd80501754c6c6599ffea09b874a327dae4
live main tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233
latest theorem-bearing PR = #159
validated theorem head = b2a064ad5d1f0acbd93309a9257c5661cfa3ec28
validated theorem tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233
RHRC #1021 / run 34736245287 = SUCCESS
Permansson #794 / run 34736245311 = SUCCESS
control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose. The validated #159 head and merged main are distinct commits sharing the theorem tree above.

## Exact validation evidence

At `b2a064ad5d1f0acbd93309a9257c5661cfa3ec28`, RHRC #1021 and Permansson #794 completed successfully. The theorem-bearing closure includes aggregate CCM and ExceptionalZero builds, R003 normalization/source checks, Control-v2/regression tests and the forbidden-placeholder/project-axiom gate.

## Relevant theorem progression

### #153

Retained whole-cell regular first-bad ancestry and negative canonical source energy; exact finite pole-prime discrepancy/full-channel normal form.

### #155

Finite discrepancy integrability; anchored Riesz primitives; AC/a.e. derivative seam; legal arbitrary-order conditional integration by parts; source oddness and all even endpoint jets.

### #157

Genuine complex production D transport; boundary-flat jets through 6; even jets through 8; exact complete Riesz 6/even 8; retained transformed negativity; off-line-zero -> retained Riesz-6 negative certificate.

### #159 — production moment jets

**PROVED:**

```text
iteratedDeriv_one_sourceAtomRealEnergy_eq_two_normSq_sum
iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix
iteratedDeriv_seven_sourceAtomRealEnergy_eq_moment_three
iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
```

Hence the previously derived exact seventh and even ninth self-energy moment formulas are now theorem authority.

### #159 — signed Riesz boundary recurrence

**PROVED:**

```text
canonicalPolePrimeRieszEndpointScalar
canonicalPolePrimeRieszBoundaryTerm
canonicalPolePrimeRiesz_integral_step_with_boundary
canonicalPolePrimeRieszEnergy_eq_succ_add_boundary
canonicalRieszSourceChannelEnergy_eq_succ_add_boundary
```

The complete transformed channel retains the reduced archimedean and scalar pieces. No endpoint-scalar sign is asserted.

### #159 — retained first-bad boundary decompositions

**PROVED:**

```text
RegularCellMinimalNegativeEnergyCertificate.rieszSix_eq_rieszSeven_sub_momentThree
RegularCellMinimalNegativeEnergyCertificate.rieszSeven_lt_momentThreeBoundary
RegularCellMinimalNegativeEnergyCertificate.rieszEight_eq_rieszNine_add_momentFour_of_even
RegularCellMinimalNegativeEnergyCertificate.rieszNine_lt_neg_momentFourBoundary_of_even
```

The R8/R9 statements require even retained parity.

## What #159 does not prove

No current Lean theorem establishes:

```text
endpoint-scalar positivity
same-state shifted negative secular trial x #159 Riesz composition
retained opposite-parity-bad OR explicit-source-moment-nonzero fork
mixed quadratic-normal source-pairing seventh jet = constant*M4
independent contradiction-producing arithmetic restriction
negative-root exclusion
terminal RiemannHypothesis
```

The mixed source-pairing jet must not be inferred from #159's self-energy jet theorem.

## Post-green composition discovered

The repository already proves that at an even negative secular root

```text
odd secular scalar
  = overlap * evenQuadraticSourceMoment(even shifted trial),
```

and separately proves `evenQuadraticSourceMoment = explicitCanonicalSourceMoment` with exact pole/arch/prime decomposition.

Global first-bad minimality already supplies predecessor nonnegativity for arbitrary parity at every smaller size.

Therefore the highest-information next theorem is to put these existing interfaces and #159 on the **same shifted trial**, not to continue treating the endpoint scalar in isolation.

Expected fail-closed consequence:

```text
odd successor ParityBad
OR
explicitCanonicalSourceMoment(even negative secular trial) != 0.
```

No factorwise division is required.

## Exact route falsification still active

The K=2 boundary-flat fixtures continue to refute universal pointwise fixed-sign smoothed-integrand positivity. This does not refute the exact integrated Riesz recurrence or same-state source composition.

## Current execution order

```text
FB-01  retained first-bad certificate                              PROVED / #153
FB-02  exact pole-prime discrepancy                                PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex transport / retained transformed negativity       PROVED / #157
FB-04A moment jets + signed Riesz boundary recurrence               PROVED / #159
FB-04B shifted Riesz x cross-parity source composition             OPEN / NEXT
FB-04C mixed source-pairing jet -> M4                              DERIVED / OPEN
FB-05  independent contradiction-producing arithmetic restriction OPEN
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  terminal seam                                               OPEN
```

## Permanent firewalls

- compiler/CI validity is authoritative;
- theorem authority through #159 and machine claim promotion are separate;
- complete retained transformed negativity is not a contradiction;
- exact discrepancy/Riesz identities are not arithmetic sign theorems;
- no division by transfer factors without nonzeroness;
- `D` algebraic != `D` unitary/isometric;
- #159 self-energy moment jets != mixed source-pairing jet;
- pointwise smoothed-integrand positivity remains dead as a universal route;
- interval-certified finite numerics are falsification evidence, not Lean authority;
- negative-root exclusion != terminal Mathlib RH without final seam;
- RH remains OPEN.

Newest research implications:
`research/RHRC/RESEARCH_LEADS_POST_159_RIESZ_CROSS_PARITY_FRONTIER_DELTA.md`.

**RH remains OPEN.**
