# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
live main after merged PR #157 = e304f07c9e83165ebf066db0d67c2cc24f8961c2
live main tree = 706dfde7f9e7b0b8403a671769d424ac7862f5e7

latest theorem-bearing PR = #157
validated theorem head = 4b517db1d4a50277d325e77e771a30fc0db5c777
validated theorem tree = 706dfde7f9e7b0b8403a671769d424ac7862f5e7
RHRC #1017 / run 34731682546 = SUCCESS
Permansson #790 / run 34731682544 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI remain authoritative. The #157 validated head and merged `main` share the theorem tree but not the commit SHA.

## One-screen frontier

```text
DONE THROUGH #153
  off-line zero -> retained regular cell-minimal first-bad certificate
  exact negative canonical source-channel energy on that retained state
  exact finite pole-prime discrepancy and full-channel normal form

DONE / #155
  finite discrepancy interval integrability
  anchored iterated discrepancy primitives
  positive-order absolute continuity / a.e. derivative seam
  legal generic repeated integration by parts
  arbitrary-order conditional Riesz energy identity
  source-coordinate oddness
  all even endpoint derivatives vanish
  even reversal parity -> M3 = 0

DONE / #157 — FB-03E/F CLOSED
  genuine complex production D transport
  zero-sum annihilation of the rank-two defect
  exact two-step higher-jet transport
  boundary-flat jets 1..6 vanish
  even boundary-flat jets 1..8 vanish
  exact complete production Riesz order 6
  exact complete production Riesz order 8 under even parity
  retained complete Riesz-6 source-channel energy < 0
  retained complete Riesz-8 source-channel energy < 0 under even first-bad parity
  off-line zero -> retained complete Riesz-6 negative certificate

NOW — FB-04 ARITHMETIC-MECHANISM FALSIFICATION
  formulate a specific candidate mechanism for the EXACT complete transformed residual
  preserve discrepancy/archimedean/scalar cancellation
  align numerical/Arb tooling with the theorem-backed transformed observable
  try to falsify the mechanism before theorem investment

HIGHEST-LEVERAGE SUBLEAD — FIRST RIESZ BOUNDARY TERM
  prove a generic signed recurrence

    E_r = E_(r+1) + B_r

  expose the first nonvanishing endpoint contribution
  theoremize exact seventh/ninth leading-jet formulas only if needed
  probe scalar endpoint factors across fixed cutoff cells and prime-power thresholds

DECISIVE OPEN ARITHMETIC TARGET
  prove on the exact forced retained state

    complete transformed residual >= 0

  independently of successor positivity / one-step domination restatements

TARGET
  same-state contradiction
  -> negative-root exclusion
  -> explicit outside-strip/trivial-zero seam
  -> Mathlib RiemannHypothesis wrapper
  RH OPEN
```

## Exact #157 theorem package consumed by the new frontier

### FB-03E — complex production D transport

**PROVED / #157**

Key declarations:

```text
sourceEntrySecondDerivative_transport
sourceContractRealSecondDerivative_transport_with_defect
sourceContractRealSecondDerivative_transport
sourceAtomRealEnergy_eq_re_im_contracts
sourceAtomRealEnergySecondDerivative_eq_indexAction
```

The proof explicitly handles complex production coefficients. The rank-two defect is not erased before the zero-sum hypothesis is applied.

### FB-03E — endpoint jets

**PROVED / #157**

```text
iteratedDeriv_one_sourceAtomRealEnergy_zero_of_sum_eq_zero
iteratedDeriv_two_sourceAtomRealEnergy_eq_indexAction
iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
sourceAtomRealEnergy_boundaryFlat_jets_through_six
sourceAtomRealEnergy_even_boundaryFlat_jets_through_eight
```

Hence:

```text
BoundaryFlatCoefficients -> jets 1..6 vanish
BoundaryFlatCoefficients + evenCoefficientSubspace -> jets 1..8 vanish.
```

### FB-03E — exact complete production Riesz representations

**PROVED / #157**

```text
canonicalRieszSourceChannelEnergy
canonicalPolePrimeDiscrepancyEnergy_eq_rieszSix_of_boundaryFlat
canonicalPolePrimeDiscrepancyEnergy_eq_rieszEight_of_even_boundaryFlat
canonicalSourceChannelEnergy_eq_rieszSix_of_boundaryFlat
canonicalSourceChannelEnergy_eq_rieszEight_of_even_boundaryFlat
```

No pointwise sign theorem is included. The transformed complete channel retains both reduced archimedean matrices and the scalar correction.

### FB-03F — retained transformed-negative state

**PROVED / #157**

```text
RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszSix
RegularCellMinimalNegativeEnergyCertificate.rieszSixNeg
RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszEight_of_even
RegularCellMinimalNegativeEnergyCertificate.rieszEightNeg_of_even
exists_regularFirstBad_rieszSixNegativeCertificate_of_offLine_zero
exists_regularFirstBad_rieszSixNegativeCertificate_of_exists_offLine_zero
```

No parallel certificate type is introduced. Whole-cell ancestry, selected predecessor nonnegativity, regularity, exact preimage and negative Schur root remain attached to the same retained object.

## What #157 does not close

The following remain open:

```text
independent arithmetic nonnegativity of the complete transformed residual
exact generic one-step Riesz boundary recurrence
exact seventh/ninth leading-moment coefficient formulas
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

The derived endpoint formulas

```text
g^(7)(0) = -2*(2*pi)^6*|M3|^2
g^(9)(0) =  2*(2*pi)^8*|M4|^2
```

are not theorem authority.

## FB-04A — first Riesz boundary-term probe

This is the preferred next theorem/falsification slice because it has high information gain and small dependency debt.

### A1 — generic signed boundary recurrence

Do not create separate positive-looking defect definitions prematurely. Define one signed generic term, schematically

```text
canonicalPolePrimeRieszBoundaryTerm L r K x
  = (1/L)^(r+1)
    * canonicalPolePrimeRieszPrimitive L (r+1) L
    * iteratedDeriv (r+1) (sourceAtomRealEnergy K x) 0.
```

Target the exact recurrence

```text
canonicalPolePrimeRieszEnergy L r K x
  = canonicalPolePrimeRieszEnergy L (r+1) K x
    + canonicalPolePrimeRieszBoundaryTerm L r K x.
```

Then lift it definitionally to `canonicalRieszSourceChannelEnergy`, since the archimedean/scalar pieces do not depend on `r`.

No sign theorem belongs in A1.

### A2 — exact leading endpoint jets only if needed

The existing #157 recursion already supplies the zero cases. If the boundary recurrence makes the first surviving coefficient useful, theoremize:

```text
iteratedDeriv 1 (...) 0 = 2 * Complex.normSq (sum coefficients)
sourceIndexAction^4 coefficient sum = centeredMoment 4
boundary-flat -> g^(7)(0) = -2*(2*pi)^6 * normSq(M3)
even boundary-flat -> g^(9)(0) = 2*(2*pi)^8 * normSq(M4).
```

Do not generalize beyond what is needed by the arithmetic probe unless Lean reveals a cleaner canonical theorem.

### A3 — exact/Arb falsifier

Reuse existing R003 backends rather than introducing a parallel normalization:

```text
canonical_source_numeric.py
canonical_source_arb.py
```

Reuse fixed-cell and exact/rational helpers such as:

```text
fixed_cell_bounds
fixed_cell_membership
dyadic_inside_fixed_cell
to_arb_rational
von_mangoldt
ball_record
definitely_positive
definitely_negative.
```

Test the scalar Riesz endpoint factors / proposed boundary-sign mechanism across:

- small K including K=1 and K=2;
- both parity sectors where applicable;
- interior dyadic apertures in certified fixed cells;
- prime-power threshold neighborhoods;
- accidental `M3=0` / `M4=0` degeneracies;
- rescaling of the trial vector.

If a finite canonical state falsifies the mechanism, preserve it as a regression fixture and stop investing in that route.

## FB-04 — broader mechanism falsification

If the first-boundary-term route fails, move directly to other exact mechanism families:

1. stationarity `A x0=b` inside the transformed representation;
2. transfer to smaller-size good predecessor energies;
3. whole-cell minimality across the fixed cutoff cell;
4. cancellation identities coupling discrepancy and archimedean/scalar channels;
5. combined-parity invariants.

Do not merely rescan total signs. #157 already theoremizes the transformed negative state under the hypothetical off-line-zero route.

## Dead route — pointwise smoothed-integrand positivity

Exact boundary-flat `K=2` fixtures

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

show the relevant seventh/ninth derivatives change sign. Therefore

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

remains dead as a universal route.

A generic integrated boundary recurrence is not a revival of this dead route.

## Lead — combined parity

The first surviving local cutoff contribution has opposite signs in the two parity sectors. This motivates, but does not prove usefulness of,

```text
S_even + S_odd
S_even * S_odd
```

or another cross-parity invariant.

**Status: LEAD / HYPOTHESIS.** Cheapest next action is numerical falsification across prime-power thresholds and within fixed cells before Lean investment.

## Broad fallback

Universal `canonicalOneStepDomination` remains sufficient but is not a research reduction if its proof merely restates positivity of the successor block or absence of the negative root.

It should become primary only if a genuinely independent canonical arithmetic mechanism appears.

## Semantic work packages

```text
FB-01  retained full first-bad certificate                         PROVED / #153
FB-02  exact finite pole-prime discrepancy                         PROVED / #153
FB-03A finite discrepancy integrability                            PROVED / #155
FB-03B anchored primitives + AC / a.e. derivative                 PROVED / #155
FB-03C generic repeated IBP / conditional Riesz                    PROVED / #155
FB-03D source oddness + all even jets + even M3=0                  PROVED / #155
FB-03E complex D-transport + odd jets + exact Riesz 6/8           PROVED / #157
FB-03F retained transformed-negative wrapper                       PROVED / #157
FB-04  transformed arithmetic-mechanism falsification              OPEN / NEXT
FB-05  scoped complete-residual nonnegative sign                   OPEN
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  terminal zeta/Mathlib seam                                  OPEN
```

PR numbers are execution history, not mathematical dependencies.

## Permanent firewalls

1. A retained transformed negative certificate is not a contradiction.
2. Exact discrepancy/Riesz identities are not arithmetic positivity.
3. R8 is conditional on even retained parity.
4. Exact seventh/ninth leading-jet formulas remain open until separately theoremized.
5. Riesz smoothing is not a pointwise sign theorem.
6. Pointwise fixed-sign smoothed integrand remains falsified as a universal mechanism.
7. Interval-certified finite numerics are not Lean theorem authority.
8. Regular predecessor is not a positive successor.
9. Machine claim promotion remains separate from compiler theorem validity.
10. Negative-root exclusion is still not the terminal Mathlib RH statement without the final seam.

Newest research delta:

`RESEARCH_LEADS_POST_157_PRODUCTION_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`

**RH remains OPEN.**
