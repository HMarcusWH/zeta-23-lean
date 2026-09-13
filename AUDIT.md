# RHRC formal audit — theorem authority through PR #157; transformed arithmetic frontier

> **RH remains OPEN.**

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

Live GitHub head + exact compiler/CI evidence outrank this prose. The validated #157 head and merged main are distinct commits that share the same theorem tree.

## Exact validation evidence for #157

At validated theorem head

```text
4b517db1d4a50277d325e77e771a30fc0db5c777
```

RHRC run #1017 (`34731682546`) completed successfully. Permansson run #790 (`34731682544`) also completed successfully.

The successful theorem-bearing closure includes the aggregate CCM build, ExceptionalZero build, R003 normalization/source firewalls, no-sorry/no-project-axiom checks, and the independent Permansson verification lane.

## Exact theorem-state progression relevant to #157

### PR #153 — retained certificate + exact finite discrepancy

**PROVED:** the complete whole-cell regular first-bad ancestry and negative canonical source-channel state are retained in `RegularCellMinimalNegativeEnergyCertificate`; the pole-minus-prime channel is rewritten through the exact finite `canonicalPolePrimeDiscrepancy` before the reduced archimedean/scalar terms are subtracted.

### PR #155 — legal generic smoothing + source parity/even jets

**PROVED:** finite discrepancy integrability, left-anchored Riesz primitives, positive-order absolute continuity, the a.e. derivative seam, generic arbitrary-order legal repeated integration by parts under explicit endpoint-jet hypotheses, production source-coordinate oddness, all even endpoint derivatives at zero, and even-parity `M3=0`.

### PR #157 — genuine complex production D transport

**PROVED:**

```text
sourceEntrySecondDerivative_transport
sourceContractRealSecondDerivative_transport_with_defect
sourceContractRealSecondDerivative_transport
sourceAtomRealEnergy_eq_re_im_contracts
sourceAtomRealEnergySecondDerivative_eq_indexAction
```

The complex production identity is proved through an explicit real/imaginary decomposition. The rank-two defect remains visible until the complex zero-sum condition kills it.

### PR #157 — production endpoint jets

**PROVED:**

```text
iteratedDeriv_one_sourceAtomRealEnergy_zero_of_sum_eq_zero
iteratedDeriv_two_sourceAtomRealEnergy_eq_indexAction
iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
sourceAtomRealEnergy_boundaryFlat_jets_through_six
sourceAtomRealEnergy_even_boundaryFlat_jets_through_eight
```

Thus boundary-flat production carriers have jets 1..6 zero, while even boundary-flat carriers have jets 1..8 zero.

### PR #157 — complete production Riesz channel

**PROVED:**

```text
canonicalRieszSourceChannelEnergy
canonicalPolePrimeDiscrepancyEnergy_eq_rieszSix_of_boundaryFlat
canonicalPolePrimeDiscrepancyEnergy_eq_rieszEight_of_even_boundaryFlat
canonicalSourceChannelEnergy_eq_rieszSix_of_boundaryFlat
canonicalSourceChannelEnergy_eq_rieszEight_of_even_boundaryFlat
```

The complete transformed channel retains both reduced archimedean pieces and the scalar correction.

### PR #157 — retained transformed-negative state

**PROVED:**

```text
RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszSix
RegularCellMinimalNegativeEnergyCertificate.rieszSixNeg
RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszEight_of_even
RegularCellMinimalNegativeEnergyCertificate.rieszEightNeg_of_even
exists_regularFirstBad_rieszSixNegativeCertificate_of_offLine_zero
exists_regularFirstBad_rieszSixNegativeCertificate_of_exists_offLine_zero
```

Every retained regular first-bad certificate carries strict complete Riesz-6 negativity. The stronger retained Riesz-8 result requires even first-bad parity. A hypothetical off-line zero therefore reaches the retained complete Riesz-6 negative certificate directly.

## What #157 did not prove

No current Lean theorem establishes:

```text
an independent nonnegative sign for the complete transformed residual
an exact first Riesz boundary-term sign theorem
exact g^(7)(0) / g^(9)(0) leading-moment coefficient formulas
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

The formulas

```text
g^(7)(0) = -2*(2*pi)^6*|M3|^2
g^(9)(0) =  2*(2*pi)^8*|M4|^2
```

remain **DERIVED / OPEN IN LEAN**. #157 proves the zero cases needed for Riesz 6/8, not these exact leading coefficients.

## Exact route falsification still active

The boundary-flat `K=2` fixtures

```text
even = (1,-4,6,-4,1)
odd  = (1,-2,0,2,-1)
```

show that the relevant seventh/ninth source derivatives change sign. Therefore the universal implication

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

remains **DEAD**.

This does not refute the Riesz identity. It refutes a proposed pointwise sign mechanism. The complete integrated transformed residual may still admit an arithmetic sign through stationarity, whole-cell ancestry, lower-size transfer, a boundary-term identity or a different cancellation invariant.

## Current formal endpoint

From a hypothetical off-line zero, current theorem authority now yields

```text
retained regular first-bad certificate
  -> complete canonical source-channel energy < 0
  -> exact complete Riesz-6 source-channel representation
  -> complete retained Riesz-6 source-channel energy < 0.
```

The former FB-03E/FB-03F bridge is closed. The only missing contradiction-producing implication is now genuinely arithmetic.

## Current execution order

```text
FB-01  retained first-bad certificate                              PROVED / #153
FB-02  exact pole-prime discrepancy                                PROVED / #153
FB-03A discrepancy integrability                                   PROVED / #155
FB-03B anchored primitives + AC / a.e. derivative                 PROVED / #155
FB-03C generic repeated IBP / conditional Riesz                    PROVED / #155
FB-03D source oddness + all even jets + even M3=0                  PROVED / #155
FB-03E complex D-transport + production odd jets + Riesz 6/8      PROVED / #157
FB-03F retained transformed-negative wrapper                       PROVED / #157
FB-04  complete transformed-residual arithmetic mechanism          OPEN / NEXT
FB-05  scoped complete-residual nonnegative sign                   OPEN
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  terminal outside-strip/trivial-zero seam                    OPEN
```

## Highest-leverage next mathematical probe

The next theorem/falsification package should expose a generic one-step Riesz boundary recurrence

```text
E_r = E_(r+1) + B_r
```

without asserting a sign, then theoremize exact leading endpoint jets only if needed and immediately try to falsify any proposed scalar boundary-factor sign numerically/with Arb.

This is a **LEAD / HYPOTHESIS**, not theorem authority.

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- theorem authority through #157 and machine claim promotion are separate;
- complete retained Riesz negativity is not itself a contradiction;
- exact discrepancy/Riesz identities are not arithmetic sign theorems;
- R8 is conditional on even retained parity;
- exact seventh/ninth leading-jet coefficients remain open;
- Riesz smoothing is not a pointwise sign theorem;
- pointwise smoothed-integrand positivity remains falsified as a universal route;
- interval-certified finite numerics are scoped falsification evidence, not Lean theorem authority;
- regularity is not successor positivity;
- `D` algebraic != `D` unitary/isometric;
- negative-root exclusion != terminal Mathlib RH without the final seam;
- RH remains OPEN.

Newest research implications:
`research/RHRC/RESEARCH_LEADS_POST_157_PRODUCTION_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**
