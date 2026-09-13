# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #157. COMPLEX PRODUCTION D-TRANSPORT + EXACT COMPLETE RIESZ 6/8 + RETAINED TRANSFORMED NEGATIVITY ARE CLOSED; CURRENT FRONTIER = SPECIFIC COMPLETE TRANSFORMED-RESIDUAL ARITHMETIC MECHANISMS. RH OPEN.**

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

## Closed internal ladder

```text
F1 finite canonical obstruction                                  PROVED / #94
constrained / Euclidean finite wall                              PROVED / #96-#98
N-FLOW + parity + first-bad geometry                             PROVED / #100-#112
shifted/zero-shift Schur/secular package                        PROVED / #113-#128
source-explicit parity transfer                                  PROVED / #129
exact source-moment decomposition                                PROVED / #131
whole-kernel zero-shift source transport                         PROVED / #134
absolute canonical source energy                                 PROVED / #136
exact canonical source pairing + one-step determinant            PROVED / #137
regular selected first-bad endpoint                              PROVED / #140-#150
retained full first-bad / negative-energy certificates           PROVED / #153
exact finite pole-prime discrepancy / full-channel normal form   PROVED / #153
finite discrepancy interval integrability                       PROVED / #155
anchored Riesz primitives + AC / a.e. derivative                PROVED / #155
generic legal repeated IBP / conditional Riesz                   PROVED / #155
source oddness + all even endpoint jets                          PROVED / #155
even reversal parity -> M3=0                                    PROVED / #155
genuine complex production D transport                           PROVED / #157
boundary-flat jets 1..6 / even jets 1..8                         PROVED / #157
exact complete production Riesz 6 / even Riesz 8                 PROVED / #157
retained complete Riesz-6 negativity                             PROVED / #157
retained complete Riesz-8 negativity when parity even            PROVED / #157
ExceptionalZero -> retained Riesz-6 negative certificate          PROVED / #157
```

## Retained first-bad certificate surface

PR #153 exports

```text
RegularCellMinimalFirstBadCertificate
RegularCellMinimalNegativeEnergyCertificate
```

with theorem constructors

```text
exists_regular_cellMinimal_firstBadCertificate
exists_regular_cellMinimal_negativeCanonicalEnergyCertificate
exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero.
```

The current forced state therefore retains whole-cell minimality, selected-aperture smaller-size goodness, regularity, predecessor nonnegativity, the negative explicit Schur root, exact `A x0=b`, and strict negative production source-channel energy.

## Exact discrepancy + production Riesz surface

The exact finite discrepancy is

```text
D_L(t)
 = canonicalPolePrimeDiscrepancy L t
 = 4*sinh(t/2)
   - sum_{q in Icc 2 floor(exp L), log q <= t} Lambda(q)/sqrt(q).
```

PR #153 proves

```text
matrixRealEnergy_pole_sub_prime_eq_discrepancy
canonicalSourceChannelEnergy_eq_discrepancy.
```

PR #155 proves legal left-anchored smoothing through `canonicalPolePrimeRieszPrimitive` without differentiating the prime staircase.

PR #157 consumes the remaining production endpoint hypotheses and defines

```text
canonicalRieszSourceChannelEnergy L r K x
```

as the complete transformed channel:

```text
canonicalPolePrimeRieszEnergy L r K x
- reduced arch diagonal energy
- reduced arch offdiagonal energy
- canonicalArchScalarCorrection L * ||x||^2.
```

## Exact #157 complex production surface

Validated production declarations include:

```text
sourceAtomRealEnergy_eq_re_im_contracts
sourceAtomRealEnergySecondDerivative_eq_indexAction
iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
sourceAtomRealEnergy_boundaryFlat_jets_through_six
sourceAtomRealEnergy_even_boundaryFlat_jets_through_eight
canonicalSourceChannelEnergy_eq_rieszSix_of_boundaryFlat
canonicalSourceChannelEnergy_eq_rieszEight_of_even_boundaryFlat.
```

The previous FB-03E implementation firewall is closed for this exact theorem surface. `D` remains algebraic; no unitary/isometric transport is implied.

## Exact #157 retained transformed-negative surface

Validated declarations include:

```text
RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszSix
RegularCellMinimalNegativeEnergyCertificate.rieszSixNeg
RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszEight_of_even
RegularCellMinimalNegativeEnergyCertificate.rieszEightNeg_of_even
exists_regularFirstBad_rieszSixNegativeCertificate_of_offLine_zero.
```

Therefore every retained first-bad certificate has complete Riesz-6 energy `< 0`; the stronger complete Riesz-8 theorem requires retained even parity.

A hypothetical off-line zero yields the retained complete Riesz-6 negative certificate. No contradiction is claimed.

## Current frontier — FB-04 exact arithmetic mechanism

The transformed negative state is theorem-backed. The immediate question is now:

```text
What independent canonical arithmetic statement can force the exact same
complete transformed residual to be >= 0?
```

The first step is mechanism falsification, not theorem inflation.

Candidate families:

```text
stationarity A x0=b inside the transformed representation
lower-size predecessor-energy transfer
whole-cell first-bad minimality across the fixed cutoff cell
first nonvanishing Riesz boundary term
exact discrepancy/archimedean/scalar cancellation identity
combined-parity invariant.
```

## First Riesz boundary-term sublead

**Status: LEAD / HYPOTHESIS.**

The preferred next theorem package should first expose a generic signed recurrence

```text
E_r = E_(r+1) + B_r
```

where `B_r` is the right-endpoint contribution from one further integration by parts.

Only after that identity exists should we theoremize, if needed, the derived endpoint formulas

```text
g^(7)(0) = -2*(2*pi)^6*|M3|^2
g^(9)(0) =  2*(2*pi)^8*|M4|^2.
```

Those formulas are not #157 theorem authority.

## Post-#155 exact falsification remains active

The exact `K=2` boundary-flat vectors

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

show that the relevant ninth/seventh source derivatives change sign on the physical source-coordinate interval.

Therefore

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

is a dead universal route.

This does not refute the #155/#157 Riesz identities. A generic integrated boundary recurrence is not a revival of the dead pointwise-sign shortcut.

## #152 interval-certification harness

The historical `post150_*` tooling names remain unchanged. The harness is scoped falsification/certification infrastructure, not theorem authority.

After #157 the transformed observable is theorem-backed, so the harness may now be retargeted to **specific exact mechanisms** aligned with `canonicalRieszSourceChannelEnergy`.

Do not merely rescan for negative total energy: #157 already proves retained transformed negativity under the hypothetical off-line-zero route.

Reuse the production backends:

```text
canonical_source_numeric.py
canonical_source_arb.py
```

and their fixed-cell / Arb helpers rather than creating a parallel normalization.

## Highest-leverage next theorem order

```text
FB-01  retained full first-bad certificate                         PROVED / #153
FB-02  exact finite pole-prime discrepancy                         PROVED / #153
FB-03A finite discrepancy integrability                            PROVED / #155
FB-03B anchored primitives + AC / a.e. derivative                 PROVED / #155
FB-03C generic repeated IBP / conditional Riesz                    PROVED / #155
FB-03D source oddness + all even jets + even M3=0                  PROVED / #155
FB-03E complex D-transport + production odd jets + Riesz 6/8      PROVED / #157
FB-03F retained transformed-negative wrapper                       PROVED / #157
FB-04  transformed arithmetic-mechanism falsification              OPEN / NEXT
FB-05  scoped complete-residual nonnegative sign                   OPEN
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  outside-strip/trivial-zero seam + Mathlib RH wrapper         OPEN
```

## Permanent normalization / claim firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix` under the repaired source convention;
- legacy `finiteMatrix` cannot supply absolute sign automatically;
- theorem authority is through #157;
- compiler theorem authority beyond machine-promoted claim IDs is not automatic claim promotion;
- retained transformed negative energy is not itself a contradiction;
- exact discrepancy / Riesz identities are not arithmetic sign theorems;
- R8 retained negativity is conditional on even parity;
- exact seventh/ninth leading-jet formulas remain open;
- pointwise smoothed-integrand positivity remains falsified as a universal mechanism;
- no inverse is load-bearing before regularity; prefer unique preimage;
- no division by unproved transfer factors;
- `D` is algebraic, not unitary/isometric;
- interval-certified finite numerics are scoped falsification evidence, not Lean theorem authority;
- terminal negative-root exclusion still needs the explicit outside-strip/trivial-zero bridge to Mathlib `RiemannHypothesis`;
- RH remains OPEN.

Detailed current implications:
`../../RESEARCH_LEADS_POST_157_PRODUCTION_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**
