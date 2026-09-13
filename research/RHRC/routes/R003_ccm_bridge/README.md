# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #163. MIXED QUADRATIC-NORMAL JET × RIESZ COUPLING IS CLOSED; CURRENT FRONTIER = FB-05 CANONICAL ARITHMETIC RESTRICTION. RH OPEN.**

## Current authority split

```text
live main after merged PR #163 = bd3fa1aafa7df2aa35873df532bdb6f17ddd2bbd
live main tree = c397b3a015ea54e38ecfe626d6e29556fe963839
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS
control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

## Closed internal ladder

```text
finite canonical obstruction / Euclidean wall                   PROVED / #94-#98
N-flow + parity + first-bad + Schur/secular                     PROVED / #100-#128
source-explicit cross-parity transfer                            PROVED / #129
exact canonical source-moment decomposition                      PROVED / #131
zero-shift source transport / absolute energy / determinant      PROVED / #134-#137
regular selected first-bad endpoint                              PROVED / #140-#150
retained first-bad + exact pole-prime discrepancy                PROVED / #153
legal generic Riesz smoothing + parity/even jets                 PROVED / #155
complex production D transport + exact Riesz 6/even 8            PROVED / #157
retained transformed negativity + ExceptionalZero R6 wrapper     PROVED / #157
general moment-prefix odd-jet law                                PROVED / #159
exact seventh / even ninth leading-moment self-energy jets        PROVED / #159
generic signed complete-channel Riesz boundary recurrence        PROVED / #159
retained R6->R7 / even R8->R9 moment-square boundaries           PROVED / #159
same-state shifted Riesz x cross-parity source composition       PROVED / #161
odd-good -> exact production source moment nonzero                PROVED / #161
odd-bad OR explicit-source-nonzero retained fork                 PROVED / #161
mixed quadratic-normal source seventh jet -> M4                  PROVED / #163
finite-prime sampling of the same mixed source observable        PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling              PROVED / #163
retained even-shifted mixed-jet/Riesz specialization             PROVED / #163
```

## Exact #163 production surface

Validated declarations include:

```text
iteratedDeriv_seven_quadraticNormalSourceAtom_eq_moment_four
explicitCanonicalSourceMoment_eq_quadraticNormalSourceAtom_sum
normSq_iteratedDeriv_seven_quadraticNormalSourceAtom
two_pi_four_mul_rieszBoundaryEight_eq_endpointScalar_mul_mixedJetNormSq
two_pi_four_mul_rieszEight_sub_nine_eq_endpointScalar_mul_mixedJetNormSq
RegularCellMinimalNegativeEnergyCertificate.evenShiftedMixedSourceSeventhJet_eq_momentFour
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNine_eq_mixedJetBoundary
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_mixedJetBoundary
RegularCellMinimalNegativeEnergyCertificate.crossParityGamma_ne_zero_of_even_of_not_oddBad
```

No sign of the endpoint scalar is asserted. No implication between the global explicit source moment and nonzero `M4` is asserted. The finite-prime source sum samples `quadraticNormalSourceAtom`, but that finite weighted sum is not identified with the seventh jet at zero.

## Same retained state now theorem-backed through #163

For the retained even-selected branch, one canonical shifted negative state now carries all of:

```text
R8(u_lambda) < 0
F_odd(lambda) = Gamma(lambda)*explicitCanonicalSourceMoment(u_lambda)
odd successor bad OR explicitCanonicalSourceMoment(u_lambda) != 0
h^(7)(0) = -2*(2*pi)^6*M4(u_lambda)
2*(2*pi)^4*(R8(u_lambda)-R9(u_lambda)) = S8(L)*|h^(7)(0)|^2
2*(2*pi)^4*R9(u_lambda) < -S8(L)*|h^(7)(0)|^2
```

The strict R9 inequality uses no sign assumption on `S8(L)`.

This closes FB-04C. It does not close the arithmetic contradiction.

## Current frontier — FB-05 canonical arithmetic restriction

**Status: OPEN / ACTIVE.**

The local analytic/Riesz coupling is no longer the missing theorem. The remaining question is whether exact canonical arithmetic supplies an independent restriction incompatible with the retained state.

Highest-information candidate subroutes:

1. **Endpoint scalar.** Analyze the exact production object `canonicalPolePrimeRieszEndpointScalar L 8` for sign, nonvanishing, or a weaker inequality strong enough to constrain the retained recurrence.
2. **Prime-sample / jet rigidity.** The finite-prime part of `explicitCanonicalSourceMoment` samples the same `quadraticNormalSourceAtom`. Test whether the canonical prime coordinates, weights, cutoff-cell structure, or additional source identities constrain its seventh jet in a way a generic finite sample sum does not.
3. **Simultaneous parity badness.** Test whether both parity successors can be bad simultaneously once the exact arithmetic source structure is imposed.
4. **Odd-selected coverage.** Preserve the selected-odd first-bad branch as real coverage debt; there is no WLOG-even theorem.
5. **Other cancellation-preserving invariants.** Search for a canonical restriction that composes with the exact retained state without restating successor positivity.

Do not infer `M4 != 0` from source-moment nonzeroness, or conversely, without a theorem.

## Falsification discipline

Reuse existing R003 numerical/Arb backends to attack candidate FB-05 mechanisms across:

- certified fixed cutoff cells;
- prime-power thresholds;
- small sizes and parity sectors;
- source-moment zero/near-zero cases;
- `M4` / mixed-jet zero or near-zero cases;
- sourceMoment != 0 with mixed jet = 0 and conversely where realizable;
- simultaneous both-parity badness;
- endpoint-scalar zeros/sign changes;
- modified-source controls;
- multiple prime-sample configurations testing whether interpolation-style claims are actually special to the canonical state.

Do not merely rescan the already-proved mixed seventh-jet or Riesz-boundary identities.

## Parallel branch — simultaneous parity badness

#161's left fork still permits both even and odd successor sectors to be bad at the same size. #163 does not close that branch. Before strong Lean investment, exact generic/rank-one parity countermodels and canonical numerical probes should test whether simultaneous badness is structurally easy or arithmetically constrained.

## Odd-selected coverage gap

The retained same-state mixed/Riesz theorem is still conditional on selected parity being even when strict Riesz negativity is used. No WLOG-even reduction exists: `D` remains algebraic, not unitary/isometric.

## Dead shortcut remains dead

Exact boundary-flat K=2 fixtures still refute

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand.
```

#159's integrated signed recurrence, #161's same-state composition, and #163's mixed-jet boundary rewrite are not a revival of this pointwise route.

## Highest-leverage order

```text
FB-01  retained full first-bad certificate                         PROVED / #153
FB-02  exact finite pole-prime discrepancy                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex transport / retained transformed negativity       PROVED / #157
FB-04A exact moment jets + signed Riesz boundary recurrence         PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source composition  PROVED / #161
FB-04C mixed quadratic-normal jet x Riesz boundary coupling        PROVED / #163
FB-05  independent contradiction-producing arithmetic restriction  OPEN / NEXT
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  terminal seam + Mathlib RH wrapper                          OPEN
```

## Permanent firewalls

- canonical sign-sensitive object remains `canonicalSourceMatrix`;
- theorem authority is through #163; machine-promoted claim IDs remain a separate, older surface;
- retained/shifted transformed negative energy is not a contradiction;
- exact Riesz identities are not arithmetic sign theorems;
- R8/R9 statements are conditional on even parity where stated;
- no factorwise division without theorem-backed nonzeroness;
- `D` is algebraic, not unitary/isometric;
- the mixed source-pairing seventh jet is theorem authority after #163, but the global sourceMoment<->M4 relation remains open;
- exact finite-prime sampling does not by itself determine a local jet;
- endpoint-scalar sign/nonvanishing remains open;
- nonzero explicit source moment does not imply nonzero M4;
- simultaneous even/odd badness remains open;
- interval-certified finite numerics are scoped falsification evidence only;
- negative-root exclusion still needs the outside-strip/trivial-zero seam;
- RH remains OPEN.

Detailed current implications:
`../../RESEARCH_LEADS_POST_163_MIXED_SOURCE_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**
