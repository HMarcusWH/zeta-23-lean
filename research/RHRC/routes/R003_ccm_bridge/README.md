# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #161. SAME-STATE SHIFTED RIESZ × CROSS-PARITY SOURCE COMPOSITION IS CLOSED; CURRENT FRONTIER = MIXED SOURCE / M4 RIGIDITY. RH OPEN.**

## Current authority split

```text
live main after merged PR #161 = ef29b45de683962122c1e898ed31bf9417757125
live main tree = b080572e87068889a72b4e612f99ddf0bd67f482
latest theorem-bearing PR = #161
validated theorem head = 188407fb02a37de2e380ede3b60e140953b01441
validated theorem tree = b080572e87068889a72b4e612f99ddf0bd67f482
RHRC #1026 = SUCCESS
Permansson #799 = SUCCESS
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
```

## Exact #161 production surface

Validated declarations include:

```text
parityBad_of_negative_eigenmode
RegularCellMinimalFirstBadCertificate.predecessorNonnegative_anyParity
parityCanonicalSourceEnergy_cubicSecularTrialVector_eq_lam_normSq_of_root
parityCanonicalSourceEnergy_cubicSecularTrialVector_neg_of_root
canonicalSourceChannelEnergy_cubicSecularTrialVector_neg_of_root
canonicalRieszSourceChannelEnergy_eight_neg_of_even_secular_root
canonicalRieszSourceChannelEnergy_nine_lt_neg_momentFourBoundary_of_even_secular_root
cubicSecularScalar_ne_zero_of_not_parityBad
RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial
RegularCellMinimalNegativeEnergyCertificate.evenSecularRoot_of_even
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNeg
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_momentFourBoundary
RegularCellMinimalNegativeEnergyCertificate.oddSecularScalar_eq_gamma_mul_explicitSource_of_even
RegularCellMinimalNegativeEnergyCertificate.explicitSourceMoment_ne_zero_of_even_of_not_oddBad
RegularCellMinimalNegativeEnergyCertificate.oddBad_or_explicitSourceMoment_ne_zero_of_even
```

No sign of the endpoint scalar is asserted and no source factor is divided out.

## Same-state state now theorem-backed

For the retained even-selected branch, one canonical shifted negative state now carries:

```text
R8(u_lambda) < 0
R9(u_lambda) < -2*(2*pi)^8*S8(L)*|M4(u_lambda)|^2
F_odd(lambda) = Gamma(lambda)*explicitCanonicalSourceMoment(u_lambda)
```

with

```text
odd successor bad
OR
explicitCanonicalSourceMoment(u_lambda) != 0.
```

This closes FB-04B. It does not close the arithmetic contradiction.

## Current frontier — FB-04C mixed source / M4 rigidity

**Status: DERIVED / OPEN IN LEAN.**

Define the elementary mixed observable

```text
h_v(omega) = <centeredQuadraticNormal, sourceMatrix(omega) v>
             / <centeredQuadraticNormal, centeredQuadraticNormal>.
```

For even boundary-flat `v`, the post-green calculation predicts

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v).
```

If theoremized, this would connect the linear quadratic-normal source jet to the quadratic `|M4|^2` Riesz boundary exposed by #159/#161.

The crucial open question is whether, on the **canonical shifted secular state**, that local mixed jet is constrained by the global arithmetic quantity `explicitCanonicalSourceMoment` in a way generic vectors are not.

Do not infer `M4 != 0` from #161's source-moment nonzeroness, or conversely, without a theorem.

## Falsification discipline

Reuse existing R003 numerical/Arb backends to test the current mechanism across:

- certified fixed cutoff cells;
- prime-power thresholds;
- small sizes and parity sectors;
- source-moment zero/near-zero cases;
- `M4` zero/near-zero cases;
- sourceMoment != 0 with M4 = 0 and conversely where realizable;
- simultaneous both-parity badness;
- endpoint-scalar degeneracies;
- modified-source controls.

Do not merely scan transformed total energy: retained/shifted transformed negativity is already theorem-backed.

## Parallel branch — simultaneous parity badness

#161's left fork allows both even and odd successor sectors to be bad at the same size. Before Lean investment, exact generic/rank-one parity countermodels should test whether this is structurally easy. If so, canonical arithmetic must do additional work there too.

## Odd-selected coverage gap

The #161 retained theorem is conditional on selected parity being even. No WLOG-even reduction exists: `D` remains algebraic, not unitary/isometric.

## Dead shortcut remains dead

Exact boundary-flat K=2 fixtures still refute

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand.
```

#159's integrated signed recurrence and #161's same-state composition are not a revival of this pointwise route.

## Highest-leverage order

```text
FB-01  retained full first-bad certificate                         PROVED / #153
FB-02  exact finite pole-prime discrepancy                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex transport / retained transformed negativity       PROVED / #157
FB-04A exact moment jets + signed Riesz boundary recurrence         PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source composition  PROVED / #161
FB-04C mixed source-pairing jet -> M4 rigidity bridge              DERIVED / OPEN / NEXT
FB-05  independent contradiction-producing arithmetic restriction  OPEN
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  terminal seam + Mathlib RH wrapper                          OPEN
```

## Permanent firewalls

- canonical sign-sensitive object remains `canonicalSourceMatrix`;
- theorem authority is through #161; machine-promoted claim IDs remain a separate, older surface;
- retained/shifted transformed negative energy is not a contradiction;
- exact Riesz identities are not arithmetic sign theorems;
- R8/R9 statements are conditional on even parity where stated;
- no factorwise division without theorem-backed nonzeroness;
- `D` is algebraic, not unitary/isometric;
- the mixed source-pairing jet is not yet theorem authority;
- nonzero explicit source moment does not imply nonzero M4;
- simultaneous even/odd badness remains open;
- interval-certified finite numerics are scoped falsification evidence only;
- negative-root exclusion still needs the outside-strip/trivial-zero seam;
- RH remains OPEN.

Detailed current implications:
`../../RESEARCH_LEADS_POST_161_SAME_STATE_RIESZ_SOURCE_RIGIDITY_DELTA.md`.

**RH remains OPEN.**
