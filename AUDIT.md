# RHRC formal audit — theorem authority through PR #161; mixed-source rigidity frontier

> **RH remains OPEN.**

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

Live GitHub head + exact compiler/CI evidence outrank this prose. The validated #161 head and merged main are distinct commits sharing the theorem tree above.

## Exact validation evidence

At `188407fb02a37de2e380ede3b60e140953b01441`, RHRC #1026 and Permansson #799 completed successfully. The theorem-bearing closure includes aggregate CCM and ExceptionalZero builds, R003 normalization/source checks, Control-v2/regression tests and the forbidden-placeholder/project-axiom gate.

## Relevant theorem progression

### #153

Retained whole-cell regular first-bad ancestry and negative canonical source energy; exact finite pole-prime discrepancy/full-channel normal form.

### #155

Finite discrepancy integrability; anchored Riesz primitives; AC/a.e. derivative seam; legal arbitrary-order conditional integration by parts; source oddness and all even endpoint jets.

### #157

Genuine complex production D transport; boundary-flat jets through 6; even jets through 8; exact complete Riesz 6/even 8; retained transformed negativity; off-line-zero -> retained Riesz-6 negative certificate.

### #159

General moment-prefix odd-jet law, exact seventh/even-ninth self-energy leading-moment formulas, generic signed Riesz boundary recurrence and retained R6->R7 / even R8->R9 exact moment-square boundary decompositions.

### #161 — spectral/ancestry interfaces

**PROVED:**

```text
parityBad_of_negative_eigenmode
RegularCellMinimalFirstBadCertificate.predecessorNonnegative_anyParity
```

### #161 — shifted secular-root Riesz layer

**PROVED:**

```text
parityCanonicalSourceEnergy_cubicSecularTrialVector_eq_lam_normSq_of_root
parityCanonicalSourceEnergy_cubicSecularTrialVector_neg_of_root
canonicalSourceChannelEnergy_cubicSecularTrialVector_neg_of_root
canonicalRieszSourceChannelEnergy_eight_neg_of_even_secular_root
canonicalRieszSourceChannelEnergy_nine_lt_neg_momentFourBoundary_of_even_secular_root
cubicSecularScalar_ne_zero_of_not_parityBad
```

The R8/R9 statements are even-sector statements on the genuine shifted secular-root trial. No endpoint-scalar sign is asserted.

### #161 — retained same-state composition

**PROVED:**

```text
RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial
RegularCellMinimalNegativeEnergyCertificate.evenSecularRoot_of_even
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNeg
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_momentFourBoundary
RegularCellMinimalNegativeEnergyCertificate.oddSecularScalar_eq_gamma_mul_explicitSource_of_even
RegularCellMinimalNegativeEnergyCertificate.explicitSourceMoment_ne_zero_of_even_of_not_oddBad
RegularCellMinimalNegativeEnergyCertificate.oddBad_or_explicitSourceMoment_ne_zero_of_even
```

Thus #161 formally aligns the negative spectral state, the complete Riesz obstruction and the cross-parity arithmetic source obstruction on the **same shifted trial**.

## What #161 does not prove

No current Lean theorem establishes:

```text
mixed quadratic-normal source-pairing seventh jet = constant*M4
explicitCanonicalSourceMoment != 0 -> M4 != 0
M4 != 0 -> explicitCanonicalSourceMoment != 0
simultaneous even+odd bad exclusion
odd-selected first-bad branch reduction/closure
independent contradiction-producing arithmetic restriction
negative-root exclusion
terminal RiemannHypothesis
```

The mixed source-pairing jet must not be inferred from #159's self-energy jet theorem.

## Post-green frontier

The same retained even shifted negative state now satisfies

```text
R8(u_lambda) < 0
R9(u_lambda) < -2*(2*pi)^8*S8(L)*|M4(u_lambda)|^2
F_odd(lambda) = Gamma(lambda)*explicitCanonicalSourceMoment(u_lambda)
```

and

```text
odd successor bad OR explicitCanonicalSourceMoment(u_lambda) != 0.
```

The highest-information next theorem is therefore the mixed quadratic-normal source observable expected to satisfy

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v)
```

on even boundary-flat carriers, followed by a theorem-aligned falsification of any proposed relation between that local jet and the global explicit source moment.

## Derived but not separately theorem-locked

Under even-selected + odd-good, #161 gives a nonzero odd secular scalar equal to `Gamma * explicitCanonicalSourceMoment`; therefore both factors are nonzero. No division is needed.

## Exact route falsification still active

The K=2 boundary-flat fixtures continue to refute universal pointwise fixed-sign smoothed-integrand positivity. This does not refute the exact integrated Riesz recurrence, #161 same-state source composition, or a future mixed source/M4 rigidity theorem.

## Current execution order

```text
FB-01  retained first-bad certificate                              PROVED / #153
FB-02  exact pole-prime discrepancy                                PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex transport / retained transformed negativity       PROVED / #157
FB-04A moment jets + signed Riesz boundary recurrence               PROVED / #159
FB-04B shifted Riesz x cross-parity source composition             PROVED / #161
FB-04C mixed source-pairing jet -> M4 rigidity                     DERIVED / OPEN / NEXT
FB-05  independent contradiction-producing arithmetic restriction OPEN
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  terminal seam                                               OPEN
```

## Permanent firewalls

- compiler/CI validity is authoritative;
- theorem authority through #161 and machine claim promotion are separate;
- complete retained/shifted transformed negativity is not a contradiction;
- exact discrepancy/Riesz identities are not arithmetic sign theorems;
- no division by transfer factors without nonzeroness;
- `D` algebraic != `D` unitary/isometric;
- #159 self-energy moment jets != mixed source-pairing jet;
- nonzero explicit source moment !=> nonzero M4;
- nonzero M4 !=> nonzero explicit source moment;
- simultaneous even/odd badness remains open;
- selected parity cannot be assumed even WLOG;
- pointwise smoothed-integrand positivity remains dead as a universal route;
- interval-certified finite numerics are falsification evidence, not Lean authority;
- negative-root exclusion != terminal Mathlib RH without final seam;
- RH remains OPEN.

Newest research implications:
`research/RHRC/RESEARCH_LEADS_POST_161_SAME_STATE_RIESZ_SOURCE_RIGIDITY_DELTA.md`.

**RH remains OPEN.**
