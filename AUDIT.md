# RHRC formal audit — theorem authority through PR #163; FB-05 arithmetic frontier

> **RH remains OPEN.**

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

Live GitHub head + exact compiler/CI evidence outrank this prose. The validated #163 head and merged main are distinct commits sharing the theorem tree above.

## Exact validation evidence

At `b418ff034428f92594bab0e5b8276181a086ee4b`, RHRC #1039 and Permansson #812 completed successfully. The theorem-bearing closure includes aggregate CCM and ExceptionalZero builds, R003 normalization/source checks, Control-v2/regression tests and the forbidden-placeholder/project-axiom gate.

## Relevant theorem progression

### #153

Retained whole-cell regular first-bad ancestry and negative canonical source energy; exact finite pole-prime discrepancy/full-channel normal form.

### #155

Finite discrepancy integrability; anchored Riesz primitives; AC/a.e. derivative seam; legal arbitrary-order conditional integration by parts; source oddness and all even endpoint jets.

### #157

Genuine complex production D transport; boundary-flat jets through 6; even jets through 8; exact complete Riesz 6/even 8; retained transformed negativity; off-line-zero -> retained Riesz-6 negative certificate.

### #159

General moment-prefix odd-jet law, exact seventh/even-ninth self-energy leading-moment formulas, generic signed Riesz boundary recurrence and retained R6->R7 / even R8->R9 exact moment-square boundary decompositions.

### #161

Same-state shifted negative secular trial; strict even R8 negativity; exact R9/M4 boundary inequality; cross-parity `Gamma * explicitCanonicalSourceMoment` identity; odd-good source-moment nonvanishing; odd-bad OR source-moment-nonzero fork.

### #163 — generic mixed-source package

**PROVED:**

```text
iteratedDeriv_seven_quadraticNormalSourceAtom_eq_moment_four
explicitCanonicalSourceMoment_eq_quadraticNormalSourceAtom_sum
normSq_iteratedDeriv_seven_quadraticNormalSourceAtom
two_pi_four_mul_rieszBoundaryEight_eq_endpointScalar_mul_mixedJetNormSq
two_pi_four_mul_rieszEight_sub_nine_eq_endpointScalar_mul_mixedJetNormSq
```

Therefore, for even boundary-flat `v` with `K>=1`, Lean proves

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v)
|h_v^(7)(0)|^2 = 4*(2*pi)^12*|M4(v)|^2
2*(2*pi)^4*(R8(v)-R9(v)) = S8(L)*|h_v^(7)(0)|^2.
```

The source-moment decomposition also theoremizes that the finite-prime term samples the same `quadraticNormalSourceAtom` at the production prime-source coordinates.

### #163 — retained same-state mixed/Riesz specialization

**PROVED:**

```text
RegularCellMinimalNegativeEnergyCertificate.evenShiftedMixedSourceSeventhJet_eq_momentFour
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNine_eq_mixedJetBoundary
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_mixedJetBoundary
RegularCellMinimalNegativeEnergyCertificate.crossParityGamma_ne_zero_of_even_of_not_oddBad
```

The strict retained R9 upper bound does not assume any sign for the endpoint scalar.

## What #163 does not prove

No current Lean theorem establishes:

```text
explicitCanonicalSourceMoment != 0 -> M4 != 0
M4 != 0 -> explicitCanonicalSourceMoment != 0
finite production samples determine h^(7)(0)
canonicalPolePrimeRieszEndpointScalar L 8 >= 0
canonicalPolePrimeRieszEndpointScalar L 8 != 0
simultaneous even+odd bad exclusion
odd-selected first-bad branch reduction/closure
independent contradiction-producing arithmetic restriction
negative-root exclusion
terminal RiemannHypothesis
```

The exact shared observable is an interface, not yet a global sampling/interpolation theorem.

## Post-green frontier

The same retained even shifted negative state now satisfies

```text
R8(u_lambda) < 0
F_odd(lambda) = Gamma(lambda)*explicitCanonicalSourceMoment(u_lambda)
h^(7)(0) = -2*(2*pi)^6*M4(u_lambda)
2*(2*pi)^4*(R8(u_lambda)-R9(u_lambda)) = S8(L)*|h^(7)(0)|^2
```

and, in the even-selected branch,

```text
2*(2*pi)^4*R9(u_lambda) < -S8(L)*|h^(7)(0)|^2.
```

The highest-information next work is FB-05: falsify candidate arithmetic restrictions before theorem investment, especially endpoint-scalar sign/nonvanishing and canonical sample-to-jet rigidity.

## Exact route falsification still active

The K=2 boundary-flat fixtures continue to refute universal pointwise fixed-sign smoothed-integrand positivity. This does not refute the exact integrated Riesz recurrence, #161 same-state source composition, or #163 mixed-jet/Riesz coupling.

## Current execution order

```text
FB-01  retained first-bad certificate                              PROVED / #153
FB-02  exact pole-prime discrepancy                                PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex transport / retained transformed negativity       PROVED / #157
FB-04A moment jets + signed Riesz boundary recurrence               PROVED / #159
FB-04B shifted Riesz x cross-parity source composition             PROVED / #161
FB-04C mixed quadratic-normal jet x Riesz boundary coupling        PROVED / #163
FB-05  independent contradiction-producing arithmetic restriction OPEN / NEXT
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  terminal seam                                               OPEN
```

## Permanent firewalls

- compiler/CI validity is authoritative;
- theorem authority through #163 and machine claim promotion are separate;
- complete retained/shifted transformed negativity is not a contradiction;
- exact discrepancy/Riesz identities are not arithmetic sign theorems;
- no division by transfer factors without nonzeroness;
- `D` algebraic != `D` unitary/isometric;
- #159 self-energy moment jets and #163 mixed source-pairing jets are distinct theorem surfaces;
- nonzero explicit source moment !=> nonzero M4;
- nonzero M4 !=> nonzero explicit source moment;
- finite samples != local derivative determination without a theorem;
- endpoint-scalar sign/nonvanishing remains open;
- simultaneous even/odd badness remains open;
- selected parity cannot be assumed even WLOG;
- pointwise smoothed-integrand positivity remains dead as a universal route;
- interval-certified finite numerics are falsification evidence, not Lean authority;
- negative-root exclusion != terminal Mathlib RH without final seam;
- RH remains OPEN.

Newest research implications:
`research/RHRC/RESEARCH_LEADS_POST_163_MIXED_SOURCE_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**
