# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

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

Live GitHub head + exact Lean/compiler/CI remain authoritative. The validated #161 head and merged `main` are distinct commits with the same theorem tree.

## One-screen frontier

```text
DONE THROUGH #153
  off-line zero -> retained regular cell-minimal first-bad certificate
  exact negative canonical source-channel energy on that retained state
  exact finite pole-prime discrepancy and full-channel normal form

DONE / #155
  finite discrepancy integrability
  anchored Riesz primitives + AC / a.e. derivative seam
  legal arbitrary-order conditional Riesz smoothing
  source-coordinate oddness + all even endpoint jets
  even parity -> M3 = 0

DONE / #157
  genuine complex production D transport
  boundary-flat jets 1..6 / even jets 1..8
  exact complete production Riesz 6 / even Riesz 8
  retained complete Riesz negativity
  off-line zero -> retained complete Riesz-6 negative certificate

DONE / #159 — FB-04A
  exact first source-energy jet
  general moment-prefix odd-jet theorem
  exact seventh derivative = -2*(2*pi)^6*|M3|^2
  exact even ninth derivative = 2*(2*pi)^8*|M4|^2
  generic signed pole-prime / complete-channel Riesz boundary recurrence
  retained R6->R7 M3^2 and even R8->R9 M4^2 decompositions

DONE / #161 — FB-04B
  negative eigenmode -> ParityBad
  predecessor nonnegativity available for either parity from first-bad ancestry
  genuine shifted negative secular trial has exact negative canonical/source energy
  same even shifted trial has R8 < 0
  same even shifted trial has exact R9/M4 boundary inequality
  odd-good -> odd secular scalar != 0
  retained even root: odd scalar = Gamma * explicitCanonicalSourceMoment on same trial
  odd-good -> explicitCanonicalSourceMoment != 0
  headline fork: odd successor bad OR explicit source moment != 0

NOW — FB-04C MIXED SOURCE / M4 RIGIDITY
  theoremize the exact quadratic-normal mixed source observable
  verify the expected seventh jet proportional to M4
  specialize it to the retained even shifted trial
  test whether the linear source observable and quadratic Riesz M4^2 boundary impose a new canonical-state restriction
  preserve exact pole/prime/archimedean cancellation
  falsify stronger coupling/sign claims before theorem investment

PARALLEL FALSIFICATION
  test whether simultaneous even+odd badness is generic in abstract rank-one parity models
  test whether sourceMoment != 0 and M4 != 0 can be separated on canonical shifted states
  keep odd-selected first-bad branch as an explicit coverage gap

DECISIVE OPEN TARGET
  independent contradiction-producing canonical arithmetic restriction on the exact forced state
  -> same-state contradiction
  -> negative-root exclusion
  -> outside-strip/trivial-zero seam
  -> Mathlib RiemannHypothesis wrapper
```

## Exact #161 theorem package

### Spectral / first-bad interfaces — PROVED

```text
parityBad_of_negative_eigenmode
RegularCellMinimalFirstBadCertificate.predecessorNonnegative_anyParity
```

These close the converse negative-eigenmode interface and expose both-parity predecessor nonnegativity without requiring simultaneous zero-shift regularity.

### Shifted secular-root Riesz layer — PROVED

```text
parityCanonicalSourceEnergy_cubicSecularTrialVector_eq_lam_normSq_of_root
parityCanonicalSourceEnergy_cubicSecularTrialVector_neg_of_root
canonicalSourceChannelEnergy_cubicSecularTrialVector_neg_of_root
canonicalRieszSourceChannelEnergy_eight_neg_of_even_secular_root
canonicalRieszSourceChannelEnergy_nine_lt_neg_momentFourBoundary_of_even_secular_root
cubicSecularScalar_ne_zero_of_not_parityBad
```

The R8/R9 statements are even-sector statements on the actual shifted secular-root trial. No sign of the endpoint scalar is asserted.

### Retained same-state composition — PROVED

```text
RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial
RegularCellMinimalNegativeEnergyCertificate.evenSecularRoot_of_even
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNeg
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_momentFourBoundary
RegularCellMinimalNegativeEnergyCertificate.oddSecularScalar_eq_gamma_mul_explicitSource_of_even
RegularCellMinimalNegativeEnergyCertificate.explicitSourceMoment_ne_zero_of_even_of_not_oddBad
RegularCellMinimalNegativeEnergyCertificate.oddBad_or_explicitSourceMoment_ne_zero_of_even
```

The zero-shift retained trial is not identified with the shifted secular trial. The composition is genuinely same-state only after reconstructing the retained explicit root as the canonical even secular root through an eigenmode bridge.

## Derived consequences worth theoremizing only if useful

Under the even-selected + odd-good branch:

```text
odd secular scalar != 0
odd secular scalar = Gamma * explicitCanonicalSourceMoment
```

so directly:

```text
Gamma != 0
AND
explicitCanonicalSourceMoment != 0.
```

This requires no division. It is DERIVED, not yet a separate Lean theorem.

## FB-04C target

Conceptually define the mixed observable

```text
h_v(omega)
  = <centeredQuadraticNormal, sourceMatrix(omega) v>
      / <centeredQuadraticNormal, centeredQuadraticNormal>.
```

Expected target for even boundary-flat `v`:

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v).
```

Then #159 gives the quadratic boundary term

```text
B8(v) = 2*(2*pi)^8*S8(L)*|M4(v)|^2,
```

so formally one expects

```text
B8(v) = S8(L)/(2*(2*pi)^4) * |h_v^(7)(0)|^2.
```

The mixed-jet formula and this boundary rewrite remain OPEN IN LEAN.

## Falsification requirements

Before promoting a stronger arithmetic mechanism, attack it with:

- small canonical sizes and both parity sectors;
- exact/Arb reconstruction using existing R003 backends;
- source-moment zero / near-zero cases;
- M4 zero / near-zero cases;
- examples with sourceMoment != 0 but M4 = 0 and conversely when available;
- simultaneous both-parity badness;
- scaling and normalization checks;
- modified-source controls when the proposed mechanism looks too structural.

## Dead route remains dead

Exact boundary-flat `K=2` fixtures still refute

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand.
```

#159/#161 integrated boundary and same-state identities do not revive that pointwise claim.

## Semantic work packages

```text
FB-01  retained full first-bad certificate                         PROVED / #153
FB-02  exact finite pole-prime discrepancy                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex production transport / retained Riesz negativity  PROVED / #157
FB-04A exact moment jets + signed Riesz boundary recurrence         PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source composition  PROVED / #161
FB-04C mixed source-pairing jet -> M4 rigidity bridge              DERIVED / OPEN
FB-05  independent contradiction-producing arithmetic restriction  OPEN
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  terminal zeta/Mathlib seam                                  OPEN
```

PR numbers are execution history, not mathematical dependencies.

## Permanent firewalls

1. A retained transformed negative certificate is not a contradiction.
2. Exact discrepancy/Riesz identities are not arithmetic positivity.
3. R8/R9 retained/shifted statements are conditional on even parity.
4. The #159 self-energy seventh/ninth jet formulas are not the mixed source-pairing seventh-jet theorem.
5. `explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely, without a theorem.
6. Simultaneous even/odd badness remains possible until excluded.
7. The selected first-bad parity cannot be assumed even WLOG; D is not unitary/isometric.
8. Riesz smoothing is not a pointwise sign theorem.
9. Pointwise fixed-sign smoothed-integrand positivity remains falsified.
10. No division by alpha/Gamma/overlap/source moment without a theorem.
11. Interval-certified numerics are not Lean theorem authority.
12. Machine claim promotion remains separate from compiler theorem validity.
13. Negative-root exclusion is not the terminal Mathlib RH statement without the final seam.

Newest research delta:

`RESEARCH_LEADS_POST_161_SAME_STATE_RIESZ_SOURCE_RIGIDITY_DELTA.md`

**RH remains OPEN.**
