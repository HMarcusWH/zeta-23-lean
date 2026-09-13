# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

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

Live GitHub head + exact Lean/compiler/CI remain authoritative. The validated #159 head and merged `main` are distinct commits with the same theorem tree.

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

DONE / #159 — FB-04A BOUNDARY SUBLEAD CLOSED
  exact first source-energy jet
  general moment-prefix odd-jet theorem
  exact seventh derivative = -2*(2*pi)^6*|M3|^2
  exact even ninth derivative = 2*(2*pi)^8*|M4|^2
  generic signed pole-prime Riesz boundary recurrence
  generic signed complete-channel Riesz boundary recurrence
  retained R6->R7 M3^2 decomposition
  retained even R8->R9 M4^2 decomposition

NOW — FB-04 SAME-STATE ARITHMETIC COMPOSITION
  put the negative secular root, transformed Riesz state and cross-parity source moment on the same canonical shifted trial
  use global first-bad ancestry to expose predecessor nonnegativity for both parities
  derive the even-root fork: opposite parity also bad OR explicit canonical source moment is nonzero
  preserve exact pole/prime/archimedean cancellation
  falsify any stronger sign/rigidity claim before theorem investment

NEXT IF THAT SURVIVES
  theoremize the mixed quadratic-normal source-pairing jet
  expected target on even boundary-flat v:
    h_v^(7)(0) = -2*(2*pi)^6*M4(v)
  connect the linear cross-parity source defect to the quadratic #159 M4^2 Riesz boundary

DECISIVE OPEN TARGET
  independent contradiction-producing canonical arithmetic restriction on the exact forced state
  -> same-state contradiction
  -> negative-root exclusion
  -> outside-strip/trivial-zero seam
  -> Mathlib RiemannHypothesis wrapper
```

## Exact #159 theorem package

### Moment-prefix production jets — PROVED

```text
iteratedDeriv_one_sourceAtomRealEnergy_eq_two_normSq_sum
iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix
iteratedDeriv_seven_sourceAtomRealEnergy_eq_moment_three
iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
```

The general theorem is

```text
M0=...=M(r-1)=0
  -> g^(2r+1)(0) = 2 * (-(2*pi)^2)^r * normSq(Mr).
```

This is production complex source energy, not a real-helper extrapolation.

### Signed Riesz boundary recurrence — PROVED

```text
canonicalPolePrimeRieszEndpointScalar
canonicalPolePrimeRieszBoundaryTerm
canonicalPolePrimeRiesz_integral_step_with_boundary
canonicalPolePrimeRieszEnergy_eq_succ_add_boundary
canonicalRieszSourceChannelEnergy_eq_succ_add_boundary
```

No sign of the endpoint scalar is asserted.

### Retained first-bad boundary decompositions — PROVED

```text
RegularCellMinimalNegativeEnergyCertificate.rieszSix_eq_rieszSeven_sub_momentThree
RegularCellMinimalNegativeEnergyCertificate.rieszSeven_lt_momentThreeBoundary
RegularCellMinimalNegativeEnergyCertificate.rieszEight_eq_rieszNine_add_momentFour_of_even
RegularCellMinimalNegativeEnergyCertificate.rieszNine_lt_neg_momentFourBoundary_of_even
```

R8/R9 remains conditional on retained even parity.

## Post-green composition with existing theorem inventory

The repository already proves at a negative even secular root

```text
odd secular scalar
  = overlap coefficient * evenQuadraticSourceMoment(even shifted trial).
```

It also proves

```text
evenQuadraticSourceMoment
  = explicitCanonicalSourceMoment
  = pole - reduced arch diagonal - reduced arch offdiagonal - finite prime-source sum.
```

And global first-bad minimality already implies predecessor nonnegativity for either parity below the first globally bad size.

These are existing theorem interfaces. What is not yet theorem-packaged is their composition with #159 on the same shifted trial.

## Preferred next theorem-bearing package

1. Prove negative eigenmode -> `ParityBad`, complementing the existing converse.
2. Expose first-bad predecessor nonnegativity for an arbitrary chosen parity.
3. Move exact complete Riesz negativity / #159 boundary recurrence from the retained zero-shift trial onto a genuine negative secular trial.
4. Specialize to retained even first-bad root and the existing cross-parity source transfer.
5. Prove the fail-closed fork

```text
odd successor ParityBad
OR
explicitCanonicalSourceMoment(even negative secular trial) != 0.
```

Do not divide by overlap/Gamma/source moment.

## Falsification requirements

Before promoting a stronger arithmetic mechanism, attack it with:

- small canonical sizes and both parity sectors;
- same fixed cutoff cell and prime-power threshold neighborhoods;
- exact/Arb reconstruction using existing R003 backends;
- source-moment zero / near-zero cases;
- simultaneous both-parity badness;
- scaling and normalization checks;
- modified-source controls when the proposed mechanism looks too structural.

## Dead route remains dead

Exact boundary-flat `K=2` fixtures still refute

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand.
```

#159's integrated boundary recurrence is not a revival of that pointwise claim.

## Semantic work packages

```text
FB-01  retained full first-bad certificate                         PROVED / #153
FB-02  exact finite pole-prime discrepancy                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex production transport / retained Riesz negativity  PROVED / #157
FB-04A exact moment jets + signed Riesz boundary recurrence         PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source composition  OPEN / NEXT
FB-04C mixed source-pairing jet -> M4 bridge                       DERIVED / OPEN
FB-05  independent contradiction-producing arithmetic restriction  OPEN
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  terminal zeta/Mathlib seam                                  OPEN
```

PR numbers are execution history, not mathematical dependencies.

## Permanent firewalls

1. A retained transformed negative certificate is not a contradiction.
2. Exact discrepancy/Riesz identities are not arithmetic positivity.
3. R8/R9 retained statements are conditional on even parity.
4. The #159 seventh/ninth self-energy jet formulas are PROVED; the mixed quadratic-normal source-pairing seventh-jet formula is not.
5. Riesz smoothing is not a pointwise sign theorem.
6. Pointwise fixed-sign smoothed-integrand positivity remains falsified.
7. No division by alpha/Gamma/overlap/source moment without a theorem.
8. `D` remains algebraic, not unitary/isometric.
9. Interval-certified numerics are not Lean theorem authority.
10. Machine claim promotion remains separate from compiler theorem validity.
11. Negative-root exclusion is not the terminal Mathlib RH statement without the final seam.

Newest research delta:

`RESEARCH_LEADS_POST_159_RIESZ_CROSS_PARITY_FRONTIER_DELTA.md`

**RH remains OPEN.**
