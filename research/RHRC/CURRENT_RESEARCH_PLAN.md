# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

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

Live GitHub head + exact Lean/compiler/CI remain authoritative. The validated #163 head and merged `main` are distinct commits with the same theorem tree.

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

DONE / #163 — FB-04C
  exact complex mixed source-pairing derivative transport
  exact quadraticNormalSourceAtom normalization
  h_v^(7)(0) = -2*(2*pi)^6*M4(v) on even boundary-flat carriers
  exact mixed seventh-jet norm square = constant*|M4|^2
  explicitCanonicalSourceMoment finite-prime term samples the same quadraticNormalSourceAtom
  exact complete-channel R8-R9 boundary rewrite through |h_v^(7)(0)|^2
  retained even-shifted first-bad specialization
  strict retained R9 upper bound through the mixed jet without endpoint-scalar sign
  crossParityGamma != 0 under even-selected + odd-good

NOW — FB-05 CANONICAL ARITHMETIC RESTRICTION
  find an independently meaningful arithmetic restriction on the exact retained state
  attack endpoint-scalar sign/nonvanishing before assuming it
  test whether canonical prime sampling constrains the local seventh jet
  test simultaneous even+odd badness with theorem-aligned controls
  keep the odd-selected first-bad branch explicit
  preserve exact pole/prime/archimedean cancellation
  reject any route that merely restates successor positivity

DECISIVE OPEN TARGET
  independent contradiction-producing canonical arithmetic restriction
  -> same-state contradiction
  -> negative-root exclusion
  -> outside-strip/trivial-zero seam
  -> Mathlib RiemannHypothesis wrapper
```

## Exact #163 theorem package

### Generic mixed-source calculus — PROVED

```text
quadraticNormalSourceAtom
iteratedDeriv_seven_quadraticNormalSourceAtom_eq_moment_four
explicitCanonicalSourceMoment_eq_quadraticNormalSourceAtom_sum
normSq_iteratedDeriv_seven_quadraticNormalSourceAtom
two_pi_four_mul_rieszBoundaryEight_eq_endpointScalar_mul_mixedJetNormSq
two_pi_four_mul_rieszEight_sub_nine_eq_endpointScalar_mul_mixedJetNormSq
```

For even boundary-flat `v` with `K >= 1`, Lean proves

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v)
|h_v^(7)(0)|^2 = 4*(2*pi)^12*|M4(v)|^2
2*(2*pi)^4*(R8(v)-R9(v)) = S8(L)*|h_v^(7)(0)|^2.
```

The source-moment decomposition theorem also exposes the finite-prime term as a weighted sum of values of this same `quadraticNormalSourceAtom` at the production prime-source coordinates. Pole and archimedean terms remain present.

### Retained same-state specialization — PROVED

```text
RegularCellMinimalNegativeEnergyCertificate.evenShiftedMixedSourceSeventhJet_eq_momentFour
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNine_eq_mixedJetBoundary
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_mixedJetBoundary
RegularCellMinimalNegativeEnergyCertificate.crossParityGamma_ne_zero_of_even_of_not_oddBad
```

In the retained even-selected branch, strict R8 negativity and the exact boundary identity imply

```text
2*(2*pi)^4*R9 < -S8(L)*|h^(7)(0)|^2
```

without assuming a sign for `S8(L)`.

## What #163 does not prove

```text
explicitCanonicalSourceMoment != 0 -> M4 != 0        OPEN
M4 != 0 -> explicitCanonicalSourceMoment != 0        OPEN
finite prime samples determine h^(7)(0)               OPEN
canonicalPolePrimeRieszEndpointScalar L 8 >= 0        OPEN
canonicalPolePrimeRieszEndpointScalar L 8 != 0        OPEN
simultaneous even/odd bad exclusion                    OPEN
odd-selected first-bad branch closure                  OPEN
negative-root exclusion                                OPEN
RiemannHypothesis                                      OPEN
```

The phrase “mixed-source rigidity” must therefore be read narrowly: #163 proves the local mixed-jet/Riesz coupling, not a global sourceMoment<->M4 rigidity theorem.

## FB-05 candidate subroutes

### A. Endpoint-scalar route

Study the exact theorem object

```text
canonicalPolePrimeRieszEndpointScalar L 8
```

with the exact Lean normalization. First falsify global sign/nonvanishing claims numerically and symbolically across cutoff cells and prime-power thresholds. Only formalize a sign theorem if it survives.

### B. Production sample-to-jet route

The finite-prime contribution samples `quadraticNormalSourceAtom` exactly. A generic finite weighted sum of samples does not determine a seventh derivative. Search for extra canonical structure: multiple cutoff cells, exact prime-source coordinates/weights, analyticity, recurrence, interpolation, or a stronger source identity.

### C. Simultaneous parity route

#161 still allows the odd successor to be bad. Test whether simultaneous even+odd badness remains structurally easy after imposing the canonical arithmetic source data. Generic/rank-one countermodels should be used before Lean investment.

### D. Odd-selected coverage

The retained strict R8/R9 package is even-selected where stated. There is no WLOG-even reduction because `D` is algebraic rather than unitary/isometric. Reverse transfer, an odd analogue, or independent exclusion remains open.

## Falsification requirements

Before promoting a stronger arithmetic mechanism, attack it with:

- small canonical sizes and both parity sectors;
- exact/Arb reconstruction using existing R003 backends;
- endpoint-scalar zero/sign-change searches;
- source-moment zero / near-zero cases;
- mixed seventh-jet / `M4` zero or near-zero cases;
- sourceMoment != 0 with mixed jet = 0 and conversely when available;
- simultaneous both-parity badness;
- scaling and normalization checks;
- modified-source controls when the proposed mechanism looks too structural.

## Dead route remains dead

Exact boundary-flat `K=2` fixtures still refute

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand.
```

#159/#161/#163 integrated boundary, same-state and mixed-jet identities do not revive that pointwise claim.

## Semantic work packages

```text
FB-01  retained full first-bad certificate                         PROVED / #153
FB-02  exact finite pole-prime discrepancy                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex production transport / retained Riesz negativity  PROVED / #157
FB-04A exact moment jets + signed Riesz boundary recurrence         PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source composition  PROVED / #161
FB-04C mixed quadratic-normal jet x Riesz boundary coupling        PROVED / #163
FB-05  independent contradiction-producing arithmetic restriction  OPEN / ACTIVE
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  terminal zeta/Mathlib seam                                  OPEN
```

PR numbers are execution history, not mathematical dependencies.

## Permanent firewalls

1. A retained transformed negative certificate is not a contradiction.
2. Exact discrepancy/Riesz identities are not arithmetic positivity.
3. R8/R9 retained/shifted statements are conditional on even parity where stated.
4. The #159 self-energy seventh/ninth jet formulas are not the #163 mixed source-pairing theorem; #163 proved the latter independently.
5. `explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely, without a theorem.
6. Exact finite-prime sampling of a function does not by itself determine its local seventh jet.
7. No endpoint-scalar sign/nonvanishing theorem is currently available.
8. Simultaneous even/odd badness remains possible until excluded.
9. The selected first-bad parity cannot be assumed even WLOG; D is not unitary/isometric.
10. Riesz smoothing is not a pointwise sign theorem.
11. Pointwise fixed-sign smoothed-integrand positivity remains falsified.
12. No division by alpha/Gamma/overlap/source moment without a theorem.
13. Interval-certified numerics are not Lean theorem authority.
14. Machine claim promotion remains separate from compiler theorem validity.
15. Negative-root exclusion is not the terminal Mathlib RH statement without the final seam.

Newest research delta:

`RESEARCH_LEADS_POST_163_MIXED_SOURCE_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`

**RH remains OPEN.**
