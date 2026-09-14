# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

Live GitHub head + exact compiler/CI are authoritative dynamically.

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS

LATEST RESEARCH-EVIDENCE ANCHOR
merged research PR = #174
validated research head = 2d9fc5a5f7d552afb893c871fe84c9ed61a60ac0
merged research commit = 946788f09c871de5133e2a8c8f5c94d7d69b521d
research tree = 2a22b83c4d5903158c036d38420d9ae79b7726f2
RHRC #1070 = SUCCESS
Permansson #843 = SUCCESS

CONTROL SEMANTIC AUTHORITY
PR #117 merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
selected first break = E4A4-SCHUR-FB-05
RH = OPEN
```

## Recent theorem packages

```text
#129 source-explicit cubic defect + cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport
#136 absolute canonical source energy + exact channel decomposition
#137 exact source pairing + one-step determinant
#140-#150 regular-aperture / retained selected first bad
#153 retained first-bad negative-energy certificate + exact discrepancy
#155 legal generic Riesz smoothing + source oddness/even jets
#157 complex production D transport + exact complete Riesz 6/even 8 + retained negativity
#159 general moment-prefix odd jets + exact signed Riesz boundary recurrence
#161 same-state shifted Riesz x cross-parity source obstruction
#163 mixed quadratic-normal source jet x retained Riesz boundary coupling
```

No theorem-bearing PR has superseded #163.

## Research packages since theorem authority

```text
#165 exact executable Riesz-8 endpoint-scalar audit
#166 theorem-aligned shifted-state discriminator
#167 Q16 near-critical cell / interval-method audit
#168 log17 boundary-flat threshold-jet / Q17 microscope
#170 theorem-aligned Schur visibility / background-drift audit
#172 threshold-to-threshold Schur barrier falsification
#174 q13/N2/K3/even exact 2x2 scalar-barrier / interval-method audit
```

### What #174 changed

The q13 scalar reduction proposed after #172 is now consumed research infrastructure.

For `N=2 -> K*=3`, exact theorem-aligned executable geometry gives

```text
H(L) = [[a,b],[b,d]]
H1 <-> a > 0
Delta_2 = a*d - b^2
P = Delta_2/a in H1.
```

The direct 384-bit adaptive scalar interval audit respects physical Q=13/14/15 subcells but certifies no positive, bad, H1-loss, or contact interval. Each physical cell remains 100% `UNRESOLVED`.

Therefore the project should no longer ask whether scalarization itself cures the #167 dependency problem. It does not.

## Current frontier

```text
FB-01 retained certificate                                      PROVED / #153
FB-02 exact discrepancy                                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                  PROVED / #155
FB-03E-F complex transport / retained transformed negativity    PROVED / #157
FB-04A moment jets + signed Riesz boundary recurrence           PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source           PROVED / #161
FB-04C mixed quadratic-normal jet x Riesz boundary coupling     PROVED / #163
FB-05 independent contradiction-producing arithmetic restriction OPEN / NOW
  current research slice: dependency-reduced analytic q13 scalar enclosure
FB-06 negative-root exclusion                                   OPEN
FB-07 terminal Mathlib RH seam                                  OPEN
RH                                                               OPEN
```

## Current post-green clue

The method bottleneck has moved from finite geometry to analytic enclosure.

The leading research hypothesis is to reuse the fixed-unit aperture representation already developed in the #148 theorem layer. A fixed-domain pullback can remove repeated `L` dependence from the oscillatory phase and may produce materially tighter interval enclosures for `a(L)` and `Delta_2(L)`.

The first acceptance gate is not a sign theorem. It is:

```text
new evaluator agrees with existing production evaluator
AND
new evaluator materially tightens the dangerous Q14 enclosures.
```

If that succeeds, derivative/variation bounds, local Taylor models, and interval Newton/Krawczyk become justified next tools.

## Important non-revivals

This is **not**:

```text
global aperture Loewner monotonicity
global minimizing-Schur monotonicity
more brute subdivision of the full matrix
more brute subdivision of the same direct scalar formulas
endpoint-scalar positivity as a standalone contradiction
prime-sample -> local-jet implication by analogy
summing independent channel Schur pivots
universal positive arithmetic threshold replenishment
```

## New method firewalls

- scalarization alone does not eliminate canonical interval dependency;
- determinant and Schur-pivot minima are different optimization targets;
- a zero-containing interval is not a zero/contact theorem;
- more precision/depth alone is not a new route after #174;
- any new enclosure representation must first be benchmarked against the existing production evaluator;
- q13 whole-cell positivity, if eventually certified, remains a finite method/structure result until its controlling arithmetic mechanism generalizes.

## Next theorem-bearing slice

Do not theoremize a q13 finite-cell observation merely because a better enclosure succeeds. First identify the independent arithmetic reason behind any certified behavior and test it outside the one finite q13 state. The next Lean theorem should be the weakest generalizable restriction that genuinely adds information beyond successor positivity.

## Permanent firewalls

- research evidence through #174 does not move theorem authority beyond #163;
- endpoint-scalar positivity alone is not first-bad exclusion;
- arithmetic entry lift is sign-indefinite in tested canonical states;
- physical H1 does not imply q-removed-background H1;
- q13 whole-cell positivity alone would not close FB-05;
- large channel cancellation makes coarse component-sign reasoning unsafe;
- finite differences/quadrature are not derivative theorems;
- exact executable algebra is not a Lean theorem;
- finite Arb evidence is scoped only to its certified points/intervals;
- sourceMoment nonzero does not imply `M4` nonzero, nor conversely;
- simultaneous parity badness remains open;
- selected parity is not even WLOG;
- `UNRESOLVED` is not sign evidence;
- negative-root exclusion and RH remain open.

Detailed current synthesis:
`research/RHRC/RESEARCH_LEADS_POST_174_Q13_SCALAR_DEPENDENCY_FRONTIER_DELTA.md`.

**RH remains OPEN.**
