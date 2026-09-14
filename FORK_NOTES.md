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
merged research PR = #176
validated research head = c6f53131b91b18aff2a50a6db2ddaa2761e7e5aa
merged research commit = 96cccf715c02ed2bd4ae58f8362180020ae90854
research tree = 28bd302c17a6128e538a3510917dafb670f6dce8
RHRC #1072 = SUCCESS
Permansson #845 = SUCCESS

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
#176 fixed-unit q13/Q14 enclosure agreement + method-selection benchmark
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

### What #176 changed

The fixed-unit escape proposed after #174 was implemented as an independent Arb evaluator and compared against the direct `[0,L]` production path. The exact CI pipeline checks primitive, matrix, scalar, seam and zero-weight agreement, then benchmarks six frozen primary Q14 boxes around the distinct determinant and pivot basins.

Every primary box reports both `delta_strictly_narrower = true` and `delta_material_gain = true` under the predeclared factor-2 criterion, so the pipeline classifies the method as

```text
FIXED_UNIT_METHOD_ACCEPTED
```

This selects a preferred **research enclosure representation for the q13 finite laboratory**. It does not prove a determinant sign, stationary point, whole-cell barrier, arbitrary first-bad restriction, or Lean theorem.

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
  current research slice: fixed-unit Q14 derivative/stationary discrimination
FB-06 negative-root exclusion                                   OPEN
FB-07 terminal Mathlib RH seam                                  OPEN
RH                                                               OPEN
```

## Current post-green clue

The method bottleneck has moved again: #176 shows that the fixed-unit aperture representation materially reduces determinant enclosure width on the frozen q13/Q14 benchmark. The next question is whether that conditioning gain survives **differentiation** strongly enough to decide local Q14 stationary structure.

The first research chain is

```text
alpha', beta', gamma'
        -> a', b', d'
        -> Delta_2' = a'd + ad' - 2bb'.
```

The next gate remains methodological: independently check fixed-unit derivatives against high-precision centered finite differences, then test whether derivative interval widths can separate outer monotone regions from the shallow stationary basin.

Only if that succeeds should local Taylor models, interval Newton/Krawczyk or rigorous minimum/contact isolation be attempted. Do not assume those methods will work merely because the value-level enclosure improved.

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
- #176 fixed-unit method acceptance is finite and benchmark-scoped, not a sign theorem;
- determinant and Schur-pivot minima are different optimization targets;
- a zero-containing interval is not a zero/contact theorem;
- more precision/depth alone is not a new route after #174;
- the direct production evaluator remains an independent baseline rather than being replaced by the fixed-unit evaluator;
- the standalone #176 certifier should eventually bind its supplied benchmark schedule back to the frozen fixture; exact CI generated that benchmark in-pipeline, so this is replay hardening debt rather than a new mathematical claim;
- q13 whole-cell positivity, if eventually certified, remains a finite method/structure result until its controlling arithmetic mechanism generalizes.

## Next theorem-bearing slice

Do not theoremize a q13 finite-cell observation merely because a better enclosure succeeds. First identify the independent arithmetic reason behind any certified behavior and test it outside the one finite q13 state. The next Lean theorem should be the weakest generalizable restriction that genuinely adds information beyond successor positivity.

## Permanent firewalls

- research evidence through #176 does not move theorem authority beyond #163;
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
`research/RHRC/RESEARCH_LEADS_POST_176_FIXED_UNIT_METHOD_ACCEPTANCE_Q14_STATIONARY_FRONTIER_DELTA.md`.

**RH remains OPEN.**
