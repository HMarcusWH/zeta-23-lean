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
merged research PR = #178
validated research head = 28df43faed0db8c0f12a25525df6c28467ce5b07
merged research commit = fb2a181ce0d95d90396ead7730e7bf365616a153
research tree = 96ab14953e9e8bff5245953082db8a6471648614
RHRC #1074 = SUCCESS
Permansson #847 = SUCCESS

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
#178 complete fixed-unit derivative implementation + Q14 derivative discrimination
```

### What #174 changed

The q13 scalar reduction proposed after #172 is consumed research infrastructure. For `N=2 -> K*=3`, exact theorem-aligned executable geometry gives

```text
H(L) = [[a,b],[b,d]]
H1 <-> a > 0
Delta_2 = a*d - b^2
P = Delta_2/a in H1.
```

The direct 384-bit adaptive scalar interval audit respects physical Q=13/14/15 subcells but certifies no positive, bad, H1-loss, or contact interval. Each physical cell remains 100% `UNRESOLVED`.

Therefore scalarization itself does not cure the #167 dependency problem.

### What #176 changed

The fixed-unit escape proposed after #174 was implemented as an independent Arb evaluator and compared against the direct `[0,L]` production path. Every primary Q14 benchmark box reports both `delta_strictly_narrower = true` and `delta_material_gain = true` under the predeclared factor-2 criterion, so the pipeline classifies

```text
FIXED_UNIT_METHOD_ACCEPTED
```

This selects a preferred **research enclosure representation for the q13 finite laboratory**. It does not prove a determinant sign, stationary point, whole-cell barrier, arbitrary first-bad restriction, or Lean theorem.

### What #178 changed

The complete fixed-Q canonical derivative

```text
M'(L)=pole'(L)-arch'(L)-prime'(L)
```

is now implemented and independently checked through primitive, complete 7x7 matrix, theorem-aligned scalar and odd-N2 ancestry layers. The exact derivative observable is

```text
Delta_2' = a'd + ad' - 2bb'.
```

The frozen six-box Q14 certifier returns

```text
DERIVATIVE_UNRESOLVED
NO_CERTIFIED_PRIMARY_DERIVATIVE_SIGN
```

with no certified left/right derivative sign, no derived stationary existence, no bad interval and no H1-loss interval.

This does **not** mean `Delta_2'=0`. It means the raw assembled derivative interval representation remains dependency-limited on the frozen boxes.

#178 also closes the #176 replay-hardening debt: supplied benchmark schedules are now rebound to their frozen fixture and malformed schedules are rejected.

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
  current research slice: correlation-preserving Q14 derivative enclosure
FB-06 negative-root exclusion                                   OPEN
FB-07 terminal Mathlib RH seam                                  OPEN
RH                                                               OPEN
```

## Current post-green clue

The method bottleneck has moved again. #176 improved value-level determinant intervals, while #178 shows that direct interval evaluation of the differentiated assembled determinant still certifies no primary sign.

The next question is therefore **where the derivative dependency enters**.

Highest-information order:

```text
1. rigorous point Delta_2' balls at all frozen primary/control centers
2. compare exact representations
     raw: Delta_2' = a'd + ad' - 2bb'
     H1:  Delta_2' = a'P + aP'
3. if point orientation is visible, add Delta_2'' and centered mean-value/Taylor bounds
4. only after a two-sided derivative bracket, attempt interval Newton/Krawczyk.
```

The determinant and pivot minima remain distinct optimization targets. The Schur-factorized expression is only an alternative enclosure representation of the determinant derivative, not a revival of global minimizing-Schur monotonicity.

## Important non-revivals

This is **not**:

```text
global aperture Loewner monotonicity
global minimizing-Schur monotonicity
more brute subdivision of the full matrix
more brute subdivision of the same direct scalar formulas
more brute subdivision of the same raw assembled Delta_2' formula
endpoint-scalar positivity as a standalone contradiction
prime-sample -> local-jet implication by analogy
summing independent channel Schur pivots
universal positive arithmetic threshold replenishment
```

## New method firewalls

- scalarization alone does not eliminate canonical interval dependency;
- #176 fixed-unit method acceptance is finite and benchmark-scoped, not a sign theorem;
- #178 validates the derivative implementation but returns `DERIVATIVE_UNRESOLVED` on all six primary side boxes;
- `DERIVATIVE_UNRESOLVED` is not zero/stationary evidence;
- determinant and Schur-pivot minima are different optimization targets;
- a zero-containing interval is not a zero/contact theorem;
- more precision/depth alone is not a new route after #174/#178;
- the direct production evaluator remains an independent baseline;
- the #176 standalone replay-hardening debt is closed by #178;
- q13 whole-cell positivity, if eventually certified, remains a finite method/structure result until its controlling arithmetic mechanism generalizes.

## Next theorem-bearing slice

Do not theoremize a q13 finite-cell observation merely because a better enclosure succeeds. First identify the independent arithmetic reason behind any certified behavior and test it outside the one finite q13 state. The next Lean theorem should be the weakest generalizable restriction that genuinely adds information beyond successor positivity.

## Permanent firewalls

- research evidence through #178 does not move theorem authority beyond #163;
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
`research/RHRC/RESEARCH_LEADS_POST_178_DERIVATIVE_UNRESOLVED_CENTERED_ENCLOSURE_DELTA.md`.

**RH remains OPEN.**