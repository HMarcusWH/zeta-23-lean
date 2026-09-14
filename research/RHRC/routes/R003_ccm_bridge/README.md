# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #163. LATEST RESEARCH EVIDENCE THROUGH PR #176. CURRENT FRONTIER = FB-05 FIXED-UNIT Q14 DERIVATIVE/STATIONARY DISCRIMINATION. RH OPEN.**

## Authority split

Live GitHub head + exact compiler/CI remain authoritative dynamically.

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

CONTROL AUTHORITY
control-plane semantic anchor = PR #117
selected formal first break = E4A4-SCHUR-FB-05
RH = OPEN
```

## Closed theorem ladder

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
same-state shifted Riesz x cross-parity source composition       PROVED / #161
odd-good -> exact production source moment nonzero                PROVED / #161
odd-bad OR explicit-source-nonzero retained fork                 PROVED / #161
mixed quadratic-normal source seventh jet -> M4                  PROVED / #163
finite-prime sampling of the same mixed source observable        PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling              PROVED / #163
retained even-shifted mixed-jet/Riesz specialization             PROVED / #163
```

## Exact #163 retained state

For the retained even-selected branch, one exact shifted negative state carries:

```text
R8(u_lambda) < 0
F_odd(lambda) = Gamma(lambda)*explicitCanonicalSourceMoment(u_lambda)
odd successor bad OR explicitCanonicalSourceMoment(u_lambda) != 0
h^(7)(0) = -2*(2*pi)^6*M4(u_lambda)
2*(2*pi)^4*(R8(u_lambda)-R9(u_lambda)) = S8(L)*|h^(7)(0)|^2
2*(2*pi)^4*R9(u_lambda) < -S8(L)*|h^(7)(0)|^2
```

No endpoint-scalar sign, sourceMoment/`M4` implication, simultaneous-parity exclusion, selected-even WLOG reduction, or contradiction is theoremized.

## Research evidence after #163

### #165 — endpoint scalar audit

The exact executable `S8(L)` normalization is independently checked, including prime powers through von Mangoldt weights. Finite discovery and Arb fixtures found no sampled negative value.

**Firewall:** even `S8 >= 0` only yields `R9 <= R8 < 0` from the current theorem package. Sign alone is not FB-05 closure.

### #166 — shifted-state discriminator

Finite discovery is aligned with the actual shifted secular ray `u_lambda = c - W(H-lambda G)^(-1)r`. A broad finite scout found no negative successor but isolated a near-critical `Q=16,N=3,K=4,odd` family.

### #167 — Q16 barrier / method falsification

Floating full-cell optimization found no negative point. Direct dependency-heavy whole-cell Arb evaluation remained `256 / 256 UNRESOLVED` at depth 8.

### #168 — threshold moment jet

Exact executable boundary-flat parity identities give odd first surviving source-energy order 7 through `M3^2` and even first surviving order 9 through `M4^2`. The exact `L=log 17` threshold and all 18 two-sided Arb microscope points are positive.

### #170 — theorem-aligned Schur visibility/background split

The selected scalar is reconstructed in the exact `[W|c]` basis. At q17/N3/K4/odd, the threshold direction is finite-certified Schur-visible; the entering q17 atom raises the pivot at checked offsets while the q-removed background finite difference is negative.

### #172 — threshold-to-threshold production barrier

Finite current-q entry lift is sign-indefinite:

```text
q9 / even   NEGATIVE_CERTIFIED
q13 / even  NEGATIVE_CERTIFIED
q16 / odd   POSITIVE_CERTIFIED
```

The strongest near-critical target becomes

```text
q = 13 -> 16
N = 2
K* = 3
parity = even.
```

At the quantized near-minimum, Arb certifies a positive full pivot of about `5.84e-12`, positive background of about `1.22e-11`, and negative q13 entry lift of about `-6.38e-12`.

### #174 — exact q13 2x2 scalar barrier

For the q13 target the exact theorem-aligned executable geometry is 1D predecessor -> 2D successor. In `[W|c]` coordinates,

```text
H(L) = [[a(L), b(L)],
        [b(L), d(L)]]
Delta_2(L) = a(L)d(L)-b(L)^2
H1 <-> a(L)>0
P(L)=Delta_2(L)/a(L) in H1 scope.
```

The floating scout sharpens the dangerous Q14 basin and remains sampled-positive. The determinant minimum and Schur-pivot minimum are nearby but not identical.

The 384-bit direct scalar interval audit over physical Q=13/14/15 subcells returns:

```text
Q=13  100% UNRESOLVED
Q=14  100% UNRESOLVED
Q=15  100% UNRESOLVED
```

No H1-loss, bad interval, contact theorem, or strict-positive interval is certified.

**Consequence:** the scalar geometry is now consumed research infrastructure. Direct adaptive evaluation of the same scalar formulas is itself dependency-limited. The next method must change the enclosure representation or add analytic control rather than merely increase subdivision depth.

### #176 — fixed-unit q13/Q14 enclosure method selection

The fixed-unit pullback is implemented independently while preserving the direct `[0,L]` production evaluator as a baseline. The exact CI pipeline validates primitive, complete `7x7` matrix, theorem-aligned even scalar, odd-N2 ancestry, seam and zero-weight agreement.

The frozen benchmark contains six primary Q14 boxes: three radii around the sampled determinant minimum and three around the sampled pivot minimum. With predeclared material width factor `2.0`, all six report

```text
delta_strictly_narrower = true
delta_material_gain = true
```

and the certifier reports

```text
FIXED_UNIT_METHOD_ACCEPTED
```

**Consequence:** fixed-unit is the preferred research enclosure representation for this finite q13/Q14 laboratory. This is rigorous finite method-selection evidence, not a determinant sign, stationary theorem, whole-cell positivity result, first-bad theorem or Lean promotion.

## Current frontier — fixed-unit Q14 derivative / stationary discrimination

Preserve the exact q13 observables:

```text
a(L)
Delta_2(L)=a(L)d(L)-b(L)^2
odd N=2 predecessor ancestry
```

and test whether the #176 conditioning gain survives differentiation.

Primary research chain:

```text
fixed-unit alpha', beta', gamma'
-> a', b', d'
-> Delta_2' = a'd + ad' - 2bb'.
```

The first acceptance gate is:

```text
analytic fixed-unit derivative evaluator agrees with independent
high-precision centered finite differences at frozen points
AND
rigorous Delta_2' enclosures are narrow enough to distinguish
outer monotone regions from the shallow Q14 stationary basin.
```

Only after this gate should the route invest in certified local Taylor models, interval Newton/Krawczyk, or stationary/minimum/contact isolation.

The final scalar classification remains:

```text
A. H1 loss: a(L) <= 0 somewhere
B. strict bad successor: a(L)>0 and Delta_2(L)<0 somewhere
C. zero/contact: a(L)>0 and Delta_2(L)=0 somewhere
D. strict barrier: a(L)>0 and Delta_2(L)>0 everywhere
```

A zero-containing interval is not a contact theorem. `Delta_2 >= 0` without nonvanishing is not a strict barrier certificate.

## Supporting open routes

### Simultaneous parity badness

#161 still allows both parity successors to be bad. Same-q/N opposite-parity controls remain useful.

### Odd-selected coverage

No WLOG-even theorem exists because `D` is algebraic, not unitary/isometric.

### Endpoint scalar

Global sign/nonvanishing remains open, but #165 reduces its standalone priority because positivity alone is not a contradiction.

### SourceMoment / local jet rigidity

The shared analytic observable is theorem authority after #163, but finite weighted sampling still does not imply the local seventh jet without new structure.

## Current research tooling

The R003 CI layer now includes:

```text
post-#150 selected-residual finite/Arb audit
post-#163 endpoint-scalar audit (#165)
post-#165 theorem-aligned shifted-state audit (#166)
post-#166 Q16 cell-barrier audit (#167)
post-#167 threshold-jet / Q17 audit (#168)
post-#169 Schur visibility/background audit (#170)
post-#171 threshold-to-threshold barrier audit (#172)
post-#173 q13 scalar-barrier plumbing/scout/interval audit (#174)
post-#175 fixed-unit q13 enclosure plumbing (#176)
post-#175 fixed-unit q13 benchmark (#176)
post-#175 fixed-unit agreement/width certification (#176)
```

Relevant #176 assets:

```text
post175_fb05_q13_fixed_unit_enclosure.py
check_post175_fb05_q13_fixed_unit_enclosure_scope.py
probe_post175_fb05_q13_fixed_unit_enclosure_scope.py
certify_post175_fb05_q13_fixed_unit_enclosure_scope.py
fixtures/post175_fb05_q13_fixed_unit_enclosure_v1.json
```

Passing these gates means the executable research checks ran correctly on the exact head. It does not promote their numerical/SymPy/Arb output to Lean theorem authority.

### Replay-hardening debt

The exact #176 workflow generated its benchmark schedule from the frozen fixture immediately before certification. A review identified that the standalone certifier trusts a supplied `PASS` benchmark schedule rather than independently rebinding every schedule-defining field to the fixture. Future validation plumbing should close that replay gap; it does not alter the exact in-pipeline finite result.

## Highest-leverage order

```text
FB-01  retained full first-bad certificate                         PROVED / #153
FB-02  exact finite pole-prime discrepancy                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex transport / retained transformed negativity       PROVED / #157
FB-04A exact moment jets + signed Riesz boundary recurrence        PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source composition PROVED / #161
FB-04C mixed quadratic-normal jet x Riesz boundary coupling       PROVED / #163
FB-05  independent contradiction-producing arithmetic restriction OPEN / ACTIVE
  current research slice: fixed-unit Q14 determinant derivative/stationary discrimination
FB-06  same-state contradiction / negative-root exclusion         OPEN
FB-07  terminal seam + Mathlib RH wrapper                          OPEN
```

## Permanent firewalls

- theorem authority remains through #163;
- research PR green is not theorem authority;
- exact executable algebra is not a Lean theorem;
- finite Arb evidence is scoped only to its certified object;
- absence of sampled badness is not positivity;
- endpoint-scalar positivity alone is not first-bad exclusion;
- current-q arithmetic entry lift is not universally favorable;
- full physical H1 does not imply background H1;
- determinant and pivot minima are distinct optimization targets;
- independent channel pivots may not be added;
- large cancellation demands cancellation-preserving arithmetic;
- whole-cell `UNRESOLVED` is not sign evidence;
- direct scalar subdivision is not the next strategy after #174;
- #176 fixed-unit method acceptance is scoped to the frozen q13/Q14 benchmark;
- sourceMoment nonzero does not imply `M4` nonzero, nor conversely;
- simultaneous parity badness remains open;
- selected parity cannot be assumed even WLOG;
- negative-root exclusion still needs the terminal zeta/Mathlib seam;
- RH remains OPEN.

Detailed current implications:
`../../RESEARCH_LEADS_POST_176_FIXED_UNIT_METHOD_ACCEPTANCE_Q14_STATIONARY_FRONTIER_DELTA.md`.

**RH remains OPEN.**
