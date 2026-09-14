# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #163. LATEST RESEARCH EVIDENCE THROUGH PR #170. CURRENT FRONTIER = FB-05 THRESHOLD-TO-THRESHOLD SCHUR BARRIER. RH OPEN.**

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
merged research PR = #170
validated research head = 70689692d5b92252bf9da97740385aaced2bf197
merged research commit = c94242fe41ae62b59aaa392a33e35034eb2c1b1e
research tree = 38e38a1d4cf90afa0e8103e58d1cbae626ebdeef
RHRC #1058 = SUCCESS
Permansson #831 = SUCCESS

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

**Firewall:** even `S8 >= 0` would only yield `R9 <= R8 < 0` from the current theorem package. Sign alone is not FB-05 closure.

### #166 — shifted-state discriminator

The finite executable is aligned with the actual shifted secular ray `u_lambda = c - W(H-lambda G)^(-1)r`. A broad finite scout found no negative successor but isolated a near-critical `Q=16,N=3,K=4,odd` family.

### #167 — Q16 scalar barrier

Floating full-cell optimization found no negative point and pushed the apparent minimum toward `log 17`. The direct whole-cell Arb representation remained unresolved at every depth-8 leaf: `256 / 256 UNRESOLVED`.

### #168 — threshold moment jet

Exact executable boundary-flat parity identities for `K=2..8` give odd first surviving source-energy order 7 through `M3^2` and even first surviving order 9 through `M4^2`. The exact `L=log 17` threshold and all 18 two-sided Arb microscope points are positive. The full Q17 floating state is `CONTINUES_DOWN_BUT_POSITIVE`.

### #170 — theorem-aligned Schur visibility / background split

The selected scalar is reconstructed in the theorem-aligned exact basis `[W|c]`. The unit-shell pivot agrees with the post-#150 selected residual. The exact executable layer checks the rank-one Schur update and directional Schur derivative identities.

For q17/N3/K4/odd:

```text
threshold predecessor H1 positive                         finite-certified
threshold unit-shell pivot                                positive
Schur visibility rho                                      nonzero finite-certified
exact entering-q pivot effect                             positive at 7/7 checked offsets
q-removed background central finite difference            negative at 7/7 tested scales
physical scout through q19                                97/97 H1, 0 sampled negative pivots
```

**Consequence:** the favorable threshold atom is truly visible to the theorem-aligned scalar barrier, but the smooth background can move the complete pivot in the opposite direction. No whole-cell or barrier theorem follows.

## Current frontier — FB-05 threshold-to-threshold Schur barrier

The next research object is not another pivot reconstruction. Use the local Schur-envelope identity

```text
P'(L) = u_L^T M'(L) u_L
```

as a cancellation-preserving diagnostic and study the integrated evolution of the positive H1 pivot from one genuine nonzero von-Mangoldt seam to the next.

Highest-information questions:

1. how much integrated smooth-background loss occurs over one arithmetic interval?
2. which pole/archimedean/active-prime/scalar derivatives produce the near-cancellation?
3. how much positive barrier is replenished by the next entering prime power?
4. can the theorem-aligned pivot reach zero while H1 remains valid?
5. does the answer differ decisively by parity?
6. does the mechanism survive multiple sizes and genuine prime-power thresholds?

This route must preserve exact cancellation and must not repackage successor positivity or global Schur monotonicity.

## Supporting open routes

### Simultaneous parity badness

#161 still allows both parity successors to be bad. Any exclusion must use additional canonical arithmetic; `D` is not unitary/isometric.

### Odd-selected coverage

The strongest retained mixed/Riesz package is even-selected where stated. No WLOG-even theorem exists.

### Endpoint scalar

Global sign/nonvanishing remains open, but #165 reduces its standalone priority because positivity alone is not a contradiction.

### SourceMoment / local jet rigidity

The shared analytic observable is theorem authority after #163, but finite weighted sampling still does not imply the local seventh jet without new structure.

## Current research tooling

The R003 CI layer now includes:

```text
post-#150 selected-residual finite/Arb audit
post-#163 endpoint-scalar audit (#165 research)
post-#165 theorem-aligned shifted-state audit (#166 research)
post-#166 Q16 scalar-barrier audit (#167 research)
post-#167 threshold-jet / Q17 audit (#168 research)
post-#169 theorem-aligned Schur visibility algebra (#170 research)
post-#169 threshold Schur/background scout (#170 research)
post-#169 Arb Schur-visibility replay (#170 research)
```

Passing these gates means the executable research checks ran correctly on the exact head. It does not promote their numerical/SymPy output to Lean theorem authority.

## Falsification discipline

For the threshold-barrier route:

- stay in exact theorem-aligned `[W|c]` geometry;
- require H1 predecessor positivity before first-bad interpretation;
- keep von Mangoldt prime powers;
- use local envelope dynamics without assuming global monotonicity;
- preserve channel cancellation through matrix derivatives / the minimizing trial;
- integrate/certify barrier loss rather than infer it from sparse point signs;
- test both parity sectors and multiple sizes/thresholds;
- search for degenerate/zero visibility and adverse arithmetic kicks;
- distinguish finite differences from derivative theorems;
- treat `UNRESOLVED` as unresolved;
- if an actual bad successor is discovered, replay it through the #166 shifted-state machinery.

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
  current research slice: threshold-to-threshold Schur barrier
FB-06  same-state contradiction / negative-root exclusion         OPEN
FB-07  terminal seam + Mathlib RH wrapper                          OPEN
```

## Permanent firewalls

- theorem authority remains through #163;
- research PR green is not theorem authority;
- machine-promoted claims remain a separate older surface;
- exact executable algebra is not a Lean theorem;
- interval-certified finite numerics are scoped evidence only;
- finite differences are not derivative theorems;
- absence of sampled badness is not positivity;
- endpoint-scalar positivity alone is not first-bad exclusion;
- threshold prime-entry stabilization is not full-source stabilization;
- q17 Schur visibility is not a universal theorem;
- retained transformed negativity is not contradiction;
- sourceMoment nonzero does not imply `M4` nonzero, nor conversely;
- simultaneous parity badness remains open;
- selected parity cannot be assumed even WLOG;
- no factorwise division without theorem-backed nonzeroness;
- `D` remains algebraic, not unitary/isometric;
- independent channel pivots may not be added;
- whole-cell `UNRESOLVED` interval output is not sign evidence;
- negative-root exclusion still needs the terminal zeta/Mathlib seam;
- RH remains OPEN.

Detailed current implications:
`../../RESEARCH_LEADS_POST_170_SCHUR_VISIBILITY_THRESHOLD_BARRIER_DELTA.md`.

**RH remains OPEN.**
