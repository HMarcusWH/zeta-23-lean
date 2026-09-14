# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #163. LATEST RESEARCH EVIDENCE THROUGH PR #172. CURRENT FRONTIER = FB-05 Q13/N2/K3/EVEN 2X2 SCALAR DETERMINANT BARRIER. RH OPEN.**

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
merged research PR = #172
validated research head = 4c857cd031497d895232a18a4bfb9a094d9facae
merged research commit = a31bb0bb7f025d7727dd3f224c705af797f64a19
research tree = c64b098c3159d739fa15eeaa96e35693615873d7
RHRC #1063 = SUCCESS
Permansson #836 = SUCCESS

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

Floating full-cell optimization found no negative point and pushed the apparent minimum toward `log 17`. The direct dependency-heavy whole-cell Arb representation remained unresolved at every depth-8 leaf: `256 / 256 UNRESOLVED`.

### #168 — threshold moment jet

Exact executable boundary-flat parity identities for `K=2..8` give odd first surviving source-energy order 7 through `M3^2` and even first surviving order 9 through `M4^2`. The exact `L=log 17` threshold and all 18 two-sided Arb microscope points are positive. The full Q17 floating state is `CONTINUES_DOWN_BUT_POSITIVE`.

### #170 — theorem-aligned Schur visibility / background split

The selected scalar is reconstructed in the theorem-aligned exact basis `[W|c]`. The unit-shell pivot agrees with the post-#150 selected residual. At q17/N3/K4/odd, the threshold direction is finite-certified Schur-visible; the entering q17 atom raises the pivot at checked offsets while the q-removed background finite difference is negative.

### #172 — threshold-to-threshold production barrier

The research layer tests genuine nonzero von-Mangoldt intervals across multiple q/N/parity targets. No sampled bad successor appears, but finite current-q entry lift is sign-indefinite:

```text
q9 / even   NEGATIVE_CERTIFIED
q13 / even  NEGATIVE_CERTIFIED
q16 / odd   POSITIVE_CERTIFIED
```

The most dangerous sampled complete state is

```text
q = 13 -> 16
N = 2
K* = 3
parity = even.
```

At the quantized near-minimum, Arb certifies

```text
H1 predecessor positive
full unit-shell pivot      ~= +5.8401616e-12
q-removed background       ~= +1.2217611e-11
q13 entry lift             ~= -6.3774491e-12
```

The q17 replay also demonstrates that full physical H1 does not imply H1 for the q-removed background. Production channel cancellation ratios reach approximately `1e9`-`1e10`.

**Consequence:** the current object is the complete q13/even scalar barrier, not a universal favorable threshold-kick theorem.

## Current frontier — q13/N2/K3/even 2x2 scalar determinant barrier

For this exact finite target, theorem-aligned executable dimensions are 1 -> 2. In `[W|c]` coordinates,

```text
H(L) = [[a(L), b(L)],
        [b(L), d(L)]]

H1 <-> a(L) > 0
P(L) = d(L) - b(L)^2/a(L)
Delta_2(L) = a(L)d(L) - b(L)^2.
```

Hence in H1 scope

```text
sign P(L) = sign Delta_2(L).
```

The next rigorous task is to decide between

```text
exists L in (log13,log16): a(L)>0 and Delta_2(L)<0
```

and

```text
a(L)>0 and Delta_2(L)>0 for all L in [log13,log16].
```

### Physical cutoff handling

The arithmetic interval 13 -> 16 contains no nonzero von-Mangoldt seams at 14 or 15, but the production backend still tracks physical `Q=floor(exp L)`.

Therefore the rigorous backend should initially certify piecewise on

```text
[log13,log14]
[log14,log15]
[log15,log16]
```

or separately prove exact inertness of the zero-weight Q=14/15 additions in the reduced scalar representation.

This is a dependency-reduced scalar escape from the #167 full-matrix interval failure, not a revival of that failed representation.

A positive q13 whole-cell certificate would still be a finite method/structure result, not global FB-05 closure.

## Supporting open routes

### Simultaneous parity badness

#161 still allows both parity successors to be bad. #172 shows different current-q entry signs in different finite q/N/parity targets, but same-q opposite-parity controls are needed before attributing the effect to parity.

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
post-#171 threshold-barrier accounting check (#172 research)
post-#171 multi-cell threshold-barrier scout (#172 research)
post-#171 Arb finite-point barrier replay (#172 research)
```

Passing these gates means the executable research checks ran correctly on the exact head. It does not promote their numerical/SymPy/Arb output to Lean theorem authority.

## Falsification discipline

For the q13 2x2 route:

- stay in exact theorem-aligned `[W|c]` geometry;
- recheck exact `N=2 -> K*=3` dimensions;
- certify H1 with `a(L)>0` and successor sign with `Delta_2(L)`;
- keep von Mangoldt prime powers;
- respect physical Q=13/14/15 subcells or separately certify zero-weight seam inertness;
- use enough precision for the `~1e-12` residual and `~1e9-1e10` cancellation scale;
- test same-q/N opposite parity;
- search for H1 loss before determinant crossing;
- treat `UNRESOLVED` as unresolved;
- if an actual bad successor is discovered, replay it through the #166 shifted-state machinery;
- if the cell is positive, extract and falsify the generalizable arithmetic inequality before Lean theorem investment.

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
  current research slice: q13/N2/K3/even 2x2 scalar determinant barrier
FB-06  same-state contradiction / negative-root exclusion         OPEN
FB-07  terminal seam + Mathlib RH wrapper                          OPEN
```

## Permanent firewalls

- theorem authority remains through #163;
- research PR green is not theorem authority;
- machine-promoted claims remain a separate older surface;
- exact executable algebra is not a Lean theorem;
- interval-certified finite numerics are scoped evidence only;
- finite differences/quadrature are not derivative theorems;
- absence of sampled badness is not positivity;
- endpoint-scalar positivity alone is not first-bad exclusion;
- current-q arithmetic entry lift is not universally favorable;
- full physical H1 does not imply background H1;
- q13 whole-cell positivity alone would not close FB-05;
- retained transformed negativity is not contradiction;
- sourceMoment nonzero does not imply `M4` nonzero, nor conversely;
- simultaneous parity badness remains open;
- selected parity cannot be assumed even WLOG;
- no factorwise division without theorem-backed nonzeroness;
- `D` remains algebraic, not unitary/isometric;
- independent channel pivots may not be added;
- large cancellation demands cancellation-preserving arithmetic;
- whole-cell `UNRESOLVED` interval output is not sign evidence;
- negative-root exclusion still needs the terminal zeta/Mathlib seam;
- RH remains OPEN.

Detailed current implications:
`../../RESEARCH_LEADS_POST_172_Q13_EVEN_SCALAR_BARRIER_DELTA.md`.

**RH remains OPEN.**
