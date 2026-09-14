# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #163. LATEST RESEARCH EVIDENCE THROUGH PR #168. CURRENT FRONTIER = FB-05 FULL SCALAR PIVOT / BACKGROUND VARIATION. RH OPEN.**

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
merged research PR = #168
validated research head = 9657dad6f1e262b1fa7e08e6944aaa935feeaf33
merged research commit = 4e2c111a836f3fc95f8209485f726dc886c918e7
research tree = 881e1f05302041f56ae4b6a14f14e45d7bbc096b
RHRC #1055 = SUCCESS
Permansson #828 = SUCCESS

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
retained R6->R7 / even R8->R9 moment-square boundaries           PROVED / #159
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

The finite executable is aligned with the actual shifted secular ray:

```text
u_lambda = c - W(H-lambda G)^(-1)r.
```

A broad finite scout found no negative successor but isolated a near-critical `Q=16, N=3, K=4, odd` family.

### #167 — Q16 scalar barrier

Floating full-cell optimization found no negative point and pushed the apparent minimum toward `log 17`.

The direct whole-cell Arb representation remained unresolved at every depth-8 leaf:

```text
256 / 256 UNRESOLVED
```

This is a certification-method failure, not a sign result.

### #168 — threshold moment jet

Exact executable boundary-flat parity identities for `K=2..8` give:

```text
odd  first surviving source-energy order = 7, governed by M3^2
even first surviving source-energy order = 9, governed by M4^2
```

The exact `L=log 17` threshold and all 18 two-sided Arb microscope points are positive. The full Q17 floating state is `CONTINUES_DOWN_BUT_POSITIVE`.

**Consequence:** the isolated entering-prime stabilizer does not control the full canonical aperture drift.

## Current frontier — FB-05 full scalar pivot / background variation

The next research object is a dependency-reduced scalar final Sylvester/Schur pivot.

Near a prime-power threshold, study

```text
P(L) = P_background(L) + P_entering_q(L).
```

The background includes pole, archimedean, scalar-repair and already-active prime-power variation. The entering term begins at high order after boundary-flat/parity annihilation.

Highest-information questions:

1. Can the final pivot be reconstructed independently and by signed channels?
2. What is the background derivative/variation at the threshold?
3. What is the exact pivot sensitivity to the entering rank-one atom?
4. At what source-coordinate scale can the high-order arithmetic kick catch the background drift?
5. Does this create a barrier, a bad successor, or a parity incompatibility before the next meaningful threshold?
6. Does the mechanism persist across sizes, parities and prime powers?

This route must preserve exact cancellation and must not repackage successor positivity.

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
```

Passing these gates means the executable research checks ran correctly on the exact head. It does not promote their numerical/SymPy output to Lean theorem authority.

## Falsification discipline

For the pivot/background route:

- use exact canonical normalization;
- keep von Mangoldt prime powers;
- reconstruct pivot and channel contributions independently;
- test both sides of prime-power thresholds;
- compare high-precision derivatives with Arb pointwise replay;
- test both parity sectors and multiple sizes;
- search for degenerate/weak threshold kicks;
- treat `UNRESOLVED` as unresolved;
- do not revive global Loewner or Schur monotonicity;
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
  current research slice: full scalar pivot/background dynamics
FB-06  same-state contradiction / negative-root exclusion         OPEN
FB-07  terminal seam + Mathlib RH wrapper                          OPEN
```

## Permanent firewalls

- theorem authority remains through #163;
- research PR green is not theorem authority;
- machine-promoted claims remain a separate older surface;
- exact executable algebra is not a Lean theorem;
- interval-certified finite numerics are scoped evidence only;
- absence of sampled badness is not positivity;
- endpoint-scalar positivity alone is not first-bad exclusion;
- threshold prime-entry stabilization is not full-source stabilization;
- retained transformed negativity is not contradiction;
- exact Riesz identities are not arithmetic sign theorems;
- sourceMoment nonzero does not imply `M4` nonzero, nor conversely;
- simultaneous parity badness remains open;
- selected parity cannot be assumed even WLOG;
- no factorwise division without theorem-backed nonzeroness;
- `D` remains algebraic, not unitary/isometric;
- whole-cell `UNRESOLVED` interval output is not sign evidence;
- negative-root exclusion still needs the terminal zeta/Mathlib seam;
- RH remains OPEN.

Detailed current implications:
`../../RESEARCH_LEADS_POST_168_THRESHOLD_JET_BACKGROUND_DRIFT_DELTA.md`.

**RH remains OPEN.**