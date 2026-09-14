# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

Live GitHub head + exact Lean/compiler/CI are authoritative dynamically.

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

CONTROL SEMANTIC AUTHORITY
PR #117 merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
selected first break = E4A4-SCHUR-FB-05
RH = OPEN
```

Research PRs after #163 change the discovery state, not Lean theorem authority or machine claim promotion.

## Current theorem ladder

```text
off-line zero -> legal finite canonical negative obstruction            PROVED
first-bad / parity / Schur / secular machinery                          PROVED
source-explicit cross-parity transfer                                   PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131
zero-shift source transport / absolute source energy / determinant      PROVED / #134-#137
regular selected first-bad endpoint                                     PROVED / #140-#150
retained first-bad + exact pole-prime discrepancy                       PROVED / #153
legal generic Riesz smoothing + parity/even source jets                 PROVED / #155
complex production D transport + exact complete Riesz 6/even 8          PROVED / #157
retained transformed negativity + off-line-zero R6 wrapper              PROVED / #157
general moment-prefix odd-jet law                                       PROVED / #159
exact seventh / even ninth leading-moment self-energy jets              PROVED / #159
generic signed complete-channel Riesz boundary recurrence               PROVED / #159
same-state shifted Riesz x cross-parity source composition              PROVED / #161
odd-good -> nonzero exact production source moment                      PROVED / #161
headline odd-bad OR explicit-source-nonzero fork                        PROVED / #161
mixed quadratic-normal seventh source jet -> M4                         PROVED / #163
finite-prime sampling of the same mixed source observable               PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling                     PROVED / #163
retained mixed-jet/Riesz specialization                                 PROVED / #163

source-moment / M4 canonical-state rigidity                             OPEN
endpoint-scalar global sign/nonvanishing                                OPEN
full scalar pivot/background inequality                                 OPEN / ACTIVE RESEARCH
simultaneous even/odd bad exclusion                                     OPEN
odd-selected first-bad branch closure                                   OPEN
negative-root exclusion                                                 OPEN
outside-strip/trivial-zero seam + Mathlib RH wrapper                    OPEN
RH                                                                      OPEN
```

## What theorem authority through #163 gives

For the retained even shifted first-bad state, Lean proves an exact same-state package including

```text
R8(u_lambda) < 0
F_odd(lambda) = Gamma(lambda)*explicitCanonicalSourceMoment(u_lambda)
odd successor bad OR explicitCanonicalSourceMoment(u_lambda) != 0
h^(7)(0) = -2*(2*pi)^6*M4(u_lambda)
2*(2*pi)^4*(R8(u_lambda)-R9(u_lambda)) = S8(L)*|h^(7)(0)|^2
2*(2*pi)^4*R9(u_lambda) < -S8(L)*|h^(7)(0)|^2
```

No global sourceMoment/`M4` implication and no endpoint-scalar sign theorem is asserted.

## Research progression after theorem authority

### #165 — exact endpoint-scalar audit

The exact executable `S8(L)` normalization is independently checked, including prime powers. Broad finite positive evidence survives, but positivity alone would only propagate transformed negativity and therefore is not by itself the missing contradiction.

### #166 — theorem-aligned shifted-state audit

The finite state is corrected to the actual generalized shifted secular trial

```text
u_lambda = c - W(H-lambda G)^(-1)r.
```

No finite bad successor was found in the broad scout, but a near-critical odd `Q=16,N=3,K=4` family was isolated.

### #167 — Q16 scalar barrier

The near-critical full cell showed no floating negative point. The current direct whole-cell Arb representation remained 256/256 unresolved at depth 8, so brute subdivision is not being treated as mathematical progress.

### #168 — log17 threshold moment jet

Boundary-flat parity annihilation gives exact executable first surviving source-energy orders:

```text
odd  -> order 7, governed by M3^2
even -> order 9, governed by M4^2
```

The exact threshold and 18 two-sided Arb microscope points remained positive, while the full Q17 state continued downward but remained positive.

The isolated entering-prime stabilizer therefore does not determine the full canonical drift.

## Current active path

The live theorem frontier remains **FB-05**: find an independent canonical arithmetic restriction that makes the exact retained #161/#163 state impossible.

The highest-information research slice is now:

```text
full scalar final Sylvester/Schur pivot
=
smooth canonical background
+
high-order entering prime-power threshold kick.
```

The next research PR should determine the background variation, pivot sensitivity to the rank-one threshold atom, catch-up scale, parity behavior and whether this yields a real barrier or an actual finite bad successor.

This is not a revival of global Schur monotonicity and must not assume a fixed global derivative sign.

## Supporting open routes

```text
simultaneous parity badness exclusion with actual arithmetic
odd-selected first-bad coverage
endpoint-scalar sign/nonvanishing as a supporting theorem if useful
sourceMoment / M4 rigidity only if additional canonical structure appears
```

The next theorem PR should be chosen only after adversarial falsification of the pivot/background mechanism.

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_168_THRESHOLD_JET_BACKGROUND_DRIFT_DELTA.md`;
- `research/RHRC/DOCUMENTATION_AUTHORITY.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md`;
- `research/RHRC/routes/R003_ccm_bridge/README.md`;
- `research/RHRC/control_v2/README.md`.

Older dated deltas, external reviews and countermodel records remain historical evidence and are not rewritten to look current.

## Permanent firewalls

- RH remains OPEN.
- theorem authority remains through #163 until a later compiler-green Lean theorem PR.
- research PR green is not theorem authority.
- exact executable algebra is not a Lean theorem.
- finite Arb certification is not a global theorem.
- retained/shifted transformed negativity is not a contradiction.
- exact Riesz identities are not arithmetic sign theorems.
- endpoint-scalar positivity alone is not first-bad exclusion.
- threshold prime-entry stabilization is not full-source stabilization.
- `explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely.
- exact finite-prime sampling does not by itself determine the local seventh jet.
- simultaneous even/odd badness is not excluded.
- selected parity cannot be assumed even WLOG.
- no division by alpha/Gamma/overlap/source moment without separate nonzeroness.
- pointwise fixed-sign smoothed-integrand positivity remains dead.
- `UNRESOLVED` interval output is not sign evidence.
- `D` remains algebraic, not unitary/isometric.
- negative-root exclusion is not the terminal Mathlib `RiemannHypothesis` statement without the final seam.

**RH remains OPEN.**