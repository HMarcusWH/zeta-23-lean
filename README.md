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
merged research PR = #170
validated research head = 70689692d5b92252bf9da97740385aaced2bf197
merged research commit = c94242fe41ae62b59aaa392a33e35034eb2c1b1e
research tree = 38e38a1d4cf90afa0e8103e58d1cbae626ebdeef
RHRC #1058 = SUCCESS
Permansson #831 = SUCCESS

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
threshold-to-threshold Schur barrier                                    OPEN / ACTIVE RESEARCH
simultaneous even/odd bad exclusion                                     OPEN
odd-selected first-bad branch closure                                   OPEN
negative-root exclusion                                                 OPEN
outside-strip/trivial-zero seam + Mathlib RH wrapper                    OPEN
RH                                                                      OPEN
```

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

### #170 — theorem-aligned Schur visibility/background audit

The scalar diagnostic is aligned with the actual one-step `[W|c]` geometry. The unit-shell pivot matches the post-#150 selected residual, the q17 threshold direction is finite-certified Schur-visible (`rho != 0`), and the exact entering-q atom raises the pivot at all seven checked positive offsets.

At the same time, the q-removed smooth background has negative central finite differences at all seven tested scales. The direct physical scout remains H1-aligned at all 97 sampled states through q19 and finds no sampled negative pivot.

This is finite research evidence, not an interval/barrier theorem.

## Current active path

The live theorem frontier remains **FB-05**: find an independent canonical arithmetic restriction that makes the exact retained #161/#163 state impossible.

The highest-information research slice is now a **threshold-to-threshold Schur barrier**.

Use the local envelope identity

```text
P'(L) = u_L^T M'(L) u_L
```

as a cancellation-preserving diagnostic, without assuming global monotonicity, and compare the integrated background loss between genuine arithmetic seams against the arithmetic replenishment at threshold entry.

The next research PR should test whether the theorem-aligned H1 pivot can reach zero before the next nonzero von-Mangoldt seam, across multiple q/N/parity targets.

This is not a revival of global Schur monotonicity.

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_170_SCHUR_VISIBILITY_THRESHOLD_BARRIER_DELTA.md`;
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
- finite-difference enclosures are not derivative theorems.
- retained/shifted transformed negativity is not a contradiction.
- exact Riesz identities are not arithmetic sign theorems.
- endpoint-scalar positivity alone is not first-bad exclusion.
- threshold prime-entry stabilization is not full-source stabilization.
- Schur visibility at q17 is not a universal visibility theorem.
- sums of independent channel pivots are invalid because the Schur map is nonlinear.
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
