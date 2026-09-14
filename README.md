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
merged research PR = #172
validated research head = 4c857cd031497d895232a18a4bfb9a094d9facae
merged research commit = a31bb0bb7f025d7727dd3f224c705af797f64a19
research tree = c64b098c3159d739fa15eeaa96e35693615873d7
RHRC #1063 = SUCCESS
Permansson #836 = SUCCESS

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
q13 even 2x2 scalar barrier                                             OPEN / ACTIVE RESEARCH
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

The near-critical full cell showed no floating negative point. The current direct whole-cell Arb representation remained 256/256 unresolved at depth 8, so brute dependency-heavy subdivision is not being treated as mathematical progress.

### #168 — log17 threshold moment jet

Boundary-flat parity annihilation gives exact executable first surviving source-energy orders:

```text
odd  -> order 7, governed by M3^2
even -> order 9, governed by M4^2
```

The exact threshold and 18 two-sided Arb microscope points remained positive, while the full Q17 state continued downward but remained positive.

### #170 — theorem-aligned Schur visibility/background audit

The scalar diagnostic is aligned with the actual one-step `[W|c]` geometry. The q17 threshold direction is finite-certified Schur-visible (`rho != 0`), the exact q17 entering atom raises the pivot at checked offsets, and the q-removed background has negative certified finite differences.

### #172 — threshold-to-threshold barrier falsification

The research layer tests genuine arithmetic intervals across q/N/parity. All sampled complete physical states remain positive, but the arithmetic-entry heuristic changes materially:

```text
q9 / even   current-q entry lift  NEGATIVE_CERTIFIED
q13 / even  current-q entry lift  NEGATIVE_CERTIFIED
q16 / odd   current-q entry lift  POSITIVE_CERTIFIED
```

The most dangerous sampled state is `q=13 -> 16, N=2, K*=3, even`. Arb certifies at the quantized near-minimum

```text
full unit-shell pivot      ~= +5.8401616e-12
q-removed background       ~= +1.2217611e-11
q13 entry lift             ~= -6.3774491e-12
```

with H1 predecessor positivity certified there.

Thus arithmetic entry lift is sign-indefinite in the tested canonical states. The next problem is the complete physical scalar barrier, not a universal favorable threshold-kick theorem.

## Current active path

The live theorem frontier remains **FB-05**: find an independent canonical arithmetic restriction that makes the exact retained #161/#163 state impossible.

The highest-information research target is now the **q13/N2/K3/even 2x2 Schur determinant barrier**.

For this exact low-dimensional target, theorem-aligned executable geometry gives a one-dimensional predecessor and two-dimensional successor. In `[W|c]` coordinates,

```text
H(L) = [[a(L), b(L)],
        [b(L), d(L)]]

H1      <-> a(L) > 0
P(L)     = d(L) - b(L)^2/a(L)
Delta_2  = a(L)d(L) - b(L)^2
```

so on H1 scope

```text
sign P(L) = sign Delta_2(L).
```

The next rigorous research PR should try to certify or falsify

```text
a(L) > 0 and Delta_2(L) > 0
```

through the entire arithmetic interval `log 13 <= L <= log 16`.

Because the production backend tracks physical `Q=floor(exp L)`, the rigorous interval must respect the subcells

```text
[log 13, log 14]
[log 14, log 15]
[log 15, log 16]
```

unless exact inertness of the zero-von-Mangoldt Q=14/15 additions is separately certified.

A positive q13-cell certificate would be a method/structure result, **not** FB-05 closure: the retained first-bad state forced by an off-line zero is not known to lie in this one finite cell.

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_172_Q13_EVEN_SCALAR_BARRIER_DELTA.md`;
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
- finite Arb certification is not a global or whole-cell theorem.
- finite-difference/envelope quadrature evidence is not a derivative theorem.
- retained/shifted transformed negativity is not a contradiction.
- exact Riesz identities are not arithmetic sign theorems.
- endpoint-scalar positivity alone is not first-bad exclusion.
- arithmetic threshold entry lift is not known to have a universal favorable sign.
- full physical H1 does not imply q-removed-background H1.
- sums of independent channel pivots are invalid because the Schur map is nonlinear.
- large channel cancellation makes coarse component-sign reasoning unsafe at tiny residual scales.
- `explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely.
- exact finite-prime sampling does not by itself determine the local seventh jet.
- simultaneous even/odd badness is not excluded.
- selected parity cannot be assumed even WLOG.
- no division by alpha/Gamma/overlap/source moment without separate nonzeroness.
- pointwise fixed-sign smoothed-integrand positivity remains dead.
- `UNRESOLVED` interval output is not sign evidence.
- `D` remains algebraic, not unitary/isometric.
- q13 whole-cell positivity alone would not imply global first-bad exclusion.
- negative-root exclusion is not the terminal Mathlib `RiemannHypothesis` statement without the final seam.

**RH remains OPEN.**
