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
merged research PR = #180
validated research head = a87469da9e611b53ae400cb4b18ce4afeb94e6d2
merged research commit = 93ea3df51f2671e316197c1530ea504dee76e821
research tree = 8199cdc543f1b761c70466dfd602c143a277e6a2
RHRC #1077 = SUCCESS
Lean #837 = SUCCESS
Permansson #850 = SUCCESS

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
q13 scalar barrier sign/contact                                         OPEN / ACTIVE RESEARCH
simultaneous even/odd bad exclusion                                     OPEN
odd-selected first-bad branch closure                                   OPEN
negative-root exclusion                                                 OPEN
outside-strip/trivial-zero seam + Mathlib RH wrapper                    OPEN
RH                                                                      OPEN
```

## Research progression after theorem authority

### #165 — endpoint scalar

The exact executable `S8(L)` normalization is audited with prime powers. Broad finite positive evidence survives, but positivity alone would only propagate transformed negativity and is not by itself the missing contradiction.

### #166 — theorem-aligned shifted state

The finite state is corrected to the actual generalized shifted secular trial `u_lambda = c - W(H-lambda G)^(-1)r`. A near-critical odd Q16/N3/K4 family is isolated.

### #167 — Q16 full-cell barrier

No floating negative point is found. Direct whole-cell Arb subdivision remains 256/256 unresolved, so brute subdivision of the dependency-heavy full matrix is rejected as the current method.

### #168 — log17 threshold moment jet

Boundary-flat parity annihilation gives exact executable first surviving source-energy orders 7 through `M3^2` in odd parity and 9 through `M4^2` in even parity. The exact threshold and 18 two-sided Arb microscope points remain positive.

### #170 — theorem-aligned Schur visibility/background audit

The scalar diagnostic is aligned with the actual one-step `[W|c]` geometry. The q17 threshold direction is finite-certified Schur-visible; the entering q17 atom raises the pivot at checked offsets while the q-removed background has negative finite differences.

### #172 — threshold-to-threshold barrier audit

Current-q arithmetic lift is sign-indefinite in finite Arb replay. The strongest sampled target becomes `q=13 -> 16, N=2, K*=3, even` with full unit-shell pivot near `+5.84e-12`.

### #174 — q13 exact 2x2 scalar barrier audit

The q13 target is reduced exactly to

```text
H(L) = [[a(L), b(L)],
        [b(L), d(L)]]
Delta_2(L)=a(L)d(L)-b(L)^2
H1 <-> a(L)>0
sign pivot = sign Delta_2 in H1.
```

The floating basin remains sampled-positive. The 384-bit direct scalar interval audit over physical Q=13/14/15 subcells returns 100% `UNRESOLVED` in every cell, with no positive, bad, H1-loss, or contact interval certified.

This is a method result, not a sign result: exact scalarization does not by itself eliminate interval dependency.

### #176 — fixed-unit q13/Q14 method benchmark

The fixed-unit pullback is implemented as an independent Arb evaluator while the direct `[0,L]` production evaluator remains the baseline. The exact PR pipeline checks primitive, full `7x7` matrix, theorem-aligned scalar, seam and zero-weight agreement, then benchmarks six frozen primary Q14 boxes around the distinct determinant and pivot basins.

The predeclared routing criterion passes in every primary box: `Delta_2` is strictly narrower and satisfies the factor-2 material-width criterion throughout the frozen benchmark. The certifier reports `FIXED_UNIT_METHOD_ACCEPTED`.

This is rigorous finite **method-selection evidence**, not a determinant sign, stationary-point theorem, whole-cell positivity result, arbitrary first-bad statement, or Lean theorem.

### #178 — complete fixed-unit derivative discrimination

The fixed-unit derivative backend differentiates the complete fixed-Q canonical source,

```text
M'(L) = pole'(L) - arch'(L) - prime'(L),
```

and propagates the result through the theorem-aligned `[W|c]` restriction to

```text
Delta_2' = a'd + ad' - 2bb'.
```

Analytic primitive, full 7x7 matrix, theorem-aligned scalar and odd-N2 ancestry derivatives agree with independent centered finite differences on the frozen implementation checks. Derivative seam continuation is required only at the zero-von-Mangoldt seams 14 and 15.

The six frozen primary Q14 derivative boxes nevertheless return

```text
DERIVATIVE_UNRESOLVED
NO_CERTIFIED_PRIMARY_DERIVATIVE_SIGN
```

with no certified left/right derivative sign, no derived stationary existence, no bad interval and no H1-loss interval. This is a rigorous finite method result: it says the current raw assembled derivative interval representation is not yet discriminating, not that `Delta_2'` vanishes.

#178 also closes the #176 standalone replay-hardening debt by binding the supplied benchmark schedule back to its frozen fixture and rejecting malformed schedules.

### #180 — exact-center derivative basin / Schur-scope audit

The inherited #178 schedule is reused exactly. At all six frozen primary Q14 exact centers, rigorous Arb point balls give

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers:  3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
```

The Schur point graph agrees on the same six H1-usable points. This supports a **derived stationary-existence statement if continuity is invoked**, but `uniqueness_claim = false`.

For the nonzero-width primary boxes the result is instead

```text
SCHUR_OUT_OF_H1_SCOPE
applicable_primary_count = 0
sign_recovery_labels = []
strict_width_gain_labels = []
material_2x_gain_labels = []
```

So #180 does **not** establish a finite-box Schur width gain. The width comparison is blocked before it becomes applicable because H1 is not certified over those boxes. No bad or H1-loss interval is certified.

**Post-green consequence:** first try centered H1 recovery from the sharp point value `a(L0)>0` and the already-validated first derivative `a'`; only then retry the Schur box representation. Build `Delta_2''` for centered derivative propagation only if that cheaper preflight is insufficient.

## Current active path

The live theorem frontier remains **FB-05**: find an independent canonical arithmetic restriction that makes the exact retained #161/#163 state impossible.

The q13/N2/K3/even finite laboratory now has validated value and derivative infrastructure, but #178 shows that raw box evaluation of

```text
Delta_2' = a'd + ad' - 2bb'
```

does not certify a sign on the frozen primary side boxes.

The next highest-information question is now **how to propagate the rigorously signed point basin without losing H1/correlation**. The preferred order is:

```text
1. centered H1 recovery from point a(L0)>0 plus rigorous a'(I)
2. inside recovered H1, retry Delta_2'=a'P+aP' on nonzero-width boxes
3. if still unresolved, add Delta_2'' and centered mean-value/Taylor propagation of the signed point values
4. only after signed left/right neighborhoods, attempt interval Newton/Krawczyk
5. in parallel, test/theoremize the source-specific log-drift/contact derivative law.
```

The determinant and Schur-pivot minima remain distinct optimization targets. The Schur factorization is only an alternative dependency graph for the same determinant derivative; it does not revive global Schur monotonicity.

A positive q13-cell certificate would still be a method/structure result, **not** FB-05 closure: the retained first-bad state forced by an off-line zero is not known to lie in this one finite cell.

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_180_POINT_DERIVATIVE_BASIN_CENTERED_TAYLOR_FRONTIER_DELTA.md`;
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
- transformed negativity is not a contradiction.
- endpoint-scalar positivity alone is not first-bad exclusion.
- arithmetic threshold entry lift is not universally favorable.
- full physical H1 does not imply q-removed-background H1.
- sums of independent channel pivots are invalid because the Schur map is nonlinear.
- large channel cancellation makes coarse component-sign reasoning unsafe.
- `explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely.
- simultaneous even/odd badness is not excluded.
- selected parity cannot be assumed even WLOG.
- pointwise fixed-sign smoothed-integrand positivity remains dead.
- `UNRESOLVED` interval output is not sign evidence.
- direct scalar subdivision is not the next strategy after #174.
- #176 fixed-unit method acceptance is scoped to the frozen finite q13/Q14 benchmark and is not a sign theorem.
- #178 `DERIVATIVE_UNRESOLVED` is not zero/stationary evidence.
- repeating the same raw assembled derivative boxes with only more precision/subdivision is not a new route.
- determinant and pivot minima are distinct optimization targets.
- `D` remains algebraic, not unitary/isometric.
- q13 whole-cell positivity alone would not imply global first-bad exclusion.
- negative-root exclusion is not the terminal Mathlib `RiemannHypothesis` statement without the final seam.

**RH remains OPEN.**