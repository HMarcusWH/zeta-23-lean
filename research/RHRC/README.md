# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

Live GitHub head + exact Lean compiler + CI are authoritative dynamically.

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
selected formal first break = E4A4-SCHUR-FB-05
RH = OPEN
```

Research PRs after #163 refine the attack surface; they do not create Lean theorem authority.

## Theorem-backed route

```text
finite negative obstruction / first-bad / Schur machinery            PROVED
source-explicit cross-parity transfer                                 PROVED / #129
exact canonical source-moment decomposition                           PROVED / #131
zero-shift transport / absolute energy / determinant                  PROVED / #134-#137
regular selected first bad                                            PROVED / #140-#150
retained certificate + exact pole-prime discrepancy                   PROVED / #153
legal generic Riesz smoothing + source parity/even jets               PROVED / #155
complex production transport + exact complete Riesz 6/even 8          PROVED / #157
retained transformed negativity + ExceptionalZero R6 wrapper          PROVED / #157
general moment-prefix odd-jet law                                     PROVED / #159
exact seventh / even ninth leading-moment self-energy jets             PROVED / #159
generic signed complete-channel Riesz boundary recurrence             PROVED / #159
same-state shifted Riesz x cross-parity source composition            PROVED / #161
odd-good -> explicit source moment nonzero                             PROVED / #161
mixed quadratic-normal seventh source jet -> M4                       PROVED / #163
finite-prime sampling of the same mixed source observable             PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling                   PROVED / #163
retained mixed-jet/Riesz specialization                               PROVED / #163

source-moment / M4 global rigidity                                    OPEN
endpoint-scalar global sign/nonvanishing                              OPEN
q13 scalar barrier sign/contact                                       OPEN / ACTIVE RESEARCH
simultaneous even/odd bad exclusion                                   OPEN
odd-selected branch closure                                           OPEN
negative-root exclusion                                               OPEN
terminal zeta/Mathlib seam                                            OPEN
RH                                                                    OPEN
```

## Post-#163 research progression

- **#165:** exact executable `S8(L)` audited; positivity alone is not a contradiction.
- **#166:** discovery aligned with the true shifted secular ray; near-critical Q16/N3/K4/odd family isolated.
- **#167:** full Q16 direct Arb audit remains 256/256 unresolved; brute dependency-heavy matrix subdivision rejected.
- **#168:** exact threshold jets identified; exact log17 threshold and two-sided microscope positive.
- **#170:** theorem-aligned `[W|c]` Schur visibility/background split validated in the research layer.
- **#172:** current-q entry lift found sign-indefinite; q13/N2/K3/even isolated as the strongest near-critical target.
- **#174:** exact q13 1D->2D scalar reduction validated; direct 384-bit scalar interval audit remains 100% unresolved on physical Q=13,14,15 subcells.
- **#176:** independent fixed-unit evaluator agrees with the direct production path and passes the frozen six-box Q14 factor-2 determinant-width routing criterion; method classification `FIXED_UNIT_METHOD_ACCEPTED`.
- **#178:** complete fixed-Q derivative implementation validated against independent centered value differences; all six primary Q14 raw `Delta_2'` boxes remain `DERIVATIVE_UNRESOLVED`; no bad/H1-loss interval certified; #176 replay-hardening debt closed.

## Immediate frontier — FB-05J correlation-preserving Q14 derivative enclosure

For the q13 target, the exact executable geometry remains:

```text
H(L) = [[a(L), b(L)],
        [b(L), d(L)]]
Delta_2(L)=a(L)d(L)-b(L)^2
H1 <-> a(L)>0
P(L)=Delta_2(L)/a(L) in H1.
```

#174 shows scalarization alone does not cure interval dependency. #176 selects the fixed-unit pullback as the preferred finite research representation. #178 validates the complete derivative machinery but the raw assembled interval expression

```text
Delta_2' = a'd + ad' - 2bb'
```

certifies no sign on any primary side box.

The next discriminator is therefore not another raw derivative subdivision. It is a **correlation-preserving enclosure comparison**:

```text
1. rigorous point Delta_2' balls at frozen primary/control centers
2. compare exact representations in H1
     raw: Delta_2' = a'd + ad' - 2bb'
     Schur-factorized: Delta_2' = a'P + aP'
3. if point orientation is visible, add Delta_2'' and centered mean-value/Taylor control
4. only after a two-sided bracket, use interval Newton/Krawczyk.
```

A positive q13 whole-cell result would still be a finite method/structure result, not FB-05 closure.

## Current execution priority

1. **Compute rigorous point `Delta_2'` signs at the frozen centers.**
2. **Benchmark raw versus Schur-factorized derivative enclosures where H1 is certified.**
3. **Do not assume a second-derivative/Taylor route is useful until point orientation is visible.**
4. **Keep determinant and pivot stationary problems distinct.**
5. **If a bad state appears, replay it immediately through #166/#161/#163.**
6. **If positive, identify and falsify the generalizable arithmetic reason.**
7. **Theoremize only an independent restriction that adds information beyond successor positivity.**
8. **Compose with #161/#163, then close FB-06/FB-07.**

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and theorem gates.
- `RESEARCH_LEADS_POST_178_DERIVATIVE_UNRESOLVED_CENTERED_ENCLOSURE_DELTA.md` — newest audited research synthesis.
- `RESEARCH_LEADS_POST_176_FIXED_UNIT_METHOD_ACCEPTANCE_Q14_STATIONARY_FRONTIER_DELTA.md` — previous synthesis.
- `OBSTRUCTION_LEDGER.md` / `DEAD_ROUTES.md` — reusable blockers.
- `routes/R003_ccm_bridge/README.md` — active route theorem/research surface.
- `control_v2/README.md` — executable routing semantics.

## Permanent firewalls

- RH remains OPEN.
- theorem authority remains through #163 until a later Lean theorem PR is compiler-green.
- research PR green is not theorem authority.
- exact executable algebra is not a Lean theorem.
- finite Arb certification is not a global theorem.
- transformed negativity is not a contradiction.
- endpoint-scalar positivity alone is not first-bad exclusion.
- arithmetic entry lift is not universally favorable.
- physical H1 does not imply q-removed-background H1.
- independent channel Schur pivots may not be added.
- large channel cancellation makes coarse component-sign reasoning unsafe.
- simultaneous even/odd badness remains open.
- selected parity cannot be assumed even WLOG.
- `UNRESOLVED` interval output is not sign evidence.
- direct scalar subdivision is not the next strategy after #174.
- #176 fixed-unit method acceptance is scoped to the frozen finite q13/Q14 benchmark.
- #178 `DERIVATIVE_UNRESOLVED` is not zero or stationary evidence.
- raw assembled derivative boxes with only more precision/subdivision are not a new route.
- determinant and pivot minima are distinct optimization targets.
- q13 whole-cell positivity alone would not imply global first-bad exclusion.
- the #176 replay-hardening debt is closed by #178.
- negative-root exclusion still needs the terminal seam before `RiemannHypothesis`.

**RH remains OPEN.**