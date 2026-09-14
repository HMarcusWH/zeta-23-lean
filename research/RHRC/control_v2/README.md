# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Separate authority anchors

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #163
merged theorem-bearing main = bd3fa1aafa7df2aa35873df532bdb6f17ddd2bbd
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
control-plane semantic anchor = PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PRs #165-#168 refresh research evidence and routing context only. They do not change the controller's capability/authority model and do not move theorem authority beyond #163.

## Current routed frontier

```text
FB-01 retained full first-bad/Schur certificate                    PROVED / #153
FB-02 exact finite pole-prime discrepancy                          PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex production transport / retained Riesz negativity PROVED / #157
FB-04A exact moment jets + signed Riesz boundary recurrence        PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source composition PROVED / #161
FB-04C mixed quadratic-normal jet x Riesz boundary coupling       PROVED / #163
FB-05 independent contradiction-producing arithmetic restriction  NOW / sole selected first break
  current research slice: full scalar pivot/background dynamics
A4b2b universal one-step domination                               BROAD FALLBACK
GLOBAL first-bad exclusion                                        AFTER scoped arithmetic closure
```

The selected action remains `E4_A4_REGULAR_SCHUR_ENERGY_SIGN` under frontier `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN`.

The selected first-break ID remains `E4A4-SCHUR-FB-05`.

## Why routing changes after #165-#168

The formal break has not changed, but the best way to interrogate it has.

### #165 — endpoint scalar

The exact executable `canonicalPolePrimeRieszEndpointScalar L 8` normalization was audited. Broad finite positive evidence survived, but endpoint positivity alone would only propagate retained Riesz negativity. It is therefore not the default standalone closure mechanism.

### #166 — actual shifted state

Discovery was aligned with the theorem state:

```text
u_lambda = c - W(H-lambda G)^(-1)r.
```

The broad scout found no finite negative successor but isolated a near-critical odd `Q16/N3/K4` family.

### #167 — Q16 scalar barrier

No floating negative point was found. The direct whole-cell Arb representation remained unresolved in all 256 depth-8 leaves.

Therefore repeated subdivision of the same dependency-heavy full matrix is not the current research strategy.

### #168 — prime-entry threshold jet

Boundary-flat parity annihilation gives exact executable first surviving source-energy orders:

```text
odd  -> order 7 through M3^2
even -> order 9 through M4^2
```

The exact log17 threshold and 18 two-sided Arb microscope points remained positive, while the full Q17 state continued downward but remained positive.

Therefore the favorable isolated entering-prime jet does not determine the full canonical drift.

## Selected action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

The sole live first break remains:

```text
Given the exact #161/#163 same-state spectral, source, mixed-jet and Riesz constraints,
find an independent canonical arithmetic property that makes the retained shifted
negative state impossible.
```

The current highest-information attack is now:

```text
full scalar final Sylvester/Schur pivot
=
smooth canonical background
+
high-order entering prime-power threshold kick.
```

Research questions:

1. reconstruct the scalar pivot independently and by signed channels;
2. measure/background-bound its threshold variation;
3. derive the pivot sensitivity to the high-order rank-one prime-entry term;
4. estimate/test the catch-up scale;
5. determine whether a real barrier, finite bad successor, or parity incompatibility results;
6. preserve simultaneous-parity and odd-selected coverage as live obligations.

This is not a revival of global Schur monotonicity. No fixed global derivative sign is assumed.

## Evidence-class firewall

```text
retained first-bad certificate                              PROVED / #153
exact pole-prime discrepancy                                PROVED / #153
generic legal Riesz smoothing                               PROVED / #155
complex production D transport                              PROVED / #157
complete production Riesz 6 / even Riesz 8                  PROVED / #157
retained transformed negativity                             PROVED / #157
general moment-prefix odd-jet law                           PROVED / #159
exact seventh/ninth self-energy leading jets                PROVED / #159
generic signed Riesz boundary recurrence                    PROVED / #159
same-state shifted Riesz x cross-parity source composition  PROVED / #161
mixed quadratic-normal seventh jet -> M4                    PROVED / #163
finite-prime sampling of same mixed source observable       PROVED / #163
mixed-jet squared R8-R9 boundary coupling                   PROVED / #163
retained mixed-jet/Riesz specialization                     PROVED / #163

endpoint-scalar executable audit                            RESEARCH / #165
shifted-state same-state finite discriminator               RESEARCH / #166
Q16 scalar-barrier / interval-method audit                  RESEARCH / #167
threshold moment-jet / Q17 microscope                       RESEARCH / #168

source-moment <-> M4 coupling                               OPEN
endpoint-scalar global sign/nonvanishing                    OPEN
full scalar pivot/background inequality                     OPEN / ACTIVE
simultaneous even/odd bad exclusion                         OPEN
odd-selected branch closure                                 OPEN
final contradiction-producing arithmetic restriction       OPEN
```

## Negative controls

- universal one-step domination is not a research reduction when obtained by restating successor positivity;
- generic shell/parity/KKT/displacement structure is insufficient without exact canonical arithmetic;
- no division by `alpha`, `Gamma`, overlap or source moment without theorem-backed nonzeroness;
- `D` remains algebraic, not unitary/isometric;
- exact discrepancy/Riesz cancellation must not be discarded by coarse channel bounds;
- endpoint-scalar positivity alone is not first-bad exclusion;
- exact finite-prime sampling does not by itself determine a local derivative;
- threshold prime-entry stabilization does not imply full-source stabilization;
- simultaneous even/odd badness remains open;
- selected parity is not even WLOG;
- finite Arb certification is not Lean theorem authority;
- `UNRESOLVED` interval output is not sign evidence;
- global aperture/Schur monotonicity remains quarantined;
- brute direct whole-cell subdivision of the current dependency-heavy matrix representation is not the current certification route.

## CI expectations

`tools/run_suite.py` runs Control-v2 unit tests. The RHRC workflow smoke must continue to assert:

- theorem anchor is #163;
- theorem merge/tree correspond to the exact validated #163 state;
- control anchor remains #117;
- frontier and selected action remain unchanged;
- FB-05 is the sole selected first break for `E4_A4_REGULAR_SCHUR_ENERGY_SIGN`;
- terminal claim remains `RH_OPEN`;
- controller theorem authority and terminal-claim mutation remain false.

Control-v2 tests additionally lock the post-#168 routing context so the selected action cannot silently revert to pre-#165 priorities.

Newest research implications:

`../RESEARCH_LEADS_POST_168_THRESHOLD_JET_BACKGROUND_DRIFT_DELTA.md`

**RH remains OPEN.**