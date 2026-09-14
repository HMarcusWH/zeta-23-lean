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
merged research PR = #170
validated research head = 70689692d5b92252bf9da97740385aaced2bf197
merged research commit = c94242fe41ae62b59aaa392a33e35034eb2c1b1e
research tree = 38e38a1d4cf90afa0e8103e58d1cbae626ebdeef
RHRC #1058 = SUCCESS
Permansson #831 = SUCCESS

CONTROL SEMANTIC AUTHORITY
control-plane semantic anchor = PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PRs #165-#170 refresh research evidence and routing context only. They do not change the controller's capability/authority model and do not move theorem authority beyond #163.

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
  current research slice: threshold-to-threshold Schur barrier
A4b2b universal one-step domination                               BROAD FALLBACK
GLOBAL first-bad exclusion                                        AFTER scoped arithmetic closure
```

The selected action remains `E4_A4_REGULAR_SCHUR_ENERGY_SIGN` under frontier `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN`.

The selected first-break ID remains `E4A4-SCHUR-FB-05`.

## Why routing changes after #165-#170

The formal break has not changed, but the best way to interrogate it has.

- #165 shows endpoint-scalar positivity alone is not a contradiction mechanism.
- #166 aligns finite discovery with the true shifted secular ray and isolates a near-critical Q16/N3/K4/odd family.
- #167 shows direct whole-cell Arb subdivision is dependency-limited: 256/256 depth-8 leaves remain unresolved.
- #168 identifies the boundary-flat seventh/ninth-order threshold jets and finds the full Q17 state continues downward but positive.
- #170 moves the scalar to theorem-aligned `[W|c]` geometry, finite-certifies q17 Schur visibility, separates a positive entering-q pivot effect from a negative smooth-background finite difference, and finds the sampled physical H1 pivot remains positive through q19.

Therefore the pivot/background decomposition itself is consumed research infrastructure. The current question is whether integrated local envelope dynamics create a threshold-to-threshold barrier.

## Selected action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

The sole live first break remains:

```text
Given the exact #161/#163 same-state spectral, source, mixed-jet and Riesz constraints,
find an independent canonical arithmetic property that makes the retained shifted
negative state impossible.
```

The current highest-information attack is:

```text
use the theorem-aligned H1 Schur envelope locally,
preserve pole/arch/prime/scalar cancellation,
and compare integrated background loss from one genuine arithmetic seam
to the next against arithmetic threshold replenishment.
```

Research questions:

1. can the local envelope derivative be bounded/certified on an arithmetic interval without assuming global monotonicity?
2. which exact channel derivatives create the q17 near-cancellation?
3. how much positive barrier can the background consume before the next nonzero von-Mangoldt seam?
4. how much barrier is replenished by the entering prime-power threshold response?
5. can the H1 pivot reach zero before the next seam?
6. does the mechanism persist across sizes and both parities?
7. can any surviving inequality be composed with the exact #161/#163 retained state without restating successor positivity?

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
theorem-aligned Schur visibility/background audit           RESEARCH / #170

source-moment <-> M4 coupling                               OPEN
endpoint-scalar global sign/nonvanishing                    OPEN
threshold-to-threshold Schur barrier                        OPEN / ACTIVE
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
- q17 visibility is a finite certificate, not a universal theorem;
- independent channel Schur pivots cannot be summed;
- finite Arb central differences are not derivative theorems;
- simultaneous even/odd badness remains open;
- selected parity is not even WLOG;
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

Control-v2 tests additionally lock the post-#170 routing context so the selected action cannot silently revert to the pre-#170 pivot-construction priority.

Newest research implications:

`../RESEARCH_LEADS_POST_170_SCHUR_VISIBILITY_THRESHOLD_BARRIER_DELTA.md`

**RH remains OPEN.**
