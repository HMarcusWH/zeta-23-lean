# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Separate theorem and control anchors

```text
latest theorem-bearing PR = #163
merged theorem-bearing main = bd3fa1aafa7df2aa35873df532bdb6f17ddd2bbd
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #163 advances theorem authority. This synchronization changes routing metadata and regression locks, not the controller's capability/authority model.

## Current routed frontier

```text
FB-01 retained full first-bad/Schur certificate                    PROVED / #153
FB-02 exact finite pole-prime discrepancy                          PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex production transport / retained Riesz negativity  PROVED / #157
FB-04A exact moment jets + signed Riesz boundary recurrence         PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source composition  PROVED / #161
FB-04C mixed quadratic-normal jet x Riesz boundary coupling        PROVED / #163
FB-05 independent contradiction-producing arithmetic restriction  NOW / first live break
A4b2b universal one-step domination                                BROAD FALLBACK
GLOBAL first-bad exclusion                                         AFTER scoped arithmetic closure
```

The selected action remains `E4_A4_REGULAR_SCHUR_ENERGY_SIGN` under frontier `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN`.

## Why routing changes after #163

#163 consumes the former FB-04C mixed-source sublead:

1. the exact complex mixed source pairing is theoremized independently of the #159 self-energy theorem;
2. the normalized quadratic-normal observable `quadraticNormalSourceAtom` has exact seventh jet `-2*(2*pi)^6*M4` on every even boundary-flat carrier with `K>=1`;
3. its seventh-jet norm square is exactly the corresponding constant times `|M4|^2`;
4. `explicitCanonicalSourceMoment` is rewritten so its finite-prime term samples that same `quadraticNormalSourceAtom` at the production prime-source coordinates;
5. the complete-channel Riesz-8/Riesz-9 recurrence is rewritten as endpoint scalar times the squared seventh mixed jet;
6. those identities are specialized to the retained #161 even shifted first-bad trial;
7. strict retained Riesz-8 negativity yields a strict Riesz-9 upper bound through the mixed jet without assuming a sign for the endpoint scalar;
8. under opposite-parity goodness the retained cross-parity Gamma factor is nonzero.

The controller must no longer present the mixed-source seventh-jet or its Riesz coupling as open theorem work.

## Selected action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

The first live break is now FB-05:

```text
Given the exact #161/#163 same-state spectral, source, mixed-jet and Riesz constraints,
find an independent canonical arithmetic property that makes the retained shifted
negative state impossible.
```

Highest-information candidate subroutes are:

```text
1. exact sign/nonvanishing analysis of canonicalPolePrimeRieszEndpointScalar L 8;
2. theorem-aligned production prime-sample -> local-jet rigidity for quadraticNormalSourceAtom;
3. simultaneous even+odd badness exclusion that genuinely spends canonical arithmetic;
4. odd-selected first-bad coverage;
5. another cancellation-preserving arithmetic invariant on the same retained state.
```

These are research candidates, not theorem claims. In particular, #163 does not prove a sign for the endpoint scalar and does not prove `explicitCanonicalSourceMoment != 0 <-> M4 != 0`.

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
retained R6->R7 / even R8->R9 boundary decompositions       PROVED / #159
same-state shifted Riesz x cross-parity source composition  PROVED / #161
odd-good -> explicit source moment nonzero                   PROVED / #161
mixed quadratic-normal seventh jet -> M4                    PROVED / #163
finite-prime sampling of the same mixed source observable   PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling         PROVED / #163
retained mixed-jet/Riesz specialization                     PROVED / #163
source-moment <-> M4 coupling                               OPEN
endpoint-scalar sign/nonvanishing                           OPEN
simultaneous even/odd bad exclusion                         OPEN
odd-selected branch closure                                 OPEN
pointwise fixed-sign smoothed-integrand route               DEAD / exact finite falsification
#152 interval harness                                       TOOLING / scoped certification
final contradiction-producing arithmetic restriction       OPEN / ACTIVE
```

## Negative controls

- universal one-step domination is not a research reduction when obtained by restating successor positivity;
- generic shell/parity/KKT/displacement structure is insufficient without exact canonical arithmetic;
- no division by `alpha`, `Gamma`, overlap or source moment without a nonzeroness theorem;
- `D` remains algebraic, not unitary/isometric;
- exact discrepancy/Riesz cancellation must not be discarded by coarse channel bounds;
- DR-024 kills pointwise fixed-sign smoothed-integrand positivity only; the integrated boundary/cross-parity/mixed-source route does not revive it;
- `explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely, without a new theorem;
- exact finite-prime sampling of `quadraticNormalSourceAtom` does not by itself determine its seventh derivative at zero;
- the mixed source-pairing jet is theorem authority after #163, but it is not an arithmetic contradiction;
- simultaneous even/odd badness is not excluded by #163;
- finite Arb certification does not become Lean theorem authority.

## CI expectations

`tools/run_suite.py` runs Control-v2 unit tests. The RHRC workflow smoke must assert:

- theorem anchor is #163;
- theorem merge/tree correspond to the exact validated #163 state;
- control anchor remains #117;
- frontier and selected action remain unchanged;
- consumed FB-04C is no longer a live first break;
- FB-05 is the sole selected first break for `E4_A4_REGULAR_SCHUR_ENERGY_SIGN`;
- DR-024 remains a negative-control objection with no revival blocker;
- terminal claim remains `RH_OPEN`;
- controller theorem authority and terminal-claim mutation remain false.

Newest research implications:

`../RESEARCH_LEADS_POST_163_MIXED_SOURCE_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`

**RH remains OPEN.**
