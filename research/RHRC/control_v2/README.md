# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Separate authority anchors

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #184
merge = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
head  = a756494ebe7e2530715e996b9a9a341fbe07c683
tree  = 6c77cd470809959a403b3bcc5f08d39f4076fa4c

LATEST RESEARCH EVIDENCE
merged research PR = #195
head  = ef8af439b4723062061553bfee0ae3eba0205684
merge = 380b0011ffa3fac9684ec05496e241b47878be69
tree  = cc403fc55454c0f865c17a36d971a9e7947f1a1a
research disposition = PARTIAL_TRAJECTORY_ORIENTATION

CONTROL SEMANTIC AUTHORITY
PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
```

The theorem, research and control anchors are intentionally distinct.

## Routed frontier

```text
FB-05A generic real Schur/contact orientation calculus             PROVED / #182
FB-05B Hermitian production/log-cover Schur drift decomposition    PROVED / #184
FB-05C broad remainder domination on frozen panel                  FALSIFIED / #186 research
FB-05D frozen selector family                                      AUDITED / #188
FB-05E individual selector sufficiency in ambient algebra          CLOSED / #189 research
FB-05F joint seven-selector sufficiency in ambient algebra         CLOSED / #190 research
FB-05G canonical production realizability Layer 0 -> Layer 5       EXECUTED / #192 research
FB-05H first-order Q14 parity-trajectory enclosure                 UNRESOLVED / #193 research
FB-05I second-order same-hull sharp enclosure                      PARTIAL / #195 research
FB-05J residual one-span source-mechanism audit                    NOW / selected research bottleneck
```

The selected action remains `E4_A4_REGULAR_SCHUR_ENERGY_SIGN` under frontier `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN`. The selected first-break ID remains `E4A4-SCHUR-FB-05`.

## Why routing changes after #195

#190 closed the frozen selector surface only in ambient algebra. #192 then imposed canonical production structure: the particular negative-scalar witness is excluded, but the general reflection mechanism is not. #193 moved to the actual fixed-Q aperture trajectory but its first-order finite-width representation failed H1 on 63/96 cells and signed no nonzero-width J cell.

#195 keeps that exact population and validates the complete canonical second-aperture jet. Its result is:

```text
PARTIAL_TRAJECTORY_ORIENTATION
48 J_POSITIVE
48 J_UNRESOLVED
0 J_NEGATIVE
0 H1_UNRESOLVED
second_order_h1_recovery_count = 63
representation_conflict_count = 0
unresolved_span_count = 1
certified_t_fraction = 63/64
global_positive_hull = false
bounded_distinct_aperture_twin_exclusion = false
```

Thus the old H1 gate is consumed on the frozen run. The current bottleneck is one residual orientation span, not positivity recovery.

Therefore Control-v2 must not recommend another selector combination, another #192 replay, a new Q/N/K/parity search, or merely a larger subdivision budget on the same #195 dependency graph.

## Selected action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

The sole live first break is still an independently meaningful canonical arithmetic restriction on the exact same retained/contact state. What changed is the highest-information research object.

### Highest-information research lane

Audit the **source mechanism behind the residual Q14 parity-trajectory span on the same frozen hull**.

Reuse:

```text
J = o'e - e'o
P2 = L*J/(o*e)
sign(P1') = sign(P2) = sign(J)  under L,e,o>0
J' = o''e - e''o
```

The next executable experiment should decompose the complete canonical pole/arch/prime production jet and reconstruct `J'` from all bilinear channel pairs:

```text
sum_{c,d} (o_c'' * e_d - e_c'' * o_d)
```

with signs absorbed consistently. The recombination must rigorously contain/equal the direct canonical total.

Primary hypothesis to falsify remains `J(L)>0` throughout the exact inherited Q14 hull. `63/64` is evidence, not closure.

### Formal infrastructure lane

Actual production derivative witnesses and an instantiated `HasDerivAt` Schur identity remain useful. Formalize the smallest exact trajectory/production relation shown by research to be decisive; do not theoremize weak scalar positivity, partial coverage, or revive universal domination merely because they are easy to state.

### Pair-A decision rule

If the residual span is certified positive for a structural reason, distill that mechanism and compose it with #184 and an independently proved opposing first-bad property on the exact same state. If the span contains a genuine fold or the orientation is cancellation-fragile, downgrade Pair A and prioritize the alternative incompatibility lanes.

## Evidence firewall

```text
#184 Hermitian/log-cover package          PROVED
#190 joint semantic independence          EXACT EXECUTABLE RESEARCH
#192 canonical-realizability ladder       EXACT / RIGOROUS FINITE RESEARCH
#193 exact trajectory centers             RIGOROUS POINT RESEARCH
#193 first-order finite-width orientation TRAJECTORY_RIGIDITY_UNRESOLVED
#195 second-order finite-width orientation PARTIAL_TRAJECTORY_ORIENTATION
J>0 on full Q14 hull                      OPEN
FB-05 closure                             OPEN
negative-root exclusion                   OPEN
RH                                        OPEN
```

## CI expectations

`tools/run_suite.py` runs Control-v2 tests. The workflow smoke must continue to assert:

- theorem anchor #184;
- control anchor #117;
- unchanged frontier/action/first-break IDs;
- controller theorem authority false;
- terminal-claim mutation false;
- terminal claim `RH_OPEN`.

Historical sync tests remain untouched and continue to guard their consumed research vocabulary. `test_post195_sync.py` advances the living research anchor and residual-span routing without rewriting history.

Newest implications: `../RESEARCH_LEADS_POST_195_PARITY_TRAJECTORY_SHARP_ENCLOSURE_DELTA.md`.

**RH remains OPEN.**
