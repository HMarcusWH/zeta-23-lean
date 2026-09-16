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
merged research PR = #193
head  = 085634ca7dafe4d9f598b2b5e081be80e050ba8c
merge = fdd6606f85e92bf632b4cdaf1d4af85f6fa5b195
tree  = db569150046459f4b87a931d3e8d01054bbbedff
RHRC #1109 = SUCCESS
Permansson #882 = SUCCESS
post-190 canonical realizability audit #5 = SUCCESS
post-192 parity trajectory rigidity #3 = SUCCESS
research disposition = TRAJECTORY_RIGIDITY_UNRESOLVED

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
FB-05I sharper same-hull parity-trajectory enclosure               NOW / selected research bottleneck
```

The selected action remains `E4_A4_REGULAR_SCHUR_ENERGY_SIGN` under frontier `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN`. The selected first-break ID remains `E4A4-SCHUR-FB-05`.

## Why routing changes after #193

#190 closed the frozen selector surface only in ambient algebra. #192 then imposed canonical production structure: the particular negative-scalar witness is excluded, but the general reflection mechanism is not. #193 moved to the actual fixed-Q aperture trajectory.

At all six exact Q14 centers #193 certifies:

```text
e > 0
o > 0
J > 0
P2 > 0
```

but the finite-width first-order run returns:

```text
63/96 H1_UNRESOLVED
33/96 J_UNRESOLVED
0 J_NEGATIVE
0 J_POSITIVE
TRAJECTORY_RIGIDITY_UNRESOLVED
```

Therefore Control-v2 must not recommend another selector combination, another #192 replay, or merely a larger subdivision budget on the same #193 graph.

## Selected action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

The sole live first break is still an independently meaningful canonical arithmetic restriction on the exact same retained/contact state. What changed is the highest-information research object.

### Highest-information research lane

Audit **sharper parity-trajectory orientation on the same frozen Q14 hull**.

Reuse:

```text
J = o'e - e'o
P2 = L*J/(o*e)
sign(P1') = sign(P2) = sign(J)  under L,e,o>0
```

Compare:

```text
A. first-order Wronskian enclosure      [#193 baseline]
B. direct P2 log-slope enclosure
C. centered second-order/Taylor enclosure
```

Primary hypothesis to falsify: `J(L)>0` throughout the exact inherited Q14 hull.

Exact-center positivity is a clue, not a bounded monotonicity result. A complete signed cover is required.

### Formal infrastructure lane

Actual production derivative witnesses and an instantiated `HasDerivAt` Schur identity remain useful. Formalize the smallest exact trajectory/production relation shown by research to be decisive; do not theoremize weak scalar positivity or revive universal domination merely because they are easy to state.

### Pair-A decision rule

If a sharper representation certifies a genuine bounded monotonicity mechanism, attempt to distill and compose it with #184 and an independently proved opposing first-bad property on the exact same state. If the route fails structurally, downgrade Pair A and prioritize other incompatibility pairs.

## Evidence firewall

```text
#184 Hermitian/log-cover package          PROVED
#190 joint semantic independence          EXACT EXECUTABLE RESEARCH
#192 canonical-realizability ladder       EXACT / RIGOROUS FINITE RESEARCH
#193 exact trajectory centers             RIGOROUS POINT RESEARCH
#193 finite-width orientation             UNRESOLVED
J>0 on Q14 hull                           OPEN
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

The historical `test_post190_sync.py` remains untouched and continues to guard the consumed Layer 0 -> Layer 5 canonical production realizability vocabulary. `test_post193_sync.py` adds the new authority and trajectory-frontier regression without rewriting history.

Newest implications: `../RESEARCH_LEADS_POST_193_PARITY_TRAJECTORY_DELTA.md`.

**RH remains OPEN.**
