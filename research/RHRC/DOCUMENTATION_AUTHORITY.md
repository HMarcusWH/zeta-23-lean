# RHRC documentation authority and update law

This file defines which documentation is authoritative and how to prevent research-state drift after rapid theorem and discovery changes.

## Authority order

When sources disagree:

1. **Live GitHub head + Lean compiler + CI** — exact checked object wins.
2. **Merged theorem declarations and machine registries** — theorem/claim surfaces.
3. **Active route README**.
4. **Living research-control SSOTs** — newest dated research delta plus `CURRENT_RESEARCH_PLAN.md` and current RHRC/root summaries.
5. **Current external build-plan / handover SSOT**.
6. **PR-specific settlement documents**.
7. **Historical roadmaps, audits, numerical receipts, external reviews and old implementation plans**.

Research certificates, exact-rational audits, Arb output and external reviews are routing evidence unless separately theoremized in Lean.

## Three-anchor model

### Theorem-state anchor

```text
latest theorem-bearing PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c
```

PR #184 remains the current compiler-validated mathematical authority.

### Research-evidence anchor

```text
latest merged research PR = #197
validated research head = 2d936f9764abdfeaa82127d5c834c6c3e429da25
merged research commit = 162df6ce8bc13a816937d747f2965bff6764fad0
validated research tree = 97f6372a4c7c131006b4abc090c86767b9e99990
research disposition = GLOBAL_MONOTONE_ORIENTATION
```

PR #197 is research/falsification authority only. It does not move Lean theorem authority.

### Control-plane semantic anchor

```text
control-plane semantic anchor = PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
```

This changes only when controller capability/authority semantics change.

## Living SSOT update law

Update these when their underlying state changes:

- root `README.md`, `FORK_NOTES.md`, `AUDIT.md`;
- `research/RHRC/README.md`;
- active route README;
- `research/RHRC/RESEARCH_LEADS.md`;
- newest dated research delta;
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md` when validation anchors/evidence classes change;
- obstruction/dead-route ledgers when reusable classifications change;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or descriptive research state change;
- `control_v2/ACTION_REGISTRY.json` only when routing priority/first-break semantics change;
- `routes/ROUTE_REGISTRY.json` when route state/claim surfaces or its living route note changes;
- retro aliases/regression tests when intentionally hard-coded research vocabulary changes.

Historical dated deltas are not rewritten to look current. Historical regression tests are not repurposed to erase earlier consumed layers.

## Current synchronized state

### Theorem authority through #184

Lean proves the Hermitian 2x2 Schur/contact calculus, exact frozen production log-cover family, fixed-cell production bridge, N2 predecessor/canonical-shell reconstruction and orthogonality, and

```text
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

No later research PR promotes additional Lean theorem authority.

### Completed research history through #197

```text
#186 -> broad remainder domination returns DOMINATION_SIGNAL_MIXED
#188 -> frozen normalization-safe selector family audited
#189 -> every individual frozen selector ambiently separable from target sign
#190 -> complete seven-selector vector jointly ambiently separable from target sign
        -> all 127 nonempty subsets insufficient in ambient algebra
#192 -> canonical production realizability Layer 0 -> Layer 5 executed
        -> specific negative-scalar witness excluded
        -> general reflected mechanism unresolved
        -> six-state production panel has 0/15 seven-vector overlaps
#193 -> Q14 parity-trajectory rigidity audit
        -> 6/6 exact centers e,o,J,P2 positive
        -> 63/96 H1_UNRESOLVED
        -> 33/96 J_UNRESOLVED
        -> TRAJECTORY_RIGIDITY_UNRESOLVED
#195 -> validated canonical M,M',M'' sharp trajectory enclosure
        -> 63 second-order H1 recoveries
        -> 48 J_POSITIVE, 48 J_UNRESOLVED
        -> one unresolved span, certified t-fraction 63/64
        -> PARTIAL_TRAJECTORY_ORIENTATION
#197 -> unique inherited budget leaf replayed once
        -> A J_UNRESOLVED; B/C J_POSITIVE
        -> GLOBAL_MONOTONE_ORIENTATION
        -> uniform J_POSITIVE
        -> certified t-fraction 1
        -> global_positive_hull = true
        -> bounded_distinct_aperture_twin_exclusion = true
```

Historical #195 `PARTIAL_TRAJECTORY_ORIENTATION` / `63/64` remains preserved. PR #197 advances only the latest research-evidence anchor.

### Current route

```text
PROVED THROUGH #184
  exact Hermitian/log-cover/contact algebra

RESEARCHED THROUGH #197
  #190 ambient selector surface insufficient
  #192 specific reflected witness noncanonical; general reflection unresolved
  #193 positive exact centers; first-order propagation unresolved
  #195 H1 obstruction removed; 63/64 bounded partial orientation
  #197 complete frozen-Q14 positive orientation and bounded twin exclusion

NOW
  same canonical source lineage
  -> do not refine an already complete frozen cover
  -> audit the mechanism behind J>0
  -> use J' = o''e - e''o
  -> decompose pole/arch/prime contributions with all bilinear cross terms
  -> require rigorous reconstruction of the direct canonical total
  -> falsify any apparent source law before theoremization
```

A complete signed finite-width cover supports **rigorous bounded research**, not arbitrary-Q theorem authority.

## Historical-state rule

The post-#190, post-#193 and post-#195 deltas remain historical evidence and must not be edited to pretend they were written after #197. `RESEARCH_LEADS_POST_197_Q14_RESIDUAL_CELL_REPLAY_DELTA.md` is the newest current delta.

Historical `test_post195_sync.py` continues to verify that #195 evidence remains represented, while `test_post197_sync.py` verifies that the living current state advances to #197.

## Claim firewall

- green research is not theorem promotion;
- exact executable algebra is not automatically a Lean theorem;
- ambient algebra countermodels are not automatically canonical arithmetic states;
- #192 excludes a declared specific witness, not the general reflected class;
- #193 exact-center signs are not finite-width monotonicity;
- #195 `PARTIAL_TRAJECTORY_ORIENTATION` / `63/64` is historical bounded-partial evidence;
- #197 `GLOBAL_MONOTONE_ORIENTATION` is complete bounded research on one frozen Q14 domain;
- `global_positive_hull = true` is not an FB-05 theorem;
- bounded distinct-aperture twin exclusion is not global canonical injectivity;
- theorem authority remains #184;
- control semantic authority remains #117;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**