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
latest merged research PR = #193
validated research head = 085634ca7dafe4d9f598b2b5e081be80e050ba8c
merged research commit = fdd6606f85e92bf632b4cdaf1d4af85f6fa5b195
validated research tree = db569150046459f4b87a931d3e8d01054bbbedff
RHRC #1109 = SUCCESS
Permansson #882 = SUCCESS
post-190 canonical realizability audit #5 = SUCCESS
post-192 parity trajectory rigidity #3 = SUCCESS
research disposition = TRAJECTORY_RIGIDITY_UNRESOLVED
```

The #193 head tree is identical to the merge tree. This is research/falsification authority only. It does not move Lean theorem authority.

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
- `control_v2/ACTION_REGISTRY.json` when routing priority, surviving objections, or first-break specification changes;
- `routes/ROUTE_REGISTRY.json` explanatory notes when route state changes;
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

### Completed research history through #193

```text
#186 -> broad remainder domination returns DOMINATION_SIGNAL_MIXED
#188 -> frozen normalization-safe selector family audited
#189 -> every individual frozen selector is ambiently separable from target sign
#190 -> complete seven-selector vector jointly ambiently separable from target sign
        with identical nonboundary threshold signature
        -> all 127 nonempty subsets insufficient in ambient algebra
#192 -> canonical production realizability Layer 0 -> Layer 5 executed
        -> specific negative-scalar witness excluded
        -> general reflected mechanism unresolved
        -> six-state production panel has 0/15 seven-vector overlaps
#193 -> Q14 parity-trajectory rigidity audit
        -> 6/6 exact centers e,o,J,P2 positive
        -> finite-width first-order cover unresolved
        -> TRAJECTORY_RIGIDITY_UNRESOLVED
```

The #190 code explicitly keeps canonical realizability, FB-05 closure, negative-root exclusion and RH false/unclaimed. #192 and #193 do not change that theorem firewall.

### Current route

```text
PROVED THROUGH #184
  exact Hermitian/log-cover/contact algebra

RESEARCHED THROUGH #193
  #190 ambient selector surface insufficient
  #192 specific reflected witness noncanonical; general reflection unresolved
  #193 exact-center parity orientation uniformly positive; finite-width rigidity unresolved

NOW
  same frozen Q14 hull
  -> sharpen neighborhood representation
  -> compare first-order J, direct P2 log-slope, centered second-order/Taylor
  -> test whether J(L)>0 can be rigorously certified across the bounded hull
```

A complete signed finite-width cover may support bounded monotonicity research. Six signed centers alone may not.

## Historical-state rule

The post-#190 delta and OBS-054 remain historical evidence and must not be edited to pretend they were written after #193. The current living docs point to the new post-#193 delta while preserving the #190/#192 layer history needed for regression and provenance.

## Claim firewall

- green research is not theorem promotion;
- exact executable algebra is not automatically a Lean theorem;
- ambient algebra countermodels are not automatically canonical arithmetic states;
- #192 excludes a declared specific witness, not the general reflected class;
- six positive #193 centers are not a complete hull proof;
- first-order enclosure nonresolution is not monotonicity falsification;
- theorem authority remains #184;
- control semantic authority remains #117;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**
