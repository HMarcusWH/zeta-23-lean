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
latest merged research PR = #199
validated research head = fabe301c95277345f0efe764252ce1c1213a4112
merged research commit = 27dda545b7ccdb2870088ebaf317d85e3d999555
validated research tree = 85eb8ea25d240c4a9c339262bdc611fae881f7f0
research disposition = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
```

PR #199 is research/falsification authority only. It consumes and exactly replays PR #197's bounded `GLOBAL_MONOTONE_ORIENTATION` / `J_POSITIVE` certificate before classifying the present source decomposition as dependency-unresolved. It does not move Lean theorem authority and does not downgrade the #197 direct sign result.

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

### Completed research history through #199

```text
#186 -> broad remainder domination returns DOMINATION_SIGNAL_MIXED
#190 -> complete seven-selector vector jointly ambiently separable from target sign
#192 -> canonical production realizability Layer 0 -> Layer 5 executed
#193 -> first-order Q14 parity trajectory remains finite-width unresolved
#195 -> validated M,M',M''; PARTIAL_TRAJECTORY_ORIENTATION / 63/64 historical
#197 -> unique residual leaf replay closes the frozen Q14 cover
        -> GLOBAL_MONOTONE_ORIENTATION / uniform J_POSITIVE
        -> certified fraction 1
        -> bounded distinct-aperture twin exclusion
#199 -> exact #197 cover replayed unchanged
        -> four-way source mechanism = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
        -> collapsed three-way mechanism = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
        -> no unique collapsed uniform lock
        -> direct bounded J_POSITIVE unchanged
```

Historical #195 and #197 states remain preserved. PR #199 advances only the latest research-evidence anchor.

### Current route

```text
PROVED THROUGH #184
  exact Hermitian/log-cover/contact algebra

RESEARCHED THROUGH #199
  frozen Q14 direct orientation is complete and positive
  current source-separated interaction graph loses sign resolution

NOW
  do not refine the completed cover
  do not rerun the same independent source split
  preserve known pole-prime cancellation before interval transport
  construct D = pole + prime_signed and A = direct_arch_signed
  build D,D',D'' and A,A',A'' upstream
  parity-restrict only after pairing
  require exact reconstruction of independent direct Method C
  if still unresolved, search for a higher-level composite identity
```

A complete signed finite-width cover supports **rigorous bounded research**, not arbitrary-Q theorem authority. A dependency-unresolved decomposition does not negate an independently certified direct sign.

## Historical-state rule

The post-#190, post-#193, post-#195 and post-#197 deltas remain historical evidence and must not be edited to pretend they were written after #199. `RESEARCH_LEADS_POST_199_Q14_SOURCE_DECOMPOSITION_DELTA.md` is the newest current delta.

Historical `test_post195_sync.py` and `test_post197_sync.py` continue to verify that their evidence remains represented. `test_post199_sync.py` owns the current #199 assertions.

## Claim firewall

- green research is not theorem promotion;
- exact executable algebra is not automatically a Lean theorem;
- ambient algebra countermodels are not automatically canonical arithmetic states;
- #197 `GLOBAL_MONOTONE_ORIENTATION` is complete bounded research on one frozen Q14 domain;
- #199 `SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED` is a representation/mechanism classification, not a loss of #197 `J_POSITIVE`;
- no unique source lock is not a theorem that no source law exists;
- theorem authority remains #184;
- control semantic authority remains #117;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**