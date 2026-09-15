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

External reviews and numerical discovery are evidence for routing, not theorem authority. Control-v2 route certificates are diagnostic only.

A green but unmerged PR is branch evidence. A merged Lean file is theorem authority only when its declarations lie in an exact successful authoritative compiler/import closure or were explicitly compiled by such a gate.

## Three-anchor model

### 1. Theorem-state anchor

```text
latest theorem-bearing PR = #182
validated theorem head = 0c3f63cdc4774ba1a68b21d1558ea0ee860a938d
merged theorem commit = a69160d37a84049711aaff6c3d5db804583a7306
validated theorem tree = e0b260b3b3a1ed470d54c14d8c0c46b32379f3fb
RHRC #1082 = SUCCESS
Permansson #855 = SUCCESS
```

#182 is the current compiler-validated mathematical authority. It adds theorem-backed generic real 2x2 Schur-envelope derivative calculus and H1 contact-orientation transfer.

### 2. Research-evidence anchor

```text
latest merged research PR = #180
validated research head = a87469da9e611b53ae400cb4b18ce4afeb94e6d2
merged research commit = 93ea3df51f2671e316197c1530ea504dee76e821
research tree = 8199cdc543f1b761c70466dfd602c143a277e6a2
RHRC #1077 = SUCCESS
Lean #837 = SUCCESS
Permansson #850 = SUCCESS
```

#180 records the newest green finite/discovery state. It does not upgrade Arb, floating, executable or interval-method output into Lean theorem authority.

### 3. Control-plane semantic anchor

```text
control-plane semantic anchor = PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
```

This changes only when controller capability/authority semantics change, not merely when theorem/research routing metadata is refreshed.

## Dynamic live-head rule

Do **not** freeze a mutable documentation merge as permanent `live main` state inside long-lived prose. When an exact current `main` SHA is needed, record it in the time-specific execution/PR/delta document.

## Living SSOT update law

Update these when their underlying state changes:

- root `README.md`, `FORK_NOTES.md`, `AUDIT.md`;
- `research/RHRC/README.md`;
- active route README;
- `research/RHRC/RESEARCH_LEADS.md`;
- newest dated research delta;
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md` when validation anchors/gates change;
- obstruction/dead-route ledgers when reusable classifications change;
- claim/route registries only when their own formal or explanatory state changes;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or descriptive research state change;
- `control_v2/ACTION_REGISTRY.json` when routing priority, surviving objections, or first-break specification changes;
- retro aliases/regression tests when intentionally hard-coded research vocabulary changes.

Historical dated deltas are not rewritten to look current.

## Current synchronized state

### Theorem authority through #182

PR #182 imports `Zeta23/CCM/SchurEnvelopeDerivative.lean` into the validated aggregate CCM closure and proves, for the generic real 2x2 Schur block, the exact determinant/pivot factorization, the correlation-preserving pivot derivative, its quotient-rule equivalent, actual scalar `HasDerivAt` theorems, and at H1 contact the sign-equivalence of determinant and pivot derivatives.

#182 does **not** prove contact existence, production arithmetic sign, global Schur monotonicity, first-bad exclusion, negative-root exclusion or RH.

### Research progression through #180

```text
#165 endpoint-scalar executable audit
#166 true shifted-state finite discriminator
#167 Q16 whole-cell interval method falsification
#168 threshold moment jet / Q17 microscope
#170 theorem-aligned one-step Schur visibility/background audit
#172 threshold-to-threshold production barrier audit
#174 q13/N2/K3/even exact 2x2 scalar barrier
#176 fixed-unit q13/Q14 value representation acceptance
#178 complete fixed-unit derivative implementation; raw side boxes unresolved
#180 exact-center derivative basin minimum-oriented; nonzero-width Schur graph out of H1 scope
```

#180's finite result remains:

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers: 3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
SCHUR_OUT_OF_H1_SCOPE
applicable_primary_count = 0
uniqueness_claim = false
```

### Current route

```text
PROVED THROUGH #182
  retained first-bad/source/Riesz/mixed-jet state
  -> generic 2x2 Schur-envelope derivative
  -> H1 contact determinant/pivot orientation transfer

RESEARCHED THROUGH #180
  -> q13/N2/K3/even finite microscope
  -> exact-center derivative basin minimum-oriented
  -> finite-width H1 is first Schur-box gate

NOW
  finite lane:
    centered H1 recovery
    -> theorem-backed Schur-box retry
    -> Delta_2'' only if needed

  formal Pair-A lane:
    production/Hermitian Schur-envelope interface
    -> fixed-cell -log(L)I + remainder
    -> -||u||^2/L universal drift
    -> source-specific remainder/contact bound
```

The formal first break remains `E4A4-SCHUR-FB-05`; the terminal claim remains `RH_OPEN`.

## Production bridge warning after #182

The q13 research tool uses an exact integer shell generator that spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified at the same magnitude. The production carrier is complex Hermitian while #182 is generic real 2x2 calculus.

Therefore the next theorem should prefer an invariant/Hermitian interface or separately prove the required real-coordinate normalization bridge. Do not silently identify research and formal shell coordinates.

## Claim firewall

- green research is not theorem promotion;
- generic #182 contact calculus is not a zeta-arithmetic sign law;
- finite #180 point orientation is not a whole-cell theorem;
- `SCHUR_OUT_OF_H1_SCOPE` is not evidence of sign failure;
- global Schur monotonicity remains quarantined;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**
