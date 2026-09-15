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
latest theorem-bearing PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c
RHRC #1089 = SUCCESS
Permansson #862 = SUCCESS
```

#184 is the current compiler-validated mathematical authority. It adds the complex-Hermitian Schur calculus, full frozen parity family on the logarithmic cover, exact fixed-cell production bridge, N2 predecessor/shell geometry, the algebraic universal-minus-remainder envelope derivative, and the conditional negative-orientation criterion.

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

### Theorem authority through #184

PR #184 imports `Zeta23/CCM/HermitianSchurEnvelopeDerivative.lean` and `Zeta23/CCM/FrozenN2SchurLogDrift.lean` into the validated aggregate CCM closure.

It proves, in the exact scope of those declarations:

```text
Hermitian 2x2 pivot/determinant calculus using |b|^2/a
real-component HasDerivAt theorems for the complex off-diagonal coordinate
contact-local determinant/pivot orientation equivalence under H1
full frozen parity production family on logarithmic cover M~(t)=-tI+R~(t)
exact fixed-cell equality with parityCompressedCanonical
log-cover deck-translation law
N2 predecessor/shell reconstruction
nonzero canonical cubic shell
exact predecessor-shell orthogonality
algebraic P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0
```

#184 does **not** yet assemble the actual source-specific real remainder-coordinate derivative witnesses from existing complex analyticity. It therefore does not yet prove a fully instantiated production `HasDerivAt` theorem for the N2 Schur pivot or a source-specific domination bound.

It also does not prove contact existence/uniqueness, first-bad crossing orientation on the same retained state, global Schur monotonicity, first-bad exclusion, negative-root exclusion or RH.

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
#178 complete fixed-unit physical-L derivative implementation; raw side boxes unresolved
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
PROVED THROUGH #184
  retained first-bad/source/Riesz/mixed-jet state
  -> generic real Schur calculus
  -> complex-Hermitian Schur calculus
  -> full frozen parity log-cover production family
  -> exact fixed-cell bridge
  -> N2 orthogonal predecessor/shell geometry
  -> algebraic universal-negative-drift + remainder decomposition
  -> conditional negative orientation under remainder domination

RESEARCHED THROUGH #180
  -> q13/N2/K3/even finite microscope
  -> exact-center derivative basin minimum-oriented
  -> finite-width H1 is first Schur-box gate

NOW
  research falsification lane:
    reuse exact #180 physical-L schedule
    -> split full pivot derivative into -E/L + remainder_drift_L
    -> measure domination margin and ratio L*remainder_drift_L/E

  formal Pair-A lane:
    existing complex frozen-source holomorphy
    -> parity/N2 scalar derivative witnesses
    -> actual production HasDerivAt identity
    -> source-specific contact-local remainder domination
    -> same-state opposing first-bad contact orientation
```

The formal first break remains `E4A4-SCHUR-FB-05`; the terminal claim remains `RH_OPEN`.

## Coordinate firewall after #184

PR #184's natural variable is logarithmic coordinate `t=log L`:

```text
dP/dt = -E + dR/dt.
```

The #178/#180 R003 derivative backend is in physical aperture `L`. Before comparison, use

```text
dP/dL = -E/L + dR/dL
```

and test `dR/dL < E/L`, equivalently `L*dR/dL < E`.

Do not compare a `t`-derivative remainder term directly against a physical-`L` derivative or vice versa.

## Claim firewall

- green research is not theorem promotion;
- #184 Hermitian/log-cover structure is not a source-specific arithmetic derivative bound;
- analyticity does not imply the needed domination magnitude;
- q13/N2/K3 is a finite microscope, not automatic arbitrary-first-bad coverage;
- `SCHUR_OUT_OF_H1_SCOPE` is not evidence of sign failure;
- global Schur monotonicity remains quarantined;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**