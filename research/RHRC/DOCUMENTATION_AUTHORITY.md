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
latest merged research PR = #190
validated research head = 8701920b0da18ae6595ad0eee55c1f6cb291a94f
merged research commit = f87da9fde71dd1e74419c6ae5848eee3787c27e4
validated research tree = af8774b65c898de221a5bf32977ccff3407a7b2d
RHRC #1096 = SUCCESS
Permansson #869 = SUCCESS
research disposition = JOINT_EXACT_VECTOR_SEPARABLE / JOINT_THRESHOLD_SIGNATURE_SEPARABLE
```

This is research/falsification authority only. It does not move Lean theorem authority.

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

Historical dated deltas are not rewritten to look current.

## Current synchronized state

### Theorem authority through #184

Lean proves the Hermitian 2x2 Schur/contact calculus, exact frozen production log-cover family, fixed-cell production bridge, N2 predecessor/canonical-shell reconstruction and orthogonality, and

```text
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

No later research PR promotes additional Lean theorem authority.

### Research progression through #190

```text
#186 -> broad remainder domination returns DOMINATION_SIGNAL_MIXED
#188 -> frozen normalization-safe selector family audited
#189 -> every individual frozen selector is ambiently separable from target sign
#190 -> complete seven-selector vector is jointly ambiently separable from target sign
        with identical nonboundary threshold signature
        -> all 127 nonempty subsets are also insufficient in that ambient algebra
```

The exact #190 executable classifications are:

```text
JOINT_EXACT_VECTOR_SEPARABLE
JOINT_THRESHOLD_SIGNATURE_SEPARABLE
```

The #190 code explicitly keeps canonical realizability, FB-05 closure, negative-root exclusion and RH false/unclaimed.

### Current route

```text
PROVED THROUGH #184
  exact Hermitian/log-cover/contact algebra

RESEARCHED THROUGH #190
  broad domination falsified
  frozen selector surface individually and jointly insufficient in ambient algebra

NOW
  characterize canonical production realizability
  -> impose common-aperture/source-channel/geometry constraints on the #190 reflected twin
  -> isolate the first exact production relation that destroys it
  -> formalize only a relation shown to be mathematically decisive
```

The concrete first lead comes from the executable production source decomposition:

```text
scalar_shift = 2*cCorrection'(L) I
arch_signed  = -arch_direct - scalar_shift
```

This demonstrates that the ambient #190 source coordinates omit production coupling. It is a research lead, not yet a theorem excluding the reflected class.

## Historical-state rule

The post-#186 delta and obstruction supplement remain historical evidence and must not be edited to pretend they were written after #190. The current living docs should point to the new post-#190 delta while retaining #186 as ancestry.

## Claim firewall

- green research is not theorem promotion;
- a green falsification can invalidate its tested hypothesis;
- exact executable algebra is not automatically a Lean theorem;
- ambient algebra countermodels are not automatically canonical arithmetic states;
- #190 closes only the declared frozen strong-selector observation surface in its ambient model;
- theorem authority remains #184;
- control semantic authority remains #117;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**