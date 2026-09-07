# RHRC documentation authority and update law

This file defines which documentation is authoritative and how to keep the repository from drifting after rapid research changes.

## Authority order

When two sources disagree:

1. **Live GitHub head + Lean compiler + CI** — exact checked object wins.
2. **Merged theorem declarations and machine registries** — `CLAIM_REGISTRY.json`, `routes/ROUTE_REGISTRY.json`.
3. **Active route README** — e.g. `routes/R003_ccm_bridge/README.md`.
4. **Living research-control SSOTs** — `RESEARCH_LEADS.md` plus the newest post-green delta for accumulated option/status memory, and `CURRENT_RESEARCH_PLAN.md` for current execution order.
5. **Current external build-plan / handover SSOT**.
6. **PR-specific settlement documents**.
7. **Historical roadmaps, release audits, numerical receipts and old implementation plans**.

Control-v2 route certificates and retro-search receipts sit inside level 4 as diagnostic research-control artifacts only. They do not outrank theorem declarations, machine claim surfaces, active route authority or compiler evidence.

A green but unmerged PR is branch evidence, not merged repository truth.

A merged source file is not automatically theorem authority: compiler validity attaches only to declarations in the exact successful import/build closure or a module separately built by an authoritative gate.

## Document classes

### Living SSOTs

Update these when the underlying state changes:

- root `README.md`;
- `FORK_NOTES.md`;
- `AUDIT.md`;
- `research/RHRC/README.md`;
- claim/route registries when formal promotion state actually changes;
- active route README;
- `research/RHRC/RESEARCH_LEADS.md` **or** a newer post-green delta when lead/status memory changes;
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- dead-route and obstruction ledgers when classifications change;
- `VALIDATION_PROTOCOL.md` when validation semantics change;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or the control frontier change materially;
- `control_v2/ACTION_REGISTRY.json` when the executable research frontier changes.

Dated post-green delta files remain historical evidence and must not be rewritten to look current. A newer delta may supersede older deltas for current priority without altering their historical content.

### Historical settlements

PR-specific settlement and dated audit files record what was known at that time. Do not rewrite their mathematical history merely to make them look current.

### Immutable provenance snapshots

Do not rewrite:

- `UPSTREAM_BASELINE.json`;
- pinned external source/reference manifests;
- numerical receipts;
- historical normalization locks;
- qualified RUN42C FFBBP profile/reference objects.

Create a new versioned object if semantics change.

## Theorem-state versus control-plane anchors

The repository keeps separate anchors when needed:

- **theorem-state anchor** — last meaningful theorem-bearing merge whose Lean surface defines current mathematical authority;
- **control-plane anchor** — last meaningful merged green research-control/assurance state.

A control-only PR does not advance theorem authority. A theorem-only PR does not automatically advance Control-v2 semantics.

### Current synchronized anchors after PR #122

```text
theorem-state anchor = PR #122 merge b2d1210902d430f3cdd3c24c2961ab843469b5d6
validated theorem head = 9c8154e3ea7a5762f8e65d508dc68bb9246db869
theorem tree = db51419fb7cc8b2e3dbe5cf2e770390086db9862
E3-B1 metric control + E4-A1 zero-resonance coupling classification = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

PRs #118/#119/#121/#122 changed theorem files but did not change Control-v2 semantics. Therefore theorem authority advances to #122 while control-plane authority remains #117.

Machine registries and compiler/CI evidence still outrank prose anchors.

## Control-v2 authority law

`research/RHRC/control_v2/CONTROL_BOUNDARY.json` is the explicit capability cap for the research controller. Control v2 may rank research actions and emit route/retro receipts. It may not:

- write `CLAIM_REGISTRY.json` as a consequence of a research recommendation;
- write `BOUNDARY.json` terminal status;
- write `routes/ROUTE_REGISTRY.json` by inference;
- emit the terminal RH answer;
- promote a Lean theorem;
- convert historical or numerical clues into theorem evidence.

`runner/terminal_answer.py` remains independent of Control v2. Historical clues are `requires_revalidation=true` by default. Counterfactual replay must be bounded by an `as_of` anchor, and external time-travel sources require availability metadata.

## Update triggers

After a post-green research pass, update documentation when any of these changes:

- canonical mathematical object;
- theorem status;
- dependency order;
- dead/quarantined route classification;
- source normalization or parameter convention;
- public repository identity;
- next critical gate;
- lead classification, resurrection or falsification state;
- execution priority, parallel-lane choice, route-selection gate or stop condition;
- Control-v2 theorem anchor/frontier, control-plane anchor, assurance semantics or archaeology scope.

## Post-green synchronization sequence

After every meaningful green result:

1. verify exact head, declarations, assumptions, axioms and CI;
2. update claim/route registries only if formal promotion state changed;
3. update the active route README if route state changed;
4. update `RESEARCH_LEADS.md` or add a new dated post-green delta when a lead was added, promoted, blocked, falsified, superseded, resurrected or composed;
5. update `CURRENT_RESEARCH_PLAN.md` if execution order or a decision gate changed;
6. update Control-v2 state/action metadata if the theorem frontier or control anchor changed;
7. update root/RHRC README and audit records when the public critical path changed;
8. update obstruction/dead-route ledgers when a reusable blocker changed;
9. leave historical settlements untouched except for an authority banner when necessary.

## Validated import-closure law

Repository presence, PR inclusion, merge inclusion and no-placeholder scanning are weaker states than Lean elaboration.

A theorem may be promoted only when its declaration is in the exact compiler-tested transitive import closure or its module was separately compiled by an authoritative successful gate. Production claim promotion may require theorem-specific `#check` / `#print axioms` coverage in addition to compilation.

Historical examples:

- PR #103 showed that a merged but unimported theorem file is not compiler authority.
- PR #110 showed that compiler validity and machine claim promotion are separate checks.
- PRs #112/#113 advanced theorem authority faster than machine claim-promotion surfaces.
- PR #115 theoremized cubic shell incidence.
- PR #117 hardened Control v2 without changing theorem declarations.
- PR #118 theoremized the canonical cubic quotient coordinate and normalized Schur reduction.
- PR #119 theoremized the exact negative secular root/eigenmode equivalence.
- PR #121 theoremized the pointwise explicit cubic Schur bridge.
- PR #122 theoremized projected metric/resolvent control, real unconjugated scalarization, the first root metric bound and E4-A1 zero-resonance coupling classification.

See `VALIDATION_PROTOCOL.md`.

## Claim rule

Documentation may explain implications, but it may not promote a claim beyond the exact theorem surface.

Use the project labels consistently:

- **PROVED** — exact statement established by Lean/CI;
- **DERIVED** — straightforward consequence of proved results, not yet separately formalized;
- **LEAD / HYPOTHESIS** — mathematically motivated route worth testing;
- **EXPERIMENTAL SIGNAL** — numerical/discovery evidence only;
- **OPEN** — not established.

RH remains OPEN until the exact terminal theorem is proved and claim-validated.

## Promoted theorem-binding completeness

For R003, `R003_PROMOTED_BINDINGS.json` is the declared production binding surface. Every `PROVED_UNCONDITIONAL` R003 claim with a theorem must agree exactly across `CLAIM_REGISTRY.json`, `R003_PROMOTED_BINDINGS.json`, and the exact production binding/axiom surface.

Supporting theorem checks may exist without individual registry promotion. CI does not equate every theorem with a promoted claim; promotion intent must be explicit.

## Current transition after PR #122

The theorem frontier is **E4-A2 zero-shift/range-endpoint classification**, with E3-C monotonicity and E4-B shifted-nullity in parallel.

The previous E3-B representation obstruction is closed:

```text
#119 exact quotient secular root detector
  + #121 conjugated explicit Schur bridge
  + #122 symmetry/realness
  -> exact real pointwise scalar representation.
```

The zero-resonance question is also sharper. For `A=P_W T|_W`, `b=Bc`, #122 proves

```text
Az=0 -> (<z,b>=0 <-> Tz=0).
```

The next job is to determine what each branch implies for the zero-shift endpoint:

```text
b ⟂ ker A
  -> attempt b ∈ range A and a solution-based finite endpoint without A^-1;

some z∈ker A has <z,b>!=0
  -> theoremize the zero-resonant contribution to R_lam b and the secular scalar near 0-.
```

Only after this and/or an independent scalar monotonicity theorem should the project attempt a CCM-specific negative-root exclusion theorem. Even root uniqueness remains weaker than exclusion.

The post-#122 implications and falsification plan are recorded in `RESEARCH_LEADS_POST_122_DELTA.md`.

**RH remains OPEN.**