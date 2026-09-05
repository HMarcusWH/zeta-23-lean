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

Control-v2 route certificates and retro-search receipts sit inside level 4 as **diagnostic research-control artifacts only**. They do not outrank theorem declarations, machine claim surfaces, active route authority, or compiler evidence.

The living research-control records have different scopes and must not be used to overrule theorem truth: the lead ledger/deltas record hypotheses and research state; the current plan records priority and dependency decisions.

A green but unmerged PR is branch evidence, not merged repository truth.

A merged source file is also not automatically theorem authority: compiler validity attaches only to declarations in the exact successful import/build closure or a module separately built by an authoritative gate.

## Document classes

### Living SSOTs

These must be updated when the underlying state changes:

- root `README.md`;
- `FORK_NOTES.md`;
- `AUDIT.md`;
- `research/RHRC/README.md`;
- claim/route registries;
- active route README;
- `research/RHRC/RESEARCH_LEADS.md` plus the newest post-green delta;
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- dead-route and obstruction ledgers;
- `research/RHRC/VALIDATION_PROTOCOL.md` when validation semantics or gates change;
- `research/RHRC/control_v2/CONTROL_STATE.json` when the merged theorem anchor, merged control anchor, or control frontier changes materially.

Dated post-green delta files remain historical evidence and should not be rewritten to make them look current. A newer delta may explicitly supersede an older delta for current research priority without altering the older file.

### Historical settlements

PR-specific settlement and dated audit files record what was known at that time. Do not rewrite their mathematical history merely to make them look current.

If necessary add a short banner:

~~~text
HISTORICAL SETTLEMENT
Current authority: live Lean/CI + registries + active route README.
~~~

### Immutable provenance snapshots

Do not rewrite:

- `UPSTREAM_BASELINE.json`;
- pinned external source/reference manifests;
- numerical receipts;
- historical normalization locks;
- qualified RUN42C FFBBP profile/reference objects.

Create a new versioned object if current semantics need a new machine-readable map. This is why FFBBP v1.6 assurance is additive rather than a rewrite of the RUN42C reference.

## Theorem-state anchors versus control-plane anchors

A living documentation PR cannot know its own future merge SHA. Therefore living prose must not create an endless docs-only hash chase.

The repository keeps two different anchors when needed:

- **theorem-state anchor** — last meaningful theorem-bearing merge whose Lean surface defines current mathematical authority;
- **control-plane anchor** — last meaningful merged green research-control/assurance state.

A control-only PR does not advance the theorem-state anchor. A theorem-bearing PR may advance both if it also changes the control state.

Current synchronized anchors:

~~~text
theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
E1 cubic-shell incidence = PROVED / MERGED

control-plane anchor = PR #116 merge 8921572170e89d74216f0c5577b669696626219e
control-plane tree = fc138b517c6835230515167386eafe3ef3495baf
Control v2 / FFBBP v1.6 assurance = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
~~~

Machine registries and compiler/CI evidence still outrank prose anchors.

## Control-v2 authority law

`research/RHRC/control_v2/CONTROL_BOUNDARY.json` is the explicit capability cap for the research controller. Control v2 may rank research actions and emit route/retro receipts. It may not:

- write `CLAIM_REGISTRY.json`;
- write `BOUNDARY.json`;
- write `routes/ROUTE_REGISTRY.json`;
- emit the terminal RH status;
- promote a Lean theorem;
- convert historical or numerical clues into theorem evidence.

`runner/terminal_answer.py` must remain independent of Control v2. Historical clues are `requires_revalidation=true` by default. Counterfactual replay must be bounded by an `as_of` anchor, and external time-travel sources require availability metadata.

Archaeology scope must be stated literally. `ALL_REFS_BEFORE_ANCHOR_IN_DECLARED_PATHS` means all historical refs in the declared Git search paths, not every repository byte. Search paths are part of the retro receipt identity.

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
2. update claim/route registries if formal promotion state changed;
3. update the active route README if the route state changed;
4. update `RESEARCH_LEADS.md` or add a new dated post-green delta when a lead was added, promoted, blocked, falsified, superseded, resurrected or composed;
5. update `CURRENT_RESEARCH_PLAN.md` if execution order or a decision gate changed;
6. update Control-v2 state/action metadata if the research frontier or control anchor changed;
7. update the root/RHRC README and audit records when the public critical path changed;
8. leave historical settlements untouched except for an authority banner when necessary.

A green but unmerged PR remains branch evidence until merged and registered.

## Validated import-closure law

Repository presence, PR inclusion, merge inclusion and no-placeholder scanning are weaker states than Lean elaboration.

A theorem may be promoted only when its declaration is in the exact compiler-tested transitive import closure or its module was separately compiled by an authoritative successful gate. For production R003 promotion, the required `#check` / `#print axioms` surface must also be present.

PR #103 is the canonical historical example: `ConstrainedParityGeometry.lean` was imported by `Zeta23.CCM`; `ParityBadness.lean` was merged but not imported. PR #105 later closed that gap by importing and compiling `ParityBadness.lean`.

PR #110 supplies a second lesson: theorem validity was authoritative because the final repair remained in the exact successful `Zeta23.CCM` import/build closure, while production claim promotion still required theorem-specific binding/axiom inspection.

PRs #112/#113 showed that theorem validity can advance faster than machine claim-promotion surfaces. PR #115 theoremized E1 in the authoritative CCM/ExceptionalZero umbrella closures. PR #116 then changed only supporting control infrastructure; it did not advance theorem authority.

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

For R003, `R003_PROMOTED_BINDINGS.json` is the declared production binding surface. Every `PROVED_UNCONDITIONAL` R003 claim with a theorem must agree exactly across `CLAIM_REGISTRY.json`, `R003_PROMOTED_BINDINGS.json`, and the exact `#check` / `#print axioms` declarations in `Zeta23/CCM/ClaimBindings.lean`.

The RHRC suite enforces this through `promoted_binding_lint.py`. Supporting theorem checks may exist without individual registry promotion, so CI does not equate every `#check` with a claim; promotion intent must be declared explicitly.

## Current transition after PR #116

The theorem frontier remains E1b/E2: use the theorem-backed nonzero negative-mode shell coordinate and nonzero cubic shell coordinate inside the same one-dimensional intrinsic shell, transfer the shifted Schur identity to the canonical cubic shell line, and normalize scalar choice.

The post-#116 research composition is recorded in `RESEARCH_LEADS_POST_116_DELTA.md`: E2 and E3 are expected to supply the operator-theoretic mechanism for a certified one-step deformation bound, while the deformation-budget numerical/paper lane remains a parallel falsification route. A genuine positive rigidity horizon, combined with already-proved upward persistence of badness, would exclude the whole fixed-`(L,p)` N-axis rather than merely produce a finite search window. This remains a research strategy until separately theoremized and certified.

**RH remains OPEN.**
