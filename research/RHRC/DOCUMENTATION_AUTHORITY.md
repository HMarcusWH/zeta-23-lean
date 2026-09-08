# RHRC documentation authority and update law

This file defines which documentation is authoritative and how to keep the repository from drifting after rapid research changes.

## Authority order

When two sources disagree:

1. **Live GitHub head + Lean compiler + CI** — exact checked object wins.
2. **Merged theorem declarations and machine registries** — `CLAIM_REGISTRY.json`, `routes/ROUTE_REGISTRY.json`.
3. **Active route README** — e.g. `routes/R003_ccm_bridge/README.md`.
4. **Living research-control SSOTs** — the newest post-green delta plus `RESEARCH_LEADS.md` for accumulated option/status memory, and `CURRENT_RESEARCH_PLAN.md` for current execution order.
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
- `VALIDATION_PROTOCOL.md` when validation semantics or a factual current-anchor example changes;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or the control frontier change materially;
- `control_v2/ACTION_REGISTRY.json` when the executable research frontier changes.

Dated post-green delta files remain historical evidence and must not be rewritten to look current. A newer delta may supersede older deltas for current priority without altering their historical content. The large accumulated `RESEARCH_LEADS.md` ledger may likewise preserve old per-entry text when a newer delta explicitly carries the current authority banner and supersession rule.

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
- **control-plane semantic anchor** — last meaningful merged green research-control/assurance semantics.

A documentation/control-metadata PR does not advance theorem authority. A theorem-only PR does not automatically advance Control-v2 semantics.

### Current synchronized anchors after PR #132

```text
live main after documentation PR #132 = 38f65ce4abf5eec258d51425e7c9c88b63b21ffb
live main tree = 1cc939300fb269f798d25dc88f8eaff4eccc181a

theorem-state anchor = PR #131 merge 436d524d0cdeb5986d76dcbb988f771d19836c55
validated theorem head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
theorem tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a
RHRC #854 = SUCCESS
Permansson #627 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1

RH = OPEN
```

PR #132 synchronized documentation/control metadata and the research frontier but added no Lean theorem. Theorem authority therefore remains #131. The routing metadata may advance while Control-v2 authority/algorithm semantics remain anchored at #117.

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
8. update obstruction/dead-route/countermodel ledgers when a reusable blocker or falsifier changed;
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
- PR #122 theoremized projected metric/resolvent control, real scalarization, the first root metric bound and E4-A1 coupling classification.
- PR #124 theoremized projected kernel/range geometry, zero-shift solution canonicity and the exact resonant identity/bound.
- PR #125 theoremized the canonical zero-shift endpoint, exact complete square and strict regular endpoint sign.
- PR #127 theoremized the special zero-shift shell response and its exact relation to `S0`.
- PR #128 theoremized the signed regular response and canonical resonant kernel pole.
- PR #129 theoremized the source-explicit cubic defect, exact cross-parity secular transfer, overlap representation and global off-line-zero source-explicit certificate.
- PR #131 theoremized the exact canonical source-moment decomposition: pole-even channel, reduced arch diagonal/off-diagonal channels, finite von-Mangoldt prime atomization, scalar arch annihilation, pole odd-profile cancellation, and `cubicDefectFunctional = explicitCanonicalSourceMoment`.
- PR #132 changed documentation/control metadata only and therefore did not advance theorem authority.

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

## Current transition after PR #132

The newest current-priority delta is `RESEARCH_LEADS_POST_132_DELTA.md`. `RESEARCH_LEADS_POST_131_DELTA.md` remains historical evidence for the state immediately after theorem PR #131.

The post-#132 audit changes routing without changing theorem truth:

```text
NEXT THEOREM
  E4-A4b0 kernel/source zero-shift transport

NEXT ARITHMETIC LAYER
  absolute canonical source-energy decomposition retaining scalar normalization

DECISIVE OPEN TARGET
  canonical one-step domination/coercivity in both parities

OPTIONAL SIMPLIFIER
  log-lift dense regular-aperture selection
```

The exact rational countermodel campaign additionally quarantines generic factorwise `alpha`/`Gamma`/overlap/source-moment sign or nonvanishing closure. Scalar-shift covariance demonstrates that the generic transfer package cannot determine the absolute spectral origin. The replacement route must spend exact canonical normalization information.

Permanent firewalls now include:

```text
Re S0<0 != contradiction by itself
Re sigma0<0 != contradiction by itself
canonical 1/(-lam) pole != contradiction
D algebraic != D unitary/isometric
source decomposition != source sign/nonzeroness
linear source observable != universal raw positivity
factorwise transfer nonvanishing is not structural
shift-invariant transfer data != absolute spectral sign
positive-definite predecessors != positive successor
root uniqueness != root exclusion
```

The current post-#132 implications and falsification plan are recorded in `RESEARCH_LEADS_POST_132_DELTA.md`.

**RH remains OPEN.**
