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
- **control-plane anchor** — last meaningful merged green research-control/assurance state.

A control-only PR does not advance theorem authority. A theorem-only PR does not automatically advance Control-v2 semantics.

### Current synchronized anchors after PR #129

```text
theorem-state anchor = PR #129 merge e1192857afed9f68fa4a13143ce690b62191b997
validated theorem head = 440be3e5b6bf05e94ae2c65b1704d52d20acc9af
theorem tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7
RHRC #838 = SUCCESS
Permansson #611 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

PRs #118/#119/#121/#122/#124/#125/#127/#128/#129 changed theorem files but did not change Control-v2 semantics. Therefore theorem authority advances to #129 while control-plane authority remains #117.

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

## Current transition after PR #129

The theorem frontier is **E4-A4 canonical-source branch exclusion**, with E4-B shifted-nullity, E3-C monotonicity and E3-B3 deformation in parallel.

The old E4-A3 construction problem is closed:

```text
#127: special zero-shift image is pure shell; sigma0*c=T u0;
      S0=star(sigma0)<c,c>.

#128: regular Re sigma0<0; canonical kernel coordinate k;
      resonant exact (-lam)K(R_lam b)=k and divided pole.

#129: cubic defect = actual canonical quadratic source moment;
      exact cross-parity secular transfer;
      off-line zero -> source-explicit global first-bad certificate.
```

The next job is not to re-prove shell response, pole decomposition or generic branch structure. Post-#128 countermodels show that generic parity/KKT/rank-one/displacement structure can coexist with bad finite states. The next theorem must therefore spend information from the actual `canonicalSourceMatrix` source formula.

Permanent firewalls:

```text
Re S0<0 != contradiction
Re sigma0<0 != contradiction
canonical 1/(-lam) pole != contradiction
D algebraic != D unitary/isometric
source transfer != source sign/nonzeroness
root uniqueness != root exclusion
```

The current post-#129 implications and falsification plan are recorded in `RESEARCH_LEADS_POST_129_DELTA.md`.

**RH remains OPEN.**