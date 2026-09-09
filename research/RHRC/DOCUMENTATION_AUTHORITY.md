# RHRC documentation authority and update law

This file defines which documentation is authoritative and how to prevent research-state drift after rapid theorem changes.

## Authority order

When two sources disagree:

1. **Live GitHub head + Lean compiler + CI** — exact checked object wins.
2. **Merged theorem declarations and machine registries** — `CLAIM_REGISTRY.json`, `routes/ROUTE_REGISTRY.json`.
3. **Active route README** — e.g. `routes/R003_ccm_bridge/README.md`.
4. **Living research-control SSOTs** — newest post-green delta plus `CURRENT_RESEARCH_PLAN.md` and current RHRC/root summaries.
5. **Current external build-plan / handover SSOT**.
6. **PR-specific settlement documents**.
7. **Historical roadmaps, audits, numerical receipts and old implementation plans**.

Control-v2 route certificates and retro-search receipts are diagnostic research-control artifacts only. They do not outrank theorem declarations, machine claim surfaces, active route authority or compiler evidence.

A green but unmerged PR is branch evidence, not merged repository truth. A merged source file is theorem authority only when its declarations lie in the exact successful compiler/import closure or were separately compiled by an authoritative gate.

## Living SSOTs

Update these when the underlying state changes:

- root `README.md`;
- `FORK_NOTES.md`;
- `AUDIT.md`;
- `research/RHRC/README.md`;
- active route README;
- newest post-green research delta;
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md` when theorem/control validation anchors or gate examples change;
- dead-route and obstruction ledgers when classifications change;
- claim/route registries only when formal promotion state actually changes;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or the research frontier change;
- `control_v2/ACTION_REGISTRY.json` when the executable research frontier changes.

Dated post-green deltas are historical evidence. Do not rewrite older deltas to look current; add a newer delta and update current-priority pointers.

## Theorem-state versus control-plane anchors

The repository keeps distinct anchors:

- **theorem-state anchor** — latest meaningful theorem-bearing merge whose compiled Lean surface defines current mathematical authority;
- **control-plane semantic anchor** — latest meaningful merged green research-control/assurance semantics.

A documentation/control-metadata PR does not advance theorem authority. A theorem-only PR does not automatically advance Control-v2 algorithm/authority semantics.

### Current synchronized anchors after theorem PR #137

```text
live main after theorem PR #137 = fa2f209a6eb8b4059968e8d61239d80588ca256c
live main tree = e3de4dc0377f0124832822b6f97ab5bbd7718640

theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
validated theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

PR #136 theoremized absolute scalar-sensitive canonical source energy. PR #137 theoremized the exact source pairing, one-step determinant reduction, conditional domination sufficiency and global domination-failure/sign-witness endpoint. Theorem authority therefore advances to #137.

PR #117 remains the Control-v2 semantic anchor because the present synchronization changes theorem/frontier data, archaeology vocabulary and regression assertions, not the controller's authority model or ranking algorithm.

Machine registries and compiler/CI evidence still outrank prose anchors.

## Control-v2 authority law

`research/RHRC/control_v2/CONTROL_BOUNDARY.json` is the explicit capability cap. Control v2 may rank research actions and emit route/retro receipts. It may not:

- write `CLAIM_REGISTRY.json` as a consequence of a research recommendation;
- write `BOUNDARY.json` terminal status;
- write `routes/ROUTE_REGISTRY.json` by inference;
- emit the terminal RH answer;
- promote a Lean theorem;
- convert historical or numerical clues into theorem evidence.

`runner/terminal_answer.py` remains independent of Control v2.

## Update triggers

After a post-green research pass, update documentation when any of these changes:

- canonical mathematical object;
- theorem status;
- dependency order;
- dead/quarantined route classification;
- source normalization or parameter convention;
- next critical gate;
- lead classification, resurrection or falsification state;
- execution priority, route-selection gate or stop condition;
- Control-v2 theorem anchor/frontier, control-plane anchor, assurance semantics or archaeology scope.

## Post-green synchronization sequence

After every meaningful green result:

1. verify exact head, declarations, assumptions, axioms and CI;
2. update claim/route registries only if formal promotion state changed;
3. update active route README if route state changed;
4. add a new post-green delta if lead/status memory changed;
5. update `CURRENT_RESEARCH_PLAN.md` if execution order or decision gates changed;
6. update `VALIDATION_PROTOCOL.md` if exact validation anchors/examples changed;
7. update Control-v2 state/action metadata if theorem frontier or control anchor changed;
8. update root/RHRC README and audit records when the public critical path changed;
9. update obstruction/dead-route/countermodel ledgers when reusable blockers/falsifiers changed;
10. leave historical settlements untouched except for explicit authority banners when necessary.

## Validated import-closure law

Repository presence, PR inclusion, merge inclusion and no-placeholder scanning are weaker states than Lean elaboration.

A theorem may be treated as compiler-validated project authority only when its declaration is in the exact compiler-tested transitive import closure or its module was separately compiled by an authoritative successful gate. Production claim promotion may require theorem-specific `#check` / `#print axioms` coverage in addition to compilation.

Relevant historical examples:

- PR #103: merged but unimported theorem file is not compiler authority.
- PR #110: compiler validity and machine claim promotion are separate checks.
- PR #117: hardened Control v2 without changing theorem declarations.
- PR #129: source-explicit cubic defect and cross-parity transfer.
- PR #131: exact production source-moment decomposition.
- PR #134: denominator-free kernel/source transport and direct zero-shift transfer.
- PR #136: absolute canonical source energy and exact production channel decomposition.
- PR #137: exact canonical source pairing, one-step determinant reduction and global sign-failure endpoint.

## Current transition after PR #137

The newest current-priority delta is `RESEARCH_LEADS_POST_137_DELTA.md`. Older deltas remain historical evidence.

Current route:

```text
PROVED THROUGH #137
  absolute source energy
  exact source pairing
  one-step determinant
  conditional domination sufficiency
  off-line zero -> domination failure -> q_c<0 OR exists Δ<0

NEXT THEOREM
  canonical shell-energy + determinant nonnegativity under the exact
  first-bad-compatible source hypotheses

OPTIONAL SIMPLIFIER
  A4R log-lift dense regular-aperture selection
```

Permanent firewalls include:

```text
conditional domination sufficiency != domination theorem
domination failure witness != contradiction
source decomposition != source sign
termwise source-atom sign != full-source sign
generic structure != canonical arithmetic source
D algebraic != D unitary/isometric
positive predecessor != positive successor by itself
root uniqueness != root exclusion
```

## Claim rule

Documentation may explain implications but may not promote a claim beyond the exact theorem surface.

Use labels consistently:

- **PROVED** — exact statement established by Lean/CI;
- **DERIVED** — straightforward consequence of proved results, not separately formalized;
- **LEAD / HYPOTHESIS** — mathematically motivated route worth testing;
- **EXPERIMENTAL SIGNAL** — numerical/discovery evidence only;
- **OPEN** — not established.

RH remains OPEN until the exact terminal theorem is proved and claim-validated.
