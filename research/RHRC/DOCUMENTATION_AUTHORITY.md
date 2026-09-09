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

### Current synchronized anchors after theorem PR #134

```text
live main after theorem PR #134 = 7f1fec480d1ccbff04a456ab937accf7b23cc1af
live main tree = c142efa141036331d139c532d06e7a976c5b50c2

theorem-state anchor = PR #134 merge 7f1fec480d1ccbff04a456ab937accf7b23cc1af
validated theorem head = 753ee53a7fc08bd3be9a5a0f37417629122395f9
validated theorem tree = c142efa141036331d139c532d06e7a976c5b50c2
RHRC #870 = SUCCESS
Permansson #643 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12

RH = OPEN
```

PR #134 is theorem-bearing. It theoremizes the denominator-free kernel/source transport, direct zero-shift cross-parity transfer, zero-shift Gamma overlap formula, and `Gamma0*mu(z)=0` whole-kernel compatibility. Theorem authority therefore advances from #131 to #134.

PR #117 remains the Control-v2 semantic anchor because current routing updates change theorem/frontier data, not the controller's authority model or algorithms.

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
6. update Control-v2 state/action metadata if theorem frontier or control anchor changed;
7. update root/RHRC README and audit records when the public critical path changed;
8. update obstruction/dead-route/countermodel ledgers when reusable blockers/falsifiers changed;
9. leave historical settlements untouched except for explicit authority banners when necessary.

## Validated import-closure law

Repository presence, PR inclusion, merge inclusion and no-placeholder scanning are weaker states than Lean elaboration.

A theorem may be promoted only when its declaration is in the exact compiler-tested transitive import closure or its module was separately compiled by an authoritative successful gate. Production claim promotion may require theorem-specific `#check` / `#print axioms` coverage in addition to compilation.

Relevant historical examples:

- PR #103: merged but unimported theorem file is not compiler authority.
- PR #110: compiler validity and machine claim promotion are separate checks.
- PR #117: hardened Control v2 without changing theorem declarations.
- PR #122: projected metric/resolvent control and zero-resonance coupling classification.
- PR #124/#125: kernel/range zero-shift geometry and strict endpoint sign.
- PR #127/#128: exact shell response, signed regular response and canonical resonant pole.
- PR #129: source-explicit cubic defect and cross-parity transfer.
- PR #131: exact production source-moment decomposition.
- PR #132/#133: documentation/control synchronization only; no theorem authority expansion.
- PR #134: exact denominator-free kernel/source transport and direct zero-shift transfer; theorem authority advances.

## Current transition after PR #134

The newest current-priority delta is `RESEARCH_LEADS_POST_134_DELTA.md`. Older post-#132/#131 deltas remain historical evidence.

Current route:

```text
PROVED THROUGH #134
  denominator-free whole-kernel source transport
  direct zero-shift cross-parity transfer
  Gamma0*mu(z)=0 on the full even predecessor kernel

NEXT THEOREM
  E4-A4b1 absolute canonical source-energy decomposition

DECISIVE OPEN TARGET
  E4-A4b2 canonical one-step domination/coercivity in both parities

OPTIONAL SIMPLIFIER
  E4-A4R log-lift dense regular-aperture selection
```

Permanent firewalls include:

```text
Re S0<0 != contradiction by itself
Re sigma0<0 != contradiction by itself
canonical 1/(-lam) pole != contradiction
D algebraic != D unitary/isometric
Gamma0*mu(z)=0 != either factor separately zero
source decomposition != source sign/nonzeroness
factorwise transfer nonvanishing is not structural
shift-invariant transfer data != absolute spectral sign
positive-definite predecessors != positive successor
root uniqueness != root exclusion
```

## Claim rule

Documentation may explain implications but may not promote a claim beyond the exact theorem surface.

Use labels consistently:

- **PROVED** — exact statement established by Lean/CI;
- **DERIVED** — straightforward consequence of proved results, not yet separately formalized;
- **LEAD / HYPOTHESIS** — mathematically motivated route worth testing;
- **EXPERIMENTAL SIGNAL** — numerical/discovery evidence only;
- **OPEN** — not established.

RH remains OPEN until the exact terminal theorem is proved and claim-validated.
