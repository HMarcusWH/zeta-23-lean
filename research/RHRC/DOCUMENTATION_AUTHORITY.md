# RHRC documentation authority and update law

This file defines which documentation is authoritative and how to prevent research-state drift after rapid theorem changes.

## Authority order

When sources disagree:

1. **Live GitHub head + Lean compiler + CI** — exact checked object wins.
2. **Merged theorem declarations and machine registries** — theorem/claim surfaces.
3. **Active route README**.
4. **Living research-control SSOTs** — newest dated research delta plus `CURRENT_RESEARCH_PLAN.md` and current RHRC/root summaries.
5. **Current external build-plan / handover SSOT**.
6. **PR-specific settlement documents**.
7. **Historical roadmaps, audits, numerical receipts, external reviews and old implementation plans**.

External model/reviewer reports are discovery evidence unless independently reproduced or theoremized. They may reroute research when their reasoning survives audit, but they do not outrank Lean/CI or become theorem authority by being copied into the repository.

Control-v2 route certificates and retro-search receipts are diagnostic research-control artifacts only. They do not outrank theorem declarations, machine claim surfaces, active route authority or compiler evidence.

A green but unmerged PR is branch evidence, not merged repository truth. A merged source file is theorem authority only when its declarations lie in the exact successful compiler/import closure or were separately compiled by an authoritative gate.

## Current synchronized anchors

```text
live main after merged PR #140 = fa96196b5bd6ed754853b0bdacee1dbd2356022f
live main tree = 2015404927540ae79a64469af82813463694b71d

theorem-state anchor = PR #140 merge fa96196b5bd6ed754853b0bdacee1dbd2356022f
validated theorem head = 77b52cfc73dfd83d2a0ed4373befba97d77e48e5
validated theorem tree = 2015404927540ae79a64469af82813463694b71d
RHRC #882 = SUCCESS
Permansson #655 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

PR #140 is theorem-bearing and advances theorem authority. The post-#140 documentation synchronization changes research/control metadata only; it does not add theorem authority beyond #140.

## Living SSOTs

Update these when the underlying state changes:

- root `README.md`;
- `FORK_NOTES.md`;
- `AUDIT.md`;
- `research/RHRC/README.md`;
- active route README;
- newest dated research delta;
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md` when validation anchors or gate semantics change;
- dead-route and obstruction ledgers when reusable classifications change;
- claim/route registries only when their own formal state actually changes;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or research frontier change;
- `control_v2/ACTION_REGISTRY.json` when executable research priority or first-break specification changes.

Dated deltas and external reviews are historical evidence. Do not rewrite older deltas to look current; add a newer delta and update current-priority pointers.

## Theorem-state versus control-plane anchors

The repository keeps distinct anchors:

- **theorem-state anchor** — latest meaningful theorem-bearing merge whose compiled Lean surface defines current mathematical authority;
- **control-plane semantic anchor** — latest meaningful merged green research-control/assurance semantics.

PR #140 advances the theorem-state anchor because it adds and validates theorem-bearing Lean modules. PR #117 remains the Control-v2 semantic anchor because #140 does not change the controller's capability/authority model.

A documentation/control PR that updates the theorem anchor to #140 does not itself create new theorem authority.

## Control-v2 authority law

`research/RHRC/control_v2/CONTROL_BOUNDARY.json` remains the explicit capability cap. Control v2 may rank research actions and emit route/retro receipts. It may not:

- promote `CLAIM_REGISTRY.json` from a research recommendation;
- write terminal `BOUNDARY.json` status;
- infer route claim promotion;
- emit the terminal RH answer;
- promote a Lean theorem;
- convert external review, symbolic discovery or numerical clues into theorem evidence.

`runner/terminal_answer.py` remains independent of Control v2.

## Update triggers

After a post-green or independent research pass, update documentation when any of these changes:

- canonical mathematical object;
- theorem status;
- dependency order;
- dead/quarantined route classification;
- source normalization or parameter convention;
- next critical gate;
- lead classification, resurrection or falsification state;
- execution priority, route-selection gate or stop condition;
- Control-v2 theorem anchor/frontier, control-plane anchor, assurance semantics or archaeology scope.

## Post-green / post-audit synchronization sequence

1. verify exact head, declarations, assumptions, axioms and CI;
2. separate theorem facts from derived/external/experimental findings;
3. update claim/route registries only if their formal promotion state changed;
4. update active route README when route state changed;
5. add a new dated research delta when lead/status memory changed;
6. update `CURRENT_RESEARCH_PLAN.md` when execution order or decision gates changed;
7. update `VALIDATION_PROTOCOL.md` when exact validation anchors/examples changed;
8. update Control-v2 state/action metadata if theorem frontier or research priority changed;
9. update root/RHRC README and audit records when the public critical path changed;
10. update obstruction/dead-route/countermodel records when reusable blockers/falsifiers changed;
11. leave historical settlements untouched unless an explicit authority banner requires correction.

## Current transition after PR #140

Newest current-priority delta:

`RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md`

Current route:

```text
PROVED THROUGH #137
  absolute source energy
  exact source pairing
  one-step determinant
  conditional domination sufficiency
  off-line zero -> q_c<0 OR exists Delta<0

PROVED / #140
  off-line zero -> finite negative canonical witness at every sufficiently large aperture
  -> AnyParityBad at every sufficiently large aperture
  -> freshly selectable global-first-bad at every sufficiently large aperture
  predecessor det!=0 <-> injective
  regular predecessor -> unique cubic zero-shift preimage
  frozen prime-cell equality
  threshold atom vanishing
  exact real-axis -log(L) scalar extraction

DERIVED POST-#140 PLANNING CORRECTION
  choose a frozen cutoff cell first;
  obtain a finite witness there;
  regularize only the finitely many predecessor sizes up to that witness size;
  preserve negativity locally and reselect first-bad.

NEXT THEOREM
  fixed-cell finite regular-aperture selection:
  continuity + full production predecessor analyticity/log-cover +
  fixed-block determinant nonidentity + finite simultaneous avoidance.

AFTER
  regular source countercertificate with unique A x0=b
  -> independent canonical Schur-energy sign on u0=c-x0.

BROAD FALLBACK
  universal canonical one-step domination if an independent arithmetic
  mechanism is discovered.
```

The countable all-size Baire route is not classified dead; it is a fallback that should not be built unless the finite-cell theorem fails for a specific theoremized reason.

## Permanent firewalls

```text
aperture freedom != dense regularity
regular predecessor != positive successor
conditional domination sufficiency != domination theorem
universal domination restatement != research reduction
regular first-bad negative trial != contradiction
source decomposition != source sign
external exact check != Lean theorem
high-precision numerical agreement != interval proof
modified-source countermodel != zeta counterexample
D algebraic != D unitary/isometric
root uniqueness != root exclusion
```

## Claim vocabulary

- **PROVED** — exact statement established by Lean/CI;
- **DERIVED** — mathematical consequence not separately theorem-locked;
- **LEAD / HYPOTHESIS** — motivated route with unclosed obligations;
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only;
- **OPEN** — not established.

RH remains OPEN until the exact terminal theorem is proved and claim-validated.
