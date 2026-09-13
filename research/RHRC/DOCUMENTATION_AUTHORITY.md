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
live main after merged PR #157 = e304f07c9e83165ebf066db0d67c2cc24f8961c2
live main tree = 706dfde7f9e7b0b8403a671769d424ac7862f5e7

latest theorem-bearing PR = #157
validated theorem head = 4b517db1d4a50277d325e77e771a30fc0db5c777
validated theorem tree = 706dfde7f9e7b0b8403a671769d424ac7862f5e7
RHRC #1017 / run 34731682546 = SUCCESS
Permansson #790 / run 34731682544 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

The validated #157 PR head and merged main are different commits with the same theorem tree. Documentation must distinguish:

```text
current live main
latest theorem-bearing merge
exact validated PR head
theorem tree
control-plane semantic anchor.
```

A later docs-only merge may move live `main` without changing theorem authority. Do not encode those concepts as one hash.

## Living SSOTs

Update these when the underlying state changes:

- root `README.md`;
- `FORK_NOTES.md`;
- `AUDIT.md`;
- `research/RHRC/README.md`;
- active route README;
- `research/RHRC/RESEARCH_LEADS.md` — compact living lead index;
- newest dated research delta;
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md` when validation anchors or gate semantics change;
- `research/RHRC/OBSTRUCTION_LEDGER.md` / `DEAD_ROUTES.md` when reusable classifications change;
- countermodel registry when a new reusable falsifier is established;
- claim/route registries only when their own formal state actually changes;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or research frontier change;
- `control_v2/ACTION_REGISTRY.json` when executable research priority or first-break specification changes;
- Control-v2 retro aliases, regression tests and workflow smoke locks when their intentionally hard-coded state changes.

Dated deltas and external reviews are historical evidence. Do not rewrite older deltas to look current; add a newer delta and update current-priority pointers.

## Theorem-state versus control-plane anchors

The repository keeps distinct anchors:

- **theorem-state anchor** — latest meaningful theorem-bearing merge whose compiled Lean surface defines current mathematical authority;
- **validated theorem head** — exact PR head checked by authoritative CI;
- **theorem tree** — tree shared by the validated head and merged theorem-bearing result when applicable;
- **control-plane semantic anchor** — latest meaningful merged green research-control/assurance semantics.

PR #157 advances theorem authority because it compiler-validates the genuine complex production D-transport theorem, the boundary-flat production endpoint jets through orders 6/8, exact complete production Riesz order 6 / even order 8 representations, retained transformed negativity, and the ExceptionalZero order-6 negative wrapper.

PR #117 remains the Control-v2 semantic anchor because #157 changes mathematical state, not the controller's capability/authority model.

A documentation/control PR that updates the theorem anchor to #157 does not itself create theorem authority.

## Current transition after PR #157

Newest project synthesis:

`RESEARCH_LEADS_POST_157_PRODUCTION_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`

Historical pre-#157 synthesis:

`RESEARCH_LEADS_POST_155_RIESZ_D_TRANSPORT_FRONTIER_DELTA.md`

Exact finite route-falsification memory:

`countermodels/POST_155_RIESZ_POINTWISE_SIGN_COUNTERMODELS_2026_09_13.md`

Current route:

```text
PROVED THROUGH #157
  off-line zero
  -> retained regular cell-minimal first-bad certificate
  -> exact canonical source-channel energy < 0
  -> exact finite pole-prime discrepancy normal form
  -> genuine complex production D transport
  -> boundary-flat jets 1..6 / even jets 1..8
  -> exact complete Riesz order 6 / even order 8
  -> retained complete Riesz-6 source-channel energy < 0

NOW
  formulate a specific arithmetic mechanism for the exact complete transformed residual
  -> theorem-aligned numerical / interval falsification
  -> if a mechanism survives, prove the smallest independent nonnegative arithmetic inequality

PROMISING SUBLEAD
  generic first Riesz boundary-term recurrence
  -> exact seventh/ninth leading jets only if needed
  -> scalar endpoint-factor falsification

AFTER
  independent nonnegative complete-residual theorem
  -> same-state contradiction
  -> negative-root exclusion
  -> outside-strip/trivial-zero seam
  -> explicit Mathlib RiemannHypothesis wrapper.
```

Universal one-step domination remains a broad fallback, not the immediate reduction.

## Post-#157 classification correction

The following status changes must be reflected in every living summary:

```text
complex production D transport
  OPEN after #155
  -> PROVED / #157

production odd jets through the required R6/R8 orders
  OPEN after #155
  -> PROVED / #157

exact complete production Riesz order 6
exact complete even-parity production Riesz order 8
  OPEN after #155
  -> PROVED / #157

retained transformed-negative wrapper
  OPEN after #155
  -> PROVED / #157

exact seventh/ninth leading-jet coefficient formulas
independent complete transformed-residual nonnegative sign
  remain DERIVED/LEAD or OPEN.
```

OBS-035 and OBS-036 remain useful historical firewalls but their immediate escape requirements are consumed by #157; they must not continue to describe FB-03E/F as open.

## Permanent firewalls

```text
supporting theorem green != machine claim promotion
regular predecessor != positive successor
retained transformed negative energy != contradiction
exact discrepancy / Riesz identity != arithmetic sign
R8 retained negativity != parity-unconditional theorem
exact seventh/ninth leading-jet formulas remain open
Riesz smoothing != pointwise sign
pointwise smoothed-integrand positivity is falsified as a universal route
numerical falsification != theorem
interval-certified finite evidence != Lean theorem authority
coth aperture coordinate != log-cover deck coordinate
modified/generic source countermodel != zeta counterexample
negative-root exclusion != terminal Mathlib RH wrapper without the final seam
```

## Claim vocabulary

- **PROVED** — exact statement established by Lean/CI;
- **DERIVED** — mathematical consequence not separately theorem-locked;
- **LOCAL LEAN CHECK** — standalone/local compilation evidence not merged into theorem authority;
- **EXTERNAL DERIVED** — exact/symbolic reasoning supplied externally and not yet repository-theoremized;
- **LEAD / HYPOTHESIS** — motivated route worth testing;
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only;
- **OPEN** — not established.

RH remains OPEN until the exact terminal theorem is proved and claim-validated.
