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
live main after merged PR #153 = 474a88d76ecd2f4eee6178685b2e8d8b104171ca
live main tree = dd69f1c612047f2d2f15a7ba158664634284b42e

theorem-state anchor = PR #153 merge 474a88d76ecd2f4eee6178685b2e8d8b104171ca
validated theorem head = b6622dadab911008c0a7238e9dc711c6f9946302
validated theorem tree = dd69f1c612047f2d2f15a7ba158664634284b42e
RHRC #994 / run 34709905190 = SUCCESS
Permansson #767 / run 34709905198 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

PR #153 is theorem-bearing and advances theorem authority beyond #150. This documentation/control synchronization changes research/control metadata only; it does not add theorem authority beyond #153.

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
- claim/route registries only when their own formal state actually changes;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or research frontier change;
- `control_v2/ACTION_REGISTRY.json` when executable research priority or first-break specification changes;
- Control-v2 regression tests and workflow smoke locks when their intentionally hard-coded state changes.

Dated deltas and external reviews are historical evidence. Do not rewrite older deltas to look current; add a newer delta and update current-priority pointers.

Large accumulated historical ledgers should not be destructively rewritten merely to manufacture currentness. In this synchronization the old full per-entry research-leads ledger is preserved byte-for-byte as

```text
RESEARCH_LEADS_LEGACY_FULL_THROUGH_110.md
```

while `RESEARCH_LEADS.md` becomes a compact living index with a current authority block. `OBSTRUCTION_LEDGER.md` remains the accumulated blocker ledger but its authority header and post-#153 additive classifications are current.

## Theorem-state versus control-plane anchors

The repository keeps distinct anchors:

- **theorem-state anchor** — latest meaningful theorem-bearing merge whose compiled Lean surface defines current mathematical authority;
- **control-plane semantic anchor** — latest meaningful merged green research-control/assurance semantics.

PR #153 advances theorem authority because it compiler-validates:

```text
RegularCellMinimalFirstBadCertificate
RegularCellMinimalNegativeEnergyCertificate
exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero
contDiff_sourceAtomRealEnergy
matrixRealEnergy_pole_sub_prime_eq_discrepancy
canonicalSourceChannelEnergy_eq_discrepancy
```

among the surrounding exact bridge declarations.

PR #117 remains the Control-v2 semantic anchor because #153 does not change the controller's capability/authority model.

A documentation/control PR that updates the theorem anchor to #153 does not itself create theorem authority.

## Current transition after PR #153

Newest project synthesis:

`RESEARCH_LEADS_POST_153_CERTIFICATE_DISCREPANCY_GREEN_JET_FRONTIER_DELTA.md`

Historical external-review provenance:

`external_reviews/ASTRA_POST_150_ARITHMETIC_FRONTIER_ASSESSMENT_2026_09_12.md`

Historical post-#150 diagnostics/falsification memory:

```text
countermodels/POST_150_ARITHMETIC_DIAGNOSTICS_2026_09_12.md
countermodels/POST_150_SELECTED_RESIDUAL_SCOPE_AUDIT_2026_09_12.md
```

Current route:

```text
PROVED THROUGH #153
  off-line zero
  -> retained regular cell-minimal first-bad certificate
  -> predecessor nonnegativity + regularity + exact A x0=b
  -> exact canonical source-channel energy < 0
  -> exact finite pole-prime discrepancy normal form

NOW
  determine the actual source-energy endpoint jets
  -> generic iterated primitives / repeated integration by parts
  -> instantiate only to theorem-backed order
  -> interval-certified transformed-arithmetic falsification
  -> independent selected-residual nonnegativity theorem

AFTER
  same-state contradiction
  -> negative-root exclusion
  -> outside-strip/trivial-zero seam
  -> explicit Mathlib RiemannHypothesis wrapper.
```

Universal one-step domination remains a broad fallback, not the immediate reduction.

## Post-#153 classification correction

The following status changes must be reflected in every living summary:

```text
full retained first-bad certificate
  OPEN / LEAD after #150
  -> PROVED / #153

exact pole-prime discrepancy identity
  EXTERNAL DERIVED after #150
  -> PROVED / #153

order-seven generic source-energy zero
order-nine even-parity source-energy zero
sixth/eighth-order Riesz formulas
  remain DERIVED / LEAD
  -> NOT promoted by #153
```

The key firewall is that coefficient/function-level boundary-flat moment information does not automatically prove the same high-order zero for `sourceAtomRealEnergy`. The admissible repeated-IBP order is a theorem output.

## Permanent firewalls

```text
supporting theorem green != machine claim promotion
regular predecessor != positive successor
negative exact source-channel energy != contradiction
exact discrepancy identity != discrepancy sign
C-infinity source-atom energy != high-order endpoint flatness
boundary-flat moments != automatically order-seven/order-nine source-energy jets
Riesz smoothing != arithmetic sign
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
