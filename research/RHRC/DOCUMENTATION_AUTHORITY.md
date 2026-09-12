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
live main after merged PR #150 = fb92d5749d6f7a65cfc9129d49d8213219c059db
live main tree = 999ef44d44855cdffd5be5843e9f072867c0a7a8

theorem-state anchor = PR #150 merge fb92d5749d6f7a65cfc9129d49d8213219c059db
validated theorem head = b1be9eca5f544d4356ea88089c0f7264f75d2220
validated theorem tree = 999ef44d44855cdffd5be5843e9f072867c0a7a8
RHRC #971 / run 34690959720 = SUCCESS
Permansson #744 / run 34690959699 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

PR #150 is theorem-bearing and advances theorem authority beyond #148. This documentation/control synchronization changes research/control metadata only; it does not add theorem authority beyond #150.

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
- dead-route and obstruction records when reusable classifications change;
- claim/route registries only when their own formal state actually changes;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or research frontier change;
- `control_v2/ACTION_REGISTRY.json` when executable research priority or first-break specification changes;
- Control-v2 regression tests and workflow smoke locks when their intentionally hard-coded state changes.

Dated deltas and external reviews are historical evidence. Do not rewrite older deltas to look current; add a newer delta and update current-priority pointers.

Large accumulated historical ledgers should not be destructively rewritten merely to manufacture currentness. When the reusable history remains valid, preserve it and place additive new state in the newest dated delta / diagnostics record, with living SSOTs pointing there.

## Theorem-state versus control-plane anchors

The repository keeps distinct anchors:

- **theorem-state anchor** — latest meaningful theorem-bearing merge whose compiled Lean surface defines current mathematical authority;
- **control-plane semantic anchor** — latest meaningful merged green research-control/assurance semantics.

PR #150 advances theorem authority because it compiler-validates assembled production source/predecessor holomorphy, algebraic deck-forced determinant nonidentity, analytic open-interval predecessor regularity, cell-minimal regular first-bad selection, and the exact regular negative canonical source-channel endpoint.

PR #117 remains the Control-v2 semantic anchor because #150 does not change the controller's capability/authority model.

A documentation/control PR that updates the theorem anchor to #150 does not itself create theorem authority.

## Current transition after PR #150

Newest project synthesis:

`RESEARCH_LEADS_POST_150_REGULARIZATION_CLOSED_ARITHMETIC_FRONTIER_DELTA.md`

External-review provenance:

`external_reviews/ASTRA_POST_150_ARITHMETIC_FRONTIER_ASSESSMENT_2026_09_12.md`

Post-#150 diagnostics/falsification memory:

`countermodels/POST_150_ARITHMETIC_DIAGNOSTICS_2026_09_12.md`

Current route:

```text
PROVED THROUGH #150
  off-line zero
  -> sufficiently-large finite badness
  -> whole-cell least bad size
  -> persistent negative witness
  -> actual regular predecessor selection
  -> unique zero-shift preimage
  -> exact canonical source-channel energy < 0

NOW
  retain full first-bad ancestry
  -> exact pole/prime discrepancy identity
  -> boundary-flat Taylor annihilation
  -> Riesz-smoothed discrepancy identities
  -> interval-certified falsification
  -> independent selected-residual nonnegativity theorem

AFTER
  contradiction with #150 negative certificate
  -> negative-root exclusion
  -> outside-strip/trivial-zero seam
  -> explicit Mathlib RiemannHypothesis wrapper.
```

Universal one-step domination remains a broad fallback, not the immediate reduction.

## Permanent firewalls

```text
supporting theorem green != machine claim promotion
regular predecessor != positive successor
open-interval regular selection != separately theoremized dense-set declaration
nonnegative + regular predecessor -> positive definite is DERIVED unless packaged
negative exact source-channel energy != contradiction
external exact discrepancy != Lean theorem
boundary-flat Taylor algebra != arithmetic sign
Riesz smoothing != arithmetic sign
coth aperture coordinate != log-cover deck coordinate
numerical falsification != theorem
modified/generic source countermodel != zeta counterexample
negative-root exclusion != terminal Mathlib RH wrapper without the final seam
```

## Claim vocabulary

- **PROVED** — exact statement established by Lean/CI;
- **DERIVED** — mathematical consequence not separately theorem-locked;
- **LOCAL LEAN CHECK** — standalone/local compilation evidence not merged into theorem authority;
- **EXTERNAL DERIVED** — exact/symbolic reasoning supplied externally and not yet repository-theoremized;
- **LEAD / HYPOTHESIS** — motivated route with unclosed obligations;
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only;
- **OPEN** — not established.

RH remains OPEN until the exact terminal theorem is proved and claim-validated.
