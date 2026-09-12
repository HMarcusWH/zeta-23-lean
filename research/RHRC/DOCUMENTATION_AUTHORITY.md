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
live main after merged PR #155 = 7bd3f1028d42272fcadc347c43371b992d9c0bd7
live main tree = 9a4f21ed55aa0cbdf54527164c2f5f96912c65de

latest theorem-bearing PR = #155
validated theorem head = ecfd075c07923e6fc80ab1a5b4f2d49c724f5577
validated theorem tree = 9a4f21ed55aa0cbdf54527164c2f5f96912c65de
RHRC #1005 / run 34720946254 = SUCCESS
Permansson #778 / run 34720946242 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

The validated #155 PR head and merged main are different commits with the same theorem tree. Documentation must distinguish:

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

PR #155 advances theorem authority because it compiler-validates the new discrepancy integrability, generic Riesz smoothing, source oddness/all-even-jets and even-parity `M3=0` packages.

PR #117 remains the Control-v2 semantic anchor because #155 changes mathematical state, not the controller's capability/authority model.

A documentation/control PR that updates the theorem anchor to #155 does not itself create theorem authority.

## Current transition after PR #155

Newest project synthesis:

`RESEARCH_LEADS_POST_155_RIESZ_D_TRANSPORT_FRONTIER_DELTA.md`

External-review provenance:

`external_reviews/ASTRA_POST_155_RH_PATH_ASSESSMENT_2026_09_13.md`

Exact finite route-falsification memory:

`countermodels/POST_155_RIESZ_POINTWISE_SIGN_COUNTERMODELS_2026_09_13.md`

Current route:

```text
PROVED THROUGH #155
  off-line zero
  -> retained regular cell-minimal first-bad certificate
  -> exact canonical source-channel energy < 0
  -> exact finite pole-prime discrepancy normal form
  -> legal generic conditional Riesz representation
  -> source oddness + all even endpoint jets + even M3=0

NOW
  complex production D-transport
  -> moment-prefix recursion
  -> production odd endpoint jets
  -> exact Riesz order 6 / even order 8
  -> retained transformed-negative first-bad wrapper

AFTER
  specific arithmetic-mechanism falsification on the complete transformed residual
  -> independent nonnegative complete-residual theorem
  -> same-state contradiction
  -> negative-root exclusion
  -> outside-strip/trivial-zero seam
  -> explicit Mathlib RiemannHypothesis wrapper.
```

Universal one-step domination remains a broad fallback, not the immediate reduction.

## Post-#155 classification correction

The following status changes must be reflected in every living summary:

```text
finite discrepancy integrability
  OPEN after #153
  -> PROVED / #155

anchored primitives + legal generic repeated IBP / conditional Riesz
  OPEN after #153
  -> PROVED / #155

source-coordinate oddness + all even endpoint jets
  OPEN after #153
  -> PROVED / #155

even parity M3=0
  OPEN after #153
  -> PROVED / #155

complex D-transport
production odd jets
unconditional Riesz order 6/8
retained transformed-negative wrapper
  remain DERIVED / OPEN IN LEAN
```

The new key firewall is that a real contraction derivative identity is not automatically the complex production source-energy theorem.

## Permanent firewalls

```text
supporting theorem green != machine claim promotion
regular predecessor != positive successor
negative exact source-channel energy != contradiction
exact discrepancy identity != discrepancy sign
generic legal Riesz smoothing != unconditional production order 6/8
real contraction identity != complex production source-energy identity
Riesz smoothing != arithmetic sign
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
