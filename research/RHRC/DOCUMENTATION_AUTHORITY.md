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

External reviews and numerical discovery are evidence for routing, not theorem authority. Control-v2 route certificates are diagnostic only.

A green but unmerged PR is branch evidence. A merged Lean file is theorem authority only when its declarations lie in an exact successful authoritative compiler/import closure or were explicitly compiled by such a gate.

## Current synchronized anchors

```text
live main after merged PR #159 = 63862cd80501754c6c6599ffea09b874a327dae4
live main tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233

latest theorem-bearing PR = #159
validated theorem head = b2a064ad5d1f0acbd93309a9257c5661cfa3ec28
validated theorem tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233
RHRC #1021 / run 34736245287 = SUCCESS
Permansson #794 / run 34736245311 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

The validated #159 PR head and merged main are distinct commits with the same theorem tree. Documentation must distinguish current live main, latest theorem-bearing merge, exact validated head/tree, and control-plane semantic anchor.

A later docs-only merge may move live `main` without changing theorem authority.

## Living SSOTs

Update these when their underlying state changes:

- root `README.md`, `FORK_NOTES.md`, `AUDIT.md`;
- `research/RHRC/README.md`;
- active route README;
- `research/RHRC/RESEARCH_LEADS.md`;
- newest dated research delta;
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md` when validation anchors/gates change;
- obstruction/dead-route ledgers only when reusable classifications change;
- claim/route registries only when their own formal state changes;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or frontier change;
- `control_v2/ACTION_REGISTRY.json` when priority or first-break specification changes;
- retro aliases, regression tests and workflow smoke locks when intentionally hard-coded state changes.

Historical dated deltas are not rewritten to look current.

## Theorem-state versus control-plane anchors

- **theorem-state anchor** — latest meaningful theorem-bearing merge whose compiled surface defines current mathematical authority;
- **validated theorem head** — exact PR head checked by authoritative CI;
- **theorem tree** — tree shared by validated head and merged theorem-bearing state when applicable;
- **control-plane semantic anchor** — latest meaningful green controller capability/authority semantics.

PR #159 advances theorem authority because it compiler-validates the exact complex first source-energy jet, a general moment-prefix odd-jet theorem, exact seventh/ninth leading-moment formulas, a generic signed Riesz boundary recurrence for the pole-prime and complete transformed channels, and the retained first-bad R6->R7 / even R8->R9 boundary decompositions.

PR #117 remains the Control-v2 semantic anchor because #159 changes mathematical state, not controller authority/capability semantics.

This docs/control synchronization records #159; it does not create theorem authority.

## Current transition after PR #159

Newest project synthesis:

`RESEARCH_LEADS_POST_159_RIESZ_CROSS_PARITY_FRONTIER_DELTA.md`

Historical predecessor:

`RESEARCH_LEADS_POST_157_PRODUCTION_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`

Current route:

```text
PROVED THROUGH #159
  off-line zero
  -> retained regular cell-minimal first-bad certificate
  -> exact negative canonical source channel
  -> exact finite pole-prime discrepancy
  -> legal production Riesz 6 / even 8
  -> retained transformed negativity
  -> general moment-prefix odd-jet law
  -> exact seventh/ninth leading-moment formulas
  -> generic signed complete-channel Riesz boundary recurrence
  -> retained R6->R7 / even R8->R9 moment-square boundary decompositions

NOW
  compose #159 with existing negative-shift cross-parity source transfer
  on the same even negative secular trial
  -> expose both-parity predecessor nonnegativity from global first-bad ancestry
  -> derive opposite-parity-bad OR explicit source-moment-nonzero obstruction
  -> falsify stronger arithmetic consequences before sign-theorem investment

NEXT LEAD
  mixed quadratic-normal source-pairing jet
  -> expected seventh jet proportional to M4
  -> connect linear source defect to quadratic Riesz M4^2 boundary

AFTER
  independent contradiction-producing arithmetic restriction
  -> same-state contradiction
  -> negative-root exclusion
  -> outside-strip/trivial-zero seam
  -> explicit Mathlib RiemannHypothesis wrapper
```

## Post-#159 classification correction

Every living summary must now reflect:

```text
generic signed Riesz boundary recurrence
  DERIVED/OPEN after #157
  -> PROVED / #159

exact seventh/ninth self-energy leading-moment formulas
  DERIVED/OPEN after #157
  -> PROVED / #159

retained R6->R7 / even R8->R9 boundary decompositions
  OPEN before #159
  -> PROVED / #159

same-state shifted-root Riesz x cross-parity source composition
  -> OPEN / NEXT

mixed quadratic-normal source-pairing seventh-jet -> M4
  -> DERIVED / OPEN IN LEAN

independent contradiction-producing arithmetic restriction
  -> OPEN
```

Do not confuse the proved #159 self-energy ninth derivative with the unproved mixed source-pairing seventh derivative.

## Permanent firewalls

```text
supporting theorem green != machine claim promotion
regular predecessor != positive successor
retained transformed negative energy != contradiction
exact discrepancy / Riesz identity != arithmetic sign
R8/R9 retained statements != parity-unconditional theorem
#159 seventh/ninth self-energy jets != mixed source-pairing jet theorem
Riesz smoothing != pointwise sign
pointwise smoothed-integrand positivity remains falsified
no division by alpha/Gamma/overlap/source moment without a theorem
D remains algebraic, not unitary/isometric
numerical falsification != theorem
interval-certified finite evidence != Lean theorem authority
modified/generic source countermodel != zeta counterexample
negative-root exclusion != terminal Mathlib RH wrapper without final seam
```

## Claim vocabulary

- **PROVED** — exact statement established by Lean/CI;
- **DERIVED** — direct consequence not separately theorem-locked;
- **LOCAL LEAN CHECK** — standalone/local compilation outside merged theorem authority;
- **EXTERNAL DERIVED** — exact/symbolic reasoning not yet repository-theoremized;
- **LEAD / HYPOTHESIS** — motivated route worth testing;
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only;
- **OPEN** — not established.

RH remains OPEN until the exact terminal theorem is proved and claim-validated.
