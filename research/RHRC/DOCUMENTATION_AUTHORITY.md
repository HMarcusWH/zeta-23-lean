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
live main after merged PR #161 = ef29b45de683962122c1e898ed31bf9417757125
live main tree = b080572e87068889a72b4e612f99ddf0bd67f482

latest theorem-bearing PR = #161
validated theorem head = 188407fb02a37de2e380ede3b60e140953b01441
validated theorem tree = b080572e87068889a72b4e612f99ddf0bd67f482
RHRC #1026 = SUCCESS
Permansson #799 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

The validated #161 PR head and merged main are distinct commits with the same theorem tree. Documentation must distinguish current live main, latest theorem-bearing merge, exact validated head/tree, and control-plane semantic anchor.

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

PR #161 advances theorem authority because it compiler-validates: negative-eigenmode -> `ParityBad`; first-bad predecessor nonnegativity for either parity; exact canonical/source-channel negativity on a genuine shifted secular-root trial; strict even Riesz-8 negativity and the exact Riesz-9/M4 boundary inequality on that same shifted trial; opposite-parity secular nonvanishing under opposite-parity goodness; the retained odd-secular = Gamma * explicit-source identity at an even retained root; odd-good -> nonzero explicit production source moment; and the headline odd-successor-bad OR explicit-source-moment-nonzero fork.

PR #117 remains the Control-v2 semantic anchor because #161 changes mathematical state, not controller authority/capability semantics.

This docs/control synchronization records #161; it does not create theorem authority.

## Current transition after PR #161

Newest project synthesis:

`RESEARCH_LEADS_POST_161_SAME_STATE_RIESZ_SOURCE_RIGIDITY_DELTA.md`

Historical predecessor:

`RESEARCH_LEADS_POST_159_RIESZ_CROSS_PARITY_FRONTIER_DELTA.md`

Current route:

```text
PROVED THROUGH #161
  off-line zero
  -> retained regular cell-minimal first-bad certificate
  -> exact negative canonical source channel
  -> exact finite pole-prime discrepancy
  -> legal production Riesz 6 / even 8
  -> retained transformed negativity
  -> general moment-prefix odd-jet law
  -> exact seventh/ninth leading-moment self-energy formulas
  -> generic signed complete-channel Riesz boundary recurrence
  -> retained R6->R7 / even R8->R9 moment-square boundary decompositions
  -> both-parity predecessor nonnegativity interface
  -> genuine shifted negative secular state
  -> same shifted even state has R8<0 and exact R9/M4 boundary inequality
  -> same shifted even state has odd scalar = Gamma * explicit source moment
  -> odd-good forces explicit source moment != 0
  -> odd successor bad OR explicit source moment != 0

NOW
  theoremize the mixed quadratic-normal source observable
  -> verify seventh jet proportional to M4
  -> specialize to the retained even shifted state
  -> test whether linear source information and quadratic Riesz M4^2 information produce a genuinely new canonical rigidity relation

PARALLEL
  falsify simultaneous even+odd badness in generic/rank-one controls before theorem investment
  preserve odd-selected branch as open coverage debt

AFTER
  independent contradiction-producing arithmetic restriction
  -> same-state contradiction
  -> negative-root exclusion
  -> outside-strip/trivial-zero seam
  -> explicit Mathlib RiemannHypothesis wrapper
```

## Post-#161 classification correction

Every living summary must now reflect:

```text
same-state shifted-root Riesz x cross-parity source composition
  OPEN / NEXT after #159
  -> PROVED / #161

negative eigenmode -> ParityBad
  implicit/converse-only before #161
  -> PROVED / #161

first-bad predecessor nonnegativity for arbitrary parity
  derived from ancestry before #161
  -> PROVED / #161

odd-good -> explicitCanonicalSourceMoment != 0 on retained even shifted state
  -> PROVED / #161

mixed quadratic-normal source-pairing seventh-jet -> M4
  -> DERIVED / OPEN IN LEAN

explicit source moment <-> M4 coupling
  -> OPEN

simultaneous even/odd bad exclusion
  -> OPEN

independent contradiction-producing arithmetic restriction
  -> OPEN
```

Do not confuse the proved #159 self-energy ninth derivative with the unproved mixed source-pairing seventh derivative. Do not infer `M4 != 0` from #161's nonzero explicit source moment.

## Permanent firewalls

```text
supporting theorem green != machine claim promotion
regular predecessor != positive successor
retained transformed negative energy != contradiction
exact discrepancy / Riesz identity != arithmetic sign
R8/R9 retained or shifted statements != parity-unconditional theorem
#159 seventh/ninth self-energy jets != mixed source-pairing jet theorem
explicitCanonicalSourceMoment != 0 !=> M4 != 0
M4 != 0 !=> explicitCanonicalSourceMoment != 0
simultaneous even/odd badness remains open
selected parity cannot be assumed even WLOG
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
