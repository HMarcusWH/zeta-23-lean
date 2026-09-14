# RHRC documentation authority and update law

This file defines which documentation is authoritative and how to prevent research-state drift after rapid theorem and discovery changes.

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

## Three-anchor model

### 1. Theorem-state anchor

```text
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS
```

This remains the compiler-validated mathematical authority until a later theorem-bearing PR passes the same gates.

### 2. Research-evidence anchor

```text
latest merged research PR = #174
validated research head = 2d9fc5a5f7d552afb893c871fe84c9ed61a60ac0
merged research commit = 946788f09c871de5133e2a8c8f5c94d7d69b521d
research tree = 2a22b83c4d5903158c036d38420d9ae79b7726f2
RHRC #1070 = SUCCESS
Permansson #843 = SUCCESS
```

This records the newest green research/discovery state. It does **not** upgrade executable identities, floating searches, Arb finite-point/interval certifications, or finite-difference diagnostics into Lean theorem authority.

### 3. Control-plane semantic anchor

```text
control-plane semantic anchor = PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
```

This changes only when controller capability/authority semantics change, not merely when research routing metadata is refreshed.

## Dynamic live-head rule

Do **not** freeze a mutable documentation merge as a permanent `live main` string inside long-lived authority prose. A docs or research merge moves `main` without changing theorem authority.

When an exact current `main` SHA is needed for execution or handover, record it in the time-specific execution document, PR description, or dated research delta.

## Living SSOT update law

Update these when their underlying state changes:

- root `README.md`, `FORK_NOTES.md`, `AUDIT.md`;
- `research/RHRC/README.md`;
- active route README;
- `research/RHRC/RESEARCH_LEADS.md`;
- newest dated research delta;
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md` when validation anchors/gates change;
- obstruction/dead-route ledgers when reusable classifications change;
- claim/route registries only when their own formal or explanatory state changes;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or descriptive research state change;
- `control_v2/ACTION_REGISTRY.json` when routing priority, surviving objections, or first-break specification changes;
- retro aliases/regression tests when intentionally hard-coded research vocabulary changes.

Historical dated deltas are not rewritten to look current.

## Current synchronized state

### Theorem authority through #163

PR #163 compiler-validates the exact mixed quadratic-normal source pairing, the seventh mixed jet `-2*(2*pi)^6*M4`, finite-prime sampling of the same observable, the squared-jet Riesz-8/Riesz-9 boundary, the retained even-shifted specialization, and scoped cross-parity Gamma nonvanishing.

No later research PR changes those theorem declarations.

### Research progression #165-#174

```text
#165 exact executable S8 audit
     -> broad finite positive evidence
     -> positivity alone not a contradiction

#166 theorem-aligned shifted-state executable
     -> generalized H-lambda G resolvent
     -> near-critical Q16/N3/K4/odd family isolated

#167 Q16 full-cell attack
     -> no floating negative point
     -> direct whole-cell Arb 256/256 UNRESOLVED
     -> brute dependency-heavy matrix subdivision rejected

#168 boundary-flat threshold jet
     -> odd order 7 ~ M3^2
     -> even order 9 ~ M4^2
     -> exact threshold + 18/18 two-sided Arb points positive

#170 theorem-aligned one-step Schur visibility/background audit
     -> [W|c] pivot aligned with selected residual
     -> q17 direction finite-certified Schur-visible
     -> entering atom raises pivot at checked offsets
     -> q-removed background finite difference negative

#172 threshold-to-threshold production barrier audit
     -> current-q entry lift finite-certified with both signs
     -> q13/N2/K3/even strongest near-critical target

#174 exact q13 2x2 scalar-barrier audit
     -> predecessor dimension 1, successor dimension 2
     -> H1 <-> a>0
     -> Delta_2=a*d-b^2
     -> pivot sign = determinant sign in H1
     -> physical Q=13/14/15 scalar continuations checked
     -> direct 384-bit adaptive scalar interval audit remains
        100% UNRESOLVED in every physical subcell
```

The newest project synthesis is:

`RESEARCH_LEADS_POST_174_Q13_SCALAR_DEPENDENCY_FRONTIER_DELTA.md`.

The previous post-green synthesis is:

`RESEARCH_LEADS_POST_172_Q13_EVEN_SCALAR_BARRIER_DELTA.md`.

## Current route

```text
PROVED THROUGH #163
  off-line zero
  -> retained regular cell-minimal first-bad certificate
  -> exact negative canonical source channel
  -> exact finite pole-prime discrepancy
  -> legal Riesz engine and transformed negativity
  -> same-state shifted source/Riesz composition
  -> mixed quadratic-normal seventh jet
  -> exact finite-prime sampling of same observable
  -> exact R8-R9 squared-jet boundary

RESEARCHED THROUGH #174
  endpoint scalar audited
  theorem-aligned shifted finite state audited
  Q16 near-critical cell isolated
  full-matrix interval representation falsified as current method
  prime-entry threshold moment jet identified
  theorem-aligned [W|c] Schur pivot reconstructed
  threshold-to-threshold production dynamics tested
  arithmetic entry lift found sign-indefinite
  q13/N2/K3/even reduced exactly to a 2x2 scalar barrier
  direct scalar interval subdivision also found dependency-limited

NOW
  FB-05 analytic/dependency-reduced scalar enclosure frontier
  -> preserve a(L), Delta_2(L), odd-N2 ancestry
  -> change representation/enclosure mathematics
  -> benchmark against production evaluator
  -> only then add derivative/Taylor/Newton machinery if useful
  -> theoremize only a genuinely independent generalizable restriction
```

## Claim firewall

Research green is not theorem promotion. The #174 finite scalar audit does not prove q13 positivity, negativity, zero contact, a universal derivative law, a global threshold barrier, or first-bad exclusion.

Even a future full q13-cell positivity certificate would be a finite method/structure result unless its proof yields a theorem that applies to the arbitrary retained first-bad state forced by #153/#161.

The formal first break remains FB-05 and the terminal claim remains `RH_OPEN`.

**RH remains OPEN.**
