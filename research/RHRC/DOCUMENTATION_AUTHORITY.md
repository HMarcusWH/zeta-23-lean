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

Living docs must distinguish three different kinds of authority.

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
latest merged research PR = #172
validated research head = 4c857cd031497d895232a18a4bfb9a094d9facae
merged research commit = a31bb0bb7f025d7727dd3f224c705af797f64a19
research tree = c64b098c3159d739fa15eeaa96e35693615873d7
RHRC #1063 = SUCCESS
Permansson #836 = SUCCESS
```

This records the newest green research/discovery state. It does **not** upgrade executable identities, floating searches, Arb finite-point certifications, quadrature diagnostics, or finite-difference enclosures into Lean theorem authority.

### 3. Control-plane semantic anchor

```text
control-plane semantic anchor = PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
```

This changes only when controller capability/authority semantics change, not merely when research routing metadata is refreshed.

## Dynamic live-head rule

Do **not** freeze a mutable documentation merge as a permanent string such as

```text
live main after PR #X = <sha>
```

inside long-lived authority prose unless the exact historical commit is itself the intended object of record.

A docs or research merge moves `main` without changing theorem authority. Therefore living docs should say:

```text
Live GitHub head is authoritative dynamically.
Theorem authority = theorem-state anchor.
Latest research evidence = research-evidence anchor.
Control semantics = control-plane semantic anchor.
```

When an exact current `main` SHA is needed for an execution or handover, record it in the time-specific execution document, PR description, or dated research delta.

## Living SSOTs

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

PR #163 compiler-validates:

```text
exact complex mixed quadratic-normal source pairing
h^(7)(0) = -2*(2*pi)^6*M4 on even boundary-flat carriers
mixed-jet norm-square identity
finite-prime sampling of the same quadraticNormalSourceAtom
Riesz-8/Riesz-9 boundary through the squared seventh jet
retained even-shifted specialization
strict retained R9 upper bound without endpoint-scalar sign
crossParityGamma != 0 under opposite-parity goodness
```

No later research PR changes those theorem declarations.

### Research progression #165-#172

The current research-evidence layer adds, without theorem promotion:

```text
#165 exact executable S8 audit
     -> broad finite positive evidence
     -> positivity alone is not a contradiction mechanism

#166 theorem-aligned shifted-state executable
     -> generalized H-lambda G resolvent
     -> near-critical Q16/N3/K4/odd family isolated

#167 Q16 scalar-barrier attack
     -> no floating negative point
     -> direct whole-cell Arb remains 256/256 UNRESOLVED
     -> dependency-heavy full-matrix subdivision rejected as current method

#168 boundary-flat prime-entry threshold jet
     -> odd first surviving order 7 ~ M3^2
     -> even first surviving order 9 ~ M4^2
     -> exact threshold + 18/18 two-sided Arb points positive
     -> full Q17 state continues downward but remains positive

#170 theorem-aligned one-step Schur visibility/background audit
     -> [W|c] pivot aligned with post-#150 selected residual
     -> q17 direction finite-certified Schur-visible
     -> exact q17 entering atom raises pivot at checked offsets
     -> q-removed background finite difference negative at checked scales

#172 threshold-to-threshold production barrier audit
     -> genuine von-Mangoldt intervals tested across q/N/parity
     -> no sampled bad successor
     -> finite current-q entry lift is sign-indefinite
     -> q13/N2/K3/even isolated as strongest near-critical target
     -> Arb near-minimum full pivot ~= +5.84e-12
     -> Arb q13 entry lift ~= -6.38e-12
     -> channel cancellation ratios reach ~1e9-1e10
```

The newest project synthesis is:

`RESEARCH_LEADS_POST_172_Q13_EVEN_SCALAR_BARRIER_DELTA.md`.

The previous post-green synthesis is:

`RESEARCH_LEADS_POST_170_SCHUR_VISIBILITY_THRESHOLD_BARRIER_DELTA.md`.

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

RESEARCHED THROUGH #172
  endpoint scalar audited
  theorem-aligned shifted finite state audited
  Q16 near-critical scalar barrier isolated
  dependency-heavy full-matrix interval representation falsified as current method
  prime-entry threshold moment jet identified
  theorem-aligned [W|c] Schur pivot reconstructed
  q17 finite visibility/background competition isolated
  threshold-to-threshold production dynamics tested across multiple arithmetic cells
  arithmetic entry lift found sign-indefinite in finite Arb replay
  q13/N2/K3/even near-zero complete scalar isolated

NOW
  FB-05 q13/N2/K3/even 2x2 scalar determinant barrier
  -> predecessor scalar a(L)
  -> determinant Delta_2(L)=a(L)d(L)-b(L)^2
  -> H1 + successor sign reduce to a(L)>0 and Delta_2(L)>0
  -> rigorous physical Q=13/14/15 subcells over log13..log16
  -> opposite-parity/same-q controls
  -> theoremize only a genuinely independent generalizable restriction
```

## Claim firewall

Research green is not theorem promotion. The #172 finite certificates do not prove a whole-cell q13 sign, a universal arithmetic-entry sign, a global derivative law, a global threshold barrier, or first-bad exclusion.

Even a future full q13-cell positivity certificate would be a finite method/structure result unless its proof yields a theorem that applies to the arbitrary retained first-bad state forced by #153/#161.

The formal first break remains FB-05 and the terminal claim remains `RH_OPEN`.

**RH remains OPEN.**
