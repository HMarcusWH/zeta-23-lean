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
latest merged research PR = #168
validated research head = 9657dad6f1e262b1fa7e08e6944aaa935feeaf33
merged research commit = 4e2c111a836f3fc95f8209485f726dc886c918e7
research tree = 881e1f05302041f56ae4b6a14f14e45d7bbc096b
RHRC #1055 = SUCCESS
Permansson #828 = SUCCESS
```

This records the newest green research/discovery state. It does **not** upgrade SymPy identities, floating searches, Arb finite-point certifications, or executable checks into Lean theorem authority.

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

### Research progression #165-#168

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
     -> brute dependency-heavy subdivision rejected as current method

#168 boundary-flat prime-entry threshold jet
     -> odd first surviving order 7 ~ M3^2
     -> even first surviving order 9 ~ M4^2
     -> exact threshold + 18/18 two-sided Arb points positive
     -> full Q17 state continues downward but remains positive
     -> isolated favorable prime-entry jet does not control full drift
```

The newest project synthesis is:

`RESEARCH_LEADS_POST_168_THRESHOLD_JET_BACKGROUND_DRIFT_DELTA.md`.

The historical predecessor remains:

`RESEARCH_LEADS_POST_163_MIXED_SOURCE_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`.

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

RESEARCHED THROUGH #168
  endpoint scalar audited
  theorem-aligned shifted finite state audited
  Q16 near-critical scalar barrier isolated
  brute whole-cell interval representation falsified as current method
  prime-entry threshold moment jet identified
  Q17 remains positive but continues downward

NOW
  FB-05 full scalar pivot/background variation
  -> dependency-reduced scalar pivot
  -> exact channel/background reconstruction
  -> prime-power threshold-kick coefficient
  -> catch-up scale / barrier test
  -> simultaneous-parity / odd-selected implications if available

AFTER
  weakest useful canonical arithmetic theorem
  -> compose with exact retained state
  -> negative-root exclusion
  -> outside-strip/trivial-zero seam
  -> explicit Mathlib RiemannHypothesis wrapper
```

## Current classification

Living summaries must reflect:

```text
same-state shifted-root Riesz x cross-parity source composition
  -> PROVED / #161

mixed quadratic-normal source seventh jet -> M4
  -> PROVED / #163

finite-prime term samples same quadraticNormalSourceAtom
  -> PROVED / #163

mixed seventh-jet squared R8-R9 boundary coupling
  -> PROVED / #163

endpoint-scalar global sign/nonvanishing
  -> OPEN

endpoint-scalar finite executable audit
  -> RESEARCH / #165

true shifted-state finite discriminator
  -> RESEARCH / #166

Q16 whole-cell floating barrier + interval-method falsification
  -> RESEARCH / #167

boundary-flat threshold moment jet
  -> EXACT EXECUTABLE / FINITE EVIDENCE / #168
  -> NOT SEPARATELY LEAN-THEOREMIZED

full scalar pivot/background inequality
  -> OPEN / ACTIVE RESEARCH FRONTIER

explicit source moment <-> M4 rigidity
  -> OPEN

simultaneous even/odd bad exclusion
  -> OPEN

odd-selected closure
  -> OPEN
```

## Permanent firewalls

```text
supporting theorem green != machine claim promotion
research PR green != theorem authority
exact executable algebra != Lean theorem
finite Arb certification != whole-cell/global theorem
absence of sampled negative state != positivity theorem
retained transformed negative energy != contradiction
exact discrepancy / Riesz identity != arithmetic sign
endpoint-scalar positivity alone != first-bad exclusion
threshold prime-entry stabilization != full canonical stabilization
explicitCanonicalSourceMoment != 0 !=> M4 != 0
M4 != 0 !=> explicitCanonicalSourceMoment != 0
finite prime samples != local derivative determination without new theorem
simultaneous even/odd badness remains open
selected parity cannot be assumed even WLOG
Riesz smoothing != pointwise sign
pointwise smoothed-integrand positivity remains falsified
UNRESOLVED interval enclosure != sign evidence
no division by alpha/Gamma/overlap/source moment without theorem
D remains algebraic, not unitary/isometric
modified/generic source countermodel != zeta counterexample
negative-root exclusion != terminal Mathlib RH wrapper
```

## Claim vocabulary

- **PROVED** — exact statement established by Lean/CI;
- **DERIVED** — direct consequence not separately theorem-locked;
- **LOCAL LEAN CHECK** — local compilation outside merged theorem authority;
- **EXACT EXECUTABLE** — symbolic/executable identity locked by research tooling, not Lean theorem authority;
- **EXTERNAL DERIVED** — exact reasoning not yet repository-theoremized;
- **LEAD / HYPOTHESIS** — motivated route worth testing;
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only;
- **RIGOROUS FINITE CERTIFICATION** — interval/Arb statement in its exact finite scope only;
- **OPEN** — not established.

RH remains OPEN until the exact terminal theorem is proved and claim-validated.