# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Purpose

Control v2 provides:

1. **Forward routing.** Rank admissible next research moves by explicit cost, information gain, falsification value, closure value, residual risk and dependency debt. Every serious route declares a first-break test.
2. **Retroactive archaeology and replay.** Search repository history using concept aliases, optionally search a normalized external archive, and support `as_of` counterfactual replay so old states cannot see future clues.

The controller answers **where to look next**, never **what is mathematically true**. Lean/CI and the machine claim surfaces retain theorem/claim authority.

## Separate theorem and control anchors

`CONTROL_STATE.json` records two distinct anchors:

```text
theorem-state anchor = PR #131 merge 436d524d0cdeb5986d76dcbb988f771d19836c55
validated theorem head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #131 is the current merged theorem authority. PR #117 remains the latest merged green Control-v2 semantic authority because #118/#119/#121/#122/#124/#125/#127/#128/#129/#131 changed theorem state but not controller semantics.

## Current routed frontier

The theorem frontier has advanced from A4a source decomposition to **E4-A4b regular-branch source testing**.

Primary theorem actions should now be read as:

```text
A4b-0 source-expanded cross-parity root interface
A4b regular-branch canonical-source exclusion
A4c resonant-branch canonical-source exclusion
A4d global first-bad exclusion
```

Parallel actions remain:

```text
E4-B parity shifted-nullity
E3-C exact real secular monotonicity / root-count control
E3-B3 generalized predecessor-floor deformation theorem
deformation-budget paper falsifier
```

## Why the frontier moved

The old E4-A3 obligations are theorem-authoritative:

```text
#127:
  T u0 is pure shell for the special decoupled zero-shift trial
  sigma0*c = T u0
  S0 = star(sigma0)<c,c>

#128:
  Re sigma0<0 at the forced negative root
  canonical kernel coordinate K
  k=K(b)=0 in the decoupled branch
  k!=0 in the resonant branch
  (-lam)K(R_lam b)=k

#129:
  cubicDefectFunctional = evenQuadraticSourceMoment
  F_- = alpha F_+ + Gamma sourceMoment(u_+)
  Gamma = exact odd trial/cubic overlap ratio
  even-root source-product specialization
  off-line zero -> source-explicit global first-bad certificate

#131:
  exact canonicalSourceMatrix pole/arch/prime split
  exact arch scalar annihilation in the active observable
  exact reduced arch diagonal/off-diagonal split
  exact finite von-Mangoldt prime atomization
  exact pole even/odd profile factorization
  odd pole profile cancellation on the even boundary-flat sector
  cubicDefectFunctional = explicitCanonicalSourceMoment
```

The controller must therefore not route back to proving shell response, pole decomposition, generic cross-parity transfer, or source-moment decomposition. Those first-breaks have been consumed by theorem authority.

## Post-#131 routing rule

### Source-expanded root interface first

The highest-information immediate theorem target is to compose

```text
evenQuadraticSourceMoment
  = explicitCanonicalSourceMoment
```

directly into the #129 cross-parity/root theorems.

The same tranche should theoremize linearity/negation/scalar covariance of the explicit moment, isolate the elementary source-atom observable

```text
omega -> quadraticNormalMatrixMoment K (sourceMatrix omega K) v,
```

and theoremize endpoint zeros at `omega=0,1`.

### Universal raw source sign is not an admissible first-break

The #131 explicit source moment is linear in the vector argument. Therefore a universal theorem claiming strict positivity/nonnegativity on the whole legal vector space is structurally the wrong target: `v -> -v` reverses the value.

Control v2 should instead rank **compositional** source tests involving the canonically oriented trial vector together with overlap / `Gamma`, root parity, or branch equations.

### Regular branch source test

Use

```text
k=0
Re sigma0<0
F_- = alpha F_+ + Gamma explicitCanonicalSourceMoment(u_+)
```

plus predecessor nonnegativity and actual pole/arch/prime source values.

Permanent firewall:

```text
source decomposition != source sign/nonzeroness.
```

### Resonant branch source test

Use

```text
k!=0
(-lam)K(R_lam b)=k
F_- = alpha F_+ + Gamma explicitCanonicalSourceMoment(u_+)
```

and actual source values. The exact pole classifies resonance; it does not exclude it.

### Global exclusion

Only after both canonical branches are excluded should Control v2 route to the finite negative-root exclusion composition. No preferred root parity may be assumed. No division by `alpha`, `Gamma`, overlap or source moment is permitted without a theorem.

## Generic countermodel gate

The post-#128/#129 countermodel registry remains a first-break requirement in spirit for structural exclusion claims. Known fixtures include regular nonnegative-predecessor Schur countermodels, exact resonant countermodels, centered reversal-symmetric diagonal fixtures, and displacement-preserving diagonal perturbations.

These are experimental/synthetic regression fixtures, not zeta counterexamples.

A candidate theorem that would also rule out those fixtures without naming an additional source-specific invariant should be treated as suspect and falsified before expensive Lean work.

## E3-C routing rule

The exact root detector is theorem-identified with a real explicit scalar, so shifted-resolvent identity and strict monotonicity work remains admissible.

```text
at most one negative root != no negative root.
```

Because an off-line zero already forces a negative root, monotonicity is supportive rather than terminal.

## Main objects

- `ACTION_REGISTRY.json` — current research actions, deterministic score inputs, first-break declarations and control requirements.
- `CONTROL_BOUNDARY.json` — physical authority cap for the controller.
- `CONTROL_STATE.json` — separate merged theorem/control anchors.
- `schemas.py` / `state.py` — typed theorem/control anchors and control state.
- `router.py` — deterministic fail-closed action ranking with explicit score formula and candidate diagnostics.
- `deformation_budget.py` — RH-native deformation-budget diagnostic with Decimal arithmetic, exact prefix coverage and assured tail certificates.
- `first_break.py` — MCM-style cheapest-decisive-falsifier ordering.
- `retro/` — vocabulary-aware Git archaeology, optional external archive ingestion/search, as-of replay and dead-route revival law.

## Deformation-budget alignment rule

The theorem ancestry is now

```text
#119 exact secular equivalence
  -> #121 explicit scalar bridge
  -> #122 mu=0 metric/resolvent control
  -> #124/#125 zero-shift branch endpoint
  -> #127 shell response
  -> #128 signed response / canonical pole
  -> #129 source-explicit parity transfer
  -> #131 exact source decomposition
  -> E4-A4b/c canonical-source branch tests
```

If a future theorem uses a lower predecessor floor `mu`, the diagnostic gap must use the same theorem-backed `mu` and shell-stiffness convention. A finite prefix, fitted tail or small local residual is not enough. `PRUNE` still requires a complete assured horizon certificate under the existing v1.6 rules.

## FFBBP v1.6 assurance integration

The existing RUN42C profile and `FFBBP_REFERENCE.json` remain frozen historical qualification authority. The additive `ffbbp/v16_*` modules expose v1.6 assurance contracts without inheriting RUN42C qualification.

A small local residual is not a horizon certificate. Numerical closeness is not decision commutation.

## Dead-route law

`DEAD_ROUTES.md` remains authoritative historical failure memory. A dead/quarantined route cannot be silently resurrected; a revival record must state the original blocker, changed premise and evidence.

Post-#131, universal raw source-moment positivity is additionally dead as a theorem strategy because the observable is linear in the vector argument. Source-sensitive composition with canonical orientation data is a changed premise and remains live.

## CI

`tools/run_suite.py` runs Control-v2 unit tests. The Python RHRC workflow checks out full Git history and performs a real-history Control-v2 smoke run. Router recommendations themselves are not theorem assertions; authority, completeness, leakage, exact interval coverage and assurance invariants remain CI-fatal.

Detailed current post-green research implications: `../RESEARCH_LEADS_POST_131_DELTA.md`.

**RH remains OPEN.**
