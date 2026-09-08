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
theorem-state anchor = PR #129 merge e1192857afed9f68fa4a13143ce690b62191b997
validated theorem head = 440be3e5b6bf05e94ae2c65b1704d52d20acc9af
control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #129 is the current merged theorem authority. PR #117 remains the latest merged green Control-v2 semantic authority because #118/#119/#121/#122/#124/#125/#127/#128/#129 changed theorem state but not controller semantics.

## Current routed frontier

`ACTION_REGISTRY.json` now routes from

```text
FIRST_BAD_RIGIDITY_E4_A4_SOURCE_EXCLUSION.
```

Primary theorem actions:

```text
E4-A4 source-moment decomposition through actual canonicalSourceMatrix
E4-A4 regular-branch canonical-source exclusion
E4-A4 resonant-branch canonical-source exclusion
E4-A4 global first-bad exclusion
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
```

The controller must therefore not route back to proving shell response, pole decomposition, or generic cross-parity transfer. Those first-breaks have been consumed by theorem authority.

## Post-#129 routing rule

### Source moment decomposition first

The highest-information theorem target is to expand

```text
evenQuadraticSourceMoment L (N+1) uPlus
```

through the production `canonicalSourceMatrix` formula.

The preferred first result is an exact identity, not an assumed sign inequality. The controller should prioritize exact source decomposition because generic structural countermodels have already shown that Hermitianity/parity/KKT/rank-one/displacement structure alone can support bad finite states.

### Regular branch source test

Use the exact package

```text
k=0
Re sigma0<0
F_- = alpha F_+ + Gamma sourceMoment(u_+)
```

and test whether the actual source formula forbids it.

Permanent firewall:

```text
source transfer != source sign/nonzeroness.
```

### Resonant branch source test

Use

```text
k!=0
(-lam)K(R_lam b)=k
F_- = alpha F_+ + Gamma sourceMoment(u_+)
```

and actual source values. The exact pole classifies resonance; it does not exclude it.

### Global exclusion

Only after both canonical branches are excluded should Control v2 route to the finite negative-root exclusion composition. No preferred root parity may be assumed. No division by `alpha`, `Gamma`, overlap or source moment is permitted without a theorem.

## Generic countermodel gate

The post-#128/#129 countermodel registry is now a first-break requirement in spirit for structural exclusion claims. Known fixtures include:

- regular nonnegative-predecessor Schur countermodel;
- exact resonant countermodel with negative spectrum;
- centered radius-3 reversal-symmetric diagonal fixtures with both-parity regular negativity, one-parity badness or genuine resonance;
- displacement-preserving diagonal perturbations.

These are experimental/synthetic regression fixtures, not zeta counterexamples.

A candidate theorem that would also rule out those fixtures without naming an additional source-specific invariant should be treated as suspect and falsified before expensive Lean work.

## E3-C routing rule

The exact root detector is theorem-identified with a real explicit scalar, so shifted-resolvent identity and strict monotonicity work remains admissible.

Permanent controller firewall:

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
  -> E4-A4 canonical-source exclusion
```

If a future theorem uses a lower predecessor floor `mu`, the diagnostic gap must use the same theorem-backed `mu` and shell-stiffness convention. A finite prefix, fitted tail or small local residual is not enough. `PRUNE` still requires a complete assured horizon certificate under the existing v1.6 rules.

## FFBBP v1.6 assurance integration

The existing RUN42C profile and `FFBBP_REFERENCE.json` remain frozen historical qualification authority. The additive `ffbbp/v16_*` modules expose v1.6 assurance contracts without inheriting RUN42C qualification:

- diagnostic vs decision commutation;
- residual horizon contracts;
- explicit witness visibility/margin/masking checks;
- fail-closed reduction assurance gates.

A small local residual is not a horizon certificate. Numerical closeness is not decision commutation.

## Retro modes

Normal archaeology searches all Git refs with commits predating the theorem anchor within the declared paths

```text
research/RHRC
Zeta23
```

and records those paths in the receipt. `ALL_REFS_BEFORE_ANCHOR_IN_DECLARED_PATHS` must not be paraphrased as “every repository byte.”

Counterfactual replay searches only history reachable from the historical anchor. External archives additionally require availability metadata and hash validation to prevent hindsight leakage.

## Dead-route law

`DEAD_ROUTES.md` remains authoritative historical failure memory. A dead/quarantined route cannot be silently resurrected; a revival record must state the original blocker, changed premise and evidence.

New post-#129 quarantines include generic structural first-bad exclusion without source values and displacement-identity-only exclusion. Source-specific theorems are a changed premise; generic repackaging is not.

## CI

`tools/run_suite.py` runs Control-v2 unit tests. The Python RHRC workflow checks out full Git history and performs a real-history Control-v2 smoke run. Router recommendations themselves are not theorem assertions; authority, completeness, leakage, exact interval coverage and assurance invariants remain CI-fatal.

Detailed current post-green research implications: `../RESEARCH_LEADS_POST_129_DELTA.md`.

**RH remains OPEN.**
