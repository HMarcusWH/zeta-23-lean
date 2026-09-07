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
theorem-state anchor = PR #122 merge b2d1210902d430f3cdd3c24c2961ab843469b5d6
validated theorem head = 9c8154e3ea7a5762f8e65d508dc68bb9246db869
control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #122 is the current merged theorem authority: projected predecessor symmetry/coercivity, negative-shift resolvent metric control, the real explicit secular bridge, the first root metric bound, and E4-A1 zero-resonance coupling classification are proved. PR #117 remains the latest merged green Control-v2 authority because #118/#119/#121/#122 changed theorem state but not controller semantics.

## Current routed frontier

`ACTION_REGISTRY.json` now routes from `FIRST_BAD_RIGIDITY_E4_A2`.

Primary theorem actions:

```text
E4-A2 decoupled zero-shift/range endpoint
E4-A2 resonant kernel/resolvent theorem
E3-C exact real secular monotonicity / root-count control
E4-B parity shifted-nullity from rank-at-most-one algebra
E3-B3 generalized predecessor-floor deformation theorem
negative-root exclusion only after endpoint/resonance structure is available
```

The deformation-budget paper test remains parallel diagnostic research.

## Why the frontier moved

The post-#119 representation barrier is closed:

```text
#119 exact quotient root detector
  + #121 pointwise explicit Schur bridge
  + #122 projected symmetry/realness
  -> exact real scalar representation on lam<0.
```

PR #122 also proves the E4-A1 pointwise classification

```text
Az=0 -> (<z,Bc>=0 <-> Tz=0),
```

where `A=P_W T|_W` is the projected successor predecessor block.

The controller must not simplify this to `Bc ⟂ ker A`. The actual first-bad state may lie on either branch.

## E4-A2 routing rule

### Decoupled branch

If the coupling vanishes on `ker A`, the next theorem target is

```text
Bc ⟂ ker A -> Bc ∈ range A.
```

Then obtain a solution `x0` with `A x0=Bc` and define the zero-shift secular endpoint through the solution class. No `A^-1` at zero is permitted.

### Resonant branch

If some `z∈ker A` has `<z,Bc>!=0`, theoremize the zero-eigenspace contribution to the shifted resolvent quadratic value and its effect on the real explicit secular scalar near `lam=0-`.

This branch may force a negative root rather than exclude one; Control v2 treats that as useful classification evidence, not a failure of the research pass.

## E3-C routing rule

The exact root detector is now theorem-identified with a real explicit scalar, so shifted-resolvent identity and strict monotonicity work is admissible.

Permanent controller firewall:

```text
at most one negative root != no negative root.
```

A uniqueness theorem must route onward to endpoint/CCM-specific exclusion rather than terminal closure.

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
  -> E3-B3 generalized lower-floor one-step inequality if useful
  -> only then decision-bearing deformation bounds.
```

If a future theorem uses a lower predecessor floor `mu`, the diagnostic gap must use the same theorem-backed `mu` and shell-stiffness convention. The controller may not mix an empirical spectral floor with a theorem statement and call the result certified.

A finite prefix, fitted tail or small local residual is not enough. `PRUNE` still requires a complete assured horizon certificate under the existing v1.6 rules.

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

DR-010 remains dead. The current exact N-flow / first-bad / secular route does not use fitted small commutators, spectral-gap heuristics or eigenvector convergence.

## CI

`tools/run_suite.py` runs Control-v2 unit tests. The Python RHRC workflow checks out full Git history and performs a real-history Control-v2 smoke run. Router recommendations themselves are not theorem assertions; authority, completeness, leakage, exact interval coverage and assurance invariants remain CI-fatal.

Detailed current post-green research implications: `../RESEARCH_LEADS_POST_122_DELTA.md`.

**RH remains OPEN.**