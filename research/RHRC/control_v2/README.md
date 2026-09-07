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
theorem-state anchor = PR #125 merge 615437fd5854b4473471d9826b4d4787b2e8e42f
validated theorem head = 533beb4a42fc96cd43a97e071c6e07e3178872b6
control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #125 is the current merged theorem authority. PR #117 remains the latest merged green Control-v2 authority because #118/#119/#121/#122/#124/#125 changed theorem state but not controller semantics.

## Current routed frontier

`ACTION_REGISTRY.json` now routes from `FIRST_BAD_RIGIDITY_E4_A3`.

Primary theorem actions:

```text
E4-A3 zero-shift shell-response coefficient
E4-A3 exact resonant kernel-pole decomposition
E4-A3 CCM-specific branch rigidity / finite countermodel attack
E4-B parity shifted-nullity from rank-at-most-one algebra
E3-C exact real secular monotonicity / root-count control
E3-B3 generalized predecessor-floor deformation theorem
negative-root exclusion only after branch-rigidity information is available
```

The deformation-budget paper test remains parallel diagnostic research.

## Why the frontier moved

The post-#122 E4-A2 problem is now formally compressed by #124/#125.

PR #124 proves:

```text
W=ker A⊕range A
b annihilates ker A -> b∈range A
Ax0=b has a solution
<x,b> is solution-independent
```

and, in the resonant branch,

```text
<z,b>=(-lam)<z,R_lam b>
|<z,b>|^2 <= (-lam)||z||^2 Re<R_lam b,b>.
```

PR #125 proves the regular endpoint

```text
S0=<Tc,c>-<x0,b>,
u0=-x0+c,
predecessorPart(Tu0)=0,
<Tu0,u0>=S0,
Re S0<0
```

with an exact complete-square identity.

The controller must therefore not route back to “prove range membership,” “prove solution independence,” or “prove a useful resonant lower bound.” Those first-breaks have been consumed by theorem authority.

## E4-A3 routing rule

### Zero-shift shell response

The next theorem target is to convert the already-proved zero predecessor coordinate of `T u0` into an exact canonical shell-response coefficient using `V=W⊕S` and `dim_C S=1`.

Permanent firewall:

```text
T u0∈S != u0 eigenvector.
```

### Resonant pole decomposition

Use #124's canonical `ker A⊕range A` split to decompose `b` and isolate the exact `1/(-lam)` kernel contribution to `R_lam b`. The target is finite algebra, not heuristic spectral asymptotics.

### Branch rigidity

The decisive route is to combine regular shell response / resonant pole information with structure generic Hermitian Schur systems do not have:

- parity rank-at-most-one defect;
- KKT / parity normal-space geometry;
- canonical cubic quotient channel;
- exact N-flow and first-bad minimality.

A finite post-#125 countermodel is a valid falsifier. If such a model survives all imposed CCM constraints, do not claim root exclusion.

## E3-C routing rule

The exact root detector is theorem-identified with a real explicit scalar, so shifted-resolvent identity and strict monotonicity work is admissible.

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
  -> #124 zero-shift/resonance split
  -> #125 strict regular endpoint
  -> E4-A3 branch rigidity
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

DR-010 remains dead. The current exact N-flow / first-bad / secular route does not use fitted small commutators, spectral-gap heuristics or eigenvector convergence.

## CI

`tools/run_suite.py` runs Control-v2 unit tests. The Python RHRC workflow checks out full Git history and performs a real-history Control-v2 smoke run. Router recommendations themselves are not theorem assertions; authority, completeness, leakage, exact interval coverage and assurance invariants remain CI-fatal.

Detailed current post-green research implications: `../RESEARCH_LEADS_POST_125_DELTA.md`.

**RH remains OPEN.**