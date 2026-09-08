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
control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #132 synchronized documentation/control metadata only. PR #131 remains theorem authority. PR #117 remains the latest merged green Control-v2 semantic authority because subsequent changes have altered theorem state or routing data, not the controller's authority model/algorithms.

## Current routed frontier

The post-#132 research audit changes the immediate route to:

```text
E4-A4b0  kernel/source zero-shift transport                 NOW
E4-A4b1  absolute canonical source-energy decomposition     THEN
E4-A4b2  canonical one-step domination/coercivity           DECISIVE TARGET
E4-A4R   log-lift dense regular-aperture selection          FALLBACK SIMPLIFIER
E4-A4d   global first-bad exclusion                         AFTER COERCIVITY
```

Parallel actions remain:

```text
E4-B  parity shifted-nullity
E3-C  exact real secular monotonicity / root-count control
E3-B3 generalized predecessor-floor deformation theorem
deformation-budget paper falsifier
```

## Why routing changed

The previous routing emphasized composing #131 directly into the #129 root equation and testing regular/resonant branches factorwise. The post-#132 audit found a stronger denominator-free zero-shift identity and the exact countermodel campaign falsified several factorwise shortcuts.

### New immediate theorem target

For `z in ker A+`, the existing parity-defect/quotient identities should compose to

```text
A-(Dz) = beta(z) d + mu(z) a
<b-,Dz>/rho- = beta(z) + mu(z)
```

and hence

```text
(||K+b+||^2/rho+) K-d + mu(K+b+) K-a = 0
```

in the full odd predecessor kernel.

Under both regular couplings the derived target is

```text
Gamma0 * mu(z) = 0
```

for every even predecessor-kernel vector.

The same tranche should theoremize the direct zero-shift transfer

```text
sigma- = alpha0 sigma+ + Gamma0 * mu(u+0)
```

without a pseudoinverse, Laurent limit or whole-block inverse.

These are derived targets, not current theorem authority.

## Exact countermodel routing gate

Exact rational generic reversal-symmetric diagonal fixtures preserve the actual centered grid, parity/boundary-flat constraints, predecessor nonnegativity, KKT extraction, rank-one cubic defect, quotient transport, shifted trial reconstruction, overlap formula and the full #129 transfer while exhibiting:

```text
sourceMoment(u+) != 0 with Gamma = 0 at a common negative root
Gamma != 0 with sourceMoment(u+) = 0 at a common negative root
alpha = 0 at an odd-only negative root with positive even successor
```

Additional fixtures realize negative `Gamma`, negative `alpha`, and either sign of the source moment.

These are synthetic/generic regression fixtures, not canonical CCM sources and not zeta counterexamples.

**Routing consequence:** Control v2 should not prioritize division by `alpha`, `Gamma`, overlap or source moment, generic factorwise sign/nonzeroness, or even-only root exclusion unless a new canonical source theorem explicitly supplies the missing premise.

## Scalar-shift origin firewall

In the generic structural package, the simultaneous shift

```text
M -> M+tI
lambda -> lambda+t
```

can preserve the trial vectors, cubic defect/source functional, `alpha`, `Gamma`, and secular transfer data while moving the absolute spectrum relative to zero.

Therefore shift-invariant transfer data cannot by themselves close a sign-sensitive negative-root claim.

PR #131's quadratic-normal moment also annihilates scalar identities. The next arithmetic layer must retain the absolute canonical normalization.

## Absolute source-energy route

The next source theorem should decompose

```text
E(v) = Re<Tv,v>
```

through the exact production pole/arch/prime source while retaining the canonical archimedean scalar correction.

A decomposition alone is not closure. Its purpose is to support the decisive one-step domination target.

## Canonical one-step domination

For each parity, with predecessor `A>=0`, shell `c`, coupling `b=P_W T c`, and

```text
q_c = Re<Tc,c>,
```

the target is

```text
q_c >= 0
|<w,b>|^2 <= q_c Re<Aw,w>  for every w in W.
```

This is equivalent to positivity of the one-step block extension under `A>=0`.

If theoremized from the actual canonical source:

- kernel vectors force `<w,b>=0`, removing resonance;
- a regular solution `Ax0=b` gives `S0>=0`;
- the existing first-bad theorem gives `Re S0<0` at the forced negative root;
- contradiction.

Control v2 should treat this as the central closure-value theorem, not as an assumption or a cheap intermediate lemma.

## Regular-aperture fallback

If resonance makes the arithmetic estimate unnecessarily difficult, the admissible simplifier is frozen-cutoff analytic/log-lift regular selection:

```text
M_Q(L) = -log(L) I + B_Q(L)
L = exp(z)
```

with periodic holomorphic remainder. Determinant nonidentity + real analyticity should yield dense apertures where finitely many predecessor parity blocks are injective. Preserve a negative witness by continuity, move to such an aperture, then reselect the least-bad size.

Permanent warning:

```text
positive-definite predecessors != positive successor != RH.
```

The exact generic countermodels include strictly positive predecessors with negative successor roots, so regular selection is only simplification.

## Quantitative source lane

Boundary-flat Taylor algebra suggests source-coordinate leading orders `omega^7` and `omega^9`. High-precision checks support the predicted coefficients. This remains **DERIVED / EXPERIMENTAL** until theoremized and should be routed only when it contributes a rigorous bound for absolute source energy/coercivity.

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

The current theorem/research ancestry is

```text
#119 exact secular equivalence
  -> #121 explicit scalar bridge
  -> #122 metric/resolvent control
  -> #124/#125 zero-shift branch endpoint
  -> #127 shell response
  -> #128 signed response / canonical pole
  -> #129 source-explicit parity transfer
  -> #131 exact source-moment decomposition
  -> kernel/source zero-shift transport
  -> absolute source energy
  -> canonical one-step domination
```

If a future theorem uses a lower predecessor floor `mu`, the diagnostic gap must use the same theorem-backed `mu` and shell-stiffness convention. A finite prefix, fitted tail or small local residual is not enough. `PRUNE` still requires a complete assured horizon certificate under the existing v1.6 rules.

## Dead-route law

`DEAD_ROUTES.md` remains authoritative historical failure memory. A dead/quarantined route cannot be silently resurrected; a revival record must state the original blocker, changed premise and evidence.

Current relevant dead/quarantined lessons:

```text
universal raw source-moment positivity is dead by linearity
factorwise alpha/Gamma/overlap/source-moment closure is quarantined by exact countermodels
shift-invariant transfer data cannot determine absolute spectral sign
```

## CI

`tools/run_suite.py` runs Control-v2 unit tests. The Python RHRC workflow checks out full Git history and performs a real-history Control-v2 smoke run. Router recommendations themselves are not theorem assertions; authority, completeness, leakage, exact interval coverage and assurance invariants remain CI-fatal.

Detailed current research implications: `../RESEARCH_LEADS_POST_132_DELTA.md`.

**RH remains OPEN.**
