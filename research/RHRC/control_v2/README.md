# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Purpose

Control v2 provides:

1. **Forward routing.** Rank admissible next research moves by explicit cost, information gain, falsification value, closure value, residual risk and dependency debt. Every serious route declares a first-break test.
2. **Retroactive archaeology and replay.** Search repository history using concept aliases, optionally search a normalized external archive, and support `as_of` counterfactual replay so old states cannot see future clues.

The controller answers **where to look next**, never **what is mathematically true**. Lean/CI and machine claim surfaces retain theorem/claim authority.

## Separate theorem and control anchors

`CONTROL_STATE.json` records two distinct anchors:

```text
theorem-state anchor = PR #134 merge 7f1fec480d1ccbff04a456ab937accf7b23cc1af
validated theorem head = 753ee53a7fc08bd3be9a5a0f37417629122395f9
control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #134 is theorem-bearing and advances theorem authority. PR #117 remains the latest merged green Control-v2 semantic authority because this sync changes theorem/frontier data, not the controller's capability model or ranking algorithm.

## Current routed frontier

The post-#134 route is:

```text
E4-A4b0  kernel/source zero-shift transport                 PROVED / RETIRED FROM ROUTER
E4-A4b1  absolute canonical source-energy decomposition     NOW
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

## Why the kernel/source action is retired

PR #134 theoremized the exact denominator-free zero-shift package that Control v2 previously treated as the next action:

```text
A-(Dz) = beta(z)d + mu(z)a
<b-,Dz>/rho- = beta(z)+mu(z)
beta(z)K-d + mu(z)K-a = 0
```

for `z in ker A+`, together with the direct zero-shift transfer

```text
sigma- = alpha0 sigma+ + Gamma0 * mu(u+0)
```

and, under both parity preimage hypotheses,

```text
Gamma0 * mu(z)=0  for every z in ker A+.
```

The completed action is removed from `ACTION_REGISTRY.json` rather than left routable with a stale high score.

## Why the frontier is absolute source energy

The generic structural transfer package is blind to absolute spectral origin under

```text
M -> M+tI
lambda -> lambda+t.
```

PR #131's quadratic-normal source moment also annihilates scalar identities by design. Therefore another refinement of the same linear observable cannot by itself decide negative versus positive absolute spectrum.

The next theorem target must retain canonical normalization:

```text
E(v) = Re<Tv,v>.
```

The intended first energy PR should expose exact production bookkeeping:

```text
pole energy
- reduced arch diagonal energy
- reduced arch off-diagonal energy
- canonical arch scalar correction
- finite von-Mangoldt-weighted prime atom energies.
```

It should also connect the regular zero-shift trial energy to the existing Schur endpoint. A decomposition alone is not a positivity theorem.

## Canonical one-step domination

For each parity, with predecessor `A>=0`, shell `c`, coupling `b=P_W T c`, and

```text
q_c = Re<Tc,c>,
```

the decisive target is

```text
q_c >= 0
|<w,b>|^2 <= q_c Re<Aw,w>  for every w in W.
```

If theoremized from the actual canonical source:

- kernel vectors force `<w,b>=0`, removing resonance;
- a regular solution `Ax0=b` gives `S0>=0`;
- the existing first-bad theorem gives `Re S0<0` at the forced negative root;
- contradiction.

Control v2 must treat this as unresolved arithmetic/coercive content, not as an assumption.

## Countermodel routing gates

Exact rational generic reversal-symmetric diagonal fixtures preserve the centered grid, parity/boundary-flat constraints, predecessor nonnegativity, KKT extraction, rank-one cubic defect, quotient transport, overlap formula and cross-parity transfer while exhibiting:

```text
sourceMoment(u+) != 0 with Gamma = 0 at a common negative root
Gamma != 0 with sourceMoment(u+) = 0 at a common negative root
alpha = 0 at an odd-only negative root with positive even successor
```

Additional fixtures realize negative `Gamma`, negative `alpha`, and either sign of the source moment.

These are synthetic/generic regression fixtures, not canonical CCM sources and not zeta counterexamples.

**Routing consequence:** do not prioritize division by `alpha`, `Gamma`, overlap or source moment, generic factorwise sign/nonzeroness, or even-only root exclusion unless a new canonical source theorem supplies the missing premise.

The post-#134 product law `Gamma0*mu(z)=0` strengthens the kernel restriction but does not repeal this firewall.

## Regular-aperture fallback

If resonance makes the arithmetic estimate unnecessarily difficult, the admissible simplifier is frozen-cutoff analytic/log-lift regular selection:

```text
M_Q(L) = -log(L) I + B_Q(L)
L = exp(z)
```

with periodic holomorphic remainder. Determinant nonidentity + real analyticity may yield dense apertures where finitely many predecessor parity blocks are injective. Preserve a negative witness by continuity, move to such an aperture, then reselect the least-bad size.

Permanent warning:

```text
positive-definite predecessors != positive successor != RH.
```

## Quantitative source lane

Boundary-flat Taylor algebra suggests source-coordinate leading orders `omega^7` and `omega^9`. High-precision checks support the predicted coefficients. This remains **DERIVED / EXPERIMENTAL** until theoremized and should be routed only when it contributes a rigorous bound for absolute source energy/coercivity.

## Main objects

- `ACTION_REGISTRY.json` — current research actions, deterministic score inputs, first-break declarations and control requirements.
- `CONTROL_BOUNDARY.json` — physical authority cap for the controller.
- `CONTROL_STATE.json` — separate merged theorem/control anchors.
- `schemas.py` / `state.py` — typed theorem/control anchors and control state.
- `router.py` — deterministic fail-closed action ranking with explicit score formula and candidate diagnostics.
- `deformation_budget.py` — RH-native deformation-budget diagnostic with Decimal arithmetic, exact prefix coverage and assured tail certificates.
- `first_break.py` — MCM-style cheapest-decisive-falsifier ordering.
- `retro/` — vocabulary-aware Git archaeology, optional external archive ingestion/search, as-of replay and dead-route revival law.

## Theorem/research ancestry

```text
#119 exact secular equivalence
  -> #121 explicit scalar bridge
  -> #122 metric/resolvent control
  -> #124/#125 zero-shift branch endpoint
  -> #127 shell response
  -> #128 signed response / canonical pole
  -> #129 source-explicit parity transfer
  -> #131 exact source-moment decomposition
  -> #134 exact denominator-free kernel/source transport
  -> absolute source energy
  -> canonical one-step domination
```

## Dead-route law

`DEAD_ROUTES.md` remains authoritative historical failure memory. A dead/quarantined route cannot be silently resurrected; a revival record must state the original blocker, changed premise and evidence.

Current relevant lessons:

```text
universal raw source-moment positivity is dead by linearity
factorwise alpha/Gamma/overlap/source-moment closure is quarantined by exact countermodels
shift-invariant transfer data cannot determine absolute spectral sign
zero-shift pseudoinverse/Laurent machinery is superseded for the current transport need by PR #134's direct theorem
```

## CI

`tools/run_suite.py` runs Control-v2 unit tests. The Python RHRC workflow checks out full Git history and performs a real-history Control-v2 smoke run. Router recommendations themselves are not theorem assertions; authority, completeness, leakage, exact interval coverage and assurance invariants remain CI-fatal.

Detailed current research implications: `../RESEARCH_LEADS_POST_134_DELTA.md`.

**RH remains OPEN.**
