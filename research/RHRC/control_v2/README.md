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
theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #137 is theorem-bearing and advances theorem authority. PR #117 remains the latest merged green Control-v2 semantic authority because this sync changes theorem/frontier data, vocabulary and regression assertions, not the controller's capability model.

## Current routed frontier

```text
A4b0  kernel/source zero-shift transport                       PROVED / RETIRED
A4b1  absolute canonical source energy                         PROVED / #136 / RETIRED
A4b2a exact one-step determinant + sufficiency reduction       PROVED / #137
A4b2b canonical shell/determinant sign theorem                 NOW
A4R   log-lift dense regular-aperture selection                FALLBACK
GLOBAL canonical first-bad exclusion                           AFTER SIGN THEOREM
```

Parallel actions remain E4-B shifted-nullity, E3-C secular monotonicity, E3-B3 deformation and the deformation-budget diagnostic.

## Why the old energy action is retired

PR #136 completed the old A4b1 action. Leaving `E4_A4_ABSOLUTE_SOURCE_ENERGY` routable would let the controller recommend already-proved work.

The current source-specific action is `E4_A4_CANONICAL_ONE_STEP_DOMINATION`, now interpreted through the exact #137 objects:

```text
q_c = Re<Tc,c>
q_A(w)=Re<Aw,w>
b(w)=<w,P_WTc>
Δ(w)=q_c*q_A(w)-|b(w)|^2.
```

## Why the action is not a dead-route revival

The previous registry attached DR-012 / DR-015 / DR-016 to the domination action. After #137 that is too coarse:

- DR-012 kills **generic** shell/Schur/parity/KKT exclusion without source values;
- DR-015 kills **factorwise** alpha/Gamma/overlap/source-moment closure;
- DR-016 kills **shift-invariant** transfer data as a locator of absolute spectral sign.

The live A4b2b action instead consumes the scalar-sensitive canonical source energy and exact production pairing from #136/#137. It is therefore a changed problem, not a silent resurrection of those routes. The dead-route IDs are removed from the action's admission blockers but retained as surviving objections/firewalls.

## Deterministic routing consequence

#137 reduces the dependency debt and proof-engineering risk of the domination action: the certificate, kernel/range consequence, endpoint consequence, negative-root sufficiency theorem and global failure wrapper are already compiled. The remaining work is the arithmetic sign theorem itself.

The score inputs are therefore updated so the canonical sign action outranks the diagnostic deformation lane rather than tying it. This is a routing priority change, not theorem evidence.

## First-break contract

The current action should fail early if either of these happens:

1. a canonical low-dimensional predecessor-nonnegative state exhibits `q_c<0` or `Δ(w)<0` under the exact normalization;
2. the full pole/arch/scalar/prime pairing supplies no source-specific representation or estimate beyond generic block positivity.

If (1) occurs, retire the domination route and use the exact witness to redesign the arithmetic target. Do not reinterpret it as evidence against RH.

## Archaeology vocabulary

The `canonical_source_exclusion` concept now explicitly includes:

```text
CanonicalSourceEnergy
CanonicalSourcePairing
canonicalOneStepDomination
cubicOneStepDeterminant
cubicShellRealEnergy
cubicShellCoupling
one-step determinant
Gram determinant
shell energy
source pairing
```

This lets retro search recover both the old source-normalization language and the new determinant language without introducing generic alias noise.

## Dead-route law

`DEAD_ROUTES.md` remains authoritative historical failure memory. A dead/quarantined route cannot be silently resurrected. Removing a dead-route admission match is valid only when the live action no longer instantiates the dead route; the changed premise must be documented, as above.

## CI expectations

`tools/run_suite.py` runs Control-v2 unit tests. The Python RHRC workflow performs a real-history smoke run. The post-#137 sync tests assert:

- theorem anchor #137 and control anchor #117 remain separate;
- A4b1 is no longer routable;
- the canonical domination/sign action is routable and deterministically selected when control contracts are satisfied;
- source archaeology aliases include the new energy/pairing/determinant vocabulary;
- the real-history workflow smoke anchor is #137;
- terminal claim remains `RH_OPEN` and controller theorem authority remains false.

Detailed current research implications: `../RESEARCH_LEADS_POST_137_DELTA.md`.

**RH remains OPEN.**
