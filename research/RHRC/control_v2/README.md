# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Purpose

Control v2 provides deterministic forward routing and retroactive archaeology/replay. It answers **where to look next**, never **what is mathematically true**.

## Separate theorem and control anchors

```text
theorem-state anchor = PR #140 merge fa96196b5bd6ed754853b0bdacee1dbd2356022f
validated theorem head = 77b52cfc73dfd83d2a0ed4373befba97d77e48e5
validated theorem tree = 2015404927540ae79a64469af82813463694b71d
RHRC #882 = SUCCESS
Permansson #655 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #140 advances theorem authority. This post-#140 control synchronization changes routing metadata, not the controller's capability/authority model.

## Current routed frontier

```text
A4b0  kernel/source zero-shift transport                       PROVED / RETIRED
A4b1  absolute canonical source energy                         PROVED / #136 / RETIRED
A4b2a exact one-step determinant + sufficiency reduction       PROVED / #137
A4R0  aperture freedom + regularity/frozen-source scaffold     PROVED / #140
A4R1  fixed-cell finite regular-aperture selection             NOW
A4b2r regular minimizing-trial Schur-energy sign               AFTER A4R1
A4b2b universal one-step domination                            BROAD FALLBACK
GLOBAL first-bad exclusion                                     AFTER A4b2r OR independent domination
```

Parallel actions remain shifted-nullity, secular monotonicity, predecessor-floor deformation and the deformation-budget diagnostic.

## Why routing changed after #140

The post-#138 Astra audit established the strategic circularity warning:

```text
A>=0 and dim(shell)=1:
q_c>=0 AND forall w, Delta(w)>=0
  <-> successor one-step form is nonnegative.
```

#140 then adds the theorem-backed aperture quantifier:

```text
off-line zero
  -> every sufficiently large aperture has a fresh finite negative canonical witness.
```

That allows a smaller regularization problem.

Instead of asking for simultaneous regularity across every finite size, the selected action now works inside one frozen physical cutoff cell:

```text
choose interior L1
-> #140 produces finite N,u
-> preserve that one strict negative quadratic value locally
-> regularize only both parities and sizes 1..N
-> reselect first-bad.
```

Countable/Baire all-size regularity is a fallback, not the current dependency.

## Selected action — E4_A4_REGULAR_APERTURE_SELECTION

The active theorem attempt must establish, on the **actual production source**:

1. fixed-witness canonical energy continuity on one frozen cutoff cell;
2. analytic/log-cover representation of each fixed actual `intrinsicPredecessorBlock`;
3. determinant nonidentity for each fixed parity/size;
4. dense fixed-block regular apertures;
5. finite simultaneous avoidance through an arbitrary finite horizon `M`;
6. composition with #140 aperture freedom, preservation of the strict negative witness, and fresh global first-bad reselection.

The #140 scalar theorem already discharges the real-axis `-log(L)` extraction for `wCorrection`. It does **not** discharge the full projected-block analyticity or determinant nonidentity.

The selected action must not require a countable all-size Baire theorem unless the finite-cell route first fails for a theoremized reason.

No successor positivity, determinant sign, regular Schur sign, or RH premise may be assumed.

## Resurrected analytic infrastructure

Before adding new complex analysis around the raw production interval integrals, the route should inspect and reuse:

```text
DictionaryArchPhysical.lean
DictionaryArchBridge.lean
GammaFacts/Mu.lean
```

These provide theorem-backed physical arch normalization and a summable digamma representation. Their new A4R use is a **RESURRECTED LEAD**, not yet theoremized continuation.

## Next action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

After A4R1 is theorem-backed, the exact regular predecessor scaffold gives a unique `x0` satisfying

```text
A x0 = b.
```

Define

```text
u0 = c - x0.
```

The closing sign target is

```text
Ecanonical(u0) >= 0.
```

Inverse shorthand `<b,A^-1b><=q_c` may be used only after regularity; formal Lean should prefer the unique-preimage interface unless a dedicated inverse abstraction is justified.

The controller records this as a separate action so global exclusion does not silently stand in for the actual missing arithmetic theorem.

First-break discovery should prioritize:

- interval-certified low-dimensional minimizing-trial calculations;
- exact paired prime/arch/scalar remainder identities after substituting `A x0=b`;
- prime-weight sensitivity;
- rejection of atomwise positive determinant/SOS and overly coarse independent channel majorants unless a changed premise is proved.

## Universal domination fallback

`E4_A4_CANONICAL_ONE_STEP_DOMINATION` remains routable but is deliberately demoted. It should become primary again only if a genuinely independent canonical arithmetic mechanism is found.

Its surviving objections include the generic-geometry, factorwise-transfer, scalar-shift and atomwise-determinant firewalls already recorded in the dead-route/obstruction memory.

## Post-#140 archaeology vocabulary

The `canonical_source_exclusion` concept should recover both the old and new route language, including:

```text
aperture freedom
eventually all apertures
fixed cutoff cell
single cutoff cell
finite horizon regularization
finite simultaneous regularity
fresh first bad
regular aperture
log lift
logarithmic determinant
periodic determinant
frozen cutoff
predecessor injective
positive definite predecessor
Schur energy
regular Schur endpoint
minimizing trial
A x0=b
A^-1 b
prime coefficient sensitivity
paired source remainder
```

The previous source-energy/pairing/determinant aliases remain.

## Deterministic routing consequence

The base score formula is unchanged. The action inputs encode the post-#140 research correction:

- regular-aperture selection remains selected;
- its first-break specification is now fixed-cell and finite-horizon rather than all-size;
- regular Schur sign remains explicit but carries dependency debt until A4R1 closes;
- universal domination remains admissible but does not win merely because it would close the route if proved.

This is routing metadata, not theorem evidence.

## CI expectations

`tools/run_suite.py` runs Control-v2 unit tests. The RHRC workflow real-history smoke run must assert:

- theorem anchor is #140;
- theorem merge/head/tree correspond to the exact validated #140 state;
- control anchor remains #117;
- frontier remains `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_APERTURE_SELECTION`;
- selected action remains `E4_A4_REGULAR_APERTURE_SELECTION`;
- regular-aperture action outranks universal domination and the deformation diagnostic;
- universal domination remains routable but is not selected;
- regular Schur-energy action is present and shares the canonical-source archaeology concept;
- terminal claim remains `RH_OPEN`;
- controller theorem authority and terminal-claim mutation remain false.

Newest research implications: `../RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md`.

**RH remains OPEN.**