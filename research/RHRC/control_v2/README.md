# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Purpose

Control v2 provides deterministic forward routing and retroactive archaeology/replay. It answers **where to look next**, never **what is mathematically true**.

## Separate theorem and control anchors

```text
theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #138 and the post-#138 Astra synchronization change research state and routing metadata, not theorem authority or the controller's capability model.

## Current routed frontier

```text
A4b0  kernel/source zero-shift transport                       PROVED / RETIRED
A4b1  absolute canonical source energy                         PROVED / #136 / RETIRED
A4b2a exact one-step determinant + sufficiency reduction       PROVED / #137
A4R   regular-aperture/log-lift witness selection              NOW
A4b2r regular minimizing-trial Schur-energy sign               AFTER A4R
A4b2b universal one-step domination                            BROAD FALLBACK
GLOBAL first-bad exclusion                                     AFTER A4b2r OR independent domination
```

Parallel actions remain shifted-nullity, secular monotonicity, predecessor-floor deformation and the deformation-budget diagnostic.

## Why routing changed after #138

The post-#138 Astra audit sharpens the #137 circularity warning:

```text
A>=0 and dim(shell)=1:
q_c>=0 AND forall w, Delta(w)>=0
  <-> successor one-step form is nonnegative.
```

Universal domination is therefore still a correct sufficient theorem, but its nominal closure value should not make it look like a smaller theorem than the remaining positivity obstruction.

Regular-aperture selection has higher immediate information value because it aims only to remove predecessor singularity/resonance while preserving a strict negative witness. Generic regular negative examples show that regularity does not imply positivity.

## Selected action — E4_A4_REGULAR_APERTURE_SELECTION

The active theorem attempt must establish, from the production canonical aperture dependence:

1. exact frozen-cutoff decomposition with the canonical `-log(L)` scalar;
2. log-lift determinant nonidentity;
3. simultaneous finite avoidance of predecessor singularities in both parities;
4. continuity preservation of the strict negative witness;
5. fresh global first-bad reselection after moving the aperture;
6. positive-definite predecessor blocks for the reselected state.

No successor positivity, regular preimage, determinant sign, or RH premise may be assumed.

## Next action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

After A4R is theorem-backed, the next arithmetic object is

```text
u0 = c - A^-1 b
S0 = Ecanonical(u0) = q_c - <b,A^-1b>.
```

The closing sign target is

```text
Ecanonical(u0) >= 0.
```

The controller records this as a separate action so global exclusion does not silently stand in for the actual missing arithmetic theorem.

First-break discovery should prioritize:

- interval-certified low-dimensional minimizing-trial calculations;
- exact paired prime/arch/scalar remainder identities;
- prime-weight sensitivity;
- rejection of atomwise positive determinant/SOS and overly coarse independent channel majorants unless a changed premise is proved.

## Universal domination fallback

`E4_A4_CANONICAL_ONE_STEP_DOMINATION` remains routable but is deliberately demoted. It should become primary again only if a genuinely independent canonical arithmetic mechanism is found.

Its surviving objections include DR-012/015/016 plus the post-#138 DR-018 atomwise-determinant and DR-020 coarse-majorant firewalls.

## Post-#138 archaeology vocabulary

The `canonical_source_exclusion` concept now includes the regularity and Schur-energy language needed to recover both old and new attempts:

```text
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
A^-1 b
prime coefficient sensitivity
source sensitivity
paired source remainder
```

The previous source-energy/pairing/determinant aliases remain.

## Deterministic routing consequence

The base score formula is unchanged. The action inputs now encode the research-state correction:

- regular-aperture selection outranks the deformation diagnostic and universal domination;
- regular Schur sign remains explicit but carries dependency debt until A4R closes;
- universal domination remains admissible but no longer wins merely because it would close the route if proved.

This is routing metadata, not theorem evidence.

## CI expectations

`tools/run_suite.py` runs Control-v2 unit tests. The RHRC workflow real-history smoke run must assert:

- theorem anchor remains #137;
- control anchor remains #117;
- frontier is `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_APERTURE_SELECTION`;
- selected action is `E4_A4_REGULAR_APERTURE_SELECTION`;
- regular-aperture action outranks universal domination and the deformation diagnostic;
- universal domination remains routable but is not selected;
- regular Schur-energy action is present and shares the canonical-source archaeology concept;
- terminal claim remains `RH_OPEN`;
- controller theorem authority and terminal-claim mutation remain false.

Newest research implications: `../RESEARCH_LEADS_POST_138_ASTRA_DELTA.md`.

**RH remains OPEN.**