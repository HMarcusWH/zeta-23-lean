# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Purpose

Control v2 provides deterministic forward routing and retroactive archaeology/replay. It answers **where to look next**, never **what is mathematically true**.

## Separate theorem and control anchors

```text
theorem-state anchor = PR #142 merge 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
validated theorem head = 23d96af9aafd86ad26ae7913c3d6c14503d539de
validated theorem tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47
RHRC #889 = SUCCESS
Permansson #662 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #142 advances theorem authority. This post-#142 control synchronization changes routing metadata, not the controller's capability/authority model.

## Current routed frontier

```text
A4b0  kernel/source zero-shift transport                       PROVED / RETIRED
A4b1  absolute canonical source energy                         PROVED / #136 / RETIRED
A4b2a exact one-step determinant + sufficiency reduction       PROVED / #137
A4R0  aperture freedom + regularity/frozen-source scaffold     PROVED / #140
A4R1a fixed-cell same-witness persistence                      PROVED / #142
A4R1b analytic frozen predecessor + dense regularity           NOW
A4R1c cell-minimal regular first-bad selection                 AFTER A4R1b
A4b2r regular minimizing-trial Schur-energy sign               AFTER A4R1c
A4b2b universal one-step domination                            BROAD FALLBACK
GLOBAL first-bad exclusion                                     AFTER A4b2r OR independent domination
```

Parallel actions remain shifted-nullity, secular monotonicity, predecessor-floor deformation and the deformation-budget diagnostic.

The stable controller action ID remains `E4_A4_REGULAR_APERTURE_SELECTION`; its internal first-break specification is updated to the smaller post-#142 problem rather than introducing unnecessary action-ID churn.

## Why routing changed after #142

#140 established:

```text
off-line zero
  -> every sufficiently large aperture has a fresh finite negative canonical witness.
```

#142 now establishes, on the actual production source:

```text
one chosen interior negative witness (N,u)
  -> same N and same u remain negative on an open neighborhood
     inside the same physical cutoff cell.
```

That closes the former continuity first-break.

The post-green research pass then identifies a smaller **DERIVED** selection problem. Define the least bad size over the whole physical cutoff cell before regularization:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Every smaller size is therefore good in both parities throughout the whole cell. The predecessor at `N*=K*-1` is PSD throughout the cell. Once a bad parity witness at `K*` is selected, #142 gives an open persistent-negative set `J`; dense regularity only has to hit that set for the relevant predecessor determinant(s) at the single predecessor size.

This removes both countable all-size Baire regularization and the post-#140 finite-prefix intersection from the primary route.

## Selected action — E4_A4_REGULAR_APERTURE_SELECTION

The active theorem attempt now has two tightly coupled components:

1. package the production cell-minimal bad-state selection; and
2. prove dense regularity of the actual frozen intrinsic predecessor determinant.

The analytic part must establish, on the **actual production source**:

```text
complex continuation of the #142-regularized production channels
-> actual frozen intrinsic predecessor
-> A(L) = -Log(L) I + B(L)
-> B single-valued holomorphic on a connected punctured domain
-> logarithmic monodromy / finite-dimensional spectral obstruction
-> determinant nonidentity
-> dense real regularity in each physical cutoff cell.
```

The #140 scalar theorem already discharges the positive-real `-log(L)` extraction. #142 discharges fixed-cell continuity and strict witness persistence. Neither proves the full complex continuation or determinant nonidentity.

The active theorem must not require an all-size Baire theorem or finite-prefix regularization unless the cell-minimal route first fails for a theoremized reason.

No successor positivity, determinant sign, regular Schur sign, or RH premise may be assumed.

## Analytic infrastructure after #142

#142 regularizes the real archimedean integrands at the origin using divided slopes and `Real.sinc`.

A real change of variables `x=L t` produces fixed-unit-interval expressions whose oscillatory factors no longer move with aperture. These rescaled identities are **DERIVED**, not merged theorem declarations; high-precision agreement is **EXPERIMENTAL SIGNAL**.

Direct parameter holomorphy is therefore a primary candidate. The older infrastructure

```text
DictionaryArchPhysical.lean
DictionaryArchBridge.lean
GammaFacts/Mu.lean
```

remains useful for fallback, comparison and alternative continuation. It should not be treated as already proving the new frozen-predecessor theorem.

## Nonidentity lead

The correct log-cover proposal is:

```text
A(L) = -Log(L) I + B(L)
B is single-valued in the aperture variable
L = exp z
Ahat(z) = -z I + B(exp z)
B(exp(z+2*pi*i)) = B(exp z).
```

If `det Ahat` vanished identically, one fixed finite matrix would acquire more distinct eigenvalues `z+2*pi*i*k` than finite dimension permits.

This is a **LEAD / HYPOTHESIS**. The complex domain, branch choice, actual-predecessor equality and absence of cancelling monodromy remain proof obligations.

## New negative control

The post-#142 countermodel registry contains a generic analytic centered diagonal family with:

```text
explicit -log L scalar structure;
positive predecessors for all L>0;
persistent finite negative witnesses at every aperture;
a globally minimal bad size;
common negative behavior in both parities.
```

It is not the canonical zeta source. It is a first-break firewall: a purported contradiction based only on persistence, regularity, parity, minimality or scalar logarithmic structure is overstrong.

See `../countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`.

## Next action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

After the production regular cell-minimal first-bad state is theorem-backed, the exact regular predecessor scaffold gives a unique `x0` satisfying

```text
A x0 = b.
```

Define

```text
u0 = c - x0.
```

The forced regular countercertificate is intended to package existing #136/#137 machinery into

```text
Ecanonical(u0) = Re S0 < 0.
```

The closing sign target remains

```text
Ecanonical(u0) >= 0.
```

Inverse shorthand `<b,A^-1b><=q_c` may be used only after regularity; formal Lean should prefer the unique-preimage interface unless a dedicated inverse abstraction is justified.

The controller records this as a separate action so regularity does not silently stand in for the actual missing arithmetic theorem.

First-break discovery should prioritize:

- interval-certified low-dimensional minimizing-trial calculations;
- exact paired pole/prime/arch/scalar remainder identities after substituting `A x0=b`;
- aperture-derivative identities made possible by cell-wide predecessor PSD;
- prime-weight sensitivity;
- rejection of atomwise positive determinant/SOS and overly coarse independent channel majorants unless a changed premise is proved.

## Universal domination fallback

`E4_A4_CANONICAL_ONE_STEP_DOMINATION` remains routable but deliberately demoted. It should become primary again only if a genuinely independent canonical arithmetic mechanism is found.

Under predecessor PSD and one-dimensional shell, universal domination is DERIVED equivalent to successor positivity, so merely rewriting that positivity has no research information gain.

## Post-#142 archaeology vocabulary

The `canonical_source_exclusion` concept should recover both the historical and current route language, including:

```text
aperture freedom
eventually all apertures
fixed cutoff cell
fixed-cell witness persistence
same witness persistence
cell-minimal bad size
cell-wide minimality
cell-wide predecessor PSD
analytic frozen predecessor
punctured domain
punctured strip
single-valued remainder
logarithmic monodromy
rescaled unit interval
fixed-domain archimedean integral
regularization countermodel
regular aperture
predecessor determinant
predecessor injective
positive definite predecessor
regular first bad
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

The base score formula is unchanged. The action inputs now encode the post-#142 state:

- regular-aperture selection remains selected;
- its continuity/persistence first-break is retired because #142 proved it;
- its live first breaks are production complex continuation, determinant nonidentity and production cell-minimal composition;
- regular Schur sign remains explicit but carries dependency debt until regular selection closes;
- universal domination remains admissible but does not win merely because it would close the route if proved.

This is routing metadata, not theorem evidence.

## CI expectations

`tools/run_suite.py` runs Control-v2 unit tests. The RHRC workflow real-history smoke run must assert:

- theorem anchor is #142;
- theorem merge/head tree correspond to the exact validated #142 state;
- control anchor remains #117;
- frontier remains `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_APERTURE_SELECTION`;
- selected action remains `E4_A4_REGULAR_APERTURE_SELECTION`;
- regular-aperture action outranks universal domination and the deformation diagnostic;
- universal domination remains routable but is not selected;
- regular Schur-energy action is present and shares the canonical-source archaeology concept;
- terminal claim remains `RH_OPEN`;
- controller theorem authority and terminal-claim mutation remain false.

Newest research implications: `../RESEARCH_LEADS_POST_142_FIXED_CELL_PERSISTENCE_DELTA.md`.

**RH remains OPEN.**