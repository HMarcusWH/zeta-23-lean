# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Purpose

Control v2 provides deterministic forward routing and retroactive archaeology/replay. It answers **where to look next**, never **what is mathematically true**.

## Separate theorem and control anchors

```text
theorem-state anchor = PR #146 merge f2999d12e29d61debce130e83491ac3df410b0c2
validated theorem head = a25d238478f7b19072c5364486b8f3f994bf6b79
validated theorem tree = fe76581d445569cb838cb4df7bf50703aa34f5cc
RHRC #922 / run 34600323163 = SUCCESS
Permansson #695 / run 34600323144 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #146 advances theorem authority. This post-#146 control synchronization changes routing metadata, not the controller's capability/authority model.

## Current routed frontier

```text
A4b0  kernel/source zero-shift transport                       PROVED / RETIRED
A4b1  absolute canonical source energy                         PROVED / #136 / RETIRED
A4b2a exact one-step determinant + sufficiency reduction       PROVED / #137
A4R0  aperture freedom + regularity/frozen-source scaffold     PROVED / #140
A4R1a fixed-cell same-witness persistence                      PROVED / #142
A4R1b frozen/log-cover predecessor scaffold                    PROVED / #144
A4R1b scalar removable analyticity + production bridge         PROVED / #145-#146
A4R1b genuine parameter-integral/assembled holomorphy          NOW
A4R1b determinant nonidentity + dense regularity               AFTER HOLOMORPHY
A4R1c cell-minimal regular first-bad selection                 AFTER DENSITY
A4b2r regular minimizing-trial Schur-energy sign               AFTER A4R1c
A4b2b universal one-step domination                            BROAD FALLBACK
GLOBAL first-bad exclusion                                     AFTER A4b2r OR independent domination
```

Parallel actions remain shifted-nullity, secular monotonicity, predecessor-floor deformation and the deformation-budget diagnostic.

The stable controller action ID remains `E4_A4_REGULAR_APERTURE_SELECTION`. The action ID still names the same route; only its first-break specification moves forward as theorem prerequisites close.

## Why routing changed after #146

#142 established same-size/same-vector strict negative witness persistence inside one physical cutoff cell.

#144 then established the exact production/log-cover scaffold:

```text
actual frozen source/predecessor
-> exact -log(L) I + remainder split
-> exact complex frozen remainder
-> lifted family Ahat(z)=-z I+R(exp z)
-> exact deck-periodicity/deck-shift laws
-> exact recovery of the production predecessor at z=log L.
```

#145 theoremized local scalar removable analyticity at zero.

#146 theoremized exact equality between the removable scalar layer and the production complex scalar/remainder away from zero, plus positive-real provenance.

Therefore the old first break "construct a single-valued analytic frozen predecessor representation" is no longer one indivisible task. The exact object exists; the unresolved part is genuine complex differentiability of its parameter-dependent source integrals.

## Selected action — E4_A4_REGULAR_APERTURE_SELECTION

The active theorem attempt has three sequential first breaks:

1. prove genuine parameter holomorphy of the exact fixed-unit production source cores and assemble holomorphy of `complexFrozenIntrinsicPredecessorRemainder`;
2. prove the relevant determinant is not identically zero and derive dense regular apertures;
3. production-package the cell-minimal bad-size selection and intersect dense regularity with the #142 persistent-negative open set.

The first break should begin with the simplest source core, preferably `complexBetaCore`, and should use an actual differentiation-under-the-integral theorem with explicit local domination.

No successor positivity, determinant sign, regular Schur sign, negative-root exclusion, or RH premise may be assumed.

## Translation/deck-law negative control

The exact #144 deck identity is not an analyticity theorem.

A reusable generic countermodel is

```text
F(z) = -z + Re z.
```

Under pure imaginary translation by `2*pi*i`, the `Re z` part is unchanged and the `-z` term acquires the expected affine shift, yet `F` is not complex differentiable. Therefore translation/deck structure alone cannot discharge FB-01.

See `../countermodels/POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md`.

## Cell-minimal selection — still the preferred composition

The post-#142 derived selection remains:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Every smaller size is good in both parities throughout the cell, so the predecessor at `N*=K*-1` is PSD throughout the cell. #142 preserves one selected bad witness on an open `J`. Once dense regularity is theorem-backed, only the relevant determinant(s) at `N*` must meet `J`.

This removes countable all-size Baire regularization and finite-prefix simultaneous regularization from the primary route.

## Determinant nonidentity lead

After genuine holomorphy is proved, use the exact theorem-backed architecture

```text
Ahat(z) = -z I + R(exp z)
R(exp(z+2*pi*i)) = R(exp z).
```

If `det Ahat` vanished identically, the intended finite-dimensional spectral/root-counting argument would force one fixed finite operator to accommodate too many distinct scalar shifts. This remains a **LEAD / HYPOTHESIS** until Lean proves the determinant theorem.

## Next action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

After the production regular cell-minimal first-bad state is theorem-backed, the exact regular predecessor scaffold gives a unique `x0` satisfying

```text
A x0 = b.
```

Define `u0=c-x0`. The intended forced countercertificate is

```text
Ecanonical(u0)=Re S0<0.
```

The closing sign target remains

```text
Ecanonical(u0)>=0.
```

Inverse shorthand `<b,A^-1b><=q_c` may be used only after regularity; formal Lean should prefer the unique-preimage interface unless a dedicated inverse abstraction is justified.

The controller records this as a separate action so regularity does not silently stand in for the actual missing arithmetic theorem.

## Universal domination fallback

`E4_A4_CANONICAL_ONE_STEP_DOMINATION` remains routable but deliberately demoted. It should become primary again only if a genuinely independent canonical arithmetic mechanism is found.

Under predecessor PSD and one-dimensional shell, universal domination is DERIVED equivalent to successor positivity, so merely rewriting that positivity has no research information gain.

## Post-#146 archaeology vocabulary

The `canonical_source_exclusion` concept should recover both historical and current route language, including:

```text
aperture freedom
fixed cutoff cell
same witness persistence
cell-minimal bad size
cell-wide predecessor PSD
frozen canonical source
frozen intrinsic predecessor
complex frozen remainder
logarithmic cover
deck periodicity
deck shift
removable scalar factor
removable scalar remainder
parameter holomorphy
fixed-domain parameter integral
differentiation under the integral
local domination
translation not holomorphy
determinant nonidentity
regular aperture
predecessor determinant
predecessor injective
positive definite predecessor
regular first bad
Schur energy
minimizing trial
A x0=b
A^-1 b
prime coefficient sensitivity
paired source remainder
```

The previous source-energy/pairing/determinant aliases remain.

## Deterministic routing consequence

The base score formula is unchanged. The action inputs now encode the post-#146 state:

- regular-aperture selection remains selected;
- frozen production/log-cover construction and scalar production bridging are closed prerequisites;
- FB-01 is genuine parameter-integral/assembled holomorphy;
- FB-02 is determinant nonidentity/dense regularity;
- FB-03 is production cell-minimal composition;
- regular Schur sign remains explicit but carries dependency debt until regular selection closes;
- universal domination remains admissible but does not win merely because it would close the route if proved.

This is routing metadata, not theorem evidence.

## CI expectations

`tools/run_suite.py` runs Control-v2 unit tests. The RHRC workflow real-history smoke run must assert:

- theorem anchor is #146;
- theorem merge/tree correspond to the exact validated #146 state;
- control anchor remains #117;
- frontier remains `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_APERTURE_SELECTION`;
- selected action remains `E4_A4_REGULAR_APERTURE_SELECTION`;
- regular-aperture action outranks universal domination and the deformation diagnostic;
- universal domination remains routable but is not selected;
- regular Schur-energy action is present and shares the canonical-source archaeology concept;
- terminal claim remains `RH_OPEN`;
- controller theorem authority and terminal-claim mutation remain false.

Newest research implications: `../RESEARCH_LEADS_POST_146_APERTURE_ANALYTIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**
