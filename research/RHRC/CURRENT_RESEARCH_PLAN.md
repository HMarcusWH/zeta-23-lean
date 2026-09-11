# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
live main after merged PR #148 = fcd301ae4c1b58196ff7fca18128243f1d35a87b
live main tree = 91d537ee64b8f613bebdcf12110deba486276d35

theorem-state anchor = PR #148 merge fcd301ae4c1b58196ff7fca18128243f1d35a87b
validated theorem head = 77c2d14511004ba380b080e08b4943b267ebd863
validated theorem tree = 91d537ee64b8f613bebdcf12110deba486276d35
RHRC #930 / run 34619665717 = SUCCESS
Permansson #703 / run 34619665725 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI remain authoritative.

## One-screen frontier

```text
DONE THROUGH #142
  finite legal off-line-zero reduction
  canonical finite negative obstruction
  centered N-flow / parity / first-bad / KKT / one-dimensional shell
  shifted and zero-shift Schur machinery
  source-explicit transfer and exact source-moment decomposition
  denominator-free zero-shift source transport
  scalar-sensitive absolute canonical source energy
  exact source pairing and one-step determinant
  off-line zero -> q_c<0 OR exists w, Delta(w)<0
  eventual aperture freedom
  predecessor regularity <-> injectivity + unique zero-shift preimage
  frozen prime-cutoff equality + threshold atom vanishing
  exact real-axis scalar extraction
  fixed-cell actual-source continuity
  same-size/same-vector open negative persistence

DONE / #144 — FROZEN PRODUCTION + LOG-COVER SCAFFOLD
  exact frozen canonical source with physical-cell equality
  exact real-axis source split with coefficient -log(L) * I
  split survives parity compression and intrinsic predecessor projection
  exact complex frozen source remainder with positive-real bridge
  exact complex frozen intrinsic predecessor remainder with positive-real bridge
  lifted family Ahat(z) = -z I + R(exp z)
  exact deck-periodicity of the lifted remainder
  exact deck-shift law for the lifted block
  exact recovery of the production intrinsic predecessor at z=log L

DONE / #145-#146 — SCALAR REMOVABLE LAYER + PRODUCTION BRIDGE
  removable scalar factor has value 2 at zero
  local analyticity of the removable factor/remainder at zero
  removable factor/remainder = production complex factor/remainder for z != 0
  exact positive-real provenance back to the production real scalar formulas

DONE / #148 — FIXED-UNIT PARAMETER HOLOMORPHY
  complexArchSafeStrip = {|Im z| < pi} is open/convex/connected
  complexArchSinhSlope is zero-free throughout the strip
  complexRegularizedArchScale is analytic throughout the strip
  complexAlphaCore is analytic throughout the strip
  complexBetaCore is analytic throughout the strip
  complexGammaCore is analytic throughout the strip
  real-axis analytic corollaries require no positivity hypothesis
  genuine differentiation-under-the-integral proof; no deck-law shortcut

NOW — ASSEMBLED SOURCE / PREDECESSOR HOLOMORPHY
  use the #148 core theorems as closed inputs
  prove a common punctured source domain
  control the production scalar principal-log branch on that domain
  prove pole denominator zero-freeness there
  prove elementary/frozen prime-source analyticity
  assemble complexFrozenCanonicalSourceRemainder holomorphy
  assemble complexFrozenIntrinsicPredecessorRemainder holomorphy
  prove the lifted predecessor is analytic on a connected logarithmic-cover domain

THEN — DETERMINANT REGULARITY
  prove the lifted determinant analytic
  prove determinant nonidentity separately via the exact deck-shift law
  use a finite characteristic-polynomial root count
  split off the zero-dimensional predecessor case instead of forcing a positive-degree argument
  apply one-variable analytic identity/isolated-zero machinery
  -> dense real regular apertures on each physical cell

THEN — A4R1c REGULAR CELL-MINIMAL FIRST-BAD CERTIFICATE
  choose least bad size K* over the whole cutoff cell
  all K<K* are good in both parities throughout the cell
  predecessor size N*=K*-1 is PSD throughout the cell
  #142 gives open persistent-negative J for the selected witness
  dense regularity gives L2 in J
  regularity gives unique x0 with A x0=b
  package Ecanonical(c-x0)=Re S0<0

DECISIVE OPEN ARITHMETIC TARGET
  prove, from exact canonical pole/arch/scalar/prime interaction,

    Ecanonical(c-x0)>=0

  on the exact forced regular state.

  A potentially smaller certificate than universal domination is:

    q_c >= 0
    Delta(x0) >= 0

  but only after separately theoremizing that the zero-shift coupling <x0,b>
  is real and handling the q_A(x0)=0 edge case.

BROAD FALLBACK
  universal q_c>=0 and Delta(w)>=0 remains a valid closing theorem if a genuinely
  independent canonical arithmetic mechanism is discovered.

PARALLEL / LOWER PRIORITY
  E4-B shifted-nullity
  E3-C secular monotonicity/root-count control
  E3-B3 lower-floor deformation
  deformation-budget diagnostic
  pole-neutral finite-approximation refinement
  all-size/Baire regularity only if the cell-minimal route fails for a theoremized reason

TARGET
  assembled source/predecessor holomorphy
  -> determinant nonidentity
  -> dense regularity
  -> regular cell-minimal first-bad countercertificate
  -> exact regular Schur-energy arithmetic sign
  -> contradiction with forced Re S0<0
  -> no off-line zero through existing reduction
  -> explicit outside-strip/trivial-zero seam
  -> Mathlib RiemannHypothesis wrapper
  RH OPEN
```

## Exact theorem packages now consumed by the route

### PR #144

Headline theorem objects include:

```text
frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_fixedCell
frozenCanonicalSourceMatrix_eq_neg_log_identity_add_remainder
frozenIntrinsicPredecessorBlock_eq_actual_fixedCell
frozenIntrinsicPredecessorBlock_eq_neg_log_id_add_remainder
intrinsicPredecessorBlock_eq_neg_log_id_add_remainder_fixedCell
complexFrozenIntrinsicPredecessorRemainder_ofReal
liftedFrozenIntrinsicPredecessorRemainder_add_two_pi_I
liftedFrozenIntrinsicPredecessorBlock_add_two_pi_I
liftedFrozenIntrinsicPredecessorBlock_of_log_fixedCell
```

### PR #145-#146

`CanonicalApertureHolomorphy.lean` theorem-locks the removable scalar layer at zero and exact equality with the production scalar/remainder away from zero.

### PR #148

The new arch-domain/parameter modules theorem-lock:

```text
complexArchSafeStrip
isOpen_complexArchSafeStrip
convex_complexArchSafeStrip
isPreconnected_complexArchSafeStrip
isConnected_complexArchSafeStrip
complexArchSinhSlope_ne_zero_of_mem_strip
differentiableOn_complexRegularizedArchScale_strip
analyticOnNhd_complexRegularizedArchScale_strip
differentiableOn_complexAlphaCore_strip
analyticOnNhd_complexAlphaCore_strip
differentiableOn_complexBetaCore_strip
analyticOnNhd_complexBetaCore_strip
differentiableOn_complexGammaCore_strip
analyticOnNhd_complexGammaCore_strip
```

These close fixed-unit core holomorphy. They do **not** by themselves prove assembled frozen source/predecessor holomorphy.

## Cell-minimal selection compression

The strongest current derived composition remains:

```text
bad somewhere in I_Q
-> define K* as least size bad somewhere in I_Q
-> for all K<K* and all L in I_Q: not AnyParityBad L K
-> predecessor size N*=K*-1 is PSD throughout I_Q
-> choose L*, parity p and vector u bad at K*
-> #142 gives open J around L* preserving that exact negative witness
-> dense regularity, once proved, can be intersected with J at N*.
```

This remains **DERIVED** until production-packaged in Lean.

## Falsification firewalls

1. The generic post-#142 regularization countermodel shows that persistence + minimality + regularity + parity + a scalar logarithm do not force a contradiction.
2. The post-#146 function `F(z)=-z+Re z` remains a negative control for "translation/deck law implies holomorphy".
3. #148 only theoremizes the archimedean core strip. Prime/pole/scalar source channels still need a common-domain proof.
4. Holomorphy of a determinant does not imply determinant nonidentity.
5. Dense regularity does not imply the final canonical arithmetic sign.
6. Minimizing bad size at one aperture and then moving the aperture is invalid; the minimum must be taken over the whole physical cell.
7. The terminal Mathlib RH theorem requires an explicit formal seam from strip-zero exclusion to Mathlib's nontrivial-zero formulation.

## Highest-leverage next move

Prove or quickly falsify the scalar right-half-plane lead on the punctured arch strip, then assemble exact frozen source/predecessor holomorphy on the same common domain. This directly enables the determinant nonidentity/density route.

Newest research delta:

`RESEARCH_LEADS_POST_148_PARAMETER_HOLOMORPHY_GREEN_DELTA.md`

**RH remains OPEN.**
