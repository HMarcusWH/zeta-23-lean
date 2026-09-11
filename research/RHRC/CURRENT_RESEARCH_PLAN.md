# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
live main after merged PR #146 = f2999d12e29d61debce130e83491ac3df410b0c2
live main tree = fe76581d445569cb838cb4df7bf50703aa34f5cc

theorem-state anchor = PR #146 merge f2999d12e29d61debce130e83491ac3df410b0c2
validated theorem head = a25d238478f7b19072c5364486b8f3f994bf6b79
validated theorem tree = fe76581d445569cb838cb4df7bf50703aa34f5cc
RHRC #922 / run 34600323163 = SUCCESS
Permansson #695 / run 34600323144 = SUCCESS

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

DONE / #145 — LOCAL SCALAR REMOVABLE ANALYTICITY
  removable scalar factor has value 2 at zero
  divided exponential slope is nonzero on a genuine neighborhood of zero
  removable scalar factor is analytic at zero
  principal-log scalar remainder is analytic at zero

DONE / #146 — SCALAR <-> PRODUCTION BRIDGE
  removable scalar factor = production complex scalar factor for z != 0
  removable scalar remainder = production complex remainder for z != 0
  exact positive-real provenance back to the production real scalar formulas

DERIVED POST-#146
  the production scalar remainder has a removable analytic singularity at zero
  the scalar point singularity is no longer the obstacle to aperture holomorphy

NOW — A4R1b GENUINE PARAMETER HOLOMORPHY
  prove complex differentiability / analyticity of the exact fixed-unit production
  source integrals as functions of the aperture parameter

  required ingredients:
    fixed integration domain
    local denominator nonvanishing / zero-free control
    pointwise complex differentiability in the parameter
    locally uniform integrable domination for differentiation under the integral

  first prototype:
    complexBetaCore

  then:
    complexAlphaCore
    complexGammaCore
    assembled complexFrozenCanonicalSourceRemainder
    assembled complexFrozenIntrinsicPredecessorRemainder

  IMPORTANT:
    deck-periodicity and translation identities are structural equalities only;
    they do not imply holomorphy.

THEN — DETERMINANT REGULARITY
  determinant of the holomorphic lifted predecessor
  -> prove determinant is not identically zero
  -> isolated zero set / dense real regular apertures on each physical cell

THEN — A4R1c REGULAR CELL-MINIMAL FIRST-BAD CERTIFICATE
  choose least bad size K* over the whole cutoff cell
  all K<K* are good in both parities throughout the cell
  predecessor size N*=K*-1 is PSD throughout the cell
  #142 gives open persistent-negative J for the selected witness
  dense regularity gives L2 in J
  PSD + injective -> positive definite predecessor
  #140 gives unique x0 with A x0=b
  package Ecanonical(c-x0)=Re S0<0

DECISIVE OPEN ARITHMETIC TARGET
  prove, from exact canonical pole/arch/scalar/prime interaction,

    Ecanonical(c-x0)>=0

  on the exact forced regular state.

  Equivalent inverse shorthand after regularity:

    <b,A^-1 b> <= q_c.

  Do not obtain this by defining an auxiliary positive form whose positivity is
  equivalent to successor PSD.

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
  parameter-integral holomorphy
  -> assembled frozen predecessor holomorphy
  -> determinant nonidentity
  -> dense regularity
  -> regular cell-minimal first-bad countercertificate
  -> exact regular Schur-energy arithmetic sign
  -> contradiction with forced Re S0<0
  -> no off-line zero through existing reduction
  -> explicit terminal Mathlib RiemannHypothesis wrapper
  RH OPEN
```

## Exact post-#142 theorem packages now consumed by the route

### PR #144

The production/log-cover scaffold lives in the frozen source and predecessor modules. Headline theorem objects include:

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

These are exact algebraic/production bridges and deck laws. They do **not** prove that the parameter-dependent remainder is holomorphic.

### PR #145

`CanonicalApertureHolomorphy.lean` proves local analyticity only for the removable scalar layer at zero.

### PR #146

The same module proves the removable scalar factor/remainder agrees exactly with the production complex scalar/remainder away from zero and agrees with the real production formulas on `L>0`.

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
2. The post-#146 function `F(z)=-z+Re z` is a minimal negative control for the inference "translation/deck law implies holomorphy". It has the relevant affine deck-shift behavior but is not complex differentiable.
3. The removable scalar quotient is not globally entire: the divided exponential slope has nonzero zeros at `2*pi*i*k` for nonzero integers `k`. The theoremized scalar analyticity is local at zero, with production equality on the punctured domain.
4. Holomorphy of a determinant does not imply determinant nonidentity.
5. Dense regularity does not imply the final canonical arithmetic sign.

## Highest-leverage next move

Prove one genuine parameter-integral analyticity theorem for the simplest fixed-unit production core, preferably `complexBetaCore`, with explicit local domination. If that proof pattern survives unchanged normalization and exact production provenance, reuse it for the remaining cores before assembling the frozen source/predecessor holomorphy theorem.

**RH remains OPEN.**
