# RHRC formal audit — theorem authority through PR #150; arithmetic residual frontier

> **RH remains OPEN.**

## Current authority split

```text
live main after merged PR #150 = fb92d5749d6f7a65cfc9129d49d8213219c059db
live main tree = 999ef44d44855cdffd5be5843e9f072867c0a7a8

theorem-state anchor = PR #150 merge fb92d5749d6f7a65cfc9129d49d8213219c059db
validated theorem head = b1be9eca5f544d4356ea88089c0f7264f75d2220
validated theorem tree = 999ef44d44855cdffd5be5843e9f072867c0a7a8
RHRC #971 / run 34690959720 = SUCCESS
Permansson #744 / run 34690959699 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose.

## Exact validation evidence for #150

At validated theorem head

```text
b1be9eca5f544d4356ea88089c0f7264f75d2220
```

RHRC run #971 (`34690959720`) completed successfully.

Successful RHRC jobs included:

```text
python-rhrc
r003-normalization-audit
lean
```

The Lean job successfully completed:

```text
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden placeholder/project-axiom scan
```

The R003 normalization job successfully completed the normalization lock, finite-dictionary guard, source-normalization firewall, R004 scalar-shift audit and external-reference dependency firewall.

Permansson run #744 (`34690959699`) also completed successfully on the same theorem head.

The validated theorem head and merged `main` share theorem tree

```text
999ef44d44855cdffd5be5843e9f072867c0a7a8.
```

## Exact theorem-state progression relevant to #150

### PR #136 — absolute canonical source energy

**PROVED:** scalar-sensitive canonical self-energy; exact pole/arch/scalar/prime channel decomposition; cubic-shell energy; regular zero-shift trial energy `= Re S0`; negative explicit Schur root -> negative canonical trial energy.

### PR #137 — one-step determinant reduction

**PROVED:** exact complex source pairing and

```text
Delta(w)=q_c*q_A(w)-|<w,b>|^2.
```

Also PROVED: conditional domination sufficiency and the global off-line-zero sign-failure countercertificate.

No theorem proves the domination certificate itself.

### PR #140 — aperture freedom / regularity scaffold

**PROVED:** every sufficiently large aperture carries finite canonical badness under an off-line zero; regular predecessor `iff` determinant nonzero `iff` injective; regularity gives a unique zero-shift preimage; physical frozen-cutoff and scalar `-log L` interfaces are exact.

### PR #142 — fixed-cell continuity / persistence

**PROVED:** actual source continuity on a physical cutoff cell and same-size/same-vector persistence of a strict negative witness on an open in-cell neighborhood.

### PR #144-#148 — analytic prerequisites

**PROVED:** exact frozen source/predecessor/log-cover scaffold; removable scalar layer and production bridge; connected archimedean safe strip; genuine fixed-unit alpha/beta/gamma parameter holomorphy.

### PR #150 — assembled source holomorphy

**PROVED:** the common punctured source domain

```text
complexFrozenSourceDomain = complexArchSafeStrip \ {0}
```

is open and carries exact source-channel holomorphy.

Headline validated declarations include:

```text
analyticOnNhd_complexFrozenCanonicalPrimeMatrix_apply_sourceDomain
complexPoleQuadraticDenominator_ne_zero
analyticOnNhd_complexCanonicalPoleMatrix_apply_sourceDomain
analyticOnNhd_complexApertureScalarRemainder_sourceDomain
analyticOnNhd_complexFrozenCanonicalSourceRemainder_apply_sourceDomain
```

### PR #150 — actual predecessor holomorphy

**PROVED:** applying the exact frozen source to fixed vectors, parity-compressing it and projecting to the actual intrinsic predecessor preserves scalar-coordinate analyticity.

Validated declarations include:

```text
analyticOnNhd_complexFrozenCanonicalSourceRemainder_toEuclideanLin_apply_sourceDomain
analyticOnNhd_complexFrozenParityCompressedRemainder_apply_sourceDomain
analyticOnNhd_complexFrozenIntrinsicPredecessorRemainder_coord_sourceDomain
analyticOnNhd_liftedFrozenIntrinsicPredecessorRemainder_coord
analyticOnNhd_liftedFrozenIntrinsicPredecessorBlock_coord
```

### PR #150 — determinant rigidity

**PROVED:**

```text
exists_nat_det_sub_smul_id_ne_zero
liftedFrozenIntrinsicPredecessorBlock_add_nat_two_pi_I
exists_nat_deck_translate_liftedFrozenIntrinsicPredecessor_det_ne_zero
liftedFrozenIntrinsicPredecessor_det_not_identically_zero.
```

The proof is purely finite-dimensional/algebraic: if all deck scalar shifts were singular, one monic characteristic polynomial would have infinitely many distinct roots.

### PR #150 — determinant analyticity / open-interval regularity

**PROVED:** the lifted determinant is analytic on the true lifted domain; a connected/preconnected rigidity corridor contains the real physical logarithms and a deck nonzero witness; analytic identity machinery gives

```text
exists_intrinsicPredecessorRegular_in_open_fixedCell.
```

Exact content: every nonempty open real interval inside one fixed physical cutoff cell contains an aperture where the actual intrinsic predecessor is regular.

**DERIVED terminology:** the regular apertures are dense in the cell.

### PR #150 — cell-minimal regular first bad

**PROVED:**

```text
CellAnyParityBad
exists_least_cellAnyParityBad_two_le
not_anyParityBad_of_lt_cellMinimal
exists_regular_cellMinimal_firstBad.
```

The minimum is taken over the whole physical cell before moving the aperture. This prevents loss of the smaller-size-good conclusion.

### PR #150 — exact negative energy endpoint

**PROVED:**

```text
exists_regular_cellMinimal_negativeCanonicalEnergy
```

and the ExceptionalZero wrappers

```text
exists_fixedCanonicalCutoffCell_point_above
exists_regularFirstBad_negativeCanonicalEnergy_of_offLine_zero
exists_regularFirstBad_negativeCanonicalEnergy_of_exists_offLine_zero.
```

Thus a hypothetical off-line zero forces one finite regular state with unique zero-shift preimage and strictly negative exact canonical source-channel energy.

## What is not yet proved

No current theorem establishes:

```text
positive definiteness as a separately packaged property of the selected predecessor
simultaneous regularity of every smaller predecessor block in both parities
an exported full certificate retaining whole-cell K* minimality through the outer energy wrapper
exact pole-minus-prime discrepancy identity in the new post-#150 form
boundary-flat Taylor annihilation through order six/eight as a dedicated theorem
sixth/eighth-order Riesz-smoothed discrepancy identity
regular selected-residual nonnegativity Ecanonical(c-x0)>=0
universal canonical one-step domination
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

The first three are strengthening/interface opportunities. The selected-residual sign is the decisive current arithmetic gap.

## Derived post-#150 consequences

At the selected state:

```text
A>=0
A regular
```

are theorem-backed. Since the predecessor is finite-dimensional Hermitian, **DERIVED**:

```text
A>0.
```

The theorem `exists_intrinsicPredecessorRegular_in_open_fixedCell` supports the **DERIVED** dense-set interpretation but the exact theorem API is the open-interval existential statement.

The stronger “regular negative certificates arbitrarily far out” statement is a natural #140/#150 composition but is not yet a named theorem and remains DERIVED.

## Post-#150 research state

The analytic/regularization obstruction is closed. The active question is the sign of the exact regular zero-shift residual.

The highest-value external reduction is a cancellation-preserving pole/prime discrepancy identity. The project synthesis further derives high-order endpoint annihilation from the exact boundary-flat moments and candidate sixth/eighth-order Riesz smoothing. These are recorded in the newest research delta with non-theorem labels.

## Active falsification constraints

Current evidence argues against using, as default proof mechanisms:

```text
global aperture Loewner monotonicity
global minimizing-trial Schur monotonicity
universal positive elementary source-atom energy
independent loose absolute channel majorants
```

These are EXPERIMENTAL SIGNAL / quarantined research shortcuts, not universal mathematical theorems.

The apparent coth/deck lattice coincidence is also downgraded because the coth factor uses the aperture variable while the exact deck translation acts in the log-aperture variable.

## Current execution order

```text
1. retain/export the full #150 first-bad certificate
2. reproduce/theoremize exact pole integral and pole-minus-prime discrepancy
3. theoremize boundary-flat Taylor annihilation + Riesz smoothing
4. interval-certify/falsify candidate selected-residual sign mechanisms
5. prove Ecanonical(c-x0)>=0 on the exact forced state
6. compose with #150 to negative-root exclusion
7. close outside-strip/trivial-zero seam
8. explicit Mathlib RiemannHypothesis wrapper
```

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- theorem authority is through #150 and no further;
- supporting compiler-proved theorems are not automatically machine-promoted claims;
- regularity is not successor positivity;
- nonnegative + regular predecessor -> positive definite is DERIVED unless separately packaged;
- exact negative source-channel energy is not contradiction without an independent nonnegative sign theorem;
- external exact derivation != Lean theorem;
- Riesz smoothing != arithmetic sign;
- numerical precision != theorem authority;
- generic/modified-source countermodel != zeta counterexample;
- D algebraic != D unitary/isometric;
- no division by unproved transfer/source factors;
- negative-root exclusion != terminal Mathlib RH without the final seam;
- RH remains OPEN.

Newest research implications: `research/RHRC/RESEARCH_LEADS_POST_150_REGULARIZATION_CLOSED_ARITHMETIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**
