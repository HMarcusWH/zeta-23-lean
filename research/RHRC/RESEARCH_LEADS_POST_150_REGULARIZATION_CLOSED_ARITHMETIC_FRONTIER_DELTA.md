# Post-#150 research delta — regularization closed, arithmetic residual frontier

Date: 2026-09-12

> **Claim firewall:** this document records the post-green research state after merged PR #150. Compiler/CI evidence is authoritative for theorem validity. DERIVED statements, external reviews and numerical experiments are not silently promoted to Lean theorems. **RH remains OPEN.**

## Exact authority

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

The validated theorem head and merged `main` have the same theorem tree.

## What became formally true

### 1. Full frozen source assembly is analytic on one explicit source domain

PR #150 theorem-locks the common punctured strip

```text
complexFrozenSourceDomain = complexArchSafeStrip \ {0}
```

and proves the exact production pieces analytic there, including the frozen prime channel, pole channel, scalar remainder and the full frozen source remainder.

Headline theorem:

```text
analyticOnNhd_complexFrozenCanonicalSourceRemainder_apply_sourceDomain
```

The source theorem is entrywise because that is the exact finite-coordinate interface required downstream.

### 2. Actual intrinsic predecessor scalar coordinates are analytic

PR #150 pushes source holomorphy through the actual Euclidean application, parity compression and intrinsic predecessor projection.

Headline declarations include:

```text
analyticOnNhd_complexFrozenCanonicalSourceRemainder_toEuclideanLin_apply_sourceDomain
analyticOnNhd_complexFrozenParityCompressedRemainder_apply_sourceDomain
analyticOnNhd_complexFrozenIntrinsicPredecessorRemainder_coord_sourceDomain
analyticOnNhd_liftedFrozenIntrinsicPredecessorRemainder_coord
analyticOnNhd_liftedFrozenIntrinsicPredecessorBlock_coord
```

The logarithmic-cover domain is explicit and open; deck-domain membership is theoremized.

### 3. Deck law forces determinant nonidentity algebraically

PR #150 proves, independently of holomorphy:

```text
exists_nat_det_sub_smul_id_ne_zero
liftedFrozenIntrinsicPredecessorBlock_add_nat_two_pi_I
exists_nat_deck_translate_liftedFrozenIntrinsicPredecessor_det_ne_zero
liftedFrozenIntrinsicPredecessor_det_not_identically_zero
```

The mathematical mechanism is finite-dimensional characteristic-polynomial rigidity:

```text
B(z + 2*pi*i) = B(z) - (2*pi*i) I
```

forces a nonzero determinant somewhere on every natural deck orbit, because one nonzero finite characteristic polynomial cannot have infinitely many distinct scalar roots.

**Structural conclusion:** the nonidentity seed is algebraic. It does not require a numerical determinant witness.

### 4. Analyticity upgrades nonidentity to real regular-aperture selection

PR #150 defines a connected/preconnected rigidity corridor containing the physical real logarithms and the deck witness, proves the lifted determinant analytic there, and proves:

```text
exists_intrinsicPredecessorRegular_in_open_fixedCell
```

Exact theorem content: every nonempty open real interval contained in one physical cutoff cell contains an aperture where the actual intrinsic predecessor is regular.

**DERIVED interpretation:** regular apertures are dense in the physical cell for each fixed `(Q,p,N)`. The exact Lean declaration is the open-interval selection theorem above.

### 5. Cell-minimal first-bad regular selection is theorem-backed

PR #150 adds:

```text
CellAnyParityBad
exists_least_cellAnyParityBad_two_le
not_anyParityBad_of_lt_cellMinimal
exists_regular_cellMinimal_firstBad
```

The crucial quantifier order is now formal:

```text
choose K* minimal over the whole cutoff cell
-> every smaller size is good throughout that cell
-> preserve one strict negative witness on an open subset
-> select a regular aperture inside that same negative open set.
```

The headline regular-first-bad theorem exports, at the selected aperture:

```text
2 <= K*
1 <= N*
N*+1 = K*
L in fixed cutoff cell
ParityBad p L K*
all M<K* are not AnyParityBad at L
IntrinsicPredecessorRegular p L N*.
```

### 6. The regular first-bad state carries exact negative canonical source-channel energy

PR #150 proves:

```text
exists_regular_cellMinimal_negativeCanonicalEnergy
```

It packages one selected regular predecessor together with:

```text
lam < 0
intrinsicPredecessorBlock p L N x0
  = intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)
parityCanonicalSourceEnergy ... (cubicZeroShiftTrialVector ... x0) < 0
canonicalSourceChannelEnergy ... (cubicZeroShiftTrialVector ... x0) < 0.
```

The `ExceptionalZero` wrapper then proves:

```text
exists_fixedCanonicalCutoffCell_point_above
exists_regularFirstBad_negativeCanonicalEnergy_of_offLine_zero
exists_regularFirstBad_negativeCanonicalEnergy_of_exists_offLine_zero
```

Therefore a hypothetical off-line zeta zero now forces one finite actual-production regular state with a unique zero-shift preimage and strictly negative exact pole/arch/scalar/prime source-channel energy.

## Exact post-#150 theorem chain

```text
off-line zero
  -> every sufficiently large aperture has finite canonical badness          PROVED / #140
  -> choose one sufficiently large physical cutoff cell                     PROVED / #150 wrapper
  -> least bad size over the whole cell                                     PROVED / #150
  -> every smaller size good throughout the cell                            PROVED / #150 minimum interface
  -> selected negative witness persists on an open in-cell set              PROVED / #142
  -> every such open interval contains an actual regular predecessor point  PROVED / #150
  -> regular cell-minimal first-bad state                                   PROVED / #150
  -> unique zero-shift preimage A x0=b                                      PROVED via #140/#150
  -> safe negative explicit Schur root                                      PROVED through existing spectrum/Schur chain
  -> exact canonical zero-shift trial energy < 0                            PROVED / #150
  -> exact canonical source-channel energy < 0                              PROVED / #150
```

This is the new formal endpoint. It is not yet a contradiction.

## What changed

The active obstruction has moved decisively.

Before #150, singular/resonant predecessor geometry could block the canonical zero-shift trial. After #150, the forced state is selected at a regular predecessor. The analytic/log-cover/determinant mechanics are no longer the active bottleneck.

The remaining central question is now:

```text
Can the exact canonical zero-shift residual selected by #150 actually have negative energy?
```

At the selected state, the predecessor is nonnegative by smaller-size goodness and regular by construction.

**DERIVED:** using the already-proved Hermitian finite-dimensional predecessor structure, nonnegative + regular implies positive definite.

Thus inverse shorthand may be used mathematically:

```text
x0 = A^-1 b
u0 = c - A^-1 b
S0 = q_c - <b,A^-1 b>
Ecanonical(u0) = Re S0 < 0.
```

Formal Lean should continue to prefer the exact unique-preimage equation `A x0=b` unless a dedicated inverse API is useful.

## Full construction state versus exported endpoint

A potentially important information loss is now visible.

The cell-minimal construction internally has stronger ancestry than the outer ExceptionalZero certificate exports:

```text
K* is minimal over the whole physical cell
for every M<K* and every L in that cell: not AnyParityBad L M
both parity sectors at every smaller size are therefore nonnegative
one selected bad witness persists on an open set
the selected parity predecessor is regular at the chosen L.
```

`exists_regular_cellMinimal_firstBad` exports smaller-size goodness at the selected aperture, while `exists_regular_cellMinimal_negativeCanonicalEnergy` and the outer ExceptionalZero wrapper intentionally compress the tuple further.

**LEAD:** retain more of this ancestry in the next theorem interface before arithmetic work discards it. In particular, investigate whether one can select the persistent-negative aperture while making all finitely many predecessor blocks below `K*`, in both parities, regular simultaneously. Dense-open finite intersection should make this plausible, but it is **DERIVED / OPEN FORMALIZATION**, not current theorem authority.

If successful, the forced state would carry a positive predecessor tower rather than one positive predecessor block.

## External Astra post-#150 reduction

The associated Astra audit is preserved separately in:

`external_reviews/ASTRA_POST_150_ARITHMETIC_FRONTIER_ASSESSMENT_2026_09_12.md`.

Its strongest new algebraic reduction is a pole-minus-prime discrepancy identity. In schematic exact form:

```text
E_pole(u) - E_prime(u)
  = (1/L) * integral_0^L D(t) * g_u'(1-t/L) dt
```

with

```text
D(t) = 4*sinh(t/2) - sum_{q <= exp t} Lambda(q)/sqrt(q)
g_u(omega) = <sourceMatrix(omega) u, u>.
```

**Status:** EXTERNAL DERIVED / repository theoremization pending. It is not yet Lean authority.

Research value: it preserves the large pole/prime cancellation before applying inequalities, rather than bounding enormous channels independently.

## Boundary-flat Taylor annihilation and Riesz smoothing

The legal finite carrier has exact boundary-flat moments

```text
M0(u)=M1(u)=M2(u)=0.
```

For the exact elementary source atom, direct Taylor expansion gives

```text
g_u(omega)
  = sum_{r>=0}
      [(-1)^r * 2^(2r+1) * pi^(2r) / (2r+1)!]
      * omega^(2r+1)
      * sum_{a=0}^{2r} conjugate(M_{2r-a}(u))*M_a(u).
```

**DERIVED / not yet Lean-locked.**

Boundary flatness kills the coefficients through order six. The first generic term is

```text
g_u(omega)
  = -(8*pi^6/315) * |M3(u)|^2 * omega^7 + O(omega^9).
```

Hence

```text
g_u^(j)(0)=0,  j=1,...,6.
```

For even parity, odd centered moments vanish, so `M3=0` and the first possible term moves to

```text
g_u(omega)
  = (4*pi^8/2835) * |M4(u)|^2 * omega^9 + O(omega^11),
```

with derivatives through order eight vanishing.

Assuming the exact discrepancy identity above, let

```text
D^[0]=D
D^[r+1](t)=integral_0^t D^[r](s) ds.
```

Repeated integration by parts has no right-endpoint terms because of the boundary-flat Taylor annihilation, and no left-endpoint terms because `D^[r](0)=0`. This gives the candidate exact identities

```text
E_pole(u)-E_prime(u)
  = L^-7 * integral_0^L D^[6](t) * g_u^(7)(1-t/L) dt
```

for every legal boundary-flat `u`, and, in even parity,

```text
E_pole(u)-E_prime(u)
  = L^-9 * integral_0^L D^[8](t) * g_u^(9)(1-t/L) dt.
```

**Status:** DERIVED conditional on the discrepancy identity; awaiting independent exact repository verification and Lean theoremization.

### RH-relevant clue

**LEAD / HYPOTHESIS:** the high-order Riesz smoothing may be substantially easier to bound than the raw von-Mangoldt staircase. Repeated integration suppresses high-frequency/large-zero contributions in explicit-formula representations. Whether the exact archimedean budget can be dominated this way is completely OPEN.

## Analytic Schur residual calculus

Once `A(L)` remains regular locally, define

```text
x(L) by A(L)x(L)=b(L)
u(L)=c-x(L)
S(L)=Ecanonical_L(u(L)).
```

The zero-shift equation makes `u(L)` energy-orthogonal to the predecessor directions. The envelope calculation therefore suggests

```text
S'(L) = <M'(L)u(L),u(L)>.
```

**Status:** DERIVED / needs Lean.

This remains useful for exact sensitivity analysis even though post-#150 experiments indicate that raw scalar Schur monotonicity in the aperture is false.

## Falsification results that must be retained

Preserve the associated evidence with its correct class.

### EXPERIMENTAL SIGNAL — raw aperture Loewner monotonicity fails

Canonical numerical probes show mixed signs in the aperture derivative spectrum rather than a uniform Loewner direction. Do not build a proof around global `M'(L) >= 0` or `<= 0` without a changed premise and exact certification.

### EXPERIMENTAL SIGNAL — zero-shift Schur monotonicity fails

The derivative of the minimizing-trial Schur value changes sign in canonical samples. A global scalar monotonicity shortcut is therefore not a credible default route.

### EXPERIMENTAL SIGNAL — elementary atom energy is signed

The canonical trial atom kernel changes sign; there is no universal positive elementary-atom energy representation available from the tested structure.

### QUARANTINED — independent coarse channel bounds

Post-#138 and post-#150 numerical conditioning show the final Schur endpoint can be a tiny residue of very large pole/arch/scalar/prime contributions. Any inequality that destroys their correlated cancellation must prove it retains enough precision.

### DOWNGRADED LEAD — coth/deck lattice analogy

The removable scalar factor is

```text
L*(exp L + 1)/(exp L - 1) = L*coth(L/2)
```

in the complex aperture variable `L`.

The #150 deck translation is instead in the logarithmic-cover coordinate `z` after `L=exp z`:

```text
Ahat(z+2*pi*i)=Ahat(z)-(2*pi*i)I.
```

Therefore the two appearances of `2*pi*i` do **not** currently define one common lattice object. A transform/conjugacy theorem would be required before using a coth-resolvent identification.

## Upstream implications

1. Consider extracting the deck/characteristic-polynomial argument as a reusable finite-dimensional rigidity theorem independent of CCM.
2. Consider a first-class `RegularFirstBadCertificate` structure that retains cell minimum, smaller-size ancestry, regularity, root and energy data without repeatedly compressing the tuple.
3. Consider theoremizing the finite-intersection strengthening needed for simultaneous regularity of finitely many predecessor blocks.
4. Keep unique-preimage equations primary; introduce `A^-1` only when it materially simplifies arithmetic identities.

## Downstream implications

The old A4R regular-aperture action is complete. The current frontier is the regular selected-residual sign:

```text
Ecanonical(c-x0) >= 0
```

on the exact forced #150 state.

A proof of this scoped sign immediately contradicts the #150 negative certificate. Universal successor positivity is stronger than needed and remains a broad fallback rather than the default target.

## Resurrected routes

### Cross-parity transport

Regular selection removes the selected predecessor resonance, making the #129/#134 parity/source relations cleaner. A stronger simultaneous-both-parity regular selection would make this route more attractive.

### Low-rank displacement

The exact centered displacement identity may become useful again now that a genuine inverse/preimage exists at the selected state. The target would be to compress `<b,A^-1b>` into a small number of source/cubic moments. Generic displacement alone remains insufficient by countermodel.

### Positive predecessor tower

If simultaneous finite regularity is theoremized below `K*`, every earlier one-step pivot would be positive and the final selected Schur pivot negative. A canonical arithmetic recurrence for these pivots could potentially rule out the first sign flip. No such recurrence is presently proved.

## Highest-leverage next moves

1. **Retain the full #150 first-bad state.** Strengthen the exported certificate before throwing away cell-minimal ancestry/opposite-parity information.
2. **Reproduce and theoremize the exact pole integral / pole-minus-prime discrepancy identity.** This is the cleanest cancellation-preserving arithmetic reduction currently visible.
3. **Theoremize boundary-flat Taylor annihilation and the sixth/eighth-order Riesz-smoothed identities.** These are exact algebraic/analytic identities, not the final sign theorem.
4. **Run interval-certified canonical experiments on the exact selected-residual observables.** Falsify candidate sign kernels before committing to long Lean proofs.
5. **Only then attack the independent selected-residual inequality** `Ecanonical(c-x0)>=0`.
6. **After the sign theorem:** compose with #150 to negative-root exclusion, then close the existing outside-strip/trivial-zero seam and the explicit Mathlib `RiemannHypothesis` wrapper.

## Standing questions

Given everything that is now formally true, what becomes possible that was not possible before?

Answer: the project can reason about one exact regular canonical zero-shift residual selected by a hypothetical off-line zero without a resonance escape hatch.

If this contains a clue toward RH, where does it propagate?

Answer: into cancellation-preserving arithmetic identities for the selected residual, particularly the pole/prime discrepancy, boundary-flat stationary atom structure, cross-parity transport and low-rank displacement.

What would most efficiently tell us whether the clue is real?

Answer: exact theoremization of the discrepancy/Riesz identities plus interval-certified tests of the resulting kernel against actual canonical selected states.

## Claim firewall

```text
#150 regularity != positivity
open-interval regular selection != separately theoremized dense-set declaration
nonnegative + regular predecessor -> positive definite is DERIVED unless separately packaged
negative exact source-channel energy != contradiction
external discrepancy derivation != Lean theorem
Taylor/Riesz algebra != arithmetic sign
Riesz smoothing != RH
cross-parity/displacement structure != sign without canonical arithmetic
coth aperture variable != log-cover deck variable
numerical falsification != theorem
negative-root exclusion != terminal Mathlib RH wrapper until the final seam is closed
```

**RH remains OPEN.**
