# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

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

Live GitHub head + exact Lean/compiler/CI remain authoritative.

## One-screen frontier

```text
DONE THROUGH #148
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
  fixed-cell same-witness persistence
  exact frozen/log-cover predecessor scaffold
  scalar removable layer + production bridge
  fixed-unit alpha/beta/gamma parameter holomorphy

DONE / #150 — REGULARIZATION PIPELINE CLOSED
  explicit punctured source domain
  pole denominator zero-freeness on that domain
  full frozen prime/pole/scalar/source entrywise holomorphy
  actual intrinsic predecessor scalar-coordinate holomorphy
  lifted predecessor scalar-coordinate holomorphy
  deck-shift characteristic-polynomial determinant nonidentity
  lifted determinant analyticity on the true lifted domain
  connected/preconnected rigidity corridor
  regular predecessor in every nonempty open interval of a physical cell
  whole-cell least bad size
  smaller-size goodness survives aperture motion
  regular cell-minimal first bad
  unique zero-shift preimage A x0=b
  safe negative explicit root
  exact parity canonical energy < 0
  exact canonical pole/arch/scalar/prime channel energy < 0
  off-line zero -> one finite regular negative-energy certificate

NOW — A4b2r REGULAR SELECTED-RESIDUAL ARITHMETIC
  preserve/export the full first-bad ancestry instead of compressing it away
  reproduce/theoremize the exact pole integral
  reproduce/theoremize pole-minus-prime discrepancy identity
  theoremize boundary-flat source-atom Taylor annihilation
  theoremize sixth-order Riesz-smoothed discrepancy identity
  theoremize stronger even-parity eighth-order smoothing where applicable
  interval-certify candidate sign mechanisms on actual canonical states

DECISIVE OPEN ARITHMETIC TARGET
  prove, on the exact forced #150 state,

    Ecanonical(c-x0) >= 0

  equivalently, after regularity permits inverse shorthand,

    <b,A^-1 b> <= q_c.

BROAD FALLBACK
  universal q_c>=0 and Delta(w)>=0 remains sufficient but is not a research
  reduction if its proof simply restates successor positivity.

PARALLEL / SUPPORTIVE
  simultaneous both-parity / finite-tower regular certificate
  cross-parity source transfer at a fully regular state
  low-rank displacement compression of <b,A^-1b>
  Schur residual envelope derivative
  positive-pivot / first-sign-flip recurrence search
  interval-certified prime-threshold and aperture sensitivity probes

LOWER PRIORITY
  E4-B shifted-nullity
  E3-C secular monotonicity/root-count control
  E3-B3 lower-floor deformation
  deformation-budget diagnostic

TARGET
  exact cancellation-preserving arithmetic identities
  -> independent selected-residual nonnegativity theorem
  -> contradiction with #150 exact negative channel energy
  -> negative-root exclusion
  -> explicit outside-strip/trivial-zero seam
  -> Mathlib RiemannHypothesis wrapper
  RH OPEN
```

## Exact #150 theorem package consumed by the new frontier

### Source assembly / intrinsic holomorphy

```text
complexFrozenSourceDomain
isOpen_complexFrozenSourceDomain
analyticOnNhd_complexFrozenCanonicalSourceRemainder_apply_sourceDomain
analyticOnNhd_complexFrozenCanonicalSourceRemainder_toEuclideanLin_apply_sourceDomain
analyticOnNhd_complexFrozenParityCompressedRemainder_apply_sourceDomain
analyticOnNhd_complexFrozenIntrinsicPredecessorRemainder_coord_sourceDomain
liftedFrozenPredecessorDomain
analyticOnNhd_liftedFrozenIntrinsicPredecessorBlock_coord
```

### Deck-forced determinant rigidity

```text
exists_nat_det_sub_smul_id_ne_zero
liftedFrozenIntrinsicPredecessorBlock_add_nat_two_pi_I
exists_nat_deck_translate_liftedFrozenIntrinsicPredecessor_det_ne_zero
liftedFrozenIntrinsicPredecessor_det_not_identically_zero
```

### Analytic regularity

```text
liftedFrozenRigidityDomain
isPreconnected_liftedFrozenRigidityDomain
analyticOnNhd_liftedFrozenIntrinsicPredecessorDet
exists_mem_liftedFrozenRigidityDomain_det_ne_zero
exists_intrinsicPredecessorRegular_in_open_fixedCell
```

### Cell-minimal / energy closure

```text
CellAnyParityBad
exists_least_cellAnyParityBad_two_le
not_anyParityBad_of_lt_cellMinimal
exists_regular_cellMinimal_firstBad
exists_regular_cellMinimal_negativeCanonicalEnergy
exists_fixedCanonicalCutoffCell_point_above
exists_regularFirstBad_negativeCanonicalEnergy_of_offLine_zero
exists_regularFirstBad_negativeCanonicalEnergy_of_exists_offLine_zero
```

## Exact formal endpoint

The current formal endpoint from a hypothetical off-line zero is:

```text
exists Q,N,L,p,x0,lam,
  1 <= Q
  1 <= N
  L in fixedCanonicalCutoffCell Q
  IntrinsicPredecessorRegular p L N
  lam < 0
  intrinsicPredecessorBlock p L N x0
    = intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)
  canonicalSourceChannelEnergy L (N+1)
    (cubicZeroShiftTrialVector p L N x0) < 0.
```

No theorem currently proves that the final energy must be nonnegative.

## Full-certificate retention

The next theorem-facing interface should preserve more of the construction state.

Valuable facts currently available in the construction include:

```text
K* minimal over the whole physical cutoff cell
all M<K* good throughout the cell
both parities nonnegative at every smaller size
selected negative witness persists on an open interval
selected parity predecessor regular at the chosen L
negative root lam
unique A x0=b
negative exact source-channel energy.
```

### Candidate strengthening

**DERIVED / OPEN FORMALIZATION:** because each fixed `(p,N)` regular set meets every nonempty open interval, a finite nested-open selection should allow one aperture in the persistent-negative interval at which all finitely many predecessor blocks below `K*` and both parities are regular simultaneously.

If formalized, smaller-size goodness + regularity upgrades the entire finite predecessor tower to positive definite blocks.

This may be useful for cross-parity or Schur-pivot recurrences, but it is not required merely to state the current negative certificate.

## Arithmetic first break — cancellation before inequality

The strongest post-#150 external reduction is the proposed exact identity

```text
E_pole(u)-E_prime(u)
  = (1/L) * integral_0^L D(t) * g_u'(1-t/L) dt
```

where

```text
D(t)=4*sinh(t/2)-sum_{q<=exp(t)} Lambda(q)/sqrt(q)
g_u(omega)=<sourceMatrix(omega)u,u>.
```

**Status:** EXTERNAL DERIVED; repository reproduction and Lean theoremization required.

This becomes the first arithmetic identity to verify because it preserves the very cancellation that coarse channel bounds lose.

## Boundary-flat Riesz smoothing

Legal boundary-flat vectors satisfy

```text
M0=M1=M2=0.
```

The exact elementary atom expansion is **DERIVED** to begin

```text
g_u(omega)
  = -(8*pi^6/315)|M3|^2 omega^7 + O(omega^9).
```

For even parity, `M3=0` and the first possible term is

```text
(4*pi^8/2835)|M4|^2 omega^9 + O(omega^11).
```

Conditional on the discrepancy identity, repeated integration by parts gives candidate exact identities

```text
E_pole-E_prime
  = L^-7 * integral D^[6](t) g^(7)(1-t/L) dt
```

and in even parity

```text
E_pole-E_prime
  = L^-9 * integral D^[8](t) g^(9)(1-t/L) dt.
```

**Status:** DERIVED / LEAD, not Lean theorem authority.

## Falsification gates before a sign proof

The following default shortcuts are currently quarantined by numerical/external evidence:

1. global aperture Loewner monotonicity;
2. global minimizing-trial Schur monotonicity;
3. universal positive elementary source-atom energy;
4. independent coarse absolute majorants for pole/arch/scalar/prime channels.

Any revival must state the changed premise and survive interval-certified tests on the exact canonical scope.

The `L*coth(L/2)` / `2*pi*i` deck analogy is also downgraded: coth uses the aperture coordinate, while the deck law acts in the log-aperture coordinate after `L=exp z`.

## Highest-leverage next theorem sequence

```text
FB-01  retain full #150 certificate / optional finite simultaneous regularity
FB-02  theoremize exact pole integral + pole-minus-prime discrepancy
FB-03  theoremize boundary-flat Taylor annihilation + Riesz smoothing
FB-04  interval-certify/falsify candidate arithmetic inequalities
FB-05  prove Ecanonical(c-x0)>=0 on the exact forced state
FB-06  compose with #150 -> negative-root exclusion
FB-07  outside-strip/trivial-zero seam -> Mathlib RH wrapper
```

The first three are identity/compression work. They should not claim the final sign.

## Permanent firewalls

1. Regular predecessor is not a positive successor.
2. `A>=0` + regular gives `A>0` only as a **DERIVED** finite Hermitian consequence unless separately packaged.
3. The open-interval theorem supports a dense-set interpretation but “dense regular set” is not the exact exported declaration.
4. The stronger arbitrarily-far-out regular negative certificate is a natural #140/#150 composition but is not yet a named theorem.
5. The external discrepancy identity is not Lean authority until reproduced.
6. Riesz smoothing is not a sign theorem.
7. Cross-parity/displacement structure remains generic unless actual canonical arithmetic is spent.
8. Numerical evidence is not theorem authority.
9. Machine claim promotion remains separate from compiler theorem validity.
10. Negative-root exclusion is still not the terminal Mathlib RH statement without the final seam.

Newest research delta:

`RESEARCH_LEADS_POST_150_REGULARIZATION_CLOSED_ARITHMETIC_FRONTIER_DELTA.md`

**RH remains OPEN.**
