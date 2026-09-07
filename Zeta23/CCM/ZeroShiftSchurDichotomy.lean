import Zeta23.CCM.ZeroResonanceCoupling
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A2: zero-shift Schur dichotomy infrastructure

This module theoremizes the finite-dimensional kernel/range geometry of the
projected predecessor block

  A = P_W T|_W

and uses it to separate the two zero-shift mechanisms left open by E4-A1.

The key construction is a canonical inverse of `A` only on `range A`. No
whole-space inverse at zero is introduced. The predecessor subtype continues
to use the induced ambient successor inner product explicitly; no nested
`InnerProductSpace` instance is installed.

Firewalls:
* `ker A` is the kernel of the projected successor predecessor block, not the
  predecessor-size compressed-operator kernel;
* the range inverse is not a whole-space `A⁻¹`;
* no branch is asserted to occur at the global first-bad state;
* no zero-shift endpoint sign, root exclusion, positivity, finite-to-infinite,
  or RH theorem is claimed.
-/

/-- Every vector in `range A` is orthogonal, in the induced ambient successor
inner product, to every vector in `ker A`. -/
theorem inner_intrinsicPredecessorBlock_range_kernel_eq_zero
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (y z : intrinsicParityPredecessorSubspace p N)
    (hy : y ∈ LinearMap.range (intrinsicPredecessorBlock p L N))
    (hz : intrinsicPredecessorBlock p L N z = 0) :
    inner ℂ
        (y : euclideanParityBoundaryFlatSubspace p (N + 1))
        (z : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
  rcases hy with ⟨x, rfl⟩
  rw [intrinsicPredecessorBlock_isSymmetric p L N x z, hz]
  simp

/-- The range and kernel of the symmetric projected predecessor block are
disjoint. -/
theorem intrinsicPredecessorBlock_range_disjoint_kernel
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    Disjoint
      (LinearMap.range (intrinsicPredecessorBlock p L N))
      (LinearMap.ker (intrinsicPredecessorBlock p L N)) := by
  rw [disjoint_iff_inf_le]
  intro y hy
  rcases hy with ⟨hyrange, hyker⟩
  have hyzero : intrinsicPredecessorBlock p L N y = 0 := by
    change intrinsicPredecessorBlock p L N y = 0 at hyker
    exact hyker
  have hinner :
      inner ℂ
          (y : euclideanParityBoundaryFlatSubspace p (N + 1))
          (y : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 :=
    inner_intrinsicPredecessorBlock_range_kernel_eq_zero
      p L N y y hyrange hyzero
  have hy0Ambient :
      (y : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 :=
    (inner_self_eq_zero).mp hinner
  have hy0 : y = 0 := by
    apply Subtype.ext
    exact hy0Ambient
  simpa [hy0]

/-- Finite-dimensional rank-nullity upgrades range/kernel disjointness to a
canonical algebraic direct sum `W = ker A ⊕ range A`. -/
theorem intrinsicPredecessorBlock_kernel_isCompl_range
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    IsCompl
      (LinearMap.ker (intrinsicPredecessorBlock p L N))
      (LinearMap.range (intrinsicPredecessorBlock p L N)) := by
  let A := intrinsicPredecessorBlock p L N
  have hdim0 := A.finrank_range_add_finrank_ker
  have hdim :
      Module.finrank ℂ (intrinsicParityPredecessorSubspace p N) ≤
        Module.finrank ℂ (LinearMap.ker A) +
          Module.finrank ℂ (LinearMap.range A) := by
    rw [← hdim0]
    simp [add_comm]
  have hdisjoint : Disjoint (LinearMap.ker A) (LinearMap.range A) := by
    simpa [A] using (intrinsicPredecessorBlock_range_disjoint_kernel p L N).symm
  exact
    (Submodule.isCompl_iff_disjoint
      (LinearMap.ker A) (LinearMap.range A) hdim).2 hdisjoint

/-- Canonical algebraic coordinates `ker A × range A ≃ W`. -/
def intrinsicPredecessorKernelRangeEquiv
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    (LinearMap.ker (intrinsicPredecessorBlock p L N) ×
      LinearMap.range (intrinsicPredecessorBlock p L N)) ≃ₗ[ℂ]
      intrinsicParityPredecessorSubspace p N :=
  Submodule.prodEquivOfIsCompl
    (LinearMap.ker (intrinsicPredecessorBlock p L N))
    (LinearMap.range (intrinsicPredecessorBlock p L N))
    (intrinsicPredecessorBlock_kernel_isCompl_range p L N)

/-- Canonical kernel coordinate in `W = ker A ⊕ range A`. -/
def intrinsicPredecessorKernelPart
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    intrinsicParityPredecessorSubspace p N →ₗ[ℂ]
      LinearMap.ker (intrinsicPredecessorBlock p L N) :=
  Submodule.projectionOnto
    (LinearMap.ker (intrinsicPredecessorBlock p L N))
    (LinearMap.range (intrinsicPredecessorBlock p L N))
    (intrinsicPredecessorBlock_kernel_isCompl_range p L N)

/-- Canonical range coordinate in `W = ker A ⊕ range A`. -/
def intrinsicPredecessorRangePart
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    intrinsicParityPredecessorSubspace p N →ₗ[ℂ]
      LinearMap.range (intrinsicPredecessorBlock p L N) :=
  Submodule.projectionOnto
    (LinearMap.range (intrinsicPredecessorBlock p L N))
    (LinearMap.ker (intrinsicPredecessorBlock p L N))
    (intrinsicPredecessorBlock_kernel_isCompl_range p L N).symm

/-- Kernel plus range coordinates reconstruct every predecessor vector. -/
theorem intrinsicPredecessorKernelPart_add_rangePart
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) :
    ((intrinsicPredecessorKernelPart p L N w :
        LinearMap.ker (intrinsicPredecessorBlock p L N)) :
      intrinsicParityPredecessorSubspace p N) +
      ((intrinsicPredecessorRangePart p L N w :
          LinearMap.range (intrinsicPredecessorBlock p L N)) :
        intrinsicParityPredecessorSubspace p N) = w := by
  exact Submodule.projection_add_projection_eq_self
    (intrinsicPredecessorBlock_kernel_isCompl_range p L N) w

/-- If a predecessor vector annihilates `ker A` in the second slot, then it
lies in `range A`. This is the repository-native finite symmetric form of
`(ker A)ᗮ = range A`, stated without a nested inner-product instance. -/
theorem mem_intrinsicPredecessorBlock_range_of_inner_kernel_eq_zero
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (b : intrinsicParityPredecessorSubspace p N)
    (horth :
      ∀ z : intrinsicParityPredecessorSubspace p N,
        intrinsicPredecessorBlock p L N z = 0 →
          inner ℂ
            (z : euclideanParityBoundaryFlatSubspace p (N + 1))
            (b : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0) :
    b ∈ LinearMap.range (intrinsicPredecessorBlock p L N) := by
  let k := intrinsicPredecessorKernelPart p L N b
  let r := intrinsicPredecessorRangePart p L N b
  have hkzero : intrinsicPredecessorBlock p L N
      (k : intrinsicParityPredecessorSubspace p N) = 0 := by
    exact k.property
  have hkb :
      inner ℂ
          ((k : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 :=
    horth (k : intrinsicParityPredecessorSubspace p N) hkzero
  have hrk :
      inner ℂ
          ((r : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          ((k : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 :=
    inner_intrinsicPredecessorBlock_range_kernel_eq_zero
      p L N
      (r : intrinsicParityPredecessorSubspace p N)
      (k : intrinsicParityPredecessorSubspace p N)
      r.property hkzero
  have hkr :
      inner ℂ
          ((k : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          ((r : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
    rw [inner_eq_zero_symm]
    exact hrk
  have hrec := intrinsicPredecessorKernelPart_add_rangePart p L N b
  have hrecAmbient :
      (((k : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) +
        ((r : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))) =
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simpa using
      congrArg
        (fun w : intrinsicParityPredecessorSubspace p N =>
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))) hrec
  have hkk :
      inner ℂ
          ((k : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          ((k : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
    have hkb' := hkb
    rw [← hrecAmbient] at hkb'
    rw [inner_add_right, hkr, add_zero] at hkb'
    exact hkb'
  have hk0Ambient :
      ((k : intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 :=
    (inner_self_eq_zero).mp hkk
  have hk0 : k = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hk0Ambient
  have hrEq :
      (r : intrinsicParityPredecessorSubspace p N) = b := by
    simpa [k, r, hk0] using hrec
  rw [← hrEq]
  exact r.property

/-- `A` restricted to its own range. This is the canonical zero-shift block
that can be inverted even when `A` has a nontrivial whole-space kernel. -/
def intrinsicPredecessorRangeBlock
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    LinearMap.range (intrinsicPredecessorBlock p L N) →ₗ[ℂ]
      LinearMap.range (intrinsicPredecessorBlock p L N) where
  toFun := fun y =>
    ⟨intrinsicPredecessorBlock p L N
        (y : intrinsicParityPredecessorSubspace p N),
      ⟨(y : intrinsicParityPredecessorSubspace p N), rfl⟩⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp

/-- The range-restricted zero-shift block is injective. -/
theorem intrinsicPredecessorRangeBlock_injective
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    Function.Injective (intrinsicPredecessorRangeBlock p L N) := by
  intro x y hxy
  have hAxy :
      intrinsicPredecessorBlock p L N
          ((x : intrinsicParityPredecessorSubspace p N) -
            (y : intrinsicParityPredecessorSubspace p N)) = 0 := by
    have hxy' := congrArg Subtype.val hxy
    change
      intrinsicPredecessorBlock p L N
          (x : intrinsicParityPredecessorSubspace p N) =
        intrinsicPredecessorBlock p L N
          (y : intrinsicParityPredecessorSubspace p N) at hxy'
    rw [map_sub, hxy', sub_self]
  have hrange :
      ((x : intrinsicParityPredecessorSubspace p N) -
          (y : intrinsicParityPredecessorSubspace p N)) ∈
        LinearMap.range (intrinsicPredecessorBlock p L N) :=
    (LinearMap.range (intrinsicPredecessorBlock p L N)).sub_mem
      x.property y.property
  have hdis := intrinsicPredecessorBlock_range_disjoint_kernel p L N
  have hdiffInf :
      ((x : intrinsicParityPredecessorSubspace p N) -
          (y : intrinsicParityPredecessorSubspace p N)) ∈
        LinearMap.range (intrinsicPredecessorBlock p L N) ⊓
          LinearMap.ker (intrinsicPredecessorBlock p L N) := by
    refine ⟨hrange, ?_⟩
    change
      intrinsicPredecessorBlock p L N
          ((x : intrinsicParityPredecessorSubspace p N) -
            (y : intrinsicParityPredecessorSubspace p N)) = 0
    exact hAxy
  have hdiffBot :
      ((x : intrinsicParityPredecessorSubspace p N) -
          (y : intrinsicParityPredecessorSubspace p N)) ∈
        (⊥ : Submodule ℂ (intrinsicParityPredecessorSubspace p N)) := by
    rw [← hdis.eq_bot]
    exact hdiffInf
  have hdiff0 :
      (x : intrinsicParityPredecessorSubspace p N) -
        (y : intrinsicParityPredecessorSubspace p N) = 0 := by
    simpa using hdiffBot
  apply Subtype.ext
  exact sub_eq_zero.mp hdiff0

/-- Canonical zero-shift linear equivalence on `range A`. -/
def intrinsicPredecessorRangeEquiv
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    LinearMap.range (intrinsicPredecessorBlock p L N) ≃ₗ[ℂ]
      LinearMap.range (intrinsicPredecessorBlock p L N) := by
  let AR := intrinsicPredecessorRangeBlock p L N
  have hinj : Function.Injective AR :=
    intrinsicPredecessorRangeBlock_injective p L N
  have hsurj : Function.Surjective AR :=
    LinearMap.injective_iff_surjective.mp hinj
  exact LinearEquiv.ofBijective AR ⟨hinj, hsurj⟩

/-- Canonical zero-shift inverse, defined only on `range A`. -/
def intrinsicPredecessorRangeInverse
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    LinearMap.range (intrinsicPredecessorBlock p L N) →ₗ[ℂ]
      LinearMap.range (intrinsicPredecessorBlock p L N) :=
  (intrinsicPredecessorRangeEquiv p L N).symm.toLinearMap

/-- The canonical range inverse is a right inverse for the range-restricted
zero-shift block. -/
theorem intrinsicPredecessorRangeBlock_rangeInverse_apply
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (b : LinearMap.range (intrinsicPredecessorBlock p L N)) :
    intrinsicPredecessorRangeBlock p L N
        (intrinsicPredecessorRangeInverse p L N b) = b := by
  simpa [intrinsicPredecessorRangeInverse, intrinsicPredecessorRangeEquiv,
    LinearEquiv.ofBijective_apply] using
      (intrinsicPredecessorRangeEquiv p L N).apply_symm_apply b

/-- Ambient predecessor form of the canonical zero-shift solve `A x₀ = b` for
`b ∈ range A`. -/
theorem intrinsicPredecessorBlock_rangeInverse_apply
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (b : LinearMap.range (intrinsicPredecessorBlock p L N)) :
    intrinsicPredecessorBlock p L N
        ((intrinsicPredecessorRangeInverse p L N b :
            LinearMap.range (intrinsicPredecessorBlock p L N)) :
          intrinsicParityPredecessorSubspace p N) =
      (b : intrinsicParityPredecessorSubspace p N) := by
  have h := intrinsicPredecessorRangeBlock_rangeInverse_apply p L N b
  exact congrArg Subtype.val h

/-- Exact resonant identity. If `z ∈ ker A`, then its coupling to an arbitrary
predecessor vector `b` is exactly `(-lam)` times its coupling to the safe
negative-shift resolvent of `b`. -/
theorem inner_intrinsicPredecessorBlock_kernel_resolvent_eq
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (z b : intrinsicParityPredecessorSubspace p N)
    (hz : intrinsicPredecessorBlock p L N z = 0) :
    inner ℂ
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      (-lam : ℂ) *
        inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          ((shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b :
              intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  let y := R b
  have hsym := shiftedIntrinsicPredecessorBlock_isSymmetric p L N lam z y
  have hy : shiftedIntrinsicPredecessorBlock p L N lam y = b := by
    simpa [y, R] using
      shiftedIntrinsicPredecessorBlock_resolvent_apply
        p hL N hprev lam hlam b
  have hzshift :
      shiftedIntrinsicPredecessorBlock p L N lam z = (-lam : ℂ) • z := by
    change
      intrinsicPredecessorBlock p L N z - (lam : ℂ) • z =
        (-lam : ℂ) • z
    rw [hz, zero_sub]
    exact (neg_smul (lam : ℂ) z).symm
  rw [hzshift, hy] at hsym
  calc
    inner ℂ
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
        (((-lam : ℂ) • z : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (y : euclideanParityBoundaryFlatSubspace p (N + 1)) := hsym.symm
    _ = (-lam) •
        inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (y : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
      simpa using
        (inner_smul_real_left (𝕜 := ℂ)
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (y : euclideanParityBoundaryFlatSubspace p (N + 1)) (-lam))
    _ = (-lam : ℂ) *
        inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          ((R b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
      simp [y, R, smul_eq_mul]

/-- Denominator-free resonant lower bound. A nonzero kernel coupling forces a
quantitative `1/(-lam)` contribution in the resolvent quadratic value, stated
without division. -/
theorem norm_sq_inner_kernel_coupling_le_neg_mul_norm_sq_re_inner_resolvent
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (z b : intrinsicParityPredecessorSubspace p N)
    (hz : intrinsicPredecessorBlock p L N z = 0) :
    ‖inner ℂ
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1))‖ ^ 2 ≤
      (-lam) * ‖z‖ ^ 2 *
        Complex.re
          (inner ℂ
            ((shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b :
                intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (b : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  let y := R b
  have hid :=
    inner_intrinsicPredecessorBlock_kernel_resolvent_eq
      p hL N hprev hlam z b hz
  have hneg : 0 ≤ -lam := le_of_lt (neg_pos.mpr hlam)
  have hcs :
      ‖inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1))‖ ≤
        (-lam) * ‖z‖ * ‖y‖ := by
    calc
      ‖inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1))‖ =
        ‖(-lam : ℂ) *
          inner ℂ
            (z : euclideanParityBoundaryFlatSubspace p (N + 1))
            (y : euclideanParityBoundaryFlatSubspace p (N + 1))‖ := by
              simpa [y, R] using congrArg norm hid
      _ = (-lam) *
          ‖inner ℂ
            (z : euclideanParityBoundaryFlatSubspace p (N + 1))
            (y : euclideanParityBoundaryFlatSubspace p (N + 1))‖ := by
              rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
                abs_of_neg hlam]
      _ ≤ (-lam) * (‖z‖ * ‖y‖) := by
              have hinner :
                  ‖inner ℂ
                      (z : euclideanParityBoundaryFlatSubspace p (N + 1))
                      (y : euclideanParityBoundaryFlatSubspace p (N + 1))‖ ≤
                    ‖z‖ * ‖y‖ := by
                simpa only [Submodule.norm_coe] using
                  (norm_inner_le_norm
                    (z : euclideanParityBoundaryFlatSubspace p (N + 1))
                    (y : euclideanParityBoundaryFlatSubspace p (N + 1)))
              exact mul_le_mul_of_nonneg_left hinner hneg
      _ = (-lam) * ‖z‖ * ‖y‖ := by ring
  have hleft0 :
      0 ≤ ‖inner ℂ
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1))‖ := norm_nonneg _
  have hright0 : 0 ≤ (-lam) * ‖z‖ * ‖y‖ := by
    exact mul_nonneg (mul_nonneg hneg (norm_nonneg z)) (norm_nonneg y)
  have hsquare :
      ‖inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1))‖ ^ 2 ≤
        ((-lam) * ‖z‖ * ‖y‖) ^ 2 := by
    nlinarith
  have hcoercive :=
    neg_mul_norm_sq_resolvent_le_re_inner p hL N hprev hlam b
  change
    (-lam) * ‖y‖ ^ 2 ≤
      Complex.re
        (inner ℂ
          (y : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1))) at hcoercive
  have hfactor : 0 ≤ (-lam) * ‖z‖ ^ 2 := by
    exact mul_nonneg hneg (sq_nonneg ‖z‖)
  have hmul := mul_le_mul_of_nonneg_left hcoercive hfactor
  calc
    ‖inner ℂ
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1))‖ ^ 2 ≤
      ((-lam) * ‖z‖ * ‖y‖) ^ 2 := hsquare
    _ = ((-lam) * ‖z‖ ^ 2) * ((-lam) * ‖y‖ ^ 2) := by ring
    _ ≤ ((-lam) * ‖z‖ ^ 2) *
        Complex.re
          (inner ℂ
            (y : euclideanParityBoundaryFlatSubspace p (N + 1))
            (b : euclideanParityBoundaryFlatSubspace p (N + 1))) := hmul
    _ = (-lam) * ‖z‖ ^ 2 *
        Complex.re
          (inner ℂ
            ((R b : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (b : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
      simp [y, R, mul_assoc]

/-- Cubic specialization of the decoupled branch: if the canonical cubic
coupling vanishes on `ker A`, then the coupling vector belongs to `range A` and
therefore has a canonical zero-shift range inverse. -/
theorem cubicCoupling_mem_intrinsicPredecessorBlock_range_of_zero_on_kernel
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hzero :
      ∀ z : intrinsicParityPredecessorSubspace p N,
        intrinsicPredecessorBlock p L N z = 0 →
          inner ℂ
            (z : euclideanParityBoundaryFlatSubspace p (N + 1))
            ((intrinsicShellToPredecessor p L N
                (intrinsicCubicShellPart p N) :
                intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) = 0) :
    intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N) ∈
      LinearMap.range (intrinsicPredecessorBlock p L N) := by
  exact mem_intrinsicPredecessorBlock_range_of_inner_kernel_eq_zero
    p L N
    (intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N))
    hzero

end Zeta23.CCM

#print axioms Zeta23.CCM.inner_intrinsicPredecessorBlock_range_kernel_eq_zero
#print axioms Zeta23.CCM.intrinsicPredecessorBlock_kernel_isCompl_range
#print axioms Zeta23.CCM.mem_intrinsicPredecessorBlock_range_of_inner_kernel_eq_zero
#print axioms Zeta23.CCM.intrinsicPredecessorRangeBlock_rangeInverse_apply
#print axioms Zeta23.CCM.inner_intrinsicPredecessorBlock_kernel_resolvent_eq
#print axioms Zeta23.CCM.norm_sq_inner_kernel_coupling_le_neg_mul_norm_sq_re_inner_resolvent
#print axioms Zeta23.CCM.cubicCoupling_mem_intrinsicPredecessorBlock_range_of_zero_on_kernel
