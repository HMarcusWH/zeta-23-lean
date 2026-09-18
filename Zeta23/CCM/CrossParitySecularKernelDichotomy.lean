import Zeta23.CCM.CrossParitySecularCompletion
import Zeta23.CCM.ZeroShiftBranchResponse

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: kernel/range split for the retained odd cubic correction

PR #218 identifies the exact odd predecessor correction vector
`oddCubicGeneratorPredecessorPart N` and its safe negative-shift resolvent
quadratic.  This module connects that exact vector to the older zero-shift
kernel/range machinery.

Writing

  a = oddCubicGeneratorPredecessorPart N
  k = K(a)

for the canonical kernel coordinate of the odd projected predecessor block, we
prove:

* `k = 0` iff `a` lies in the zero-shift range, equivalently iff `A x₀ = a`
  has a solution;
* the quadratic zero-shift response is independent of the selected preimage in
  that regular branch;
* at every safe negative shift, the kernel coordinate of `R_lam a` carries the
  exact `1 / (-lam)` pole;
* the kernel norm is quantitatively controlled by the exact #218 resolvent
  quadratic.

Thus the #218 correction admits an exhaustive regular-or-resonant split.  No
branch is excluded here.

Firewalls:
* `ker A` is the kernel of the projected successor predecessor block;
* no inverse of `A` at zero is introduced;
* no assumption that the #218 vector equals the canonical shell coupling is
  made;
* no negative-root exclusion, finite-to-infinite closure, or RH theorem is
  claimed.
-/

/-- Canonical kernel coordinate of the exact odd cubic-generator predecessor
correction used by PR #218. -/
def oddCubicGeneratorKernelPart
    (L : ℝ) (N : ℕ) :
    LinearMap.ker (intrinsicPredecessorBlock .odd L N) :=
  intrinsicPredecessorKernelPart .odd L N
    (oddCubicGeneratorPredecessorPart N)

/-- The exact #218 odd cubic correction is regular at zero exactly when its
canonical kernel coordinate vanishes. -/
theorem oddCubicGeneratorKernelPart_eq_zero_iff_mem_range
    (L : ℝ) (N : ℕ) :
    oddCubicGeneratorKernelPart L N = 0 ↔
      oddCubicGeneratorPredecessorPart N ∈
        LinearMap.range (intrinsicPredecessorBlock .odd L N) := by
  simpa [oddCubicGeneratorKernelPart] using
    (intrinsicPredecessorKernelPart_eq_zero_iff_mem_range
      .odd L N (w := oddCubicGeneratorPredecessorPart N))

/-- Equivalent zero-shift formulation of the regular branch. -/
theorem oddCubicGeneratorKernelPart_eq_zero_iff_exists_zeroShiftPreimage
    (L : ℝ) (N : ℕ) :
    oddCubicGeneratorKernelPart L N = 0 ↔
      ∃ x₀ : intrinsicParityPredecessorSubspace .odd N,
        intrinsicPredecessorBlock .odd L N x₀ =
          oddCubicGeneratorPredecessorPart N := by
  rw [oddCubicGeneratorKernelPart_eq_zero_iff_mem_range]
  rfl

/-- In the regular branch the zero-shift response of the exact #218 correction
is well-defined independently of the selected preimage. -/
theorem oddCubicGeneratorKernelPart_zeroShiftPreimage_inner_unique
    (L : ℝ) (N : ℕ)
    (hk : oddCubicGeneratorKernelPart L N = 0) :
    ∃ x₀ : intrinsicParityPredecessorSubspace .odd N,
      intrinsicPredecessorBlock .odd L N x₀ =
        oddCubicGeneratorPredecessorPart N ∧
      ∀ x : intrinsicParityPredecessorSubspace .odd N,
        intrinsicPredecessorBlock .odd L N x =
            oddCubicGeneratorPredecessorPart N →
          inner ℂ
              (x : euclideanParityBoundaryFlatSubspace .odd (N + 1))
              (oddCubicGeneratorPredecessorPart N :
                euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
            inner ℂ
              (x₀ : euclideanParityBoundaryFlatSubspace .odd (N + 1))
              (oddCubicGeneratorPredecessorPart N :
                euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  rcases
      (oddCubicGeneratorKernelPart_eq_zero_iff_exists_zeroShiftPreimage
        L N).1 hk with ⟨x₀, hx₀⟩
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx
  exact inner_intrinsicPredecessorBlock_preimage_eq
    .odd L N (oddCubicGeneratorPredecessorPart N) x x₀ hx hx₀

/-- Exact resonant pole for the same #218 correction vector. -/
theorem oddCubicGeneratorKernelPart_resolvent_eq_inv_neg_smul
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0) :
    intrinsicPredecessorKernelPart .odd L N
        (shiftedIntrinsicPredecessorResolvent
          .odd hL N hprevOdd lam hlam
          (oddCubicGeneratorPredecessorPart N)) =
      ((-lam : ℂ)⁻¹) • oddCubicGeneratorKernelPart L N := by
  simpa [oddCubicGeneratorKernelPart] using
    (intrinsicPredecessorKernelPart_resolvent_eq_inv_neg_smul
      .odd hL N hprevOdd hlam (oddCubicGeneratorPredecessorPart N))

/-- The kernel norm of the exact #218 correction is controlled by its
negative-shift resolvent quadratic.  This is valid in both the regular and
resonant branches; when the kernel coordinate vanishes the statement is
trivial. -/
theorem oddCubicGeneratorKernelPart_norm_sq_le_neg_lam_mul_resolventQuadratic_re
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0) :
    ‖oddCubicGeneratorKernelPart L N‖ ^ 2 ≤
      (-lam) *
        Complex.re
          (oddCubicGeneratorResolventQuadratic
            hL N hprevOdd lam hlam) := by
  let a := oddCubicGeneratorPredecessorPart N
  let k := oddCubicGeneratorKernelPart L N
  change
    ‖k‖ ^ 2 ≤
      (-lam) *
        Complex.re
          (oddCubicGeneratorResolventQuadratic
            hL N hprevOdd lam hlam)
  by_cases hk : k = 0
  · have hnonneg :
        0 ≤
          (-lam) *
            Complex.re
              (oddCubicGeneratorResolventQuadratic
                hL N hprevOdd lam hlam) :=
      mul_nonneg
        (le_of_lt (neg_pos.mpr hlam))
        (oddCubicGeneratorResolventQuadratic_re_nonnegative
          hL N hprevOdd lam hlam)
    have hkzero : ‖k‖ ^ 2 = 0 := by
      simp [hk]
    rw [hkzero]
    exact hnonneg
  · have hknormpos : (0 : ℝ) < ‖k‖ :=
      norm_pos_iff.mpr hk
    have hkpos : 0 < ‖k‖ ^ 2 := sq_pos_of_pos hknormpos
    have hbase :=
      norm_sq_inner_kernel_coupling_le_neg_mul_norm_sq_re_inner_resolvent
        .odd hL N hprevOdd hlam
        (k : intrinsicParityPredecessorSubspace .odd N) a k.property
    have hpair :=
      inner_intrinsicPredecessorKernelPart_coupling_eq_self
        .odd L N a
    change
      inner ℂ
          ((k : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          ((k : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((k : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) at hpair
    rw [hpair] at hbase
    have hinnernorm :
        ‖inner ℂ
            ((k : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            ((k : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))‖ =
          ‖k‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [Submodule.norm_coe]
    rw [hinnernorm] at hbase
    have hbase' :
        (‖k‖ ^ 2) ^ 2 ≤
          (-lam) * (‖k‖ ^ 2) *
            Complex.re
              (oddCubicGeneratorResolventQuadratic
                hL N hprevOdd lam hlam) := by
      simpa only [Submodule.norm_coe, a,
        oddCubicGeneratorResolventQuadratic] using hbase
    nlinarith

/-- Exhaustive regular-or-resonant split for the exact #218 odd cubic
correction. -/
theorem oddCubicGenerator_regular_or_resonant
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0) :
    (∃ x₀ : intrinsicParityPredecessorSubspace .odd N,
      intrinsicPredecessorBlock .odd L N x₀ =
        oddCubicGeneratorPredecessorPart N) ∨
    (oddCubicGeneratorKernelPart L N ≠ 0 ∧
      intrinsicPredecessorKernelPart .odd L N
          (shiftedIntrinsicPredecessorResolvent
            .odd hL N hprevOdd lam hlam
            (oddCubicGeneratorPredecessorPart N)) =
        ((-lam : ℂ)⁻¹) • oddCubicGeneratorKernelPart L N) := by
  by_cases hk : oddCubicGeneratorKernelPart L N = 0
  · exact Or.inl
      ((oddCubicGeneratorKernelPart_eq_zero_iff_exists_zeroShiftPreimage
        L N).1 hk)
  · exact Or.inr ⟨hk,
      oddCubicGeneratorKernelPart_resolvent_eq_inv_neg_smul
        hL N hprevOdd hlam⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.oddCubicGeneratorKernelPart_eq_zero_iff_mem_range
#print axioms Zeta23.CCM.oddCubicGeneratorKernelPart_eq_zero_iff_exists_zeroShiftPreimage
#print axioms Zeta23.CCM.oddCubicGeneratorKernelPart_zeroShiftPreimage_inner_unique
#print axioms Zeta23.CCM.oddCubicGeneratorKernelPart_resolvent_eq_inv_neg_smul
#print axioms Zeta23.CCM.oddCubicGeneratorKernelPart_norm_sq_le_neg_lam_mul_resolventQuadratic_re
#print axioms Zeta23.CCM.oddCubicGenerator_regular_or_resonant
