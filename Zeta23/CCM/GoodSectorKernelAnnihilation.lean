import Zeta23.CCM.ParitySourceMomentFourRigidity
import Zeta23.CCM.ZeroShiftBranchResponse

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: good-sector kernel annihilation

This module extracts one narrow consequence of successor-sector goodness that is
needed by the post-#219 arithmetic composition.

For the parity-compressed canonical operator, nonnegative self-energy together
with zero self-energy forces a vector into the operator kernel.  Applied to a
vector in the kernel of the projected predecessor block, this annihilates the
actual cubic shell coupling and therefore its canonical predecessor-kernel
coordinate.

This is infrastructure, not a new arithmetic positivity mechanism.  In
particular, it does not promote one-step domination to an independent
hypothesis, does not exclude either branch of the #219 regular/resonant split,
and proves no negative-root exclusion or RH theorem.
-/

/-- For a good parity sector, a vector of zero compressed self-energy is a
genuine zero mode of the compressed canonical operator. -/
theorem parityCompressedCanonical_eq_zero_of_not_parityBad_of_selfEnergy_eq_zero
    {p : ReversalParity} {L : ℝ} {N : ℕ}
    (hgood : ¬ ParityBad p L N)
    (v : euclideanParityBoundaryFlatSubspace p N)
    (hzero :
      Complex.re
        (inner ℂ (parityCompressedCanonical p L N v) v) = 0) :
    parityCompressedCanonical p L N v = 0 := by
  let T := parityCompressedCanonical p L N
  let y := T v
  by_contra hyzero
  have hyne : y ≠ 0 := by
    change T v ≠ 0
    exact hyzero
  have hynormpos : 0 < ‖y‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hyne)
  let q : ℝ := Complex.re (inner ℂ (T y) y)
  have hqnonneg : 0 ≤ q := by
    simpa [q, T] using
      re_inner_parityCompressedCanonical_nonnegative_of_not_parityBad hgood y
  let t : ℝ := ‖y‖ ^ 2 / (q + 1)
  have hdenpos : 0 < q + 1 := by
    linarith
  have htpos : 0 < t := by
    exact div_pos hynormpos hdenpos
  have htden : t * (q + 1) = ‖y‖ ^ 2 := by
    dsimp [t]
    exact div_mul_cancel₀ (‖y‖ ^ 2) (ne_of_gt hdenpos)
  let w := v - (t : ℂ) • y
  have hw :
      0 ≤ Complex.re (inner ℂ (T w) w) := by
    simpa [T] using
      re_inner_parityCompressedCanonical_nonnegative_of_not_parityBad hgood w
  have hTv : T v = y := by
    rfl
  have hTyv :
      inner ℂ (T y) v = inner ℂ y y := by
    calc
      inner ℂ (T y) v = inner ℂ y (T v) := by
        simpa [T] using
          (parityCompressedCanonical_isSymmetric p L N y v)
      _ = inner ℂ y y := by rw [hTv]
  have hyy :
      Complex.re (inner ℂ y y) = ‖y‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) y).symm
  have hyv :
      Complex.re (inner ℂ y v) = 0 := by
    simpa [T, y] using hzero
  have hTyvRe :
      Complex.re (inner ℂ (T y) v) = ‖y‖ ^ 2 := by
    rw [hTyv, hyy]
  have hTyy :
      Complex.re (inner ℂ (T y) y) = q := by
    rfl
  have hyty :
      Complex.re (inner ℂ y ((t : ℂ) • y)) =
        t * ‖y‖ ^ 2 := by
    have h :=
      congrArg Complex.re
        (inner_smul_real_right (𝕜 := ℂ) y y t)
    simpa [Complex.smul_re, hyy] using h
  have htTyv :
      Complex.re (inner ℂ ((t : ℂ) • T y) v) =
        t * ‖y‖ ^ 2 := by
    have h :=
      congrArg Complex.re
        (inner_smul_real_left (𝕜 := ℂ) (T y) v t)
    simpa [Complex.smul_re, hTyvRe] using h
  have hTyty :
      Complex.re (inner ℂ (T y) ((t : ℂ) • y)) =
        t * q := by
    have h :=
      congrArg Complex.re
        (inner_smul_real_right (𝕜 := ℂ) (T y) y t)
    simpa [Complex.smul_re, hTyy] using h
  have htTyty :
      Complex.re (inner ℂ ((t : ℂ) • T y) ((t : ℂ) • y)) =
        t ^ 2 * q := by
    have h :=
      congrArg Complex.re
        (inner_smul_real_left (𝕜 := ℂ) (T y) ((t : ℂ) • y) t)
    calc
      Complex.re (inner ℂ ((t : ℂ) • T y) ((t : ℂ) • y)) =
          t * Complex.re (inner ℂ (T y) ((t : ℂ) • y)) := by
            simpa [Complex.smul_re] using h
      _ = t * (t * q) := by rw [hTyty]
      _ = t ^ 2 * q := by ring
  have hTw :
      T w = y - (t : ℂ) • T y := by
    dsimp [w]
    calc
      T (v - (t : ℂ) • y) =
          T v - T ((t : ℂ) • y) := by rw [map_sub]
      _ = y - (t : ℂ) • T y := by
        rw [hTv, map_smul]
  rw [hTw] at hw
  change
    0 ≤
      Complex.re
        (inner ℂ
          (y - (t : ℂ) • T y)
          (v - (t : ℂ) • y)) at hw
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    Complex.sub_re, Complex.sub_re, Complex.sub_re,
    hyv, hyty, htTyv, htTyty] at hw
  have htSq : 0 < t ^ 2 := sq_pos_of_pos htpos
  nlinarith

/-- Goodness of the full successor parity sector annihilates the actual cubic
shell coupling on every vector in the projected predecessor kernel. -/
theorem cubicCoupling_zero_on_intrinsicPredecessorBlock_kernel_of_not_parityBad
    (p : ReversalParity) (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hgood : ¬ ParityBad p L (N + 1))
    (z : intrinsicParityPredecessorSubspace p N)
    (hz : intrinsicPredecessorBlock p L N z = 0) :
    inner ℂ
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))
        ((intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N) :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
  have hzEnergy :
      Complex.re
        (inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (z : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))) = 0 := by
    rw [← inner_intrinsicPredecessorBlock_self p L N z, hz]
    simp
  have hzFull :
      parityCompressedCanonical p L (N + 1)
        (z : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 :=
    parityCompressedCanonical_eq_zero_of_not_parityBad_of_selfEnergy_eq_zero
      hgood
      (z : euclideanParityBoundaryFlatSubspace p (N + 1))
      hzEnergy
  exact
    (inner_cubicCoupling_eq_zero_iff_successor_zero_of_intrinsicPredecessorBlock_eq_zero
      p L N hN z hz).2 hzFull

/-- Goodness of the full successor parity sector kills the canonical
predecessor-kernel coordinate of the actual cubic shell coupling. -/
theorem cubicCouplingKernelPart_eq_zero_of_not_parityBad
    (p : ReversalParity) (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hgood : ¬ ParityBad p L (N + 1)) :
    cubicCouplingKernelPart p L N = 0 := by
  by_contra hk
  rcases
      (cubicCouplingKernelPart_ne_zero_iff_resonant p L N).1 hk with
    ⟨z, hz, hcouple⟩
  exact hcouple
    (cubicCoupling_zero_on_intrinsicPredecessorBlock_kernel_of_not_parityBad
      p L N hN hgood z hz)

/-- A good successor sector therefore places the actual cubic shell coupling
in the range of the predecessor block and supplies a zero-shift preimage. -/
theorem exists_cubicZeroShift_preimage_of_not_parityBad
    (p : ReversalParity) (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hgood : ¬ ParityBad p L (N + 1)) :
    ∃ x₀ : intrinsicParityPredecessorSubspace p N,
      intrinsicPredecessorBlock p L N x₀ =
        intrinsicShellToPredecessor p L N
          (intrinsicCubicShellPart p N) := by
  have hk :=
    cubicCouplingKernelPart_eq_zero_of_not_parityBad
      p L N hN hgood
  have hrange :
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N) ∈
        LinearMap.range (intrinsicPredecessorBlock p L N) := by
    exact
      (intrinsicPredecessorKernelPart_eq_zero_iff_mem_range
        p L N).1 hk
  exact hrange

end Zeta23.CCM

#print axioms Zeta23.CCM.parityCompressedCanonical_eq_zero_of_not_parityBad_of_selfEnergy_eq_zero
#print axioms Zeta23.CCM.cubicCouplingKernelPart_eq_zero_of_not_parityBad
#print axioms Zeta23.CCM.exists_cubicZeroShift_preimage_of_not_parityBad
