import Zeta23.CCM.CanonicalDeepThresholdSelection

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
The actual supplied mixed-parity finite detector bounds the actual native
global bottom. Only its legal carrier, both native pole equations, unit norm
and supplied canonical energy depth are used. Its actual parity components
are constructed; neither the original detector nor its higher moments are
identified with a subsequently selected ground.
-/

private theorem nativeTrial_reverse_norm_eq (K : ℕ)
    (p : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖WithLp.toLp 2 (reverseCoefficients K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) p))‖ = ‖p‖ := by
  have hs : ‖WithLp.toLp 2 (reverseCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) p))‖ ^ 2 = ‖p‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [← Equiv.sum_comp Fin.revPerm]
    simp [reverseCoefficients]
  nlinarith [norm_nonneg p, norm_nonneg (WithLp.toLp 2
    (reverseCoefficients K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) p)))]

theorem nativeTrial_evenOdd_norm_sq_split (K : ℕ)
    (p : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖p‖ ^ 2 =
      ‖WithLp.toLp 2 (evenPart K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) p))‖ ^ 2 +
      ‖WithLp.toLp 2 (oddPart K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) p))‖ ^ 2 := by
  let raw := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) p
  let r : EuclideanSpace ℂ (Fin (2 * K + 1)) := WithLp.toLp 2 (reverseCoefficients K raw)
  let e : EuclideanSpace ℂ (Fin (2 * K + 1)) := WithLp.toLp 2 (evenPart K raw)
  let o : EuclideanSpace ℂ (Fin (2 * K + 1)) := WithLp.toLp 2 (oddPart K raw)
  have hr : ‖r‖ = ‖p‖ := nativeTrial_reverse_norm_eq K p
  have he : e = (1 / 2 : ℂ) • (p + r) := by
    apply WithLp.ofLp_injective 2
    rw [WithLp.ofLp_smul, WithLp.ofLp_add]
    ext i
    simp [e, r, raw, evenPart, reverseCoefficients, Pi.smul_apply, smul_eq_mul]
  have ho : o = (1 / 2 : ℂ) • (p - r) := by
    apply WithLp.ofLp_injective 2
    rw [WithLp.ofLp_smul, WithLp.ofLp_sub]
    ext i
    simp [o, r, raw, oddPart, reverseCoefficients, Pi.smul_apply, smul_eq_mul]
  have hp := parallelogram_law_with_norm ℂ p r
  rw [hr] at hp
  change ‖p‖ ^ 2 = ‖e‖ ^ 2 + ‖o‖ ^ 2
  rw [he, ho, norm_smul, norm_smul]
  norm_num at *
  nlinarith

/-- No pure-parity assumption is imposed on the supplied detector. -/
theorem nativeGlobalBottom_mul_norm_sq_le_given_trial_energy {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (p : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hlegal : p ∈ euclideanBoundaryFlatSubspace K)
    (hpEven : canonicalPoleEvenFunctional L K p = 0)
    (hpOdd : canonicalPoleOddFunctional L K p = 0) :
    poleNeutralGlobalRayleighBottom L K hL hK * ‖p‖ ^ 2 ≤
      (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin p) p).re := by
  let raw := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) p
  have hraw : raw ∈ boundaryFlatSubspace K :=
    (mem_euclideanBoundaryFlatSubspace_iff K p).mp hlegal
  let elegal : euclideanEvenBoundaryFlatSubspace K :=
    ⟨WithLp.toLp 2 (evenPart K raw), (mem_euclideanEvenBoundaryFlatSubspace_iff K _).mpr
      (evenPart_mem_evenBoundaryFlatSubspace hraw)⟩
  let olegal : euclideanOddBoundaryFlatSubspace K :=
    ⟨WithLp.toLp 2 (oddPart K raw), (mem_euclideanOddBoundaryFlatSubspace_iff K _).mpr
      (oddPart_mem_oddBoundaryFlatSubspace hraw)⟩
  have hEvenOdd : poleEvenProfile L K ⬝ᵥ oddPart K raw = 0 := by
    rw [dotProduct_comm]
    exact dotProduct_eq_zero_of_reverse_odd_even K _ _
      (reverseCoefficients_oddPart K raw) (reverseCoefficients_poleEvenProfile L K)
  have hOddEven : poleOddProfile L K ⬝ᵥ evenPart K raw = 0 :=
    poleOddProfile_dot_evenBoundaryFlat_eq_zero L K elegal
  have hezero : canonicalPoleEvenFunctional L K elegal = 0 := by
    have hs := congrArg (fun u => poleEvenProfile L K ⬝ᵥ u) (evenPart_add_oddPart K raw)
    rw [dotProduct_add, hEvenOdd, add_zero] at hs
    exact hs.trans hpEven
  have hozero : canonicalPoleOddFunctional L K olegal = 0 := by
    have hs := congrArg (fun u => poleOddProfile L K ⬝ᵥ u) (evenPart_add_oddPart K raw)
    rw [dotProduct_add, hOddEven, zero_add] at hs
    exact hs.trans hpOdd
  let e : poleNeutralEvenSubspace L K := ⟨elegal, (mem_poleNeutralEvenSubspace L K _).mpr hezero⟩
  let o : poleNeutralOddSubspace L K := ⟨olegal, (mem_poleNeutralOddSubspace L K _).mpr hozero⟩
  have heBound := poleNeutralEvenRayleighBottom_mul_norm_sq_le hL K hK e
  have hoBound := poleNeutralOddRayleighBottom_mul_norm_sq_le hL K hK o
  have heEnergy : (inner ℂ (poleNeutralEvenCompressedCanonical L K e) e).re =
      (quadraticForm (canonicalSourceMatrix L K) (evenPart K raw)).re := by
    rw [inner_poleNeutralEvenCompressedCanonical_self]
    symm
    exact quadraticForm_re_eq_re_inner_apply_self _ (e.val : EuclideanSpace ℂ (Fin (2 * K + 1)))
  have hoEnergy : (inner ℂ (poleNeutralOddCompressedCanonical L K o) o).re =
      (quadraticForm (canonicalSourceMatrix L K) (oddPart K raw)).re := by
    rw [inner_poleNeutralOddCompressedCanonical_self]
    symm
    exact quadraticForm_re_eq_re_inner_apply_self _ (o.val : EuclideanSpace ℂ (Fin (2 * K + 1)))
  have hsum := congrArg Complex.re (quadraticForm_evenPart_add_oddPart L K raw)
  simp only [Complex.add_re] at hsum
  have hpEnergy : (quadraticForm (canonicalSourceMatrix L K) raw).re =
      (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin p) p).re :=
    quadraticForm_re_eq_re_inner_apply_self _ p
  have hnorm : ‖p‖ ^ 2 = ‖e‖ ^ 2 + ‖o‖ ^ 2 := nativeTrial_evenOdd_norm_sq_split K p
  have heMin := mul_le_mul_of_nonneg_right
    (min_le_left (poleNeutralEvenRayleighBottom L K hL hK) (poleNeutralOddRayleighBottom L K hL hK))
    (sq_nonneg ‖e‖)
  have hoMin := mul_le_mul_of_nonneg_right
    (min_le_right (poleNeutralEvenRayleighBottom L K hL hK) (poleNeutralOddRayleighBottom L K hL hK))
    (sq_nonneg ‖o‖)
  rw [heEnergy] at heBound
  rw [hoEnergy] at hoBound
  rw [hnorm]
  unfold poleNeutralGlobalRayleighBottom
  nlinarith

/-- The actual given unit detector's depth reaches the actual native global
bottom. This is not a premise about an independently manufactured producer. -/
theorem nativeGlobalBottom_le_neg_depth_of_given_unit_trial {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (D : ℝ) (p : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hlegal : p ∈ euclideanBoundaryFlatSubspace K)
    (hpEven : canonicalPoleEvenFunctional L K p = 0)
    (hpOdd : canonicalPoleOddFunctional L K p = 0)
    (hpUnit : ‖p‖ = 1)
    (hpDepth : (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin p) p).re ≤ -D) :
    poleNeutralGlobalRayleighBottom L K hL hK ≤ -D := by
  have hb := nativeGlobalBottom_mul_norm_sq_le_given_trial_energy hL K hK p hlegal hpEven hpOdd
  rw [hpUnit] at hb
  norm_num at hb
  exact hb.trans hpDepth

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeTrial_evenOdd_norm_sq_split
#print axioms Zeta23.CCM.nativeGlobalBottom_mul_norm_sq_le_given_trial_energy
#print axioms Zeta23.CCM.nativeGlobalBottom_le_neg_depth_of_given_unit_trial
