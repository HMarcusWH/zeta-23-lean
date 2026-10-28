import Zeta23.OPICARound4.SignedNormBound
import Zeta23.OPICARound4.TraceMetric

noncomputable section
namespace Zeta23.OPICARound4
open CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- Typed physical adjoint of the actual inverse centered-index map. -/
def nativeIndexInverseAdjoint {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) :
    poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K := by
  simpa only [] using! (LinearMap.adjoint (𝕜 := ℂ)
    (E := poleNeutralOddSubspace L K) (F := poleNeutralEvenSubspace L K)
    (poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm.toLinearMap)

/-- Typed physical adjoint of the inverse actual adjoint transport. -/
def nativeIndexAdjointInverseAdjoint {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) :
    poleNeutralOddSubspace L K →ₗ[ℂ] poleNeutralEvenSubspace L K := by
  simpa only [] using! (LinearMap.adjoint (𝕜 := ℂ)
    (E := poleNeutralEvenSubspace L K) (F := poleNeutralOddSubspace L K)
    (poleNeutralIndexAdjointEquiv hL K hK).symm.toLinearMap)

/-- S05 for an actual finite-dimensional Hermitian resolvent. Its coercivity
and spectral domain are explicit. The improvement is one-sided and retains
the signed cross term instead of its absolute-value majorant. -/
theorem hermitian_resolvent_signed_upper {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (B : F →ₗ[ℂ] F) (hB : B.IsSymmetric) (b lam : ℝ)
    (hlower : ∀ w, b * ‖w‖ ^ 2 ≤ (inner ℂ (B w) w).re)
    (hlam : lam < b) (Bi : F ≃ₗ[ℂ] F)
    (hBi : ∀ w, Bi w = B w - (lam : ℂ) • w) (z g : F) :
    (b - lam) * (inner ℂ z (Bi.symm g)).re ≤
      (‖z‖ * ‖g‖ + (inner ℂ z g).re) / 2 := by
  let e := hB.eigenvectorBasis rfl
  let mu := hB.eigenvalues rfl
  have hmu (i : Fin (Module.finrank ℂ F)) : b ≤ mu i := by
    have h := hlower (e i)
    have he := hB.apply_eigenvectorBasis rfl i
    change B (e i) = (mu i : ℂ) • e i at he
    rw [he, re_inner_ofReal_smul_self, e.norm_eq_one i] at h
    simpa using h
  have heq : e.repr (Bi.symm g) = diagonalSpectralResolvent mu lam (e.repr g) := by
    ext i
    have hh := congrArg (fun v : F => e.repr v i) (Bi.apply_symm_apply g)
    rw [hBi] at hh
    simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hh
    have hspec := hB.eigenvectorBasis_apply_self_apply rfl (Bi.symm g) i
    change e.repr (B (Bi.symm g)) i = (mu i : ℂ) * e.repr (Bi.symm g) i at hspec
    rw [hspec] at hh
    have hd : mu i - lam ≠ 0 := ne_of_gt (lt_of_lt_of_le hlam (hmu i) |> sub_pos.mpr)
    have hdC : ((mu i - lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
    change e.repr (Bi.symm g) i = ((mu i - lam)⁻¹ : ℝ) • e.repr g i
    rw [Complex.real_smul, Complex.ofReal_inv]
    apply mul_left_cancel₀ hdC
    rw [← mul_assoc, mul_inv_cancel₀ hdC, one_mul]
    push_cast
    linear_combination hh
  have hs := diagonal_signed_norm_upper mu b lam (e.repr z) (e.repr g) hmu hlam
  rw [← heq] at hs
  simpa only [e.repr.inner_map_map, e.repr.norm_map] using hs

/-- Native even one-sided bound with the actual nonunitary inverse-adjoint
source vector and the actual trace displacement. Arithmetic smallness remains
a separate open obligation. -/
theorem native_even_signed_upper {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    (poleNeutralOddRayleighBottom L K hL hK - lam) *
      (poleNeutralCorrectedCubicSource L K (poleNeutralEvenShiftedRay hL K hK lam hlam)).re ≤
      (‖nativeIndexInverseAdjoint hL K hK
          (poleNeutralCorrectedCubicRieszVector L K)‖ * ‖poleNeutralCubicCompressionVector L K‖ +
        (LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K)).re) / 2 := by
  let z : poleNeutralOddSubspace L K := nativeIndexInverseAdjoint hL K hK
    (poleNeutralCorrectedCubicRieszVector L K)
  have hs := hermitian_resolvent_signed_upper
    (poleNeutralOddCompressedCanonical L K) (poleNeutralOddCompressedCanonical_isSymmetric L K)
    (poleNeutralOddRayleighBottom L K hL hK) lam
    (poleNeutralOddRayleighBottom_mul_norm_sq_le hL K hK) hlam
    (poleNeutralOddShiftedCanonicalEquiv hL K hK lam hlam) (fun _ => rfl)
    z (poleNeutralCubicCompressionVector L K)
  have hresp : inner ℂ z ((poleNeutralOddShiftedCanonicalEquiv hL K hK lam hlam).symm
      (poleNeutralCubicCompressionVector L K)) =
      poleNeutralCorrectedCubicSource L K (poleNeutralEvenShiftedRay hL K hK lam hlam) := by
    dsimp only [z, nativeIndexInverseAdjoint]
    rw [LinearMap.adjoint_inner_left, inner_poleNeutralCorrectedCubicRieszVector]
    rfl
  have ht : inner ℂ z (poleNeutralCubicCompressionVector L K) =
      LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
        LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K) := by
    dsimp only [z, nativeIndexInverseAdjoint]
    rw [LinearMap.adjoint_inner_left, inner_poleNeutralCorrectedCubicRieszVector]
    exact (native_even_trace_displacement hL K hK).symm
  rw [hresp, ht] at hs
  exact hs

/-- The inverse adjoint transport has the actual inverse-adjoint relation.
This is algebraic duality, not a unitary identification. -/
theorem native_odd_inverse_adjoint_eq_inverse {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : poleNeutralOddSubspace L K) :
    nativeIndexAdjointInverseAdjoint hL K hK w =
      (poleNeutralIndexEquiv hL K (by omega)).symm w := by
  apply ext_inner_right ℂ
  intro v
  have hv : (poleNeutralIndexLinearMap hL K).adjoint
      ((poleNeutralIndexAdjointEquiv hL K hK).symm v) = v := by
    change poleNeutralIndexAdjointEquiv hL K hK
      ((poleNeutralIndexAdjointEquiv hL K hK).symm v) = v
    exact LinearEquiv.apply_symm_apply _ v
  have hw : poleNeutralIndexLinearMap hL K
      ((poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm w) = w := by
    change poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)
      ((poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm w) = w
    exact LinearEquiv.apply_symm_apply _ w
  have hi := LinearMap.adjoint_inner_right (poleNeutralIndexLinearMap hL K)
    ((poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm w)
    ((poleNeutralIndexAdjointEquiv hL K hK).symm v)
  rw [hv, hw] at hi
  dsimp only [nativeIndexAdjointInverseAdjoint]
  rw [LinearMap.adjoint_inner_left]
  exact hi.symm

/-- Native odd one-sided bound, with D^-1 g rather than (D^-1)* f, and reversed
trace displacement. Both orientation changes are mathematically material. -/
theorem native_odd_signed_upper {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    (poleNeutralEvenRayleighBottom L K hL hK - lam) *
      (poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam)).re ≤
      (‖(poleNeutralIndexEquiv hL K (by omega)).symm (poleNeutralCubicCompressionVector L K)‖ *
          ‖poleNeutralCorrectedCubicRieszVector L K‖ +
        (LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K)).re) / 2 := by
  let z : poleNeutralEvenSubspace L K := nativeIndexAdjointInverseAdjoint hL K hK
    (poleNeutralCubicCompressionVector L K)
  have hs := hermitian_resolvent_signed_upper
    (poleNeutralEvenCompressedCanonical L K) (poleNeutralEvenCompressedCanonical_isSymmetric L K)
    (poleNeutralEvenRayleighBottom L K hL hK) lam
    (poleNeutralEvenRayleighBottom_mul_norm_sq_le hL K hK) hlam
    (poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam) (fun _ => rfl)
    z (-poleNeutralCorrectedCubicRieszVector L K)
  have hresp : inner ℂ z ((poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam).symm
      (-poleNeutralCorrectedCubicRieszVector L K)) =
      poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) := by
    dsimp only [z, nativeIndexAdjointInverseAdjoint]
    rw [LinearMap.adjoint_inner_left]
    rfl
  have ht : inner ℂ z (-poleNeutralCorrectedCubicRieszVector L K) =
      LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K) -
        LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) := by
    dsimp only [z, nativeIndexAdjointInverseAdjoint]
    rw [LinearMap.adjoint_inner_left]
    change poleNeutralCubicPairingFunctional L K
      ((poleNeutralIndexAdjointEquiv hL K hK).symm (-poleNeutralCorrectedCubicRieszVector L K)) = _
    rw [map_neg, map_neg]
    exact (native_odd_trace_displacement hL K hK).symm
  rw [hresp, ht] at hs
  have hnorm : ‖(-poleNeutralCorrectedCubicRieszVector L K : poleNeutralEvenSubspace L K)‖ =
      ‖poleNeutralCorrectedCubicRieszVector L K‖ := by
    change ‖-(poleNeutralCorrectedCubicRieszVector L K).val.val‖ =
      ‖(poleNeutralCorrectedCubicRieszVector L K).val.val‖
    exact norm_neg _
  rw [hnorm] at hs
  change _ ≤ (‖nativeIndexAdjointInverseAdjoint hL K hK (poleNeutralCubicCompressionVector L K)‖ * _ + _) / 2 at hs
  rw [native_odd_inverse_adjoint_eq_inverse hL K hK] at hs
  exact hs

end Zeta23.OPICARound4
