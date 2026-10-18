import Zeta23.CCM.CanonicalPoleNeutralSourceMoment
import Zeta23.CCM.CanonicalSecularResolvent

/-!
# Native trial residual bounds for the corrected pole-neutral compression

The spectral parameter is the actual trial parameter. No eigenvector or
vanishing residual hypothesis enters the general R3 inequality.
-/

noncomputable section

namespace Zeta23.CCM

open scoped ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

def poleNeutralTrialResidual (L : ℝ) (K : ℕ) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K) : poleNeutralEvenSubspace L K :=
  poleNeutralEvenCompressedCanonical L K u - (lam : ℂ) • u

theorem poleNeutral_trial_residual_intertwining {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K) :
    poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
        (lam : ℂ) • poleNeutralIndexLinearMap hL K u =
      poleNeutralIndexLinearMap hL K (poleNeutralTrialResidual L K lam u) +
        poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K := by
  have hd := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K hK u
  change poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
    poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K u) = _ at hd
  rw [poleNeutralTrialResidual, map_sub, map_smul]
  rw [← hd]
  abel

theorem poleNeutralIndex_norm_le {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    ‖poleNeutralIndexLinearMap hL K u‖ ≤ (K : ℝ) * ‖u‖ := by
  exact norm_euclideanIndexLinearMap_le K u.val.val

/-- R3 with the actual corrected cubic source and actual fourth moment. -/
theorem poleNeutral_trial_residual_bound {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K) :
    (poleNeutralOddRayleighBottom L K hL hK - lam) *
        ‖poleNeutralIndexLinearMap hL K u‖ ^ 2 ≤
      ‖poleNeutralCorrectedCubicSource L K u‖ *
          ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)‖ +
        ‖poleNeutralIndexLinearMap hL K (poleNeutralTrialResidual L K lam u)‖ *
          ‖poleNeutralIndexLinearMap hL K u‖ := by
  let v := poleNeutralIndexLinearMap hL K u
  let r := poleNeutralIndexLinearMap hL K (poleNeutralTrialResidual L K lam u)
  let S := poleNeutralCorrectedCubicSource L K u
  let M := centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)
  have hrel := poleNeutral_trial_residual_intertwining hL K (by omega) lam u
  have hp := congrArg (fun z : poleNeutralOddSubspace L K => inner ℂ z v) hrel
  change inner ℂ
      ((poleNeutralOddCompressedCanonical L K v).val.val - (lam : ℂ) • v.val.val) v.val.val =
    inner ℂ (r.val.val + S • (poleNeutralCubicCompressionVector L K).val.val) v.val.val at hp
  rw [inner_sub_left, inner_smul_left, inner_add_left, inner_smul_left] at hp
  have hc := poleNeutral_cubic_pairing_eq_momentFour hL K u
  change inner ℂ (poleNeutralCubicCompressionVector L K).val.val v.val.val = M at hc
  rw [hc] at hp
  have hn : (inner ℂ v.val.val v.val.val).re = ‖v‖ ^ 2 := by
    change (inner ℂ v.val.val v.val.val).re = ‖v.val.val‖ ^ 2
    simpa only [RCLike.re_eq_complex_re] using
      (inner_self_eq_norm_sq (𝕜 := ℂ) v.val.val)
  have hlam : ((starRingEnd ℂ) (lam : ℂ) * inner ℂ v.val.val v.val.val).re = lam * ‖v‖ ^ 2 := by
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hn]
  have hpre := congrArg Complex.re hp
  rw [Complex.sub_re, Complex.add_re, hlam] at hpre
  have hb := poleNeutralOddRayleighBottom_mul_norm_sq_le hL K hK v
  change poleNeutralOddRayleighBottom L K hL hK * ‖v‖ ^ 2 ≤
    (inner ℂ (poleNeutralOddCompressedCanonical L K v).val.val v.val.val).re at hb
  have hr : (inner ℂ r.val.val v.val.val).re ≤ ‖r‖ * ‖v‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm r.val.val v.val.val)
  have hs : ((starRingEnd ℂ) S * M).re ≤ ‖S‖ * ‖M‖ := by
    calc
      _ ≤ ‖(starRingEnd ℂ) S * M‖ := Complex.re_le_norm _
      _ = _ := by
        rw [norm_mul]
        change ‖star S‖ * ‖M‖ = ‖S‖ * ‖M‖
        rw [norm_star]
  change (poleNeutralOddRayleighBottom L K hL hK - lam) * ‖v‖ ^ 2 ≤
    ‖S‖ * ‖M‖ + ‖r‖ * ‖v‖
  linarith

/-- A zero fourth moment forces a quantitative residual at a positive gap. -/
theorem poleNeutral_momentFour_zero_residual_lower {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K)
    (hgap : lam < poleNeutralOddRayleighBottom L K hL hK)
    (hm : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) = 0) :
    (poleNeutralOddRayleighBottom L K hL hK - lam) * ‖u‖ / (2 * K) ≤
      ‖poleNeutralTrialResidual L K lam u‖ := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hb := poleNeutral_trial_residual_bound hL K hK lam u
  rw [hm, norm_zero, mul_zero, zero_add] at hb
  have hupper := poleNeutralIndex_norm_le hL K (poleNeutralTrialResidual L K lam u)
  have hlower := poleNeutralIndex_norm_lower hL K u
  have hnormlower : ‖u‖ ≤ 2 * ‖poleNeutralIndexLinearMap hL K u‖ := by
    nlinarith [norm_nonneg u, norm_nonneg (poleNeutralIndexLinearMap hL K u)]
  by_cases hv : ‖poleNeutralIndexLinearMap hL K u‖ = 0
  · have hu : ‖u‖ = 0 := by nlinarith [norm_nonneg u]
    rw [hu, mul_zero, zero_div]
    exact norm_nonneg _
  · have hvpos : 0 < ‖poleNeutralIndexLinearMap hL K u‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    have hg : 0 < poleNeutralOddRayleighBottom L K hL hK - lam := sub_pos.mpr hgap
    have hh : (poleNeutralOddRayleighBottom L K hL hK - lam) *
        ‖poleNeutralIndexLinearMap hL K u‖ ≤
          (K : ℝ) * ‖poleNeutralTrialResidual L K lam u‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hupper
        (norm_nonneg (poleNeutralIndexLinearMap hL K u))]
    apply (div_le_iff₀ (mul_pos (by norm_num) hKpos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hnormlower hg.le]

end Zeta23.CCM

#print axioms Zeta23.CCM.poleNeutral_trial_residual_intertwining
#print axioms Zeta23.CCM.poleNeutralIndex_norm_le
#print axioms Zeta23.CCM.poleNeutral_trial_residual_bound
#print axioms Zeta23.CCM.poleNeutral_momentFour_zero_residual_lower
