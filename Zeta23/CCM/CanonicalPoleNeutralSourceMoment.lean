import Zeta23.CCM.CanonicalPoleNeutralNormals
import Zeta23.CCM.CanonicalTrialResidualChannels
import Zeta23.CCM.GlobalParityBottomSpectrum

noncomputable section

namespace Zeta23.CCM

open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  euclideanEvenBoundaryFlatSubspace euclideanOddBoundaryFlatSubspace

/-!
Actual finite native pole-neutral bottoms and corrected source-moment energy.

The bottoms below require `L > 0, K ≥ 3`; no artificial empty-carrier
eigenvalue is introduced. Ground eigenmodes are obtained from the actual
compressed canonical operators and the proved carrier dimensions. Their
energies are not asserted negative. The strict-gap conclusions use the
constructed corrected native source, not the original uncorrected functional.
-/

/-- Quantitative inverse of the actual algebraic centered-index equivalence. -/
theorem poleNeutralIndexInverse_norm_le_two {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K) (w : poleNeutralOddSubspace L K) :
    ‖(poleNeutralIndexEquiv hL K hK).symm w‖ ≤ 2 * ‖w‖ := by
  have hc := poleNeutralIndex_norm_lower hL K ((poleNeutralIndexEquiv hL K hK).symm w)
  have hmap : poleNeutralIndexLinearMap hL K ((poleNeutralIndexEquiv hL K hK).symm w) = w := by
    change poleNeutralIndexEquiv hL K hK ((poleNeutralIndexEquiv hL K hK).symm w) = w
    exact LinearEquiv.apply_symm_apply _ w
  rw [hmap] at hc
  nlinarith [norm_nonneg ((poleNeutralIndexEquiv hL K hK).symm w), norm_nonneg w]

/-- Actual native even Rayleigh bottom on a nontrivial carrier. -/
def poleNeutralEvenRayleighBottom (L : ℝ) (K : ℕ) (_hL : 0 < L) (_hK : 3 ≤ K) : ℝ :=
  ⨅ z : {z : poleNeutralEvenSubspace L K // z ≠ 0},
    RCLike.re (inner ℂ (poleNeutralEvenCompressedCanonical L K z) z) /
      ‖(z : poleNeutralEvenSubspace L K)‖ ^ 2

/-- Actual native odd Rayleigh bottom on a nontrivial carrier. -/
def poleNeutralOddRayleighBottom (L : ℝ) (K : ℕ) (_hL : 0 < L) (_hK : 3 ≤ K) : ℝ :=
  ⨅ z : {z : poleNeutralOddSubspace L K // z ≠ 0},
    RCLike.re (inner ℂ (poleNeutralOddCompressedCanonical L K z) z) /
      ‖(z : poleNeutralOddSubspace L K)‖ ^ 2

theorem exists_eigenmode_at_poleNeutralEvenRayleighBottom {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) :
    ∃ u : poleNeutralEvenSubspace L K, u ≠ 0 ∧
      poleNeutralEvenCompressedCanonical L K u =
        (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u := by
  have hd : 0 < Module.finrank ℂ (poleNeutralEvenSubspace L K) := by
    rw [finrank_poleNeutralEvenSubspace hL K (by omega)]
    omega
  letI : Nontrivial (poleNeutralEvenSubspace L K) := Module.nontrivial_of_finrank_pos hd
  have he := @LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
    ℂ _ (poleNeutralEvenSubspace L K) inferInstance
    (poleNeutralEven_innerProductSpace L K) inferInstance
    (poleNeutralEvenCompressedCanonical L K) inferInstance
    (poleNeutralEvenCompressedCanonical_isSymmetric L K)
  obtain ⟨u, hu⟩ := he.exists_hasEigenvector
  refine ⟨u, hu.2, ?_⟩
  simpa only [poleNeutralEvenRayleighBottom] using! hu.apply_eq_smul

theorem exists_eigenmode_at_poleNeutralOddRayleighBottom {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) :
    ∃ w : poleNeutralOddSubspace L K, w ≠ 0 ∧
      poleNeutralOddCompressedCanonical L K w =
        (poleNeutralOddRayleighBottom L K hL hK : ℂ) • w := by
  have hd : 0 < Module.finrank ℂ (poleNeutralOddSubspace L K) := by
    rw [finrank_poleNeutralOddSubspace hL K (by omega)]
    omega
  letI : Nontrivial (poleNeutralOddSubspace L K) := Module.nontrivial_of_finrank_pos hd
  have he := @LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
    ℂ _ (poleNeutralOddSubspace L K) inferInstance
    (poleNeutralOdd_innerProductSpace L K) inferInstance
    (poleNeutralOddCompressedCanonical L K) inferInstance
    (poleNeutralOddCompressedCanonical_isSymmetric L K)
  obtain ⟨w, hw⟩ := he.exists_hasEigenvector
  refine ⟨w, hw.2, ?_⟩
  simpa only [poleNeutralOddRayleighBottom] using! hw.apply_eq_smul

private theorem poleNeutralOddRayleighRange_bddBelow (L : ℝ) (K : ℕ) :
    BddBelow (Set.range fun z : {z : poleNeutralOddSubspace L K // z ≠ 0} =>
      RCLike.re (inner ℂ (poleNeutralOddCompressedCanonical L K z) z) /
        ‖(z : poleNeutralOddSubspace L K)‖ ^ 2) := by
  let T : poleNeutralOddSubspace L K →L[ℂ] poleNeutralOddSubspace L K :=
    (poleNeutralOddCompressedCanonical L K).toContinuousLinearMap
  refine ⟨-‖T‖, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hn := @ContinuousLinearMap.rayleighQuotient_le_norm
    ℂ _ (poleNeutralOddSubspace L K) inferInstance
    (poleNeutralOdd_innerProductSpace L K) T
    (z : poleNeutralOddSubspace L K)
  have hn' : |RCLike.re (inner ℂ (T z) z) / ‖(z : poleNeutralOddSubspace L K)‖ ^ 2| ≤ ‖T‖ := by
    simpa only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using! hn
  exact neg_le_of_abs_le hn'

theorem poleNeutralOddRayleighBottom_mul_norm_sq_le {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : poleNeutralOddSubspace L K) :
    poleNeutralOddRayleighBottom L K hL hK * ‖w‖ ^ 2 ≤
      (inner ℂ (poleNeutralOddCompressedCanonical L K w) w).re := by
  by_cases hw : w = 0
  · subst w
    simp
  · have hi : poleNeutralOddRayleighBottom L K hL hK ≤
        RCLike.re (inner ℂ (poleNeutralOddCompressedCanonical L K w) w) / ‖w‖ ^ 2 := by
      exact ciInf_le (poleNeutralOddRayleighRange_bddBelow L K) ⟨w, hw⟩
    have hden : 0 < ‖w‖ ^ 2 := by positivity
    have hh := (le_div_iff₀ hden).mp hi
    simpa only [RCLike.re_eq_complex_re] using hh

/-- Exact source-moment energy identity for an actual even eigenmode. -/
theorem poleNeutral_source_moment_energy_eq {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re =
    (inner ℂ (poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
      (lam : ℂ) • poleNeutralIndexLinearMap hL K u) (poleNeutralIndexLinearMap hL K u)).re := by
  have hd := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K hK u
  change poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
    poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K u) = _ at hd
  rw [hu, map_smul] at hd
  have hp := congrArg (fun z : poleNeutralOddSubspace L K =>
    inner ℂ z (poleNeutralIndexLinearMap hL K u)) hd
  have hsmul : inner ℂ
      (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K)
      (poleNeutralIndexLinearMap hL K u) =
      star (poleNeutralCorrectedCubicSource L K u) *
        inner ℂ (poleNeutralCubicCompressionVector L K) (poleNeutralIndexLinearMap hL K u) := by
    change inner ℂ
      (poleNeutralCorrectedCubicSource L K u •
        (poleNeutralCubicCompressionVector L K).val.val)
      (poleNeutralIndexLinearMap hL K u).val.val = _
    exact inner_smul_left _ _ _
  rw [hsmul] at hp
  rw [poleNeutral_cubic_pairing_eq_momentFour hL] at hp
  exact congrArg Complex.re hp.symm

theorem poleNeutral_source_moment_gap_le {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    (poleNeutralOddRayleighBottom L K hL hK - lam) * ‖poleNeutralIndexLinearMap hL K u‖ ^ 2 ≤
      (star (poleNeutralCorrectedCubicSource L K u) *
        centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re := by
  rw [poleNeutral_source_moment_energy_eq hL K (by omega) lam u hu]
  have hb := poleNeutralOddRayleighBottom_mul_norm_sq_le hL K hK
    (poleNeutralIndexLinearMap hL K u)
  have hsub : inner ℂ
      (poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
        (lam : ℂ) • poleNeutralIndexLinearMap hL K u) (poleNeutralIndexLinearMap hL K u) =
      inner ℂ (poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u))
        (poleNeutralIndexLinearMap hL K u) -
      star (lam : ℂ) *
        inner ℂ (poleNeutralIndexLinearMap hL K u) (poleNeutralIndexLinearMap hL K u) := by
    change inner ℂ
      ((poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u)).val.val -
        (lam : ℂ) • (poleNeutralIndexLinearMap hL K u).val.val)
      (poleNeutralIndexLinearMap hL K u).val.val = _
    rw [inner_sub_left, inner_smul_left]
  rw [hsub]
  rw [Complex.sub_re]
  have hn : (inner ℂ (poleNeutralIndexLinearMap hL K u) (poleNeutralIndexLinearMap hL K u)).re =
      ‖poleNeutralIndexLinearMap hL K u‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using!
      (norm_sq_eq_re_inner (𝕜 := ℂ) (poleNeutralIndexLinearMap hL K u)).symm
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hn]
  linarith

theorem poleNeutral_strictEven_source_moment_pos {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u)
    (hgap : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :
    0 < (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re := by
  have hDu : poleNeutralIndexLinearMap hL K u ≠ 0 := by
    intro hd
    apply hu0
    apply poleNeutralIndexLinearMap_injective hL K
    simpa using hd
  have hnorm : 0 < ‖poleNeutralIndexLinearMap hL K u‖ ^ 2 := by positivity
  have hp := mul_pos (sub_pos.mpr hgap) hnorm
  exact lt_of_lt_of_le hp
    (poleNeutral_source_moment_gap_le hL K hK _ u hu)

theorem poleNeutral_strictEven_source_ne_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u)
    (hgap : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :
    poleNeutralCorrectedCubicSource L K u ≠ 0 := by
  intro hs
  have hp := poleNeutral_strictEven_source_moment_pos hL K hK u hu0 hu hgap
  rw [hs, star_zero, zero_mul, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem poleNeutral_strictEven_momentFour_ne_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u)
    (hgap : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :
    centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) ≠ 0 := by
  intro hm
  have hp := poleNeutral_strictEven_source_moment_pos hL K hK u hu0 hu hgap
  rw [hm, mul_zero, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

end Zeta23.CCM

#print axioms Zeta23.CCM.poleNeutralIndexInverse_norm_le_two
#print axioms Zeta23.CCM.exists_eigenmode_at_poleNeutralEvenRayleighBottom
#print axioms Zeta23.CCM.exists_eigenmode_at_poleNeutralOddRayleighBottom
#print axioms Zeta23.CCM.poleNeutral_source_moment_energy_eq
#print axioms Zeta23.CCM.poleNeutral_source_moment_gap_le
#print axioms Zeta23.CCM.poleNeutral_strictEven_source_moment_pos
#print axioms Zeta23.CCM.poleNeutral_strictEven_source_ne_zero
#print axioms Zeta23.CCM.poleNeutral_strictEven_momentFour_ne_zero
