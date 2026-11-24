import Zeta23.OPICASupport.FourierEnergy.BoundaryFlatStrictEnergy

/-!
# A positive lower bound at each fixed aperture and cutoff

The norm is the existing physical Euclidean/PiLp_2 norm. Compactness provides
an existential constant for fixed `L,K`; no uniform aperture/cutoff bound is
asserted. The compact-set argument also covers an empty unit sphere.
-/

noncomputable section

open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4.ArithmeticFrontier

namespace Zeta23.OPICARound20

/-- The low-cutoff sample premise is empty, matching the zero-dimensional
boundary-flat carrier. -/
theorem nonresonantActualZeroSamples_of_cutoff_le_one
    (L : ℝ) (K : ℕ) (hK : K ≤ 1) : NonresonantActualZeroSamples L K := by
  have hn : 2 * K - 2 = 0 := by omega
  unfold NonresonantActualZeroSamples
  rw [hn]
  exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩

/-- At cutoff zero or one the entire physical BF carrier is zero. In
particular, a positive norm-square lower-bound constant needs no C1 premise. -/
theorem canonicalSourceEnergy_low_cutoff_euclidean_bound
    (L : ℝ) (K : ℕ) (hK : K ≤ 1)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : x ∈ euclideanBoundaryFlatSubspace K) :
    1 * ‖x‖ ^ 2 ≤ matrixRealEnergy (canonicalSourceMatrix L K) x := by
  have hu := boundaryFlat_coefficients_zero_of_cutoff_le_one K hK
    ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)
    ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat K x).mp hflat)
  have hx : x = 0 := by
    apply (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).injective
    simpa using hu
  simp [hx, matrixRealEnergy, quadraticForm]

/-- For every fixed positive aperture and cutoff, C1 and the separate actual
sample supply give a strictly positive lower bound in the native Euclidean norm. -/
theorem canonicalSourceEnergy_exists_positive_euclidean_lower_bound
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hsamples : NonresonantActualZeroSamples L K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
        x ∈ euclideanBoundaryFlatSubspace K →
        c * ‖x‖ ^ 2 ≤ matrixRealEnergy (canonicalSourceMatrix L K) x := by
  let A := canonicalSourceMatrix L K
  let S : Set (EuclideanSpace ℂ (Fin (2 * K + 1))) :=
    (euclideanBoundaryFlatSubspace K : Set _) ∩ Metric.sphere 0 1
  have hSc : IsCompact S :=
    (isCompact_sphere 0 1).inter_left
      (Submodule.closed_of_finiteDimensional (euclideanBoundaryFlatSubspace K))
  have hcont : Continuous (fun x : EuclideanSpace ℂ (Fin (2 * K + 1)) =>
      matrixRealEnergy A x) := by
    simpa only [matrixRealEnergy_eq_re_inner_apply_self, Function.comp_def, id_eq] using
      Complex.continuous_re.comp
        (A.toEuclideanLin.continuous_of_finiteDimensional.inner continuous_id)
  have hpos : ∀ x ∈ S, 0 < matrixRealEnergy A x := by
    intro x hx
    have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx.2
    have hxne : x ≠ 0 := by
      intro hz
      simp [hz] at hxnorm
    exact canonicalSourceEnergy_pos_euclidean_of_c1_and_samples
      hC1 hL K hsamples x hx.1 hxne
  obtain ⟨c, hc, hcbound⟩ := hSc.exists_forall_le' hcont.continuousOn hpos
  refine ⟨c, hc, ?_⟩
  intro x hflat
  by_cases hx : x = 0
  · simp [hx, matrixRealEnergy, quadraticForm]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let r : ℂ := ((‖x‖⁻¹ : ℝ) : ℂ)
  have hy : r • x ∈ S := by
    refine ⟨(euclideanBoundaryFlatSubspace K).smul_mem r hflat, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp only [r, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
  have hscale : matrixRealEnergy A (r • x) =
      ‖x‖⁻¹ ^ 2 * matrixRealEnergy A x := by
    unfold matrixRealEnergy
    rw [map_smul, quadraticForm_smul]
    simp [r, Complex.mul_re, pow_two]
  change c * ‖x‖ ^ 2 ≤ matrixRealEnergy A x
  calc
    c * ‖x‖ ^ 2 ≤ matrixRealEnergy A (r • x) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hcbound (r • x) hy) (sq_nonneg ‖x‖)
    _ = (‖x‖⁻¹ ^ 2 * matrixRealEnergy A x) * ‖x‖ ^ 2 := by rw [hscale]
    _ = matrixRealEnergy A x := by
      field_simp

/-- The coefficient presentation uses the explicit `WithLp.toLp 2` physical
norm, never the default sup norm on a coefficient function. -/
theorem canonicalSourceEnergy_exists_positive_coefficient_l2_lower_bound
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hsamples : NonresonantActualZeroSamples L K) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Fin (2 * K + 1) → ℂ,
      BoundaryFlatCoefficients K u →
      c * ‖WithLp.toLp 2 u‖ ^ 2 ≤
        (quadraticForm (canonicalSourceMatrix L K) u).re := by
  obtain ⟨c, hc, hbound⟩ :=
    canonicalSourceEnergy_exists_positive_euclidean_lower_bound hC1 hL K hsamples
  refine ⟨c, hc, ?_⟩
  intro u hflat
  have hx : WithLp.toLp 2 u ∈ euclideanBoundaryFlatSubspace K :=
    (mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat K _).mpr hflat
  exact hbound (WithLp.toLp 2 u) hx

end Zeta23.OPICARound20

#print axioms Zeta23.OPICARound20.nonresonantActualZeroSamples_of_cutoff_le_one
#print axioms Zeta23.OPICARound20.canonicalSourceEnergy_low_cutoff_euclidean_bound
#print axioms Zeta23.OPICARound20.canonicalSourceEnergy_exists_positive_euclidean_lower_bound
#print axioms Zeta23.OPICARound20.canonicalSourceEnergy_exists_positive_coefficient_l2_lower_bound
