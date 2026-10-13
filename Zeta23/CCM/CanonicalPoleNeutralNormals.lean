import Zeta23.CCM.CanonicalPoleNeutralCarrier
import Zeta23.CCM.CanonicalPoleNeutralIntertwining
import Zeta23.CCM.CanonicalSecularResolvent

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

-- These are the existing inherited coefficient metrics and parity wrappers.
-- Local transparency exposes their identical dictionaries to elaboration.
set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
Explicit native pole normals and the actual corrected cubic defect.

The profile vectors are the existing native real profiles. Their legal
orthogonal projections represent the unchanged elementary-pole functionals.
The scalar correction below is constructed from those normals and the actual
canonical output; it is not an assumed corrected-source interface.
-/

def canonicalPoleEvenProfileVector (L : ℝ) (K : ℕ) :
    EuclideanSpace ℂ (Fin (2 * K + 1)) := WithLp.toLp 2 (poleEvenProfile L K)

def canonicalPoleOddProfileVector (L : ℝ) (K : ℕ) :
    EuclideanSpace ℂ (Fin (2 * K + 1)) := WithLp.toLp 2 (poleOddProfile L K)

def canonicalPoleEvenLegalNormal (L : ℝ) (K : ℕ) : euclideanEvenBoundaryFlatSubspace K :=
  (euclideanEvenBoundaryFlatSubspace K).orthogonalProjectionOnto
    (canonicalPoleEvenProfileVector L K)

def canonicalPoleOddLegalNormal (L : ℝ) (K : ℕ) : euclideanOddBoundaryFlatSubspace K :=
  (euclideanOddBoundaryFlatSubspace K).orthogonalProjectionOnto
    (canonicalPoleOddProfileVector L K)

theorem inner_canonicalPoleEvenProfileVector (L : ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    inner ℂ (canonicalPoleEvenProfileVector L K) x = canonicalPoleEvenFunctional L K x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct canonicalPoleEvenFunctional
  apply Finset.sum_congr rfl
  intro i hi
  simp [canonicalPoleEvenProfileVector, poleEvenProfile, mul_comm]

theorem inner_canonicalPoleOddProfileVector (L : ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    inner ℂ (canonicalPoleOddProfileVector L K) x = canonicalPoleOddFunctional L K x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct canonicalPoleOddFunctional
  apply Finset.sum_congr rfl
  intro i hi
  simp [canonicalPoleOddProfileVector, poleOddProfile, mul_comm]

theorem inner_canonicalPoleEvenLegalNormal (L : ℝ) (K : ℕ)
    (u : euclideanEvenBoundaryFlatSubspace K) :
    inner ℂ (canonicalPoleEvenLegalNormal L K) u = canonicalPoleEvenFunctional L K u := by
  calc
    _ = inner ℂ (canonicalPoleEvenProfileVector L K)
        (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :=
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
        (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin (2 * K + 1)))
        (K := euclideanEvenBoundaryFlatSubspace K) u (canonicalPoleEvenProfileVector L K)
    _ = _ := inner_canonicalPoleEvenProfileVector L K u

theorem inner_canonicalPoleOddLegalNormal (L : ℝ) (K : ℕ)
    (u : euclideanOddBoundaryFlatSubspace K) :
    inner ℂ (canonicalPoleOddLegalNormal L K) u = canonicalPoleOddFunctional L K u := by
  calc
    _ = inner ℂ (canonicalPoleOddProfileVector L K)
        (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :=
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
        (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin (2 * K + 1)))
        (K := euclideanOddBoundaryFlatSubspace K) u (canonicalPoleOddProfileVector L K)
    _ = _ := inner_canonicalPoleOddProfileVector L K u

theorem canonicalPoleEvenLegalNormal_ne_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) : canonicalPoleEvenLegalNormal L K ≠ 0 := by
  intro hg
  apply canonicalPoleEvenFunctional_nonzeroWitness hL K hK
  rw [← inner_canonicalPoleEvenLegalNormal, hg, inner_zero_left]

theorem canonicalPoleOddLegalNormal_ne_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) : canonicalPoleOddLegalNormal L K ≠ 0 := by
  intro hg
  apply canonicalPoleOddFunctional_nonzeroWitness hL K hK
  rw [← inner_canonicalPoleOddLegalNormal, hg, inner_zero_left]

theorem poleNeutralEvenSubspace_eq_orthogonal_normal (L : ℝ) (K : ℕ) :
    poleNeutralEvenSubspace L K = (ℂ ∙ canonicalPoleEvenLegalNormal L K)ᗮ := by
  ext u
  rw [mem_poleNeutralEvenSubspace, Submodule.mem_orthogonal_singleton_iff_inner_right,
    inner_canonicalPoleEvenLegalNormal]

theorem poleNeutralOddSubspace_eq_orthogonal_normal (L : ℝ) (K : ℕ) :
    poleNeutralOddSubspace L K = (ℂ ∙ canonicalPoleOddLegalNormal L K)ᗮ := by
  ext u
  rw [mem_poleNeutralOddSubspace, Submodule.mem_orthogonal_singleton_iff_inner_right,
    inner_canonicalPoleOddLegalNormal]

/-- The exact coefficient of the actual removed even canonical output. -/
def poleNeutralEvenOutputCoefficient (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) : ℂ :=
  inner ℂ (canonicalPoleEvenLegalNormal L K) (evenCompressedCanonical L K u.val) /
    inner ℂ (canonicalPoleEvenLegalNormal L K) (canonicalPoleEvenLegalNormal L K)

theorem poleNeutralEvenOutputResidual_eq_normal (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    poleNeutralEvenOutputResidual L K u =
      poleNeutralEvenOutputCoefficient L K u • canonicalPoleEvenLegalNormal L K := by
  rw [poleNeutralEvenOutputResidual, coe_poleNeutralEvenCompressedCanonical,
    Submodule.coe_orthogonalProjectionOnto_apply]
  rw [poleNeutralEvenSubspace_eq_orthogonal_normal,
    Submodule.starProjection_orthogonal_val]
  rw [sub_sub_cancel, Submodule.starProjection_singleton ℂ]
  simp only [poleNeutralEvenOutputCoefficient, inner_self_eq_norm_sq_to_K,
    Complex.ofReal_pow]

theorem orthogonalProjection_poleNeutralOdd_normal_eq_zero (L : ℝ) (K : ℕ) :
    (Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
      (E := euclideanOddBoundaryFlatSubspace K) (poleNeutralOddSubspace L K))
        (canonicalPoleOddLegalNormal L K) = 0 := by
  apply (Submodule.orthogonalProjectionOnto_eq_zero_iff
    (𝕜 := ℂ) (E := euclideanOddBoundaryFlatSubspace K)
    (K := poleNeutralOddSubspace L K)).mpr
  rw [poleNeutralOddSubspace_eq_orthogonal_normal]
  exact (ℂ ∙ canonicalPoleOddLegalNormal L K).le_orthogonal_orthogonal
    (Submodule.mem_span_singleton_self _)

/-- Native even profile and native odd profile use their existing scale. -/
theorem euclideanIndexLinearMap_canonicalPoleEvenProfileVector
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    euclideanIndexLinearMap K (canonicalPoleEvenProfileVector L K) =
      ((L / (4 * Real.pi) : ℝ) : ℂ) • canonicalPoleOddProfileVector L K := by
  apply (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).injective
  rw [euclideanIndexLinearMap_coordinates]
  ext i
  rw [indexMatrix_mulVec_apply]
  change (centeredIndex K i : ℂ) * poleEvenProfile L K i =
    ((L / (4 * Real.pi) : ℝ) : ℂ) * poleOddProfile L K i
  have hd := ne_of_gt (poleProfileDenominator_pos hL (centeredIndex K i))
  have hr : (centeredIndex K i : ℝ) * poleEvenProfileReal (centeredIndex K i) L =
      (L / (4 * Real.pi)) * poleOddProfileReal (centeredIndex K i) L := by
    unfold poleEvenProfileReal poleOddProfileReal
    field_simp [Real.pi_ne_zero, hd]
    ring
  unfold poleEvenProfile poleOddProfile
  exact_mod_cast hr

/-- Quadratic normal coefficient of the existing native even pole profile. -/
def canonicalPoleQuadraticNormalCoefficient (L : ℝ) (K : ℕ) : ℂ :=
  inner ℂ (centeredQuadraticNormal K) (canonicalPoleEvenProfileVector L K) /
    inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K)

theorem exists_canonicalPoleEvenProfileVector_normal_decomposition (L : ℝ) (K : ℕ) :
    ∃ a0 a2 : ℂ, canonicalPoleEvenProfileVector L K =
      (canonicalPoleEvenLegalNormal L K : EuclideanSpace ℂ (Fin (2 * K + 1))) +
        a0 • centeredPowerVector K 0 + a2 • centeredPowerVector K 2 := by
  let r := canonicalPoleEvenProfileVector L K -
    (canonicalPoleEvenLegalNormal L K : EuclideanSpace ℂ (Fin (2 * K + 1)))
  have horth : r ∈ (euclideanEvenBoundaryFlatSubspace K)ᗮ := by
    exact (euclideanEvenBoundaryFlatSubspace K).sub_starProjection_mem_orthogonal
      (canonicalPoleEvenProfileVector L K)
  have hpe : canonicalPoleEvenProfileVector L K ∈ euclideanEvenCoefficientSubspace K := by
    rw [mem_euclideanEvenCoefficientSubspace_iff, mem_evenCoefficientSubspace_iff]
    exact reverseCoefficients_poleEvenProfile L K
  have hge : (canonicalPoleEvenLegalNormal L K : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
      euclideanEvenCoefficientSubspace K :=
    ((mem_euclideanEvenBoundaryFlatSubspace_iff K _).mp
      (canonicalPoleEvenLegalNormal L K).property).2
  have hr : r ∈ evenNormalSubspace K := by
    rw [← evenBoundaryFlat_normal_eq_evenNormalSubspace]
    exact ⟨horth, (euclideanEvenCoefficientSubspace K).sub_mem hpe hge⟩
  rw [evenNormalSubspace, Submodule.mem_sup] at hr
  rcases hr with ⟨y, hy, z, hz, hyz⟩
  rw [Submodule.mem_span_singleton] at hy hz
  rcases hy with ⟨a0, rfl⟩
  rcases hz with ⟨a2, rfl⟩
  refine ⟨a0, a2, ?_⟩
  have hadd := congrArg
    (fun t => t + (canonicalPoleEvenLegalNormal L K :
      EuclideanSpace ℂ (Fin (2 * K + 1)))) hyz.symm
  simpa [r, add_assoc, add_left_comm, add_comm] using hadd

theorem canonicalPoleQuadraticNormalCoefficient_eq_decomposition_a2 (L : ℝ)
    (K : ℕ) (hK : 1 ≤ K) (a0 a2 : ℂ)
    (hres : canonicalPoleEvenProfileVector L K =
      (canonicalPoleEvenLegalNormal L K : EuclideanSpace ℂ (Fin (2 * K + 1))) +
        a0 • centeredPowerVector K 0 + a2 • centeredPowerVector K 2) :
    canonicalPoleQuadraticNormalCoefficient L K = a2 := by
  have hge : inner ℂ (centeredQuadraticNormal K)
      (canonicalPoleEvenLegalNormal L K : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
    rw [inner_eq_zero_symm]
    exact ((euclideanEvenBoundaryFlatSubspace K).mem_orthogonal _).mp
      (centeredQuadraticNormal_mem_evenBoundaryFlat_orthogonal K) _
      (canonicalPoleEvenLegalNormal L K).property
  have hm := congrArg
    (fun x : EuclideanSpace ℂ (Fin (2 * K + 1)) =>
      inner ℂ (centeredQuadraticNormal K) x) hres
  simp only [inner_add_right, inner_smul_right] at hm
  rw [hge, inner_centeredQuadraticNormal_centeredPowerVector_zero_eq_zero,
    inner_centeredQuadraticNormal_centeredPowerVector_two_eq_self] at hm
  simp only [zero_add, mul_zero, add_zero] at hm
  unfold canonicalPoleQuadraticNormalCoefficient
  rw [hm]
  exact mul_div_cancel_right₀ a2 (inner_centeredQuadraticNormal_self_ne_zero K hK)

/-- Exact collinearity of the added native pole-normal projection term. -/
theorem poleNeutralOddProjection_index_evenNormal_eq_cubic
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K) :
    (Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
      (E := euclideanOddBoundaryFlatSubspace K) (poleNeutralOddSubspace L K))
        (euclideanEvenToOddIndexLinearMap K (canonicalPoleEvenLegalNormal L K)) =
      -canonicalPoleQuadraticNormalCoefficient L K • poleNeutralCubicCompressionVector L K := by
  obtain ⟨a0, a2, hres⟩ := exists_canonicalPoleEvenProfileVector_normal_decomposition L K
  have ha2 := canonicalPoleQuadraticNormalCoefficient_eq_decomposition_a2 L K hK a0 a2 hres
  have hD := congrArg (euclideanIndexLinearMap K) hres
  have hD' : ((L / (4 * Real.pi) : ℝ) : ℂ) • canonicalPoleOddProfileVector L K =
      euclideanIndexLinearMap K (canonicalPoleEvenLegalNormal L K :
        EuclideanSpace ℂ (Fin (2 * K + 1))) +
          a0 • centeredPowerVector K 1 + a2 • centeredPowerVector K 3 := by
    simpa [euclideanIndexLinearMap_canonicalPoleEvenProfileVector hL K,
      map_add, map_smul, euclideanIndexLinearMap_centeredPowerVector,
      add_assoc] using hD
  have hp1 : (euclideanOddBoundaryFlatSubspace K).orthogonalProjectionOnto
      (centeredPowerVector K 1) = 0 :=
    ((euclideanOddBoundaryFlatSubspace K).orthogonalProjectionOnto_eq_zero_iff).mpr
      (centeredPowerVector_one_mem_oddBoundaryFlat_orthogonal K)
  have hlegal := congrArg (euclideanOddBoundaryFlatSubspace K).orthogonalProjectionOnto hD'
  rw [map_smul, map_add, map_add, map_smul, map_smul,
    ← coe_euclideanEvenToOddIndexLinearMap,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, hp1] at hlegal
  simp only [smul_zero, add_zero] at hlegal
  change ((L / (4 * Real.pi) : ℝ) : ℂ) • canonicalPoleOddLegalNormal L K =
    euclideanEvenToOddIndexLinearMap K (canonicalPoleEvenLegalNormal L K) +
      a2 • oddCubicCompressionVector K at hlegal
  let Q : euclideanOddBoundaryFlatSubspace K →L[ℂ] poleNeutralOddSubspace L K :=
    Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
      (E := euclideanOddBoundaryFlatSubspace K) (poleNeutralOddSubspace L K)
  have hQ := congrArg Q hlegal
  simp only [map_smul, map_add] at hQ
  have hQg : Q (canonicalPoleOddLegalNormal L K) = 0 :=
    orthogonalProjection_poleNeutralOdd_normal_eq_zero L K
  rw [hQg, smul_zero] at hQ
  change 0 = Q (euclideanEvenToOddIndexLinearMap K (canonicalPoleEvenLegalNormal L K)) +
    a2 • poleNeutralCubicCompressionVector L K at hQ
  rw [ha2]
  calc
    _ = (Q (euclideanEvenToOddIndexLinearMap K (canonicalPoleEvenLegalNormal L K)) +
        a2 • poleNeutralCubicCompressionVector L K) -
          a2 • poleNeutralCubicCompressionVector L K := by abel
    _ = _ := by rw [← hQ]; simp

/-- Constructed correction of the actual legal canonical cubic source. -/
def poleNeutralCorrectedCubicSource (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) : ℂ :=
  cubicDefectFunctional L K u.val -
    canonicalPoleQuadraticNormalCoefficient L K * poleNeutralEvenOutputCoefficient L K u

def poleNeutralEvenOutputCoefficientLinearMap (L : ℝ) (K : ℕ) :
    poleNeutralEvenSubspace L K →ₗ[ℂ] ℂ where
  toFun := poleNeutralEvenOutputCoefficient L K
  map_add' u v := by
    change inner ℂ (canonicalPoleEvenLegalNormal L K)
        (evenCompressedCanonical L K (u.val + v.val)) / _ = _
    rw [map_add, inner_add_right, add_div]
  map_smul' c u := by
    change inner ℂ (canonicalPoleEvenLegalNormal L K)
        (evenCompressedCanonical L K (c • u.val)) / _ =
      c * (inner ℂ (canonicalPoleEvenLegalNormal L K)
        (evenCompressedCanonical L K u.val) / _)
    rw [map_smul, inner_smul_right]
    ring

/-- Linear functional needed by the existing shift and parity-swap calculus. -/
def poleNeutralCorrectedCubicFunctional (L : ℝ) (K : ℕ) :
    poleNeutralEvenSubspace L K →ₗ[ℂ] ℂ :=
  (cubicDefectFunctional L K).comp (poleNeutralEvenSubspace L K).subtype -
    canonicalPoleQuadraticNormalCoefficient L K • poleNeutralEvenOutputCoefficientLinearMap L K

@[simp] theorem poleNeutralCorrectedCubicFunctional_apply (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    poleNeutralCorrectedCubicFunctional L K u = poleNeutralCorrectedCubicSource L K u := rfl

theorem poleNeutralCorrectedCubicSource_eq_explicitCanonicalSourceMoment
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (u : poleNeutralEvenSubspace L K) :
    poleNeutralCorrectedCubicSource L K u = explicitCanonicalSourceMoment L K u.val -
      canonicalPoleQuadraticNormalCoefficient L K * poleNeutralEvenOutputCoefficient L K u := by
  unfold poleNeutralCorrectedCubicSource
  rw [cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]

/-- Actual corrected rank-one identity, with no assumed source property. -/
theorem poleNeutralCompressedIndexDefect_eq_correctedCubicSource
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (u : poleNeutralEvenSubspace L K) :
    poleNeutralCompressedIndexDefect hL K u =
      poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K := by
  rw [poleNeutralCompressedIndexDefect_eq_cubicSource_add_residual hL K hK u,
    poleNeutralEvenOutputResidual_eq_normal, map_smul, map_smul,
    poleNeutralOddProjection_index_evenNormal_eq_cubic hL K (by omega), smul_smul]
  unfold poleNeutralCorrectedCubicSource
  rw [← add_smul]
  congr 1
  ring

/-- Instantiate the existing secular interface on the actual native carriers. -/
theorem canonicalPoleNeutralRankOneIntertwining {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) :
    RankOneIntertwining (E := poleNeutralEvenSubspace L K) (O := poleNeutralOddSubspace L K)
      (poleNeutralEvenCompressedCanonical L K) (poleNeutralOddCompressedCanonical L K)
      (poleNeutralIndexEquiv hL K (by omega)) (poleNeutralCubicCompressionVector L K)
      (poleNeutralCorrectedCubicFunctional L K) := by
  intro u
  change poleNeutralCompressedIndexDefect hL K u =
    poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K
  exact poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K hK u

theorem poleNeutral_cubic_pairing_eq_momentFour {L : ℝ} (hL : 0 < L)
    (K : ℕ) (u : poleNeutralEvenSubspace L K) :
    inner ℂ (poleNeutralCubicCompressionVector L K) (poleNeutralIndexLinearMap hL K u) =
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) := by
  calc
    _ = inner ℂ (oddCubicCompressionVector K)
        (euclideanEvenToOddIndexLinearMap K u.val) :=
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
        (𝕜 := ℂ) (E := euclideanOddBoundaryFlatSubspace K)
        (K := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K u)
          (oddCubicCompressionVector K)
    _ = _ := inner_oddCubicCompressionVector_evenToOddIndex_eq_momentFour K u.val

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalPoleEvenLegalNormal_ne_zero
#print axioms Zeta23.CCM.canonicalPoleOddLegalNormal_ne_zero
#print axioms Zeta23.CCM.poleNeutralEvenOutputResidual_eq_normal
#print axioms Zeta23.CCM.poleNeutralOddProjection_index_evenNormal_eq_cubic
#print axioms Zeta23.CCM.poleNeutralCompressedIndexDefect_eq_correctedCubicSource
#print axioms Zeta23.CCM.canonicalPoleNeutralRankOneIntertwining
#print axioms Zeta23.CCM.poleNeutral_cubic_pairing_eq_momentFour
