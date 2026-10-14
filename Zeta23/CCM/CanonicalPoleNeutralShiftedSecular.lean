import Zeta23.CCM.CanonicalPoleNeutralSourceMoment
import Zeta23.CCM.CanonicalShiftedSecular
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

namespace Zeta23.CCM

open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
Actual pole-neutral shifted branches at the actual spectral value `lam`.

The even ray uses the native odd resolvent below its actual Rayleigh bottom.
The odd ray uses the actual adjoint of the centered-index map, the Riesz
vector of the constructed corrected source, and the required minus sign.
No unitarity, parity swap of source meanings, negative-depth-to-parity-gap
estimate, detector threshold substitution, or source-root producer is used.

The two predecessor inverse constants 6 and 12 concern different Schur
operators; neither is inferred from the relative parity gaps in this file.
-/

def poleNeutralEvenShiftedCanonical (L : ℝ) (K : ℕ) (lam : ℝ) :
    poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralEvenSubspace L K :=
  poleNeutralEvenCompressedCanonical L K - (lam : ℂ) • LinearMap.id

def poleNeutralOddShiftedCanonical (L : ℝ) (K : ℕ) (lam : ℝ) :
    poleNeutralOddSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K :=
  poleNeutralOddCompressedCanonical L K - (lam : ℂ) • LinearMap.id

private theorem poleNeutralEvenRayleighRange_bddBelow (L : ℝ) (K : ℕ) :
    BddBelow (Set.range fun z : {z : poleNeutralEvenSubspace L K // z ≠ 0} =>
      RCLike.re (inner ℂ (poleNeutralEvenCompressedCanonical L K z) z) /
        ‖(z : poleNeutralEvenSubspace L K)‖ ^ 2) := by
  let T : poleNeutralEvenSubspace L K →L[ℂ] poleNeutralEvenSubspace L K :=
    (poleNeutralEvenCompressedCanonical L K).toContinuousLinearMap
  refine ⟨-‖T‖, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hn := @ContinuousLinearMap.rayleighQuotient_le_norm
    ℂ _ (poleNeutralEvenSubspace L K) inferInstance
    (poleNeutralEven_innerProductSpace L K) T
    (z : poleNeutralEvenSubspace L K)
  have hn' : |RCLike.re (inner ℂ (T z) z) / ‖(z : poleNeutralEvenSubspace L K)‖ ^ 2| ≤ ‖T‖ := by
    simpa only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using! hn
  exact neg_le_of_abs_le hn'

theorem poleNeutralEvenRayleighBottom_mul_norm_sq_le {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (u : poleNeutralEvenSubspace L K) :
    poleNeutralEvenRayleighBottom L K hL hK * ‖u‖ ^ 2 ≤
      (inner ℂ (poleNeutralEvenCompressedCanonical L K u) u).re := by
  by_cases hu : u = 0
  · subst u
    simp
  · have hi : poleNeutralEvenRayleighBottom L K hL hK ≤
        RCLike.re (inner ℂ (poleNeutralEvenCompressedCanonical L K u) u) / ‖u‖ ^ 2 := by
      exact ciInf_le (poleNeutralEvenRayleighRange_bddBelow L K) ⟨u, hu⟩
    have hden : 0 < ‖u‖ ^ 2 := by positivity
    simpa only [RCLike.re_eq_complex_re] using (le_div_iff₀ hden).mp hi

theorem poleNeutralEvenShiftedCanonical_coercive {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K) :
    (poleNeutralEvenRayleighBottom L K hL hK - lam) * ‖u‖ ^ 2 ≤
      (inner ℂ (poleNeutralEvenShiftedCanonical L K lam u) u).re := by
  have hb := poleNeutralEvenRayleighBottom_mul_norm_sq_le hL K hK u
  have hs := @re_inner_ofReal_smul_self (poleNeutralEvenSubspace L K) inferInstance
    (poleNeutralEven_innerProductSpace L K) lam u
  simp only [poleNeutralEvenShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, inner_sub_left, Complex.sub_re]
  linarith

theorem poleNeutralOddShiftedCanonical_coercive {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (w : poleNeutralOddSubspace L K) :
    (poleNeutralOddRayleighBottom L K hL hK - lam) * ‖w‖ ^ 2 ≤
      (inner ℂ (poleNeutralOddShiftedCanonical L K lam w) w).re := by
  have hb := poleNeutralOddRayleighBottom_mul_norm_sq_le hL K hK w
  have hs := @re_inner_ofReal_smul_self (poleNeutralOddSubspace L K) inferInstance
    (poleNeutralOdd_innerProductSpace L K) lam w
  simp only [poleNeutralOddShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, inner_sub_left, Complex.sub_re]
  linarith

private theorem nativeCoercive_injective {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →ₗ[ℂ] E) (delta : ℝ) (hd : 0 < delta)
    (hc : ∀ u, delta * ‖u‖ ^ 2 ≤ (inner ℂ (T u) u).re) : Function.Injective T := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have hb := hc u
  rw [hu, inner_zero_left, Complex.zero_re] at hb
  have hn : ‖u‖ ^ 2 ≤ 0 := by
    by_contra hneg
    push Not at hneg
    have hp := mul_pos hd hneg
    linarith
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])

/-- Actual even inverse domain: `lam` is strictly below the native even bottom. -/
def poleNeutralEvenShiftedCanonicalEquiv {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    poleNeutralEvenSubspace L K ≃ₗ[ℂ] poleNeutralEvenSubspace L K :=
  LinearEquiv.ofInjectiveEndo (poleNeutralEvenShiftedCanonical L K lam)
    (@nativeCoercive_injective (poleNeutralEvenSubspace L K) inferInstance
      (poleNeutralEven_innerProductSpace L K) (poleNeutralEvenShiftedCanonical L K lam)
      (poleNeutralEvenRayleighBottom L K hL hK - lam) (sub_pos.mpr hlam)
      (poleNeutralEvenShiftedCanonical_coercive hL K hK lam))

/-- Actual odd inverse domain, distinct from a detector's threshold `-eta`. -/
def poleNeutralOddShiftedCanonicalEquiv {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    poleNeutralOddSubspace L K ≃ₗ[ℂ] poleNeutralOddSubspace L K :=
  LinearEquiv.ofInjectiveEndo (poleNeutralOddShiftedCanonical L K lam)
    (@nativeCoercive_injective (poleNeutralOddSubspace L K) inferInstance
      (poleNeutralOdd_innerProductSpace L K) (poleNeutralOddShiftedCanonical L K lam)
      (poleNeutralOddRayleighBottom L K hL hK - lam) (sub_pos.mpr hlam)
      (poleNeutralOddShiftedCanonical_coercive hL K hK lam))

theorem poleNeutral_shifted_rankOneIntertwining {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) :
    RankOneIntertwining (poleNeutralEvenShiftedCanonical L K lam)
      (poleNeutralOddShiftedCanonical L K lam) (poleNeutralIndexEquiv hL K (by omega))
      (poleNeutralCubicCompressionVector L K) (poleNeutralCorrectedCubicFunctional L K) :=
  (canonicalPoleNeutralRankOneIntertwining hL K (by omega)).shift (lam : ℂ)

def poleNeutralEvenShiftedRay {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    poleNeutralEvenSubspace L K :=
  secularResolventRay (poleNeutralOddShiftedCanonicalEquiv hL K hK lam hlam)
    (poleNeutralIndexEquiv hL K (by omega)) (poleNeutralCubicCompressionVector L K)

theorem poleNeutral_even_eigenvector_eq_source_smul_shiftedRay {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    u = poleNeutralCorrectedCubicSource L K u • poleNeutralEvenShiftedRay hL K hK lam hlam := by
  exact eq_smul_secularResolventRay_of_apply_eq_zero
    (poleNeutral_shifted_rankOneIntertwining hL K hK lam) (fun _ => rfl)
    (by simp only [poleNeutralEvenShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hu, sub_self])

theorem poleNeutral_even_eigen_source_ne_zero_of_lt_odd_bottom {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    poleNeutralCorrectedCubicSource L K u ≠ 0 := by
  intro hs
  have hr := poleNeutral_even_eigenvector_eq_source_smul_shiftedRay hL K hK lam hlam u hu
  rw [hs, zero_smul] at hr
  exact hu0 hr

theorem poleNeutral_even_eigen_shiftedRay_source_eq_one {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    poleNeutralCorrectedCubicSource L K (poleNeutralEvenShiftedRay hL K hK lam hlam) = 1 := by
  have hs := poleNeutral_even_eigen_source_ne_zero_of_lt_odd_bottom hL K hK lam hlam u hu0 hu
  have hr := poleNeutral_even_eigenvector_eq_source_smul_shiftedRay hL K hK lam hlam u hu
  have hf := congrArg (poleNeutralCorrectedCubicFunctional L K) hr
  simp only [map_smul, smul_eq_mul, poleNeutralCorrectedCubicFunctional_apply] at hf
  apply mul_left_cancel₀ hs
  simpa only [mul_one] using hf.symm

theorem poleNeutral_even_shifted_det_quotient {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    LinearMap.det (poleNeutralEvenShiftedCanonical L K lam) /
      LinearMap.det (poleNeutralOddShiftedCanonical L K lam) =
        1 - poleNeutralCorrectedCubicSource L K (poleNeutralEvenShiftedRay hL K hK lam hlam) :=
  det_div_det_eq_one_sub_secularResolventScalar
    (poleNeutral_shifted_rankOneIntertwining hL K hK lam) (fun _ => rfl)

/-- Riesz vector of the constructed actual corrected source, with the native metric. -/
def poleNeutralCorrectedCubicRieszVector (L : ℝ) (K : ℕ) : poleNeutralEvenSubspace L K :=
  (poleNeutralCorrectedCubicFunctional L K).adjoint 1

theorem inner_poleNeutralCorrectedCubicRieszVector (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    inner ℂ (poleNeutralCorrectedCubicRieszVector L K) u = poleNeutralCorrectedCubicSource L K u := by
  rw [poleNeutralCorrectedCubicRieszVector, LinearMap.adjoint_inner_left]
  simp

def poleNeutralCubicPairingFunctional (L : ℝ) (K : ℕ) : poleNeutralOddSubspace L K →ₗ[ℂ] ℂ :=
  innerₛₗ ℂ (poleNeutralCubicCompressionVector L K)

/-- Exact adjoint rank-one identity. The adjoint reverses the operator order. -/
theorem poleNeutral_adjoint_rankOne_identity {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : poleNeutralOddSubspace L K) :
    (poleNeutralIndexLinearMap hL K).adjoint (poleNeutralOddCompressedCanonical L K w) -
      poleNeutralEvenCompressedCanonical L K ((poleNeutralIndexLinearMap hL K).adjoint w) =
        poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K := by
  let D : poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K := poleNeutralIndexLinearMap hL K
  let A : poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralEvenSubspace L K := poleNeutralEvenCompressedCanonical L K
  let B : poleNeutralOddSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K := poleNeutralOddCompressedCanonical L K
  apply ext_inner_right ℂ
  intro v
  have hr := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K (by omega) v
  simp only [poleNeutralCompressedIndexDefect, LinearMap.sub_apply, LinearMap.comp_apply] at hr
  calc
    _ = inner ℂ w (B (D v) - D (A v)) := by
      rw [inner_sub_left, LinearMap.adjoint_inner_left,
        poleNeutralOddCompressedCanonical_isSymmetric L K w (D v),
        poleNeutralEvenCompressedCanonical_isSymmetric L K (D.adjoint w) v,
        LinearMap.adjoint_inner_left, inner_sub_right]
    _ = inner ℂ w (poleNeutralCorrectedCubicSource L K v • poleNeutralCubicCompressionVector L K) := by rw [hr]
    _ = _ := by
      rw [inner_smul_right, inner_smul_left, inner_poleNeutralCorrectedCubicRieszVector]
      change _ = star (inner ℂ (poleNeutralCubicCompressionVector L K) w) * _
      rw [inner_conj_symm]
      ring

/-- The inverse of the actual adjoint index map is the adjoint of the actual
inverse index map. No unitary property is claimed. -/
def poleNeutralIndexAdjointEquiv {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) :
    poleNeutralOddSubspace L K ≃ₗ[ℂ] poleNeutralEvenSubspace L K :=
  let Di := poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)
  { (poleNeutralIndexLinearMap hL K).adjoint with
    invFun := (Di.symm : poleNeutralOddSubspace L K →ₗ[ℂ] poleNeutralEvenSubspace L K).adjoint
    left_inv := by
      intro w
      apply ext_inner_right ℂ
      intro z
      rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
      change inner ℂ w (Di (Di.symm z)) = inner ℂ w z
      rw [LinearEquiv.apply_symm_apply]
    right_inv := by
      intro u
      apply ext_inner_right ℂ
      intro v
      rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
      change inner ℂ u (Di.symm (Di v)) = inner ℂ u v
      rw [LinearEquiv.symm_apply_apply] }

/-- Exact transformed-competitor equation for an actual odd eigenvector.
The corrected source is its actual native Riesz vector, with a minus sign. -/
theorem poleNeutral_odd_eigen_adjoint_competitor_eq_source {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (w : poleNeutralOddSubspace L K)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    poleNeutralEvenShiftedCanonical L K lam ((poleNeutralIndexLinearMap hL K).adjoint w) =
      -poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K := by
  have ha := poleNeutral_adjoint_rankOne_identity hL K hK w
  rw [hw, map_smul] at ha
  simp only [poleNeutralEvenShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, neg_smul]
  rw [← ha]
  abel

/-- An actual odd eigenmode has either nonzero native cubic pairing or a
nonzero actual adjoint-transformed even competitor at the same `lam`. -/
theorem poleNeutral_odd_eigen_adjoint_competitor_source_dichotomy {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    poleNeutralCubicPairingFunctional L K w ≠ 0 ∨
      ∃ v : poleNeutralEvenSubspace L K, v ≠ 0 ∧
        poleNeutralEvenCompressedCanonical L K v = (lam : ℂ) • v ∧
          v = (poleNeutralIndexLinearMap hL K).adjoint w := by
  by_cases hp : poleNeutralCubicPairingFunctional L K w = 0
  · right
    refine ⟨(poleNeutralIndexLinearMap hL K).adjoint w, ?_, ?_, rfl⟩
    · intro hz
      apply hw0
      apply (poleNeutralIndexAdjointEquiv hL K hK).injective
      simpa only [map_zero] using hz
    · have hc := poleNeutral_odd_eigen_adjoint_competitor_eq_source hL K hK lam w hw
      rw [hp, neg_zero, zero_smul] at hc
      exact sub_eq_zero.mp hc
  · exact Or.inl hp

theorem poleNeutral_odd_adjoint_shifted_rankOneIntertwining {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) :
    RankOneIntertwining (poleNeutralOddShiftedCanonical L K lam)
      (poleNeutralEvenShiftedCanonical L K lam) (poleNeutralIndexAdjointEquiv hL K hK)
      (-poleNeutralCorrectedCubicRieszVector L K) (poleNeutralCubicPairingFunctional L K) := by
  have hzero : RankOneIntertwining (poleNeutralOddCompressedCanonical L K)
      (poleNeutralEvenCompressedCanonical L K) (poleNeutralIndexAdjointEquiv hL K hK)
      (-poleNeutralCorrectedCubicRieszVector L K) (poleNeutralCubicPairingFunctional L K) := by
    intro w
    have ha := poleNeutral_adjoint_rankOne_identity hL K hK w
    change poleNeutralEvenCompressedCanonical L K ((poleNeutralIndexLinearMap hL K).adjoint w) -
      (poleNeutralIndexLinearMap hL K).adjoint (poleNeutralOddCompressedCanonical L K w) = _
    rw [smul_neg, ← ha]
    abel
  exact hzero.shift (lam : ℂ)

/-- The actual odd adjoint ray includes the required minus sign. -/
def poleNeutralOddAdjointShiftedRay {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    poleNeutralOddSubspace L K :=
  secularResolventRay (poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam)
    (poleNeutralIndexAdjointEquiv hL K hK) (-poleNeutralCorrectedCubicRieszVector L K)

theorem poleNeutral_odd_eigenvector_eq_pairing_smul_adjointRay {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)
    (w : poleNeutralOddSubspace L K)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    w = poleNeutralCubicPairingFunctional L K w • poleNeutralOddAdjointShiftedRay hL K hK lam hlam := by
  exact eq_smul_secularResolventRay_of_apply_eq_zero
    (poleNeutral_odd_adjoint_shifted_rankOneIntertwining hL K hK lam) (fun _ => rfl)
    (by simp only [poleNeutralOddShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hw, sub_self])

theorem poleNeutral_odd_eigen_cubic_pairing_ne_zero_of_lt_even_bottom {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)
    (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    poleNeutralCubicPairingFunctional L K w ≠ 0 := by
  intro hp
  have hr := poleNeutral_odd_eigenvector_eq_pairing_smul_adjointRay hL K hK lam hlam w hw
  rw [hp, zero_smul] at hr
  exact hw0 hr

theorem poleNeutral_odd_eigen_adjointRay_pairing_eq_one {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)
    (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) = 1 := by
  have hp := poleNeutral_odd_eigen_cubic_pairing_ne_zero_of_lt_even_bottom hL K hK lam hlam w hw0 hw
  have hr := poleNeutral_odd_eigenvector_eq_pairing_smul_adjointRay hL K hK lam hlam w hw
  have hf := congrArg (poleNeutralCubicPairingFunctional L K) hr
  rw [map_smul, smul_eq_mul] at hf
  apply mul_left_cancel₀ hp
  simpa only [mul_one] using hf.symm

theorem poleNeutral_odd_adjoint_shifted_det_quotient {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    LinearMap.det (poleNeutralOddShiftedCanonical L K lam) /
      LinearMap.det (poleNeutralEvenShiftedCanonical L K lam) =
        1 - poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) :=
  det_div_det_eq_one_sub_secularResolventScalar
    (poleNeutral_odd_adjoint_shifted_rankOneIntertwining hL K hK lam) (fun _ => rfl)

/-- The actual strict-odd ground supplies the adjoint branch's nonzero source
pairing; the original corrected even source is not silently substituted. -/
theorem poleNeutral_strictOdd_ground_cubic_pairing_ne_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w =
      (poleNeutralOddRayleighBottom L K hL hK : ℂ) • w)
    (hstrict : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK) :
    poleNeutralCubicPairingFunctional L K w ≠ 0 :=
  poleNeutral_odd_eigen_cubic_pairing_ne_zero_of_lt_even_bottom hL K hK _ hstrict w hw0 hw

/-- Construct the strict-even packet from the actual native ground theorem
at its actual bottom, without importing a ground at a detector threshold. -/
theorem exists_poleNeutral_strictEven_ground_shifted_normalization {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hstrict : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :
    ∃ u : poleNeutralEvenSubspace L K, u ≠ 0 ∧
      poleNeutralEvenCompressedCanonical L K u = (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u ∧
      poleNeutralCorrectedCubicSource L K u ≠ 0 ∧
      u = poleNeutralCorrectedCubicSource L K u •
        poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hstrict ∧
      poleNeutralCorrectedCubicSource L K
        (poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hstrict) = 1 := by
  obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralEvenRayleighBottom hL K hK
  exact ⟨u, hu0, hu,
    poleNeutral_even_eigen_source_ne_zero_of_lt_odd_bottom hL K hK _ hstrict u hu0 hu,
    poleNeutral_even_eigenvector_eq_source_smul_shiftedRay hL K hK _ hstrict u hu,
    poleNeutral_even_eigen_shiftedRay_source_eq_one hL K hK _ hstrict u hu0 hu⟩

/-- Construct the strict-odd packet from the actual native odd ground, with
its actual adjoint source pairing and the same actual spectral bottom. -/
theorem exists_poleNeutral_strictOdd_ground_adjoint_normalization {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hstrict : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK) :
    ∃ w : poleNeutralOddSubspace L K, w ≠ 0 ∧
      poleNeutralOddCompressedCanonical L K w = (poleNeutralOddRayleighBottom L K hL hK : ℂ) • w ∧
      poleNeutralCubicPairingFunctional L K w ≠ 0 ∧
      w = poleNeutralCubicPairingFunctional L K w •
        poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) hstrict ∧
      poleNeutralCubicPairingFunctional L K
        (poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) hstrict) = 1 := by
  obtain ⟨w, hw0, hw⟩ := exists_eigenmode_at_poleNeutralOddRayleighBottom hL K hK
  exact ⟨w, hw0, hw,
    poleNeutral_odd_eigen_cubic_pairing_ne_zero_of_lt_even_bottom hL K hK _ hstrict w hw0 hw,
    poleNeutral_odd_eigenvector_eq_pairing_smul_adjointRay hL K hK _ hstrict w hw,
    poleNeutral_odd_eigen_adjointRay_pairing_eq_one hL K hK _ hstrict w hw0 hw⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.poleNeutralEvenRayleighBottom_mul_norm_sq_le
#print axioms Zeta23.CCM.poleNeutralEvenShiftedCanonicalEquiv
#print axioms Zeta23.CCM.poleNeutralOddShiftedCanonicalEquiv
#print axioms Zeta23.CCM.poleNeutral_even_eigen_source_ne_zero_of_lt_odd_bottom
#print axioms Zeta23.CCM.poleNeutral_even_eigen_shiftedRay_source_eq_one
#print axioms Zeta23.CCM.poleNeutral_even_shifted_det_quotient
#print axioms Zeta23.CCM.poleNeutral_adjoint_rankOne_identity
#print axioms Zeta23.CCM.poleNeutralIndexAdjointEquiv
#print axioms Zeta23.CCM.poleNeutral_odd_eigen_adjoint_competitor_eq_source
#print axioms Zeta23.CCM.poleNeutral_odd_eigen_adjoint_competitor_source_dichotomy
#print axioms Zeta23.CCM.poleNeutral_odd_eigen_cubic_pairing_ne_zero_of_lt_even_bottom
#print axioms Zeta23.CCM.poleNeutral_odd_eigen_adjointRay_pairing_eq_one
#print axioms Zeta23.CCM.poleNeutral_odd_adjoint_shifted_det_quotient
#print axioms Zeta23.CCM.poleNeutral_strictOdd_ground_cubic_pairing_ne_zero
#print axioms Zeta23.CCM.exists_poleNeutral_strictEven_ground_shifted_normalization
#print axioms Zeta23.CCM.exists_poleNeutral_strictOdd_ground_adjoint_normalization
