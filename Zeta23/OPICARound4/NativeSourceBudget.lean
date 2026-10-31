import Zeta23.OPICARound4.SourceDiscrepancy
import Zeta23.OPICARound4.NativeWitnessCosts
import Zeta23.OPICARound4.OperatorSignedBound
import Zeta23.CCM.SourceContractionLocalized
import Mathlib.Analysis.InnerProductSpace.Rayleigh

noncomputable section
namespace Zeta23.OPICARound4
open CCM Matrix
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- The complete physical atom, with no entrywise or dimension estimate. -/
def nativeSourceAtom (K : ℕ) (ω : ℝ) :=
  (sourceMatrix ω K).toEuclideanLin.toContinuousLinearMap

theorem nativeSourceAtom_symmetric (K : ℕ) (ω : ℝ) :
    (nativeSourceAtom K ω).IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext i j
  change conj (sourceEntry ω (centeredIndex K j) (centeredIndex K i)) =
    sourceEntry ω (centeredIndex K i) (centeredIndex K j)
  rw [sourceEntry_eq_ofReal, Complex.conj_ofReal, ← sourceEntry_eq_ofReal,
    sourceEntry_symmetric]

/-- Uniform operator cost two, obtained from the proved quadratic contraction.
It has no factor depending on the Fourier cutoff. -/
theorem nativeSourceAtom_norm_le_two (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) : ‖nativeSourceAtom K ω‖ ≤ 2 := by
  rw [(nativeSourceAtom K ω).norm_eq_iSup_rayleighQuotient
    (nativeSourceAtom_symmetric K ω)]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have h := sourceContractionBound_proved K ω hω0 hω1 x
  rw [matrixRealEnergy_eq_re_inner_apply_self] at h
  change |(inner ℂ ((nativeSourceAtom K ω) x) x).re / ‖x‖ ^ 2| ≤ 2
  rw [abs_div, abs_sq]
  exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr h

theorem nativeSourceAtom_apply_norm (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖(sourceMatrix ω K).toEuclideanLin x‖ ≤ 2 * ‖x‖ :=
  ((nativeSourceAtom K ω).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (nativeSourceAtom_norm_le_two K hω0 hω1) (norm_nonneg _))

theorem native_source_mixed_norm (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖sourceAtomPairing K h u ω‖ ≤ 2 * ‖h‖ * ‖u‖ := by
  rw [sourceAtomPairing_eq_physical_inner]
  exact (norm_inner_le_norm _ _).trans (by
    nlinarith [nativeSourceAtom_apply_norm K hω0 hω1 u, norm_nonneg h])

theorem primeSourceCoordinate_mem_unit {L : ℝ} (hL : 0 < L) {q : ℕ}
    (hq : q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊) :
    0 ≤ primeSourceCoordinate q L ∧ primeSourceCoordinate q L ≤ 1 := by
  have hq' := Finset.mem_Icc.mp hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqe : (q : ℝ) ≤ Real.exp L := (Nat.le_floor_iff (Real.exp_pos _).le).mp hq'.2
  have hl : Real.log q ≤ L := by
    rw [← Real.log_exp L]
    exact Real.log_le_log hq0 hqe
  unfold primeSourceCoordinate
  constructor
  · exact sub_nonneg.mpr ((div_le_one hL).mpr hl)
  · exact sub_le_self _ (div_nonneg (Real.log_natCast_nonneg q) hL.le)

/-- Absolute mass includes every von-Mangoldt prime power. -/
def nativePrimeMass (L : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, ‖primeSourceWeight q‖

theorem native_prime_row_budget {L : ℝ} (hL : 0 < L) (K : ℕ)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖inner ℂ h ((canonicalPrimeMatrix L K).toEuclideanLin u)‖ ≤
      2 * nativePrimeMass L * ‖h‖ * ‖u‖ := by
  rw [canonicalPrimeMatrix_eq_sum_sourceMatrix]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    inner_sum, inner_smul_right]
  calc
    _ ≤ ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        ‖primeSourceWeight q * inner ℂ h
          ((sourceMatrix (primeSourceCoordinate q L) K).toEuclideanLin u)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        ‖primeSourceWeight q‖ * (2 * ‖h‖ * ‖u‖) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      obtain ⟨h0, h1⟩ := primeSourceCoordinate_mem_unit hL hq
      exact mul_le_mul_of_nonneg_left
        (by simpa [sourceAtomPairing_eq_physical_inner] using native_source_mixed_norm K h0 h1 h u)
        (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold nativePrimeMass; ring

/-- The row cost retains the complete Archimedean operator and the actual
projection-corrected normal. Arithmetic cancellation is not assumed. -/
def nativeCompleteRowBudget (L : ℝ) (K : ℕ) : ℝ :=
  ‖correctedSourceRow L K‖ *
    (‖(canonicalArchMatrix L K).toEuclideanLin.toContinuousLinearMap‖ + 2 * nativePrimeMass L)

theorem nativeCompleteRowBudget_nonneg (L : ℝ) (K : ℕ) :
    0 ≤ nativeCompleteRowBudget L K := by
  unfold nativeCompleteRowBudget nativePrimeMass
  positivity

theorem native_complete_row_budget {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : poleNeutralEvenSubspace L K) :
    ‖poleNeutralCorrectedCubicSource L K u‖ ≤ nativeCompleteRowBudget L K * ‖u‖ := by
  rw [correctedSourceRow_pole_cancelled hL K hK]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  have hp := native_prime_row_budget hL K (correctedSourceRow L K)
    (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))
  have ha := (norm_inner_le_norm (𝕜 := ℂ) (correctedSourceRow L K)
    ((canonicalArchMatrix L K).toEuclideanLin (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))).trans
    (mul_le_mul_of_nonneg_left
      ((canonicalArchMatrix L K).toEuclideanLin.toContinuousLinearMap.le_opNorm _) (norm_nonneg _))
  change _ ≤ nativeCompleteRowBudget L K * ‖(u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))‖
  unfold nativeCompleteRowBudget
  nlinarith

/-- The actual native Riesz vector has the same dimension-free row budget. -/
theorem native_corrected_riesz_budget {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K) :
    ‖poleNeutralCorrectedCubicRieszVector L K‖ ≤ nativeCompleteRowBudget L K := by
  let f := poleNeutralCorrectedCubicRieszVector L K
  have h := native_complete_row_budget hL K hK f
  rw [← inner_poleNeutralCorrectedCubicRieszVector] at h
  change ‖inner ℂ f f‖ ≤ nativeCompleteRowBudget L K * ‖f‖ at h
  rw [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  rw [abs_of_nonneg (sq_nonneg _)] at h
  change ‖f‖ ≤ nativeCompleteRowBudget L K
  by_cases hf : ‖f‖ = 0
  · simpa [f, hf] using nativeCompleteRowBudget_nonneg L K
  · have hf0 : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hf)
    nlinarith

/-- The inverse-adjoint pays the same native cost two. This follows by duality
from the actual inverse-index estimate; no unitary identification is used. -/
theorem native_inverse_adjoint_cost {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (f : poleNeutralEvenSubspace L K) :
    ‖nativeIndexInverseAdjoint hL K hK f‖ ≤ 2 * ‖f‖ := by
  let z := nativeIndexInverseAdjoint hL K hK f
  have he : inner ℂ z z = inner ℂ f
      ((poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm z) := by
    dsimp only [z, nativeIndexInverseAdjoint]
    rw [LinearMap.adjoint_inner_left]
    rfl
  have hi := norm_inner_le_norm (𝕜 := ℂ) f
    ((poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm z)
  have hz := native_index_inverse_cost hL K (show 1 ≤ K by omega) z
  rw [← he, inner_self_eq_norm_sq_to_K] at hi
  norm_cast at hi
  rw [abs_of_nonneg (sq_nonneg _)] at hi
  change ‖z‖ ≤ 2 * ‖f‖
  by_cases h0 : ‖z‖ = 0
  · rw [h0]; positivity
  · have hp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hmul := mul_le_mul_of_nonneg_left hz (norm_nonneg f)
    nlinarith

/-- Dimension-free even signed budget retains the exact trace displacement.
The unsigned row estimate is used only for the norm term. -/
theorem native_even_complete_signed_budget {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    (poleNeutralOddRayleighBottom L K hL hK - lam) *
      (poleNeutralCorrectedCubicSource L K (poleNeutralEvenShiftedRay hL K hK lam hlam)).re ≤
      (2 * nativeCompleteRowBudget L K * ‖poleNeutralCubicCompressionVector L K‖ +
        (LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K)).re) / 2 := by
  have h := native_even_signed_upper hL K hK lam hlam
  have hc := (native_inverse_adjoint_cost hL K hK
    (poleNeutralCorrectedCubicRieszVector L K)).trans
      (mul_le_mul_of_nonneg_left (native_corrected_riesz_budget hL K (by omega)) (by norm_num))
  have hp := mul_le_mul_of_nonneg_right hc (norm_nonneg (poleNeutralCubicCompressionVector L K))
  linarith

/-- The opposite orientation keeps its actual D⁻¹ input and the reversed
signed trace displacement. -/
theorem native_odd_complete_signed_budget {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    (poleNeutralEvenRayleighBottom L K hL hK - lam) *
      (poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam)).re ≤
      (2 * ‖poleNeutralCubicCompressionVector L K‖ * nativeCompleteRowBudget L K +
        (LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K)).re) / 2 := by
  have h := native_odd_signed_upper hL K hK lam hlam
  have hc := native_index_inverse_cost hL K (show 1 ≤ K by omega)
    (poleNeutralCubicCompressionVector L K)
  have hp := mul_le_mul hc (native_corrected_riesz_budget hL K (by omega))
    (norm_nonneg (poleNeutralCorrectedCubicRieszVector L K))
    (by positivity : 0 ≤ 2 * ‖poleNeutralCubicCompressionVector L K‖)
  linarith

end Zeta23.OPICARound4
