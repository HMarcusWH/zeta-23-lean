import Zeta23.OPICARound4.SourceExchangeConcentration
import Zeta23.OPICARound4.OddReciprocalSource

noncomputable section
namespace Zeta23.OPICARound4
open CCM Matrix
open scoped BigOperators

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- A source-specific finite prime-power concentration budget. The actual
left row and input are retained separately in every mixed atom. -/
def nativePrimeConcentrationBudget (L : ℝ) (K : ℕ)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    ‖primeSourceWeight q‖ * Real.sqrt
      (sourceConcentration K (primeSourceCoordinate q L) h *
        sourceConcentration K (primeSourceCoordinate q L) u)

theorem native_prime_concentration_budget {L : ℝ} (hL : 0 < L) (K : ℕ)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖inner ℂ h ((canonicalPrimeMatrix L K).toEuclideanLin u)‖ ≤
      nativePrimeConcentrationBudget L K h u := by
  rw [canonicalPrimeMatrix_eq_sum_sourceMatrix]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    inner_sum, inner_smul_right]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro q hq
  rw [norm_mul]
  obtain ⟨h0, h1⟩ := primeSourceCoordinate_mem_unit hL hq
  exact mul_le_mul_of_nonneg_left
    (by simpa [sourceAtomPairing_eq_physical_inner] using
      native_source_mixed_concentration_bound K h0 h1 h u) (norm_nonneg _)

/-- The source coordinate is complementary to log q/L. The half-aperture
estimate therefore applies to the late logarithmic prime-power regime. -/
theorem native_prime_half_coordinate_iff {L : ℝ} (hL : 0 < L) (q : ℕ) :
    primeSourceCoordinate q L ≤ 1 / 2 ↔ L / 2 ≤ Real.log q := by
  unfold primeSourceCoordinate
  constructor
  · intro h
    have hd : (1 / 2 : ℝ) ≤ Real.log q / L := by linarith
    have := (le_div_iff₀ hL).mp hd
    linarith
  · intro h
    have hd : (1 / 2 : ℝ) ≤ Real.log q / L := (le_div_iff₀ hL).mpr (by linarith)
    linarith

def nativeLatePrimePowers (L : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Real.exp L⌋₊).filter fun q => L / 2 ≤ Real.log q

def nativeOldPrimePowers (L : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Real.exp L⌋₊).filter fun q => ¬ L / 2 ≤ Real.log q

/-- Exact partition of all von-Mangoldt source atoms, including prime powers
of exponent greater than one. Nothing is silently restricted to primes. -/
theorem native_prime_power_regime_partition (L : ℝ) {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) :
    (∑ q ∈ nativeLatePrimePowers L, f q) + (∑ q ∈ nativeOldPrimePowers L, f q) =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, f q := by
  exact Finset.sum_filter_add_sum_filter_not _ _ _

theorem native_late_prime_concentration {L : ℝ} (hL : 0 < L) (K : ℕ)
    {q : ℕ} (hq : q ∈ nativeLatePrimePowers L)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceConcentration K (primeSourceCoordinate q L) u ≤ ‖u‖ ^ 2 := by
  obtain ⟨hq, hlate⟩ := Finset.mem_filter.mp hq
  exact sourceConcentration_le_norm_sq_of_half K
    (primeSourceCoordinate_mem_unit hL hq).1 ((native_prime_half_coordinate_iff hL q).mpr hlate) u

theorem native_old_prime_concentration {L : ℝ} (hL : 0 < L) (K : ℕ)
    {q : ℕ} (hq : q ∈ nativeOldPrimePowers L)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceConcentration K (primeSourceCoordinate q L) u ≤ 2 * ‖u‖ ^ 2 := by
  obtain ⟨hq, _⟩ := Finset.mem_filter.mp hq
  obtain ⟨h0, h1⟩ := primeSourceCoordinate_mem_unit hL hq
  exact sourceConcentration_le_two_norm_sq K h0 h1 u

/-- The late prime-power atoms have the stronger mixed cost one. -/
theorem native_late_mixed_concentration_cost {L : ℝ} (hL : 0 < L) (K : ℕ)
    {q : ℕ} (hq : q ∈ nativeLatePrimePowers L)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    Real.sqrt (sourceConcentration K (primeSourceCoordinate q L) h *
      sourceConcentration K (primeSourceCoordinate q L) u) ≤ ‖h‖ * ‖u‖ := by
  have h0 := (primeSourceCoordinate_mem_unit hL (Finset.mem_filter.mp hq).1).1
  have hh := native_late_prime_concentration hL K hq h
  have hu := native_late_prime_concentration hL K hq u
  have hp := mul_le_mul hh hu (sourceConcentration_nonneg K h0 u) (sq_nonneg ‖h‖)
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, by nlinarith⟩

/-- Older atoms retain the full-range factor two; no overlap is discarded. -/
theorem native_old_mixed_concentration_cost {L : ℝ} (hL : 0 < L) (K : ℕ)
    {q : ℕ} (hq : q ∈ nativeOldPrimePowers L)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    Real.sqrt (sourceConcentration K (primeSourceCoordinate q L) h *
      sourceConcentration K (primeSourceCoordinate q L) u) ≤ 2 * ‖h‖ * ‖u‖ := by
  have h0 := (primeSourceCoordinate_mem_unit hL (Finset.mem_filter.mp hq).1).1
  have hh := native_old_prime_concentration hL K hq h
  have hu := native_old_prime_concentration hL K hq u
  have hp := mul_le_mul hh hu (sourceConcentration_nonneg K h0 u)
    (by positivity : 0 ≤ 2 * ‖h‖ ^ 2)
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, by nlinarith⟩

/-- A proved fallback separates late cost one from old cost two, uniformly in
the Fourier cutoff. Further gain for the selected source remains OPEN. -/
theorem native_prime_concentration_budget_regime_fallback {L : ℝ} (hL : 0 < L)
    (K : ℕ) (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    nativePrimeConcentrationBudget L K h u ≤
      ((∑ q ∈ nativeLatePrimePowers L, ‖primeSourceWeight q‖) +
        2 * ∑ q ∈ nativeOldPrimePowers L, ‖primeSourceWeight q‖) * ‖h‖ * ‖u‖ := by
  let f : ℕ → ℝ := fun q => ‖primeSourceWeight q‖ * Real.sqrt
    (sourceConcentration K (primeSourceCoordinate q L) h *
      sourceConcentration K (primeSourceCoordinate q L) u)
  change (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, f q) ≤ _
  rw [← native_prime_power_regime_partition L f]
  have hl : (∑ q ∈ nativeLatePrimePowers L, f q) ≤
      (∑ q ∈ nativeLatePrimePowers L, ‖primeSourceWeight q‖) * (‖h‖ * ‖u‖) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left
      (native_late_mixed_concentration_cost hL K hq h u) (norm_nonneg _)
  have ho : (∑ q ∈ nativeOldPrimePowers L, f q) ≤
      (∑ q ∈ nativeOldPrimePowers L, ‖primeSourceWeight q‖) * (2 * ‖h‖ * ‖u‖) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left
      (native_old_mixed_concentration_cost hL K hq h u) (norm_nonneg _)
  nlinarith

/-- Complete corrected native row with the sharper atom-by-atom budget.
An improvement for the actual selected source is a separate arithmetic question. -/
theorem native_complete_concentration_budget {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : poleNeutralEvenSubspace L K) :
    ‖poleNeutralCorrectedCubicSource L K u‖ ≤
      ‖inner ℂ (correctedSourceRow L K)
        ((canonicalArchMatrix L K).toEuclideanLin
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))‖ +
        nativePrimeConcentrationBudget L K (correctedSourceRow L K)
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
  let A : ℂ := inner ℂ (correctedSourceRow L K)
    ((canonicalArchMatrix L K).toEuclideanLin
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
  let P : ℂ := inner ℂ (correctedSourceRow L K)
    ((canonicalPrimeMatrix L K).toEuclideanLin
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
  have he : poleNeutralCorrectedCubicSource L K u = -A - P :=
    correctedSourceRow_pole_cancelled hL K hK u
  have hp : ‖P‖ ≤ nativePrimeConcentrationBudget L K (correctedSourceRow L K)
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) := native_prime_concentration_budget hL K _ _
  change ‖poleNeutralCorrectedCubicSource L K u‖ ≤ ‖A‖ + _
  rw [he]
  have hs : ‖-A - P‖ ≤ ‖A‖ + ‖P‖ := by
    simpa only [norm_neg] using norm_sub_le (-A) P
  exact hs.trans (by linarith only [hp])

/-- The primary real interval retains the signed arch contribution exactly.
Taking its absolute value would discard cancellation already in the source. -/
theorem native_corrected_source_concentration_real_interval {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : poleNeutralEvenSubspace L K) :
    (-inner ℂ (correctedSourceRow L K)
      ((canonicalArchMatrix L K).toEuclideanLin
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))).re -
      nativePrimeConcentrationBudget L K (correctedSourceRow L K)
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) ≤
        (poleNeutralCorrectedCubicSource L K u).re ∧
    (poleNeutralCorrectedCubicSource L K u).re ≤
      (-inner ℂ (correctedSourceRow L K)
        ((canonicalArchMatrix L K).toEuclideanLin
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))).re +
        nativePrimeConcentrationBudget L K (correctedSourceRow L K)
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
  have hp := native_prime_concentration_budget hL K (correctedSourceRow L K)
    (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))
  have hr := abs_le.mp ((Complex.abs_re_le_norm
    (inner ℂ (correctedSourceRow L K) ((canonicalPrimeMatrix L K).toEuclideanLin
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))))).trans hp)
  simp only [correctedSourceRow_pole_cancelled hL K hK, Complex.sub_re]
  constructor <;> linarith [hr.1, hr.2]

/-- The actual odd response reverses the source sign and conjugates it. Its
primary one-sided interval therefore retains positive Re Arch(v). -/
theorem native_odd_concentration_real_interval {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    let v := nativeOddReciprocalInput hL K hK lam hlam
    (inner ℂ (correctedSourceRow L K)
      ((canonicalArchMatrix L K).toEuclideanLin
        (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))))).re -
      nativePrimeConcentrationBudget L K (correctedSourceRow L K)
        (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))) ≤
        (poleNeutralCubicPairingFunctional L K
          (poleNeutralOddAdjointShiftedRay hL K hK lam hlam)).re ∧
    (poleNeutralCubicPairingFunctional L K
      (poleNeutralOddAdjointShiftedRay hL K hK lam hlam)).re ≤
      (inner ℂ (correctedSourceRow L K)
        ((canonicalArchMatrix L K).toEuclideanLin
          (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))))).re +
        nativePrimeConcentrationBudget L K (correctedSourceRow L K)
          (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
  dsimp only
  have hf := native_corrected_source_concentration_real_interval hL K (show 2 ≤ K by omega)
    (nativeOddReciprocalInput hL K hK lam hlam)
  simp only [Complex.neg_re] at hf
  simp only [native_odd_response_eq_reciprocal_source hL K hK,
    Complex.neg_re, Complex.conj_re]
  constructor <;> linarith [hf.1, hf.2]

end Zeta23.OPICARound4
