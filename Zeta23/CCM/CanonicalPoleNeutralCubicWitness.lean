import Zeta23.CCM.CanonicalPoleNeutralNormals

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
An actual native pole-neutral carrier with a nonzero fourth moment.

The two input stencils already exist in `SourceSignCountermodels`. This
construction uses their exact native pole pairings to cancel the pole
functional. It makes no spectral or energy-sign claim about the canonical
matrix. The projected cubic channel is thereby nonzero for `K ≥ 3`.
-/

theorem evenSixthMomentWitness_even :
    evenSixthMomentWitness ∈ evenCoefficientSubspace 3 := by
  rw [mem_evenCoefficientSubspace_iff]
  funext i
  fin_cases i <;> rfl

theorem evenSixthMomentWitness_mem :
    evenSixthMomentWitness ∈ evenBoundaryFlatSubspace 3 := by
  obtain ⟨h0, h1, h2, -, -, -, -⟩ := evenSixthMomentWitness_moments
  exact ⟨(mem_boundaryFlatSubspace_iff 3 _).mpr ⟨h0, h1, h2⟩,
    evenSixthMomentWitness_even⟩

/-- Exact native even pole pairing of the existing sixth-moment stencil. -/
theorem poleEvenProfile_dot_evenSixthMomentWitness {L : ℝ} (hL : 0 < L) :
    poleEvenProfile L 3 ⬝ᵥ evenSixthMomentWitness =
      ((-2949120 * Real.pi ^ 6 /
        (L * (L ^ 2 + 16 * Real.pi ^ 2) * (L ^ 2 + 64 * Real.pi ^ 2) *
          (L ^ 2 + 144 * Real.pi ^ 2)) : ℝ) : ℂ) := by
  have hL0 : L ≠ 0 := hL.ne'
  have h16 : L ^ 2 + 16 * Real.pi ^ 2 ≠ 0 := by positivity
  have h64 : L ^ 2 + 64 * Real.pi ^ 2 ≠ 0 := by positivity
  have h144 : L ^ 2 + 144 * Real.pi ^ 2 ≠ 0 := by positivity
  have hr : 2 * (L / (L ^ 2 + 144 * Real.pi ^ 2)) -
      12 * (L / (L ^ 2 + 64 * Real.pi ^ 2)) +
        30 * (L / (L ^ 2 + 16 * Real.pi ^ 2)) - 20 * (L / L ^ 2) =
      -2949120 * Real.pi ^ 6 /
        (L * (L ^ 2 + 16 * Real.pi ^ 2) * (L ^ 2 + 64 * Real.pi ^ 2) *
          (L ^ 2 + 144 * Real.pi ^ 2)) := by
    field_simp [hL0, h16, h64, h144]
    ring
  have hm3 : poleProfileDenominator (-3) L = L ^ 2 + 144 * Real.pi ^ 2 := by
    unfold poleProfileDenominator
    norm_num
    ring
  have hm2 : poleProfileDenominator (-2) L = L ^ 2 + 64 * Real.pi ^ 2 := by
    unfold poleProfileDenominator
    norm_num
    ring
  have hm1 : poleProfileDenominator (-1) L = L ^ 2 + 16 * Real.pi ^ 2 := by
    simp [poleProfileDenominator]
  have h0 : poleProfileDenominator 0 L = L ^ 2 := by simp [poleProfileDenominator]
  have hp1 : poleProfileDenominator 1 L = L ^ 2 + 16 * Real.pi ^ 2 := by
    simp [poleProfileDenominator]
  have hp2 : poleProfileDenominator 2 L = L ^ 2 + 64 * Real.pi ^ 2 := by
    unfold poleProfileDenominator
    norm_num
    ring
  have hp3 : poleProfileDenominator 3 L = L ^ 2 + 144 * Real.pi ^ 2 := by
    unfold poleProfileDenominator
    norm_num
    ring
  have he : poleEvenProfile L 3 ⬝ᵥ evenSixthMomentWitness =
      ((2 * (L / (L ^ 2 + 144 * Real.pi ^ 2)) -
        12 * (L / (L ^ 2 + 64 * Real.pi ^ 2)) +
          30 * (L / (L ^ 2 + 16 * Real.pi ^ 2)) - 20 * (L / L ^ 2) : ℝ) : ℂ) := by
    simp [dotProduct, Fin.sum_univ_succ, evenSixthMomentWitness,
      poleEvenProfile, poleEvenProfileReal, centeredIndex, hm3, hm2, hm1, h0, hp1, hp2, hp3]
    push_cast
    ring
  rw [he, hr]

theorem poleEvenProfile_dot_evenSixthMomentWitness_re_neg {L : ℝ} (hL : 0 < L) :
    (poleEvenProfile L 3 ⬝ᵥ evenSixthMomentWitness).re < 0 := by
  rw [poleEvenProfile_dot_evenSixthMomentWitness hL]
  simp only [Complex.ofReal_re]
  apply div_neg_of_neg_of_pos
  · have hpi : 0 < Real.pi ^ 6 := pow_pos Real.pi_pos 6
    linarith
  · positivity

def canonicalPoleEvenSixthMomentWitness (K : ℕ) (hK : 3 ≤ K) :
    euclideanEvenBoundaryFlatSubspace K :=
  ⟨WithLp.toLp 2 (centeredZeroExtend hK evenSixthMomentWitness), by
    rw [mem_euclideanEvenBoundaryFlatSubspace_iff]
    change centeredZeroExtend hK evenSixthMomentWitness ∈ evenBoundaryFlatSubspace K
    exact centeredZeroExtend_mem_evenBoundaryFlatSubspace hK evenSixthMomentWitness_mem⟩

theorem canonicalPoleEvenSixthMomentWitness_functional {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) :
    legalCanonicalPoleEvenFunctional L K (canonicalPoleEvenSixthMomentWitness K hK) ≠ 0 := by
  have he : legalCanonicalPoleEvenFunctional L K (canonicalPoleEvenSixthMomentWitness K hK) =
      poleEvenProfile L 3 ⬝ᵥ evenSixthMomentWitness := by
    change poleEvenProfile L K ⬝ᵥ centeredZeroExtend hK evenSixthMomentWitness = _
    exact poleEvenProfile_dot_centeredZeroExtend L hK evenSixthMomentWitness
  rw [he]
  intro hz
  have hn := poleEvenProfile_dot_evenSixthMomentWitness_re_neg hL
  rw [hz, Complex.zero_re] at hn
  exact (lt_irrefl 0) hn

/-- Cancel the exact native pole functional between the two legal stencils. -/
def poleNeutralMomentFourWitness (L : ℝ) (K : ℕ) (hK : 3 ≤ K) :
    poleNeutralEvenSubspace L K :=
  let A := canonicalPoleEvenNonzeroWitness K (show 2 ≤ K by omega)
  let C := canonicalPoleEvenSixthMomentWitness K hK
  ⟨legalCanonicalPoleEvenFunctional L K C • A - legalCanonicalPoleEvenFunctional L K A • C, by
    rw [mem_poleNeutralEvenSubspace]
    change legalCanonicalPoleEvenFunctional L K
      (legalCanonicalPoleEvenFunctional L K C • A - legalCanonicalPoleEvenFunctional L K A • C) = 0
    rw [map_sub, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring⟩

theorem poleNeutralMomentFourWitness_momentFour (L : ℝ) (K : ℕ) (hK : 3 ≤ K) :
    centeredMoment K 4 (evenBoundaryFlatRawCoefficients K
      (poleNeutralMomentFourWitness L K hK).val) =
      24 * legalCanonicalPoleEvenFunctional L K (canonicalPoleEvenSixthMomentWitness K hK) := by
  change centeredMomentLinearMap K 4
    (legalCanonicalPoleEvenFunctional L K (canonicalPoleEvenSixthMomentWitness K hK) •
        centeredZeroExtend (show 2 ≤ K by omega) positiveEvenSourceWitness -
      legalCanonicalPoleEvenFunctional L K (canonicalPoleEvenNonzeroWitness K (by omega)) •
        centeredZeroExtend hK evenSixthMomentWitness) = _
  rw [map_sub, map_smul, map_smul]
  change _ * centeredMoment K 4 (centeredZeroExtend (show 2 ≤ K by omega)
      positiveEvenSourceWitness) -
    _ * centeredMoment K 4 (centeredZeroExtend hK evenSixthMomentWitness) = _
  rw [centeredMoment_centeredZeroExtend, centeredMoment_centeredZeroExtend,
    positiveEvenSourceWitness_moments.2.2.2.2,
    evenSixthMomentWitness_moments.2.2.2.2.1]
  ring

theorem poleNeutralMomentFourWitness_momentFour_ne_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) :
    centeredMoment K 4 (evenBoundaryFlatRawCoefficients K
      (poleNeutralMomentFourWitness L K hK).val) ≠ 0 := by
  rw [poleNeutralMomentFourWitness_momentFour]
  exact mul_ne_zero (by norm_num) (canonicalPoleEvenSixthMomentWitness_functional hL K hK)

theorem poleNeutralCubicCompressionVector_ne_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) : poleNeutralCubicCompressionVector L K ≠ 0 := by
  intro hg
  have hp := poleNeutral_cubic_pairing_eq_momentFour hL K (poleNeutralMomentFourWitness L K hK)
  rw [hg] at hp
  erw [inner_zero_left (𝕜 := ℂ)] at hp
  exact poleNeutralMomentFourWitness_momentFour_ne_zero hL K hK hp.symm

end Zeta23.CCM

#print axioms Zeta23.CCM.poleEvenProfile_dot_evenSixthMomentWitness
#print axioms Zeta23.CCM.canonicalPoleEvenSixthMomentWitness_functional
#print axioms Zeta23.CCM.poleNeutralMomentFourWitness_momentFour
#print axioms Zeta23.CCM.poleNeutralMomentFourWitness_momentFour_ne_zero
#print axioms Zeta23.CCM.poleNeutralCubicCompressionVector_ne_zero
