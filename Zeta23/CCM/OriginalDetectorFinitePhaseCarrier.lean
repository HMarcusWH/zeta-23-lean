import Zeta23.CCM.OriginalDetectorFinitePhasePlane

/-!
# Exact parity, pole equations and higher moments of the actual phase trials

The higher moments belong to the constructed trial vectors. They are not
constraints on a later Rayleigh minimizer or a selected ground.
-/

noncomputable section

open Set Complex Matrix
open scoped Topology ComplexConjugate

namespace Zeta23.CCM

/-- The actual finite `k=Pq` image has six zero endpoint moments because
the actual `q` image has eight. -/
theorem originalDetectorFinitePoleImageCoefficients_moment_zero_lt_six
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) {r : ℕ} (hr : r < 6) :
    centeredMoment (originalDetectorQuarticCutoff L) r
      (originalDetectorFinitePoleImageCoefficients s L c (by linarith)) = 0 := by
  have heq : centeredMoment (originalDetectorQuarticCutoff L) r
      (originalDetectorFinitePoleImageCoefficients s L c (by linarith)) =
      localizedBaseFrequency L ^ 2 * centeredMoment (originalDetectorQuarticCutoff L) (r + 2)
        (originalDetectorFiniteWindowImageCoefficients s L c (by linarith)) -
      (1 / 4 : ℂ) * centeredMoment (originalDetectorQuarticCutoff L) r
        (originalDetectorFiniteWindowImageCoefficients s L c (by linarith)) := by
    simp only [originalDetectorFinitePoleImageCoefficients, centeredMoment, localizedFrequency,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add]
    ring
  rw [heq, originalDetectorFiniteWindowImageCoefficients_moment_zero s c hL (by omega : r + 2 < 8),
    originalDetectorFiniteWindowImageCoefficients_moment_zero s c hL (by omega : r < 8)]
  ring

def originalDetectorFinitePhaseRaw (σ L c : ℝ) (hL : 0 < L) :
    Fin (2 * originalDetectorQuarticCutoff L + 1) → ℂ :=
  fun i => originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale L c hL i +
    (σ : ℂ) * originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale L c hL i.rev

theorem originalDetectorFinitePhaseVector_raw (σ L c : ℝ) (hL : 0 < L) :
    (EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
      (originalDetectorFinitePhaseVector σ L c hL) = originalDetectorFinitePhaseRaw σ L c hL := by
  ext i
  rfl

/-- All six higher zero moments survive both actual reflection phases. -/
theorem originalDetectorFinitePhaseRaw_moment_zero_lt_six
    (σ c : ℝ) {L : ℝ} (hL : 2 ≤ L) {r : ℕ} (hr : r < 6) :
    centeredMoment (originalDetectorQuarticCutoff L) r
      (originalDetectorFinitePhaseRaw σ L c (by linarith)) = 0 := by
  let u := originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale L c (by linarith)
  have heq : centeredMoment (originalDetectorQuarticCutoff L) r
      (originalDetectorFinitePhaseRaw σ L c (by linarith)) =
      centeredMoment (originalDetectorQuarticCutoff L) r u +
        (σ : ℂ) * centeredMoment (originalDetectorQuarticCutoff L) r
          (reverseCoefficients (originalDetectorQuarticCutoff L) u) := by
    simp only [centeredMoment, originalDetectorFinitePhaseRaw, reverseCoefficients,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [u]
    ring
  rw [heq, centeredMoment_reverseCoefficients,
    originalDetectorFinitePoleImageCoefficients_moment_zero_lt_six UniversalSinc.fixedScale c hL hr]
  simp only [mul_zero, add_zero]

theorem originalDetectorFinitePhaseRaw_boundaryFlat
    (σ c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    BoundaryFlatCoefficients (originalDetectorQuarticCutoff L)
      (originalDetectorFinitePhaseRaw σ L c (by linarith)) :=
  ⟨originalDetectorFinitePhaseRaw_moment_zero_lt_six σ c hL (by norm_num : 0 < 6),
    originalDetectorFinitePhaseRaw_moment_zero_lt_six σ c hL (by norm_num : 1 < 6),
    originalDetectorFinitePhaseRaw_moment_zero_lt_six σ c hL (by norm_num : 2 < 6)⟩

theorem originalDetectorFinitePhaseRaw_reversal
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (L c : ℝ) (hL : 0 < L) :
    reverseCoefficients (originalDetectorQuarticCutoff L) (originalDetectorFinitePhaseRaw σ L c hL) =
      (σ : ℂ) • originalDetectorFinitePhaseRaw σ L c hL := by
  ext i
  rcases hσ with rfl | rfl <;>
    simp [reverseCoefficients, originalDetectorFinitePhaseRaw, Fin.rev_rev] <;> ring

private theorem poleEvenFunctional_reversal (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    canonicalPoleEvenFunctional L N (WithLp.toLp 2 (reverseCoefficients N u)) =
      canonicalPoleEvenFunctional L N (WithLp.toLp 2 u) := by
  change (∑ i, poleEvenProfile L N i * u i.rev) = ∑ i, poleEvenProfile L N i * u i
  rw [← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z : ℂ => z * u i) (congrFun (reverseCoefficients_poleEvenProfile L N) i)

private theorem poleOddFunctional_reversal (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    canonicalPoleOddFunctional L N (WithLp.toLp 2 (reverseCoefficients N u)) =
      -canonicalPoleOddFunctional L N (WithLp.toLp 2 u) := by
  change (∑ i, poleOddProfile L N i * u i.rev) = -(∑ i, poleOddProfile L N i * u i)
  rw [← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hrev := congrFun (reverseCoefficients_poleOddProfile L N) i
  change poleOddProfile L N i.rev = -poleOddProfile L N i at hrev
  rw [hrev]
  ring

/-- Both unchanged native pole equations hold on every actual plane
phase, without passing pole equations as producer premises. -/
theorem originalDetectorFinitePhaseVector_native_poles_zero
    (σ c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    canonicalPoleEvenFunctional L (originalDetectorQuarticCutoff L)
      (originalDetectorFinitePhaseVector σ L c (by linarith)) = 0 ∧
    canonicalPoleOddFunctional L (originalDetectorQuarticCutoff L)
      (originalDetectorFinitePhaseVector σ L c (by linarith)) = 0 := by
  have hp := originalDetectorFinitePoleImageCoefficients_native_poles_zero UniversalSinc.fixedScale c hL
  unfold originalDetectorFinitePhaseVector originalDetectorFinitePhaseLeft originalDetectorFinitePhaseRight
  simp only [map_add, map_smul]
  rw [poleEvenFunctional_reversal, poleOddFunctional_reversal, hp.1, hp.2]
  simp

def originalDetectorFiniteEvenPhase (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L) := by
  let p := originalDetectorFinitePhaseVector 1 L c (by linarith)
  have hraw := originalDetectorFinitePhaseVector_raw 1 L c (by linarith)
  have hlegal : p ∈ euclideanEvenBoundaryFlatSubspace (originalDetectorQuarticCutoff L) := by
    apply (mem_euclideanEvenBoundaryFlatSubspace_iff _ _).mpr
    rw [hraw]
    constructor
    · exact (mem_boundaryFlatSubspace_iff _ _).mpr (originalDetectorFinitePhaseRaw_boundaryFlat 1 c hL)
    · apply (mem_evenCoefficientSubspace_iff _ _).mpr
      simpa using originalDetectorFinitePhaseRaw_reversal (Or.inl rfl) L c (by linarith)
  exact ⟨⟨p, hlegal⟩, (mem_poleNeutralEvenSubspace _ _ _).mpr
    (originalDetectorFinitePhaseVector_native_poles_zero 1 c hL).1⟩

def originalDetectorFiniteOddPhase (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    poleNeutralOddSubspace L (originalDetectorQuarticCutoff L) := by
  let p := originalDetectorFinitePhaseVector (-1) L c (by linarith)
  have hraw := originalDetectorFinitePhaseVector_raw (-1) L c (by linarith)
  have hlegal : p ∈ euclideanOddBoundaryFlatSubspace (originalDetectorQuarticCutoff L) := by
    apply (mem_euclideanOddBoundaryFlatSubspace_iff _ _).mpr
    rw [hraw]
    constructor
    · exact (mem_boundaryFlatSubspace_iff _ _).mpr (originalDetectorFinitePhaseRaw_boundaryFlat (-1) c hL)
    · apply (mem_oddCoefficientSubspace_iff _ _).mpr
      simpa using originalDetectorFinitePhaseRaw_reversal (Or.inr rfl) L c (by linarith)
  exact ⟨⟨p, hlegal⟩, (mem_poleNeutralOddSubspace _ _ _).mpr
    (originalDetectorFinitePhaseVector_native_poles_zero (-1) c hL).2⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorFinitePoleImageCoefficients_moment_zero_lt_six
#print axioms Zeta23.CCM.originalDetectorFinitePhaseRaw_moment_zero_lt_six
#print axioms Zeta23.CCM.originalDetectorFinitePhaseRaw_reversal
#print axioms Zeta23.CCM.originalDetectorFinitePhaseVector_native_poles_zero
#print axioms Zeta23.CCM.originalDetectorFiniteEvenPhase
#print axioms Zeta23.CCM.originalDetectorFiniteOddPhase
