import Zeta23.CCM.OriginalDetectorPaddedFinitePoleImage

/-! # Source-derived approximation errors for the actual finite `Pq` image -/

noncomputable section

open Set Complex
open scoped Topology

namespace Zeta23.CCM

/-- Pole killing commutes with every finite jet on actual smooth functions. -/
theorem padded_iteratedDeriv_poleKilled_infty {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (r : ℕ) (x : ℝ) :
    iteratedDeriv r (Zeta23.ExceptionalZero.poleKilled f) x =
      iteratedDeriv (r + 2) f x - (1 / 4 : ℂ) * iteratedDeriv r f x := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hr : (r : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)
  have hshift : iteratedDeriv (r + 2) f = iteratedDeriv r (deriv (deriv f)) := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
  unfold Zeta23.ExceptionalZero.poleKilled
  rw [iteratedDeriv_fun_sub ((hdd.of_le hr).contDiffAt)
    (((contDiff_const.mul hf).of_le hr).contDiffAt), iteratedDeriv_const_mul_field, hshift]

/-- The translated source entering the approximation is exactly the
unchanged physical original pole-killed test `k_s=Pq_s`. -/
theorem padded_poleKilled_originalDetectorLobe (s c : ℝ) :
    Zeta23.ExceptionalZero.poleKilled (originalDetectorLobe s c) =
      fun x => Zeta23.ExceptionalZero.originalSincTest s (x - c) := by
  funext x
  unfold Zeta23.ExceptionalZero.originalSincTest Zeta23.ExceptionalZero.poleKilled originalDetectorLobe
  have hshift : iteratedDeriv 2 (fun y => UniversalSinc.originalDensityComplex s (y - c)) x =
      iteratedDeriv 2 (UniversalSinc.originalDensityComplex s) (x - c) :=
    congrFun (iteratedDeriv_comp_sub_const 2 (UniversalSinc.originalDensityComplex s) c) x
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hshift
  rw [hshift]

/-- The explicit source-derived jet error after the same actual pole killer. -/
def originalDetectorPaddedFinitePoleImageJetBudget (s L : ℝ) (r : ℕ) : ℝ :=
  originalDetectorPaddedFiniteWindowImageJetBudget s L (r + 2) +
    (1 / 4 : ℝ) * originalDetectorPaddedFiniteWindowImageJetBudget s L r

/-- Genuine all-order approximation to the unchanged original `k_s`, in
the actual centered quartic output coordinates. -/
theorem originalDetectorPaddedFinitePoleImage_iteratedDeriv_error_le_budget
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (r : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖iteratedDeriv r (fun y => Zeta23.ExceptionalZero.originalSincTest s (y - c)) x -
      iteratedDeriv r (localizedFiniteFunction L (originalDetectorQuarticCutoff L)
        (originalDetectorPaddedFinitePoleImageCoefficients s L c (by linarith))) x‖ ≤
          originalDetectorPaddedFinitePoleImageJetBudget s L r := by
  have hLp : 0 < L := by linarith
  have hf := originalDetectorLobe_contDiff hs c
  have hp : ContDiff ℝ (⊤ : ℕ∞) (originalDetectorPaddedFiniteWindowImage s L c hLp) :=
    (originalDetectorPaddedFiniteWindow_contDiff L).mul
      (originalDetectorPaddedRawFourierPartialSum_contDiff s L c hLp)
  rw [← padded_poleKilled_originalDetectorLobe,
    localizedFiniteFunction_originalDetectorPaddedFinitePoleImageCoefficients s c hL,
    padded_iteratedDeriv_poleKilled_infty hf, padded_iteratedDeriv_poleKilled_infty hp]
  have heq :
      (iteratedDeriv (r + 2) (originalDetectorLobe s c) x -
          (1 / 4 : ℂ) * iteratedDeriv r (originalDetectorLobe s c) x) -
        (iteratedDeriv (r + 2) (originalDetectorPaddedFiniteWindowImage s L c hLp) x -
          (1 / 4 : ℂ) * iteratedDeriv r (originalDetectorPaddedFiniteWindowImage s L c hLp) x) =
      (iteratedDeriv (r + 2) (originalDetectorLobe s c) x -
          iteratedDeriv (r + 2) (originalDetectorPaddedFiniteWindowImage s L c hLp) x) -
        (1 / 4 : ℂ) * (iteratedDeriv r (originalDetectorLobe s c) x -
          iteratedDeriv r (originalDetectorPaddedFiniteWindowImage s L c hLp) x) := by ring
  rw [heq]
  refine (norm_sub_le _ _).trans ?_
  unfold originalDetectorPaddedFinitePoleImageJetBudget
  apply add_le_add
  · exact originalDetectorPaddedFiniteWindowImage_iteratedDeriv_error_le_budget hs hL hleft hright (r + 2) hx
  · rw [norm_mul]
    have hquarter : ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by norm_num
    rw [hquarter]
    exact mul_le_mul_of_nonneg_left
      (originalDetectorPaddedFiniteWindowImage_iteratedDeriv_error_le_budget hs hL hleft hright r hx)
      (by norm_num)

/-- The actual finite pole-killed output has the required global `C²`
hard extension in the unchanged localized finite space. -/
theorem originalDetectorPaddedFinitePoleImageCoefficients_hardWindow_contDiff
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ContDiff ℝ 2 (localizedFiniteVector L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFinitePoleImageCoefficients s L c (by linarith))) :=
  contDiff_localizedFiniteVector_of_boundaryFlat _ _ (by linarith)
    (originalDetectorPaddedFinitePoleImageCoefficients_boundaryFlat s c hL)

/-- The literal hard extension commutes with the actual pole killer on
legal input coefficients; both derivatives at the seams are paid by the
existing endpoint gluing theorem. -/
theorem padded_poleKilled_localizedFiniteVector_of_boundaryFlat
    {L : ℝ} (hL : 0 < L) (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hu : BoundaryFlatCoefficients N u) :
    Zeta23.ExceptionalZero.poleKilled (localizedFiniteVector L N u) =
      localizedFiniteVector L N
        (fun i => (localizedFrequency L (centeredIndex N i) ^ 2 - 1 / 4) * u i) := by
  have hf (x : ℝ) : HasDerivAt ((Icc (0 : ℝ) L).indicator (localizedFiniteFunction L N u))
      ((Icc (0 : ℝ) L).indicator (localizedFiniteFirstJet L N u) x) x :=
    hasDerivAt_indicator_Icc_of_endpoint_jets_zero hL
      (hasDerivAt_localizedFiniteFunction L N u)
      (localizedFiniteFunction_zero_of_boundaryFlat L N u hu)
      (localizedFiniteFunction_rightEndpoint_zero_of_boundaryFlat hL N u hu)
      (localizedFiniteFirstJet_zero_of_boundaryFlat L N u hu)
      (localizedFiniteFirstJet_rightEndpoint_zero_of_boundaryFlat hL N u hu)
  have hg (x : ℝ) : HasDerivAt ((Icc (0 : ℝ) L).indicator (localizedFiniteFirstJet L N u))
      ((Icc (0 : ℝ) L).indicator (localizedFiniteSecondJet L N u) x) x :=
    hasDerivAt_indicator_Icc_of_endpoint_jets_zero hL
      (hasDerivAt_localizedFiniteFirstJet L N u)
      (localizedFiniteFirstJet_zero_of_boundaryFlat L N u hu)
      (localizedFiniteFirstJet_rightEndpoint_zero_of_boundaryFlat hL N u hu)
      (localizedFiniteSecondJet_zero_of_boundaryFlat L N u hu)
      (localizedFiniteSecondJet_rightEndpoint_zero_of_boundaryFlat hL N u hu)
  unfold Zeta23.ExceptionalZero.poleKilled
  rw [localizedFiniteVector_eq_indicator, deriv_eq hf, deriv_eq hg]
  funext x
  rw [localizedFiniteVector_eq_indicator]
  by_cases hx : x ∈ Icc (0 : ℝ) L
  · simp only [Set.indicator_of_mem hx]
    unfold localizedFiniteSecondJet localizedFiniteFunction
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp only [Set.indicator_of_notMem hx, mul_zero, sub_self]

/-- The constructed hard-window `k` image is exactly `P` of the
constructed hard-window `q` image, in the same quartic coefficient space. -/
theorem originalDetectorPaddedFinitePoleImageCoefficients_hardWindow_eq_poleKilled :
    ∀ (s c : ℝ) {L : ℝ} (hL : 2 ≤ L),
      localizedFiniteVector L (originalDetectorQuarticCutoff L)
        (originalDetectorPaddedFinitePoleImageCoefficients s L c (by linarith)) =
      Zeta23.ExceptionalZero.poleKilled
        (localizedFiniteVector L (originalDetectorQuarticCutoff L)
          (originalDetectorPaddedFiniteWindowImageCoefficients s L c (by linarith))) := by
  intro s c L hL
  exact (padded_poleKilled_localizedFiniteVector_of_boundaryFlat (by linarith) _ _
    (originalDetectorPaddedFiniteWindowImageCoefficients_boundaryFlat s c hL)).symm

end Zeta23.CCM

#print axioms Zeta23.CCM.padded_iteratedDeriv_poleKilled_infty
#print axioms Zeta23.CCM.padded_poleKilled_originalDetectorLobe
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePoleImage_iteratedDeriv_error_le_budget
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePoleImageCoefficients_hardWindow_contDiff
#print axioms Zeta23.CCM.padded_poleKilled_localizedFiniteVector_of_boundaryFlat
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePoleImageCoefficients_hardWindow_eq_poleKilled
