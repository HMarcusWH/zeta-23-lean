import Zeta23.CCM.OriginalDetectorFiniteWindowImageJets
import Zeta23.CCM.OriginalDetectorFourierTailAsymptotics

/-! The literal DC padding paid by the common actual Fourier tail bound. -/

noncomputable section

open Set Complex Filter
open scoped Topology

namespace Zeta23.CCM

def originalDetectorPositivePadding (s L : ℝ) : ℝ :=
  originalDetectorDividedLobeFourierJetTailBudget s L 0

theorem originalDetectorPositivePadding_nonneg (s L : ℝ) :
    0 ≤ originalDetectorPositivePadding s L := by
  unfold originalDetectorPositivePadding originalDetectorDividedLobeFourierJetTailBudget
  have hc := originalDetectorDividedLobeFourierJetDecayConstant_nonneg s 0
  have hk := originalDetectorDividedLobeFourierDecayRate_pos s
  positivity

theorem originalDetectorPositivePadding_pos {s L : ℝ} (hs : 0 < s) (hL : 0 < L) :
    0 < originalDetectorPositivePadding s L := by
  unfold originalDetectorPositivePadding originalDetectorDividedLobeFourierJetTailBudget
    originalDetectorDividedLobeFourierJetDecayConstant
  have hb := UniversalSinc.gevreyMomentScale_pos hs
  have hk := originalDetectorDividedLobeFourierDecayRate_pos s
  positivity

def originalDetectorPaddedRawFourierCoeff (s L c : ℝ) (hL : 0 < L) (n : ℤ) : ℂ :=
  originalDetectorDividedLobeFourierCoeff s L c hL n +
    if n = 0 then (originalDetectorPositivePadding s L : ℂ) else 0

def originalDetectorPaddedRawFourierJetCoeff (s L c : ℝ) (hL : 0 < L)
    (r : ℕ) (n : ℤ) : ℂ :=
  originalDetectorFourierFrequency L n ^ r * originalDetectorPaddedRawFourierCoeff s L c hL n

def originalDetectorPaddedRawFourierPartialJet (s L c : ℝ) (hL : 0 < L)
    (r : ℕ) (x : ℝ) : ℂ :=
  letI : Fact (0 < L) := ⟨hL⟩
  ∑ n ∈ Finset.Icc (-(originalDetectorRawCutoff L : ℤ)) (originalDetectorRawCutoff L : ℤ),
    originalDetectorPaddedRawFourierJetCoeff s L c hL r n * fourier n (x : AddCircle L)

theorem originalDetectorPaddedRawFourierPartialJet_eq (s L c : ℝ) (hL : 0 < L)
    (r : ℕ) (x : ℝ) :
    originalDetectorPaddedRawFourierPartialJet s L c hL r x =
      originalDetectorDividedLobeFourierPartialJet s L c hL r x +
        if r = 0 then (originalDetectorPositivePadding s L : ℂ) else 0 := by
  classical
  unfold originalDetectorPaddedRawFourierPartialJet originalDetectorDividedLobeFourierPartialJet
    originalDetectorPaddedRawFourierJetCoeff originalDetectorDividedLobeFourierJetCoeff
    originalDetectorPaddedRawFourierCoeff
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  have hzero : (0 : ℤ) ∈ Finset.Icc (-(originalDetectorRawCutoff L : ℤ))
      (originalDetectorRawCutoff L : ℤ) := by simp
  simp only [hzero, if_true, fourier_eval_zero, mul_one]
  by_cases hr : r = 0
  · subst r; simp
  · simp [originalDetectorFourierFrequency, hr, zero_pow hr]

theorem originalDetectorPaddedRawFourierPartialJet_iteratedDeriv
    (s L c : ℝ) (hL : 0 < L) (r : ℕ) :
    iteratedDeriv r (originalDetectorPaddedRawFourierPartialJet s L c hL 0) =
      originalDetectorPaddedRawFourierPartialJet s L c hL r := by
  have hf := originalDetectorDividedLobeFourierPartialSum_contDiff s L c hL
  have heq : originalDetectorPaddedRawFourierPartialJet s L c hL 0 =
      originalDetectorDividedLobeFourierPartialJet s L c hL 0 +
        fun _ => (originalDetectorPositivePadding s L : ℂ) := by
    funext x; simp [originalDetectorPaddedRawFourierPartialJet_eq]
  rw [heq]
  funext x
  have hr : (r : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)
  change iteratedDeriv r (fun y => originalDetectorDividedLobeFourierPartialJet s L c hL 0 y +
    (originalDetectorPositivePadding s L : ℂ)) x = _
  rw [iteratedDeriv_fun_add (hf.of_le hr).contDiffAt contDiff_const.contDiffAt]
  rw [originalDetectorDividedLobeFourierPartialJet_iteratedDeriv]
  rw [originalDetectorPaddedRawFourierPartialJet_eq]
  by_cases hz : r = 0
  · subst r; simp
  · simp [iteratedDeriv_const, hz]

def originalDetectorPaddedRawFourierJetTailBudget (s L : ℝ) (r : ℕ) : ℝ :=
  originalDetectorDividedLobeFourierJetTailBudget s L r + originalDetectorPositivePadding s L

theorem originalDetectorPaddedRawFourierPartialJet_error_le_budget
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (r : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖iteratedDeriv r (originalDetectorDividedLobe s L c) x -
      originalDetectorPaddedRawFourierPartialJet s L c (by linarith) r x‖ ≤
        originalDetectorPaddedRawFourierJetTailBudget s L r := by
  rw [originalDetectorPaddedRawFourierPartialJet_eq, ← sub_sub]
  refine (norm_sub_le _ _).trans ?_
  apply add_le_add
  · exact originalDetectorDividedLobeFourierPartialJet_error_le_budget hs hL hleft hright r hx
  · split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (originalDetectorPositivePadding_nonneg s L)]
    · simpa using originalDetectorPositivePadding_nonneg s L

theorem originalDetectorPaddedRawFourierPartialSum_iteratedDeriv_error_le_budget
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (r : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖iteratedDeriv r (originalDetectorDividedLobe s L c) x -
      iteratedDeriv r (originalDetectorPaddedRawFourierPartialJet s L c (by linarith) 0) x‖ ≤
        originalDetectorPaddedRawFourierJetTailBudget s L r := by
  rw [originalDetectorPaddedRawFourierPartialJet_iteratedDeriv]
  exact originalDetectorPaddedRawFourierPartialJet_error_le_budget hs hL hleft hright r hx

theorem originalDetectorPaddedRawFourierJetTailBudget_mul_exp_tendsto_zero
    (s : ℝ) (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedRawFourierJetTailBudget s L r * Real.exp (β * L))
      atTop (𝓝 0) := by
  simpa only [originalDetectorPaddedRawFourierJetTailBudget, originalDetectorPositivePadding,
    add_mul, add_zero] using
    (originalDetectorDividedLobeFourierJetTailBudget_mul_exp_tendsto_zero s r β).add
      (originalDetectorDividedLobeFourierJetTailBudget_mul_exp_tendsto_zero s 0 β)

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPositivePadding_pos
#print axioms Zeta23.CCM.originalDetectorPaddedRawFourierPartialJet_eq
#print axioms Zeta23.CCM.originalDetectorPaddedRawFourierPartialJet_iteratedDeriv
#print axioms Zeta23.CCM.originalDetectorPaddedRawFourierPartialJet_error_le_budget
#print axioms Zeta23.CCM.originalDetectorPaddedRawFourierJetTailBudget_mul_exp_tendsto_zero
