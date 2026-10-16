import Zeta23.CCM.OriginalDetectorPositiveFourierPadding

/-! The actual symmetric truncation is real and its paid padding is nonnegative. -/

noncomputable section

open Set Complex
open scoped Topology ComplexConjugate

namespace Zeta23.CCM

theorem originalDetectorDividedLobe_conj (s L c x : ℝ) :
    conj (originalDetectorDividedLobe s L c x) = originalDetectorDividedLobe s L c x := by
  have hs : Complex.sin ((Real.pi : ℂ) * x / (L : ℂ)) =
      (Real.sin (Real.pi * x / L) : ℂ) := by push_cast; rfl
  simp only [originalDetectorDividedLobe, hs, originalDetectorLobe,
    UniversalSinc.originalDensityComplex, map_div₀, map_pow, Complex.conj_ofReal]

theorem originalDetectorDividedLobe_re_nonneg {s : ℝ} (hs : 0 < s) (L c x : ℝ) :
    0 ≤ (originalDetectorDividedLobe s L c x).re := by
  have hsin : Complex.sin ((Real.pi : ℂ) * x / (L : ℂ)) =
      (Real.sin (Real.pi * x / L) : ℂ) := by push_cast; rfl
  have hf : originalDetectorDividedLobe s L c x =
      ((UniversalSinc.originalDensityCandidate s (x - c) /
        Real.sin (Real.pi * x / L) ^ 8 : ℝ) : ℂ) := by
    simp only [originalDetectorDividedLobe, originalDetectorLobe,
      UniversalSinc.originalDensityComplex, hsin, Complex.ofReal_div, Complex.ofReal_pow]
  rw [hf, Complex.ofReal_re]
  exact div_nonneg (UniversalSinc.originalDensityCandidate_nonneg hs _) (by positivity)

theorem originalDetectorDividedLobeFourierCoeff_conj
    (s L c : ℝ) (hL : 0 < L) (n : ℤ) :
    conj (originalDetectorDividedLobeFourierCoeff s L c hL n) =
      originalDetectorDividedLobeFourierCoeff s L c hL (-n) := by
  unfold originalDetectorDividedLobeFourierCoeff
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 1
  change Complex.conjLIE.toLinearIsometry (∫ x in (0 : ℝ)..L,
    fourier (-n) (x : AddCircle (L - 0)) • originalDetectorDividedLobe s L c x) = _
  rw [← Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm]
  apply intervalIntegral.integral_congr
  intro x hx
  change conj (fourier (-n) (x : AddCircle (L - 0)) • originalDetectorDividedLobe s L c x) = _
  simp only [smul_eq_mul, map_mul,
    originalDetectorDividedLobe_conj, ← fourier_neg]

theorem originalDetectorDividedLobeFourierPartialSum_conj
    (s L c : ℝ) (hL : 0 < L) (x : ℝ) :
    conj (originalDetectorDividedLobeFourierPartialJet s L c hL 0 x) =
      originalDetectorDividedLobeFourierPartialJet s L c hL 0 x := by
  classical
  unfold originalDetectorDividedLobeFourierPartialJet
  simp only [originalDetectorDividedLobeFourierJetCoeff, pow_zero, one_mul, map_sum,
    map_mul, originalDetectorDividedLobeFourierCoeff_conj, ← fourier_neg]
  apply Finset.sum_bij (fun n _ => -n)
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn m hm hnm
    omega
  · intro n hn
    refine ⟨-n, ?_, by simp⟩
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn
    rfl

theorem originalDetectorPaddedRawFourierPartialSum_real
    (s L c : ℝ) (hL : 0 < L) (x : ℝ) :
    conj (originalDetectorPaddedRawFourierPartialJet s L c hL 0 x) =
      originalDetectorPaddedRawFourierPartialJet s L c hL 0 x := by
  simp only [originalDetectorPaddedRawFourierPartialJet_eq, if_true, map_add,
    Complex.conj_ofReal, originalDetectorDividedLobeFourierPartialSum_conj]

theorem originalDetectorPaddedRawFourierPartialSum_re_nonneg
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    0 ≤ (originalDetectorPaddedRawFourierPartialJet s L c (by linarith) 0 x).re := by
  have hb := originalDetectorDividedLobeFourierPartialJet_error_le_budget hs hL hleft hright 0 hx
  simp only [iteratedDeriv_zero] at hb
  have hre := Complex.re_le_norm
    (originalDetectorDividedLobe s L c x -
      originalDetectorDividedLobeFourierPartialJet s L c (by linarith) 0 x)
  have hf := originalDetectorDividedLobe_re_nonneg hs L c x
  simp only [originalDetectorPaddedRawFourierPartialJet_eq, if_true, Complex.add_re,
    Complex.ofReal_re, Complex.sub_re] at *
  change _ + originalDetectorDividedLobeFourierJetTailBudget s L 0 ≥ 0
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierCoeff_conj
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierPartialSum_conj
#print axioms Zeta23.CCM.originalDetectorPaddedRawFourierPartialSum_real
#print axioms Zeta23.CCM.originalDetectorPaddedRawFourierPartialSum_re_nonneg
