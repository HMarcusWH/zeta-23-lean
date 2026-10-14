import Zeta23.CCM.OriginalDetectorFourierTailBounds
import Zeta23.CCM.LocalizedFourierApproximation

/-!
# The literal windowed finite Fourier image of the original lobe

The window is exactly `sin^8(πx/L)` and the raw polynomial uses exactly
`ceil(L^4)-4` frequencies. Its finite image therefore has the prescribed
degree `ceil(L^4)`. No approximation premise is supplied by the caller.
-/

noncomputable section

open Set Complex Metric
open scoped Topology

namespace Zeta23.CCM

/-- The literal degree-four window. -/
def originalDetectorFiniteWindow (L x : ℝ) : ℂ :=
  Complex.sin ((Real.pi : ℂ) * x / (L : ℂ)) ^ 8

/-- The nine exact Fourier coefficients of the literal sine window. -/
def originalDetectorFiniteWindowCoeff (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * (Nat.choose 8 k : ℂ) / 256

/-- The sine window is the actual nine-mode Fourier polynomial. -/
theorem originalDetectorFiniteWindow_eq_fourier (L x : ℝ) :
    originalDetectorFiniteWindow L x =
      ∑ k ∈ Finset.range 9, originalDetectorFiniteWindowCoeff k *
        fourier (4 - (k : ℤ)) (x : AddCircle L) := by
  let z : ℂ := (Real.pi : ℂ) * x / (L : ℂ)
  have hmode (k : ℕ) (hk : k ∈ Finset.range 9) :
      Complex.exp (-z * I) ^ k * Complex.exp (z * I) ^ (8 - k) =
        fourier (4 - (k : ℤ)) (x : AddCircle L) := by
    have hk8 : k ≤ 8 := by simp only [Finset.mem_range] at hk; omega
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      fourier_coe_apply]
    congr 1
    push_cast
    rw [Nat.cast_sub hk8]
    dsimp [z]
    ring
  have hsin : originalDetectorFiniteWindow L x =
      (Complex.exp (-z * I) - Complex.exp (z * I)) ^ 8 / 256 := by
    have hI8 : (I : ℂ) ^ 8 = 1 := by
      calc
        _ = (I ^ 2) ^ 4 := by ring
        _ = 1 := by rw [Complex.I_sq]; norm_num
    unfold originalDetectorFiniteWindow
    change Complex.sin z ^ 8 = _
    rw [Complex.sin, div_pow, mul_pow]
    rw [hI8]
    norm_num
  rw [hsin, sub_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add, show (-1 : ℂ) ^ 8 = 1 by norm_num, mul_one]
  unfold originalDetectorFiniteWindowCoeff
  rw [← hmode k hk]
  ring

/-- Window multiplication recovers the literal original lobe everywhere,
including the zeros of the window outside its strict source collar. -/
theorem originalDetectorFiniteWindow_mul_dividedLobe
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) (x : ℝ) :
    originalDetectorFiniteWindow L x * originalDetectorDividedLobe s L c x =
      originalDetectorLobe s c x := by
  by_cases hx : x ∈ Icc 1 (L - 1)
  · have hn := originalDetectorWindow_complex_sin_lower hL hx.1 hx.2
      (z := (x : ℂ)) (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 2))
    have hne : Complex.sin ((Real.pi : ℂ) * x / (L : ℂ)) ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hn
      have hLp : 0 < L := by linarith
      exact (not_le_of_gt (one_div_pos.2 hLp)) hn
    unfold originalDetectorFiniteWindow originalDetectorDividedLobe
    field_simp
  · have hzero : originalDetectorLobe s c x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hb := originalDetectorLobe_support hs c hm
      exact hx ⟨by linarith [hb.1], hb.2.trans hright⟩
    simp only [originalDetectorDividedLobe, hzero, zero_div, mul_zero]

theorem norm_originalDetectorFiniteWindow_le_one (L x : ℝ) :
    ‖originalDetectorFiniteWindow L x‖ ≤ 1 := by
  have he : Complex.sin ((Real.pi : ℂ) * x / (L : ℂ)) =
      (Real.sin (Real.pi * x / L) : ℂ) := by push_cast; rfl
  rw [originalDetectorFiniteWindow, he, norm_pow, Complex.norm_real]
  exact (pow_le_pow_left₀ (norm_nonneg _) (by simpa using Real.abs_sin_le_one (Real.pi * x / L)) 8).trans_eq (by norm_num)

/-- The actual finite windowed image of the original source lobe. -/
def originalDetectorFiniteWindowImage (s L c : ℝ) (hL : 0 < L) (x : ℝ) : ℂ :=
  originalDetectorFiniteWindow L x * originalDetectorDividedLobeFourierPartialJet s L c hL 0 x

/-- The exact integer Fourier coordinates of the windowed raw partial sum. -/
def originalDetectorFiniteWindowImageFinsupp (s L c : ℝ) (hL : 0 < L) : ℤ →₀ ℂ :=
  ∑ n ∈ Finset.Icc (-(originalDetectorRawCutoff L : ℤ)) (originalDetectorRawCutoff L : ℤ),
    ∑ k ∈ Finset.range 9, Finsupp.single (n + (4 - (k : ℤ)))
      (originalDetectorFiniteWindowCoeff k * originalDetectorDividedLobeFourierCoeff s L c hL n)

/-- Every actual output frequency lies in the prescribed quartic space. -/
theorem originalDetectorFiniteWindowImageFinsupp_support
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ∀ n ∈ (originalDetectorFiniteWindowImageFinsupp s L c (by linarith)).support,
      n.natAbs ≤ originalDetectorQuarticCutoff L := by
  classical
  intro m hm
  unfold originalDetectorFiniteWindowImageFinsupp at hm
  obtain ⟨n, hn, hm⟩ := Finsupp.mem_support_finsetSum m hm
  obtain ⟨k, hk, hm⟩ := Finsupp.mem_support_finsetSum m hm
  have hmn : m = n + (4 - (k : ℤ)) :=
    Finset.mem_singleton.mp (Finsupp.support_single_subset hm)
  have hn' := Finset.mem_Icc.mp hn
  have hk' := Finset.mem_range.mp hk
  have hdegree := originalDetectorRawCutoff_add_four hL
  subst m
  omega

private theorem addCircleFourierPolynomial_finset_sum_apply
    {ι : Type*} (F : Finset ι) (f : ι → ℤ →₀ ℂ) {L : ℝ} (x : AddCircle L) :
    addCircleFourierPolynomial (∑ i ∈ F, f i) x =
      ∑ i ∈ F, addCircleFourierPolynomial (f i) x := by
  classical
  induction F using Finset.induction with
  | empty => simp
  | @insert i F hi ih =>
    simp only [Finset.sum_insert hi, addCircleFourierPolynomial_add, ContinuousMap.add_apply, ih]

/-- Exact polynomial evaluation, before any approximation claim. -/
theorem originalDetectorFiniteWindowImageFinsupp_eq
    (s L c : ℝ) (hL : 0 < L) (x : ℝ) :
    addCircleFourierPolynomial (originalDetectorFiniteWindowImageFinsupp s L c hL)
        (x : AddCircle L) = originalDetectorFiniteWindowImage s L c hL x := by
  classical
  unfold originalDetectorFiniteWindowImageFinsupp
  rw [addCircleFourierPolynomial_finset_sum_apply]
  simp_rw [addCircleFourierPolynomial_finset_sum_apply, addCircleFourierPolynomial_single,
    ContinuousMap.smul_apply, smul_eq_mul, fourier_add]
  unfold originalDetectorFiniteWindowImage originalDetectorDividedLobeFourierPartialJet
  simp only [originalDetectorDividedLobeFourierJetCoeff, pow_zero, one_mul]
  rw [originalDetectorFiniteWindow_eq_fourier, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The concrete output vector in the repository's normalized centered
coordinates, padded positively to exactly the mandated quartic degree. -/
def originalDetectorFiniteWindowImageCoefficients (s L c : ℝ) (hL : 0 < L) :
    Fin (2 * originalDetectorQuarticCutoff L + 1) → ℂ :=
  centeredCoefficientsOfFinsupp L (originalDetectorQuarticCutoff L)
    (originalDetectorFiniteWindowImageFinsupp s L c hL)

/-- The actual centered finite function equals the literal windowed
Fourier image. This includes the exact physical normalization `sqrt L`. -/
theorem localizedFiniteFunction_originalDetectorFiniteWindowImageCoefficients
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) (x : ℝ) :
    localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      (originalDetectorFiniteWindowImageCoefficients s L c (by linarith)) x =
        originalDetectorFiniteWindowImage s L c (by linarith) x := by
  unfold originalDetectorFiniteWindowImageCoefficients
  rw [localizedFiniteFunction_centeredCoefficientsOfFinsupp_eq (by linarith)
    _ (originalDetectorFiniteWindowImageFinsupp_support s c hL) x]
  exact originalDetectorFiniteWindowImageFinsupp_eq s L c (by linarith) x

/-- Actual source approximation by the literal windowed finite image,
with the source-derived raw Fourier budget. -/
theorem originalDetectorFiniteWindowImage_error_le_budget
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖originalDetectorLobe s c x - originalDetectorFiniteWindowImage s L c (by linarith) x‖ ≤
      originalDetectorDividedLobeFourierJetTailBudget s L 0 := by
  rw [← originalDetectorFiniteWindow_mul_dividedLobe hs hL hleft hright x]
  unfold originalDetectorFiniteWindowImage
  rw [← mul_sub, norm_mul]
  have hb := originalDetectorDividedLobeFourierPartialJet_error_le_budget
    hs hL hleft hright 0 hx
  simp only [iteratedDeriv_zero] at hb
  exact (mul_le_mul_of_nonneg_right (norm_originalDetectorFiniteWindow_le_one L x)
    (norm_nonneg _)).trans (by simpa only [one_mul] using hb)

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorFiniteWindow_eq_fourier
#print axioms Zeta23.CCM.originalDetectorFiniteWindow_mul_dividedLobe
#print axioms Zeta23.CCM.originalDetectorFiniteWindowImageFinsupp_support
#print axioms Zeta23.CCM.originalDetectorFiniteWindowImageFinsupp_eq
#print axioms Zeta23.CCM.localizedFiniteFunction_originalDetectorFiniteWindowImageCoefficients
#print axioms Zeta23.CCM.originalDetectorFiniteWindowImage_error_le_budget
