import Zeta23.CCM.OriginalDetectorFiniteWindowImage

/-!
# Genuine derivatives of the fixed finite window image

The estimates apply to iterated derivatives of one actual finite image.
The window derivative bound is proved from its nine literal coefficients.
-/

noncomputable section

open Set Complex
open scoped Topology

namespace Zeta23.CCM

def originalDetectorFiniteWindowJet (L : ℝ) (r : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range 9, originalDetectorFiniteWindowCoeff k *
    originalDetectorFourierFrequency L (4 - (k : ℤ)) ^ r *
      fourier (4 - (k : ℤ)) (x : AddCircle L)

theorem originalDetectorFiniteWindowJet_hasDerivAt
    {L : ℝ} (hL : 0 < L) (r : ℕ) (x : ℝ) :
    HasDerivAt (originalDetectorFiniteWindowJet L r)
      (originalDetectorFiniteWindowJet L (r + 1) x) x := by
  have : Fact (0 < L) := ⟨hL⟩
  unfold originalDetectorFiniteWindowJet
  apply HasDerivAt.fun_sum
  intro k hk
  convert (hasDerivAt_fourier L (4 - (k : ℤ)) x).const_mul
    (originalDetectorFiniteWindowCoeff k * originalDetectorFourierFrequency L (4 - (k : ℤ)) ^ r)
      using 1 <;>
    first | rfl | (simp only [originalDetectorFourierFrequency, pow_succ]; ring_nf)

theorem originalDetectorFiniteWindow_iteratedDeriv
    {L : ℝ} (hL : 0 < L) (r : ℕ) :
    iteratedDeriv r (originalDetectorFiniteWindow L) = originalDetectorFiniteWindowJet L r := by
  induction r with
  | zero =>
    funext x
    simp only [iteratedDeriv_zero, originalDetectorFiniteWindowJet, pow_zero, mul_one]
    exact originalDetectorFiniteWindow_eq_fourier L x
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (originalDetectorFiniteWindowJet_hasDerivAt hL r x).deriv

theorem originalDetectorFiniteWindowCoeff_norm_sum :
    (∑ k ∈ Finset.range 9, ‖originalDetectorFiniteWindowCoeff k‖) = 1 := by
  norm_num [originalDetectorFiniteWindowCoeff, Finset.sum_range_succ, norm_div, norm_mul,
    norm_pow, Complex.norm_natCast, Nat.choose]

/-- Every literal window jet has the expected degree-four frequency bound. -/
theorem norm_originalDetectorFiniteWindow_iteratedDeriv_le
    {L : ℝ} (hL : 0 < L) (r : ℕ) (x : ℝ) :
    ‖iteratedDeriv r (originalDetectorFiniteWindow L) x‖ ≤ (8 * Real.pi / L) ^ r := by
  rw [originalDetectorFiniteWindow_iteratedDeriv hL]
  unfold originalDetectorFiniteWindowJet
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.range 9, ‖originalDetectorFiniteWindowCoeff k‖ * (8 * Real.pi / L) ^ r := by
      apply Finset.sum_le_sum
      intro k hk
      have hk8 : k ≤ 8 := by simp only [Finset.mem_range] at hk; omega
      have hfreq : ‖originalDetectorFourierFrequency L (4 - (k : ℤ))‖ ≤ 8 * Real.pi / L := by
        have hkreal : (k : ℝ) ≤ 8 := by exact_mod_cast hk8
        have hkpos : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        have habs : |((4 - (k : ℤ) : ℤ) : ℝ)| ≤ 4 := by
          push_cast
          exact abs_le.2 ⟨by linarith, by linarith⟩
        simp only [originalDetectorFourierFrequency, norm_div, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_intCast, Complex.norm_I, norm_ofNat,
          abs_of_pos Real.pi_pos, abs_of_pos hL, mul_one]
        calc
          _ ≤ (2 * Real.pi * 4) / L := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left habs (by positivity)) hL.le
          _ = _ := by ring
      simp only [norm_mul, norm_pow, fourier_apply, Circle.norm_coe, mul_one]
      gcongr
    _ = _ := by rw [← Finset.sum_mul, originalDetectorFiniteWindowCoeff_norm_sum, one_mul]

theorem originalDetectorFiniteWindow_contDiff (L : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (originalDetectorFiniteWindow L) := by
  unfold originalDetectorFiniteWindow
  exact ((Complex.contDiff_sin.restrict_scalars ℝ).comp
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const (L : ℂ))).pow 8

theorem originalDetectorDividedLobeFourierPartialSum_contDiff
    (s L c : ℝ) (hL : 0 < L) :
    ContDiff ℝ (⊤ : ℕ∞) (originalDetectorDividedLobeFourierPartialJet s L c hL 0) := by
  unfold originalDetectorDividedLobeFourierPartialJet
  simp_rw [fourier_coe_apply]
  apply ContDiff.sum
  intro n hn
  exact contDiff_const.mul
    (((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const (L : ℂ)).cexp)

/-- The explicit error budget after multiplication by the literal window. -/
def originalDetectorFiniteWindowImageJetBudget (s L : ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (r + 1), (Nat.choose r i : ℝ) * (8 * Real.pi / L) ^ i *
    originalDetectorDividedLobeFourierJetTailBudget s L (r - i)

/-- Actual source-jet approximation by the single finite windowed image,
for every finite order, hence in particular through order three. -/
theorem originalDetectorFiniteWindowImage_iteratedDeriv_error_le_budget
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (r : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖iteratedDeriv r (originalDetectorLobe s c) x -
      iteratedDeriv r (originalDetectorFiniteWindowImage s L c (by linarith)) x‖ ≤
        originalDetectorFiniteWindowImageJetBudget s L r := by
  have hLp : 0 < L := by linarith
  have hw := originalDetectorFiniteWindow_contDiff L
  have hf := originalDetectorDividedLobe_contDiff hs hL hleft hright
  have hp := originalDetectorDividedLobeFourierPartialSum_contDiff s L c hLp
  have hwhole : originalDetectorFiniteWindowImage s L c hLp =
      originalDetectorFiniteWindow L * originalDetectorDividedLobeFourierPartialJet s L c hLp 0 := rfl
  have hlobe : originalDetectorLobe s c =
      originalDetectorFiniteWindow L * originalDetectorDividedLobe s L c := by
    funext y
    exact (originalDetectorFiniteWindow_mul_dividedLobe hs hL hleft hright y).symm
  have hr : (r : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)
  rw [hlobe, hwhole, iteratedDeriv_mul ((hw.of_le hr).contDiffAt) ((hf.of_le hr).contDiffAt),
    iteratedDeriv_mul ((hw.of_le hr).contDiffAt) ((hp.of_le hr).contDiffAt), ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  unfold originalDetectorFiniteWindowImageJetBudget
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_sub, norm_mul, norm_mul, Complex.norm_natCast]
  have hb := originalDetectorDividedLobeFourierPartialSum_iteratedDeriv_error_le_budget
    hs hL hleft hright (r - i) hx
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (norm_originalDetectorFiniteWindow_iteratedDeriv_le hLp i x)
      (Nat.cast_nonneg _)) hb (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorFiniteWindow_iteratedDeriv
#print axioms Zeta23.CCM.originalDetectorFiniteWindowCoeff_norm_sum
#print axioms Zeta23.CCM.norm_originalDetectorFiniteWindow_iteratedDeriv_le
#print axioms Zeta23.CCM.originalDetectorFiniteWindowImage_iteratedDeriv_error_le_budget
