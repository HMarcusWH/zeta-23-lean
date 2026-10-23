import Zeta23.OPICAFollowup.RenormalizedCoPoisson
import Zeta23.OPICAFollowup.ProfileEulerMaclaurin

/-!
Actual zero profiles (R2-S1a). For an actual zero ζ(ρ) = 0 with 0 < Re ρ < 1 the profile
h(x) = 1 - S_ρ(|x|)/b_ρ is built from the frozen inclusive finite sums `finiteSumSrho` of the
co-Poisson construction and b_ρ = `normalizationBrho` ρ; κ = ρ(1 - ρ) is `spectralKappa`.

- The zero is not 1/2 because ζ is negative on the real segment (0, 1), so b_ρ ≠ 0 needs no
  extra premise. The functional equation (Mathlib `riemannZeta_one_sub`) gives ζ(1 - ρ) = 0.
- The tail and the derivative bounds come from the second-order Euler-Maclaurin expansion
  (`ProfileEulerMaclaurin`) applied to both finite sums. Derivatives are those of the exact
  finite sums on each cell, never of a big-O remainder.
- Fourier self-duality comes from the actual zero measure (`zero_measure_exact_properties`),
  the Lebesgue functional and Poisson summation for the comb: ν = (dx + δ₀ - D₀) - h dx.
  The ordinary identity 𝓕h = h then follows from the multiplication formula and uniqueness
  against smooth compactly supported tests.
-/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ContDiff

namespace Zeta23.OPICAFollowup

/-- The reflection quotient κ = ρ(1 - ρ). -/
def spectralKappa (ρ : ℂ) : ℂ := ρ * (1 - ρ)

/-- The zero profile h(x) = 1 - S_ρ(|x|)/b_ρ, built from the actual inclusive finite sums. -/
def zeroProfile (ρ : ℂ) (x : ℝ) : ℂ := 1 - finiteSumSrho ρ |x| / normalizationBrho ρ

section Basic

lemma zeroProfile_neg (ρ : ℂ) (x : ℝ) : zeroProfile ρ (-x) = zeroProfile ρ x := by
  simp [zeroProfile]

lemma finiteSumSrho_of_lt_one (ρ : ℂ) {y : ℝ} (hy : y < 1) : finiteSumSrho ρ y = 0 := by
  have hf : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hy
  simp [finiteSumSrho, coPoissonPowerSums, hf]

lemma finiteSumSrho_one (ρ : ℂ) : finiteSumSrho ρ 1 = 0 := by
  simp [finiteSumSrho, coPoissonPowerSums]

lemma finiteSumSrho_of_le_one (ρ : ℂ) {y : ℝ} (hy : y ≤ 1) : finiteSumSrho ρ y = 0 := by
  rcases lt_or_eq_of_le hy with h | h
  · exact finiteSumSrho_of_lt_one ρ h
  · rw [h]; exact finiteSumSrho_one ρ

lemma zeroProfile_eq_one (ρ : ℂ) {x : ℝ} (hx : |x| ≤ 1) : zeroProfile ρ x = 1 := by
  simp [zeroProfile, finiteSumSrho_of_le_one ρ hx]

lemma finiteSumSrho_eq_rightPowerSum (ρ : ℂ) (y : ℝ) : finiteSumSrho ρ y =
    (y : ℂ) ^ (-ρ) * rightPowerSum (1 - ρ) y - (y : ℂ) ^ (ρ - 1) * rightPowerSum ρ y := by
  simp only [finiteSumSrho, coPoissonPowerSums, rightPowerSum, neg_sub]

lemma strip_ne {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ ≠ 0 ∧ ρ ≠ 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] at h0 h1 <;> simp at h0 h1

/-- An actual zero in the strip is not 1/2 (ζ is negative on the real segment (0, 1)). -/
lemma zero_ne_half {ρ : ℂ} (hz : riemannZeta ρ = 0) : ρ ≠ 1 / 2 := by
  intro h
  have := Zeta23.ExceptionalZero.riemannZeta_ne_zero_of_real_critical_strip
    (σ := 1 / 2) (by norm_num) (by norm_num)
  apply this
  rw [← hz, h]; push_cast; ring_nf

end Basic

section Tail

lemma cpow_sub_one' {x : ℝ} (hx : 0 < x) (a : ℂ) : (x : ℂ) ^ (a - 1) = (x : ℂ) ^ a / x := by
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]

/-- The Euler-Maclaurin remainder of S_ρ: x^(-ρ) R(1-ρ, x) - x^(ρ-1) R(ρ, x). -/
def srhoRemainder (ρ : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-ρ) * eulerMaclaurinRemainder (1 - ρ) x - (x : ℂ) ^ (ρ - 1) * eulerMaclaurinRemainder ρ x

/-- The S1a identity for every strip parameter and real cutoff x ≥ 1: the two B₁/x terms cancel. -/
theorem finiteSumSrho_expansion {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {x : ℝ} (hx : 1 ≤ x) :
    finiteSumSrho ρ x = riemannZeta (1 - ρ) * (x : ℂ) ^ (-ρ) - riemannZeta ρ * (x : ℂ) ^ (ρ - 1) +
      (1 / ρ - 1 / (1 - ρ)) + (2 * ρ - 1) * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2) +
        srhoRemainder ρ x := by
  have hx0 : 0 < x := by linarith
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hσ0 : 0 < (1 - ρ).re := by simp; linarith
  have hσ1 : 1 - ρ ≠ 1 := fun h => hρ0 (by linear_combination -h)
  have eA := rightPowerSum_expansion hσ0 hσ1 hx
  have eB := rightPowerSum_expansion h0 hρ1 hx
  have hv : (x : ℂ) ^ ρ ≠ 0 := (Complex.cpow_ne_zero_iff_of_exponent_ne_zero hρ0).mpr hxne
  have hneg : (x : ℂ) ^ (-ρ) = ((x : ℂ) ^ ρ)⁻¹ := Complex.cpow_neg _ _
  have p1 : (x : ℂ) ^ (1 - (1 - ρ)) = (x : ℂ) ^ ρ := by ring_nf
  have p2 : (x : ℂ) ^ (-(1 - ρ)) = (x : ℂ) ^ ρ / x := by
    rw [show -(1 - ρ) = ρ - 1 by ring, cpow_sub_one' hx0]
  have p3 : (x : ℂ) ^ (-(1 - ρ) - 1) = (x : ℂ) ^ ρ / x / x := by
    rw [cpow_sub_one' hx0, p2]
  have p4 : (x : ℂ) ^ (1 - ρ) = x * ((x : ℂ) ^ ρ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hxne, Complex.cpow_one, div_eq_mul_inv]
  have p5 : (x : ℂ) ^ (-ρ - 1) = ((x : ℂ) ^ ρ)⁻¹ / x := by rw [cpow_sub_one' hx0, hneg]
  have p6 : (x : ℂ) ^ (ρ - 1) = (x : ℂ) ^ ρ / x := cpow_sub_one' hx0 ρ
  have hs1 : (1 : ℂ) - (1 - ρ) = ρ := by ring
  have hs2 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  rw [finiteSumSrho_eq_rightPowerSum, eA, eB, srhoRemainder, p1, p2, p3, p4, p5, p6, hneg, hs1]
  field_simp
  ring

/-- Explicit constant of the S_ρ remainder bound. -/
def srhoRemainderConst (ρ : ℂ) : ℝ :=
  (‖1 - ρ‖ * (‖1 - ρ‖ + 1) / 6 + ‖1 - ρ‖ * (‖1 - ρ‖ + 1) * (‖1 - ρ‖ + 2) / 12) +
    (‖ρ‖ * (‖ρ‖ + 1) / 6 + ‖ρ‖ * (‖ρ‖ + 1) * (‖ρ‖ + 2) / 12)

lemma srhoRemainderConst_nonneg (ρ : ℂ) : 0 ≤ srhoRemainderConst ρ := by
  unfold srhoRemainderConst; positivity

lemma srhoRemainder_norm_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {x : ℝ} (hx : 0 < x) :
    ‖srhoRemainder ρ x‖ ≤ srhoRemainderConst ρ * x ^ (-3 : ℝ) := by
  have hσ0 : 0 < (1 - ρ).re := by simp; linarith
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hA := eulerMaclaurinRemainder_norm_le hσ0 hx
  have hB := eulerMaclaurinRemainder_norm_le h0 hx
  have e1 : x ^ (-ρ).re * x ^ (-(1 - ρ).re - 2) = x ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hx]; congr 1; simp; ring
  have e2 : x ^ (ρ - 1).re * x ^ (-ρ.re - 2) = x ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hx]; congr 1; simp; ring
  have hp1 : 0 ≤ x ^ (-ρ).re := Real.rpow_nonneg hx.le _
  have hp2 : 0 ≤ x ^ (ρ - 1).re := Real.rpow_nonneg hx.le _
  unfold srhoRemainderConst
  calc x ^ (-ρ).re * ‖eulerMaclaurinRemainder (1 - ρ) x‖ +
        x ^ (ρ - 1).re * ‖eulerMaclaurinRemainder ρ x‖
      ≤ x ^ (-ρ).re * ((‖1 - ρ‖ * (‖1 - ρ‖ + 1) / 6 +
            ‖1 - ρ‖ * (‖1 - ρ‖ + 1) * (‖1 - ρ‖ + 2) / 12) * x ^ (-(1 - ρ).re - 2)) +
          x ^ (ρ - 1).re * ((‖ρ‖ * (‖ρ‖ + 1) / 6 + ‖ρ‖ * (‖ρ‖ + 1) * (‖ρ‖ + 2) / 12) *
            x ^ (-ρ.re - 2)) := by gcongr
    _ = _ := by rw [mul_left_comm, e1, mul_left_comm, e2]; ring

lemma kappa_div_brho {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    (2 * ρ - 1) / normalizationBrho ρ = -spectralKappa ρ := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
  have hs2 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have h2 : (1 : ℂ) - 2 * ρ ≠ 0 := by
    intro h; apply hh; linear_combination -h / 2
  unfold normalizationBrho spectralKappa
  field_simp
  ring

lemma brho_eq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    normalizationBrho ρ = 1 / ρ - 1 / (1 - ρ) := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  rw [← coPoissonOriginNormalizer_eq_brho hρ0 hρ1]; rfl

/-- At an actual zero: h(x) = κ B₂({|x|})/(2x²) - E(|x|)/b_ρ exactly for |x| ≥ 1. -/
theorem zeroProfile_expansion {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {x : ℝ} (hx : 1 ≤ |x|) : zeroProfile ρ x =
      spectralKappa ρ * (bernoulliTwo |x| : ℂ) / (2 * ((|x| : ℝ) : ℂ) ^ 2) -
        srhoRemainder ρ |x| / normalizationBrho ρ := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hh := zero_ne_half hz
  have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
  have hz' : riemannZeta (1 - ρ) = 0 := by
    have hn : ∀ n : ℕ, ρ ≠ -n := fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [riemannZeta_one_sub hn hρ1, hz, mul_zero]
  have hk := kappa_div_brho h0 h1 hh
  rw [zeroProfile, finiteSumSrho_expansion h0 h1 hx, hz, hz', ← brho_eq h0 h1]
  have hx0 : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  rw [show spectralKappa ρ = -((2 * ρ - 1) / normalizationBrho ρ) by rw [hk]; ring]
  field_simp
  ring

/-- The tail: ‖h(x) - κ B₂({|x|})/(2x²)‖ ≤ C |x|^(-3) for |x| ≥ 1. -/
theorem zeroProfile_tail {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {x : ℝ} (hx : 1 ≤ |x|) :
    ‖zeroProfile ρ x - spectralKappa ρ * (bernoulliTwo |x| : ℂ) / (2 * ((|x| : ℝ) : ℂ) ^ 2)‖ ≤
      srhoRemainderConst ρ / ‖normalizationBrho ρ‖ * |x| ^ (-3 : ℝ) := by
  rw [zeroProfile_expansion hz h0 h1 hx, sub_sub_cancel_left, norm_neg, norm_div]
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (srhoRemainder_norm_le h0 h1 (by linarith)) (norm_nonneg _)

end Tail

section Cells

/-- Cell sums Σ_{1 ≤ k ≤ n} k^(ρ-1) and Σ_{1 ≤ k ≤ n} k^(-ρ). -/
def cellSumA (ρ : ℂ) (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (ρ - 1)
def cellSumB (ρ : ℂ) (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (-ρ)

/-- The smooth cell branch y^(-ρ) A_n - y^(ρ-1) B_n of S_ρ. -/
def srhoCell (ρ : ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (-ρ) * cellSumA ρ n - (y : ℂ) ^ (ρ - 1) * cellSumB ρ n

/-- Its exact derivative, the differentiated finite sums of the cell. -/
def srhoCellDeriv (ρ : ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  -ρ * (y : ℂ) ^ (-ρ - 1) * cellSumA ρ n - (ρ - 1) * (y : ℂ) ^ (ρ - 1 - 1) * cellSumB ρ n

lemma finiteSumSrho_eq_cell (ρ : ℂ) {n : ℕ} {y : ℝ} (hy : y ∈ Ico (n : ℝ) (n + 1)) :
    finiteSumSrho ρ y = srhoCell ρ n y := by
  rw [finiteSumSrho, coPoissonPowerSums, natFloor_eq_of_mem_cell hy]; rfl

lemma hasDerivAt_srhoCell (ρ : ℂ) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (srhoCell ρ n) (srhoCellDeriv ρ n y) y := by
  have h1 := (hasDerivAt_cpow_neg ρ hy).mul_const (cellSumA ρ n)
  have h2 := (hasDerivAt_cpow_neg (1 - ρ) hy).mul_const (cellSumB ρ n)
  have e : -(1 - ρ) = ρ - 1 := by ring
  rw [e] at h2
  unfold srhoCell srhoCellDeriv
  exact h1.sub h2

/-- The two cell branches agree at the integer n ≥ 1 (continuity of S_ρ). -/
lemma srhoCell_succ_eq (ρ : ℂ) (n : ℕ) : srhoCell ρ (n + 1) (n + 1 : ℕ) = srhoCell ρ n (n + 1 : ℕ) := by
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  unfold srhoCell cellSumA cellSumB
  rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
  simp only [Complex.ofReal_natCast]
  ring

/-- Exact jump of the differentiated finite sums at n ≥ 1: S'(n+) - S'(n-) = (1 - 2ρ)/n². -/
lemma srhoCellDeriv_jump (ρ : ℂ) (n : ℕ) :
    srhoCellDeriv ρ (n + 1) (n + 1 : ℕ) - srhoCellDeriv ρ n (n + 1 : ℕ) =
      (1 - 2 * ρ) / ((n + 1 : ℕ) : ℂ) ^ 2 := by
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  unfold srhoCellDeriv cellSumA cellSumB
  rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
  simp only [Complex.ofReal_natCast]
  set N : ℂ := ((n + 1 : ℕ) : ℂ)
  have e1 : N ^ (-ρ - 1) * N ^ (ρ - 1) = (N ^ 2)⁻¹ := by
    rw [← Complex.cpow_add _ _ hn, show -ρ - 1 + (ρ - 1) = -(2 : ℂ) by ring, Complex.cpow_neg]
    norm_cast
  have e2 : N ^ (ρ - 1 - 1) * N ^ (-ρ) = (N ^ 2)⁻¹ := by
    rw [← Complex.cpow_add _ _ hn, show ρ - 1 - 1 + -ρ = -(2 : ℂ) by ring, Complex.cpow_neg]
    norm_cast
  rw [div_eq_mul_inv]
  linear_combination (-ρ) * e1 - (ρ - 1) * e2

end Cells

section ProfileDerivatives

lemma zeroProfile_eventually_cell (ρ : ℂ) {n : ℕ} {x : ℝ} (hx : x ∈ Ioo (n : ℝ) (n + 1)) :
    zeroProfile ρ =ᶠ[𝓝 x] fun y => 1 - srhoCell ρ n y / normalizationBrho ρ := by
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg n) hy.1.le
  rw [zeroProfile, abs_of_nonneg hy0, finiteSumSrho_eq_cell ρ (Ioo_subset_Ico_self hy)]

/-- h' inside every cell (n, n+1): the exact differentiated finite sums. -/
theorem hasDerivAt_zeroProfile_cell (ρ : ℂ) {n : ℕ} {x : ℝ} (hx : x ∈ Ioo (n : ℝ) (n + 1)) :
    HasDerivAt (zeroProfile ρ) (-(srhoCellDeriv ρ n x / normalizationBrho ρ)) x := by
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg n) hx.1
  exact (((hasDerivAt_srhoCell ρ n hx0).div_const _).const_sub 1).congr_of_eventuallyEq
    (zeroProfile_eventually_cell ρ hx)

/-- Right derivative at the integer m ≥ 1 uses the cell [m, m+1). -/
theorem hasDerivWithinAt_zeroProfile_right (ρ : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    HasDerivWithinAt (zeroProfile ρ) (-(srhoCellDeriv ρ m m / normalizationBrho ρ)) (Ici (m : ℝ)) m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  refine (((hasDerivAt_srhoCell ρ m hm0).div_const _).const_sub 1).hasDerivWithinAt.congr_of_eventuallyEq
    ?_ ?_
  · have hmem : Ico (m : ℝ) (m + 1) ∈ 𝓝[Ici (m : ℝ)] (m : ℝ) :=
      Ico_mem_nhdsGE (by linarith)
    filter_upwards [hmem] with y hy
    rw [zeroProfile, abs_of_nonneg (by linarith [hy.1]), finiteSumSrho_eq_cell ρ hy]
  · rw [zeroProfile, abs_of_nonneg hm0.le, finiteSumSrho_eq_cell ρ ⟨le_rfl, by linarith⟩]

/-- Left derivative at the integer n + 1 uses the cell [n, n+1); S_ρ is continuous at n + 1. -/
theorem hasDerivWithinAt_zeroProfile_left (ρ : ℂ) (n : ℕ) :
    HasDerivWithinAt (zeroProfile ρ) (-(srhoCellDeriv ρ n (n + 1 : ℕ) / normalizationBrho ρ))
      (Iic ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) := by
  have hm0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have key : ∀ y ∈ Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ), finiteSumSrho ρ y = srhoCell ρ n y := by
    intro y hy
    rcases lt_or_eq_of_le hy.2 with h | h
    · exact finiteSumSrho_eq_cell ρ ⟨hy.1.le, by rw [← hcast]; exact h⟩
    · rw [h, finiteSumSrho_eq_cell ρ (n := n + 1) ⟨le_rfl, by push_cast; linarith⟩,
        srhoCell_succ_eq]
  refine (((hasDerivAt_srhoCell ρ n hm0).div_const _).const_sub 1).hasDerivWithinAt.congr_of_eventuallyEq
    ?_ ?_
  · have hmem : Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ) ∈ 𝓝[Iic ((n + 1 : ℕ) : ℝ)] ((n + 1 : ℕ) : ℝ) :=
      Ioc_mem_nhdsLE (by rw [hcast]; linarith)
    filter_upwards [hmem] with y hy
    rw [zeroProfile, abs_of_nonneg (by linarith [hy.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]),
      key y hy]
  · rw [zeroProfile, abs_of_nonneg hm0.le, key _ ⟨by rw [hcast]; linarith, le_rfl⟩]

/-- h'(1-) = 0: the profile is constant on [-1, 1]. -/
lemma srhoCellDeriv_zero (ρ : ℂ) (y : ℝ) : srhoCellDeriv ρ 0 y = 0 := by
  simp [srhoCellDeriv, cellSumA, cellSumB]

/-- The jump h'(m+) - h'(m-) = -κ/m² at every integer m ≥ 1 (for b_ρ ≠ 0). -/
theorem zeroProfile_deriv_jump {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) (n : ℕ) :
    -(srhoCellDeriv ρ (n + 1) (n + 1 : ℕ) / normalizationBrho ρ) -
        -(srhoCellDeriv ρ n (n + 1 : ℕ) / normalizationBrho ρ) =
      -spectralKappa ρ / ((n + 1 : ℕ) : ℂ) ^ 2 := by
  have hk := kappa_div_brho h0 h1 hh
  have hj := srhoCellDeriv_jump ρ n
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
  have e : (1 - 2 * ρ) / normalizationBrho ρ = spectralKappa ρ := by
    rw [show (1 - 2 * ρ) = -(2 * ρ - 1) by ring, neg_div, hk, neg_neg]
  calc -(srhoCellDeriv ρ (n + 1) (n + 1 : ℕ) / normalizationBrho ρ) -
        -(srhoCellDeriv ρ n (n + 1 : ℕ) / normalizationBrho ρ)
      = -((srhoCellDeriv ρ (n + 1) (n + 1 : ℕ) - srhoCellDeriv ρ n (n + 1 : ℕ)) /
          normalizationBrho ρ) := by ring
    _ = -((1 - 2 * ρ) / normalizationBrho ρ) / ((n + 1 : ℕ) : ℂ) ^ 2 := by rw [hj]; ring
    _ = _ := by rw [e]

/-- Explicit remainder of the differentiated finite sums. -/
def srhoDerivRemainder (ρ : ℂ) (x : ℝ) : ℂ :=
  -ρ * (x : ℂ) ^ (-ρ - 1) * eulerMaclaurinRemainder (1 - ρ) x -
    (ρ - 1) * (x : ℂ) ^ (ρ - 1 - 1) * eulerMaclaurinRemainder ρ x

/-- Euler-Maclaurin form of the differentiated finite sums inside a cell, x ≥ 1: the 1/x and
B₂/x³ terms cancel. -/
theorem srhoCellDeriv_expansion {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {n : ℕ} {x : ℝ}
    (hx : x ∈ Ico (n : ℝ) (n + 1)) (hx1 : 1 ≤ x) :
    srhoCellDeriv ρ n x = -ρ * riemannZeta (1 - ρ) * (x : ℂ) ^ (-ρ - 1) -
      (ρ - 1) * riemannZeta ρ * (x : ℂ) ^ (ρ - 1 - 1) +
        (2 * ρ - 1) * (bernoulliOneRight x : ℂ) / (x : ℂ) ^ 2 + srhoDerivRemainder ρ x := by
  have hx0 : 0 < x := by linarith
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hσ0 : 0 < (1 - ρ).re := by simp; linarith
  have hσ1 : 1 - ρ ≠ 1 := fun h => hρ0 (by linear_combination -h)
  have hA : cellSumA ρ n = rightPowerSum (1 - ρ) x := by
    rw [rightPowerSum_of_mem_cell (1 - ρ) hx, cellSumA]
    refine Finset.sum_congr rfl (fun k _ => by rw [neg_sub])
  have hB : cellSumB ρ n = rightPowerSum ρ x := by
    rw [rightPowerSum_of_mem_cell ρ hx, cellSumB]
  have eA := rightPowerSum_expansion hσ0 hσ1 hx1
  have eB := rightPowerSum_expansion h0 hρ1 hx1
  have hv : (x : ℂ) ^ ρ ≠ 0 := (Complex.cpow_ne_zero_iff_of_exponent_ne_zero hρ0).mpr hxne
  have hneg : (x : ℂ) ^ (-ρ) = ((x : ℂ) ^ ρ)⁻¹ := Complex.cpow_neg _ _
  have p1 : (x : ℂ) ^ (1 - (1 - ρ)) = (x : ℂ) ^ ρ := by ring_nf
  have p2 : (x : ℂ) ^ (-(1 - ρ)) = (x : ℂ) ^ ρ / x := by
    rw [show -(1 - ρ) = ρ - 1 by ring, cpow_sub_one' hx0]
  have p3 : (x : ℂ) ^ (-(1 - ρ) - 1) = (x : ℂ) ^ ρ / x / x := by
    rw [cpow_sub_one' hx0, p2]
  have p4 : (x : ℂ) ^ (1 - ρ) = x * ((x : ℂ) ^ ρ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hxne, Complex.cpow_one, div_eq_mul_inv]
  have p5 : (x : ℂ) ^ (-ρ - 1) = ((x : ℂ) ^ ρ)⁻¹ / x := by rw [cpow_sub_one' hx0, hneg]
  have p6 : (x : ℂ) ^ (ρ - 1 - 1) = (x : ℂ) ^ ρ / x / x := by
    rw [cpow_sub_one' hx0, cpow_sub_one' hx0]
  have hs1 : (1 : ℂ) - (1 - ρ) = ρ := by ring
  have hs2 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  rw [srhoCellDeriv, hA, hB, eA, eB, srhoDerivRemainder, p1, p2, p3, p4, p5, p6, hneg, hs1]
  field_simp
  ring

/-- Explicit constant for the derivative remainder (x^(-4)). -/
def srhoDerivRemainderConst (ρ : ℂ) : ℝ :=
  ‖ρ‖ * (‖1 - ρ‖ * (‖1 - ρ‖ + 1) / 6 + ‖1 - ρ‖ * (‖1 - ρ‖ + 1) * (‖1 - ρ‖ + 2) / 12) +
    ‖ρ - 1‖ * (‖ρ‖ * (‖ρ‖ + 1) / 6 + ‖ρ‖ * (‖ρ‖ + 1) * (‖ρ‖ + 2) / 12)

lemma srhoDerivRemainder_norm_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {x : ℝ} (hx : 0 < x) :
    ‖srhoDerivRemainder ρ x‖ ≤ srhoDerivRemainderConst ρ * x ^ (-4 : ℝ) := by
  have hσ0 : 0 < (1 - ρ).re := by simp; linarith
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hA := eulerMaclaurinRemainder_norm_le hσ0 hx
  have hB := eulerMaclaurinRemainder_norm_le h0 hx
  have e1 : x ^ (-ρ - 1).re * x ^ (-(1 - ρ).re - 2) = x ^ (-4 : ℝ) := by
    rw [← Real.rpow_add hx]; congr 1; simp; ring
  have e2 : x ^ (ρ - 1 - 1).re * x ^ (-ρ.re - 2) = x ^ (-4 : ℝ) := by
    rw [← Real.rpow_add hx]; congr 1; simp; ring
  have hp1 : 0 ≤ x ^ (-ρ - 1).re := Real.rpow_nonneg hx.le _
  have hp2 : 0 ≤ x ^ (ρ - 1 - 1).re := Real.rpow_nonneg hx.le _
  unfold srhoDerivRemainderConst
  calc ‖ρ‖ * x ^ (-ρ - 1).re * ‖eulerMaclaurinRemainder (1 - ρ) x‖ +
        ‖ρ - 1‖ * x ^ (ρ - 1 - 1).re * ‖eulerMaclaurinRemainder ρ x‖
      ≤ ‖ρ‖ * x ^ (-ρ - 1).re * ((‖1 - ρ‖ * (‖1 - ρ‖ + 1) / 6 +
            ‖1 - ρ‖ * (‖1 - ρ‖ + 1) * (‖1 - ρ‖ + 2) / 12) * x ^ (-(1 - ρ).re - 2)) +
          ‖ρ - 1‖ * x ^ (ρ - 1 - 1).re * ((‖ρ‖ * (‖ρ‖ + 1) / 6 +
            ‖ρ‖ * (‖ρ‖ + 1) * (‖ρ‖ + 2) / 12) * x ^ (-ρ.re - 2)) := by gcongr
    _ = _ := by
        rw [mul_assoc ‖ρ‖, mul_left_comm (x ^ (-ρ - 1).re), e1, mul_assoc ‖ρ - 1‖,
          mul_left_comm (x ^ (ρ - 1 - 1).re), e2]; ring

end ProfileDerivatives

section Regularity

lemma mem_cell_of_not_nat {x : ℝ} (hx : 0 < x) (hn : x ∉ Set.range (fun n : ℕ => (n : ℝ))) :
    x ∈ Ioo (⌊x⌋₊ : ℝ) (⌊x⌋₊ + 1) := by
  refine ⟨lt_of_le_of_ne (Nat.floor_le hx.le) (fun h => hn ⟨_, h⟩), Nat.lt_floor_add_one x⟩

/-- The profile is continuous (finite sums glue continuously at every integer). -/
theorem continuous_zeroProfile (ρ : ℂ) : Continuous (zeroProfile ρ) := by
  have hpos : ∀ x : ℝ, 0 < x → ContinuousAt (zeroProfile ρ) x := by
    intro x hx
    by_cases hn : x ∈ Set.range (fun n : ℕ => (n : ℝ))
    · obtain ⟨m, rfl⟩ := hn
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp at hx
        · exact h
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      rw [continuousAt_iff_continuous_left_right]
      exact ⟨(hasDerivWithinAt_zeroProfile_left ρ n).continuousWithinAt,
        (hasDerivWithinAt_zeroProfile_right ρ hm).continuousWithinAt⟩
    · exact (hasDerivAt_zeroProfile_cell ρ (mem_cell_of_not_nat hx hn)).continuousAt
  have hzero : ContinuousAt (zeroProfile ρ) 0 := by
    refine (continuousAt_const (y := (1 : ℂ))).congr ?_
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with y hy
    rw [zeroProfile_eq_one ρ (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)]
  refine continuous_iff_continuousAt.mpr (fun x => ?_)
  rcases lt_trichotomy x 0 with h | h | h
  · have hc : ContinuousAt (fun y => zeroProfile ρ (-y)) x :=
      (hpos (-x) (by linarith)).comp continuous_neg.continuousAt
    exact hc.congr (Eventually.of_forall (fun y => zeroProfile_neg ρ y))
  · rw [h]; exact hzero
  · exact hpos x h

/-- At an actual zero, h'(x) = O(x^(-2)) inside every cell above 1. -/
theorem zeroProfile_deriv_bound {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {n : ℕ} {x : ℝ} (hx : x ∈ Ico (n : ℝ) (n + 1)) (hx1 : 1 ≤ x) :
    ‖srhoCellDeriv ρ n x / normalizationBrho ρ‖ ≤
      (‖2 * ρ - 1‖ + srhoDerivRemainderConst ρ) / ‖normalizationBrho ρ‖ * x ^ (-2 : ℝ) := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hz' : riemannZeta (1 - ρ) = 0 := by
    have hn : ∀ n : ℕ, ρ ≠ -n := fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [riemannZeta_one_sub hn hρ1, hz, mul_zero]
  have hx0 : 0 < x := by linarith
  rw [srhoCellDeriv_expansion h0 h1 hx hx1, hz, hz', norm_div, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
  have hB1 : ‖(bernoulliOneRight x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_bernoulliOneRight_le x
  have hx2 : ‖(x : ℂ) ^ 2‖ = x ^ (2 : ℝ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, Real.rpow_two]
  have hR := srhoDerivRemainder_norm_le h0 h1 hx0
  have h42 : x ^ (-4 : ℝ) ≤ x ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hinv : x ^ (-2 : ℝ) = (x ^ (2 : ℝ))⁻¹ := by rw [Real.rpow_neg hx0.le]
  have hDn : 0 ≤ srhoDerivRemainderConst ρ := by unfold srhoDerivRemainderConst; positivity
  have hpos2 : 0 < x ^ (2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  calc ‖-ρ * 0 * (x : ℂ) ^ (-ρ - 1) - (ρ - 1) * 0 * (x : ℂ) ^ (ρ - 1 - 1) +
        (2 * ρ - 1) * (bernoulliOneRight x : ℂ) / (x : ℂ) ^ 2 + srhoDerivRemainder ρ x‖
      ≤ ‖(2 * ρ - 1) * (bernoulliOneRight x : ℂ) / (x : ℂ) ^ 2‖ + ‖srhoDerivRemainder ρ x‖ := by
        simp only [mul_zero, zero_mul, sub_zero, zero_add]; exact norm_add_le _ _
    _ ≤ ‖2 * ρ - 1‖ * x ^ (-2 : ℝ) + srhoDerivRemainderConst ρ * x ^ (-2 : ℝ) := by
        gcongr
        · rw [norm_div, norm_mul, hx2, hinv, div_eq_mul_inv]
          gcongr
          exact mul_le_of_le_one_right (norm_nonneg _) hB1
        · exact hR.trans (mul_le_mul_of_nonneg_left h42 hDn)
    _ = _ := by ring

end Regularity

section Integrability

/-- At an actual zero, ‖h(x)‖ ≤ K/(1 + x²). -/
theorem zeroProfile_norm_le {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, ‖zeroProfile ρ x‖ ≤ K * (1 + x ^ 2)⁻¹ := by
  set C := srhoRemainderConst ρ / ‖normalizationBrho ρ‖ with hC
  have hC0 : 0 ≤ C := div_nonneg (srhoRemainderConst_nonneg ρ) (norm_nonneg _)
  set M := max 1 (‖spectralKappa ρ‖ / 2 + C)
  refine ⟨2 * M, by positivity, fun x => ?_⟩
  have hsq : 0 < 1 + x ^ 2 := by positivity
  rcases le_or_gt |x| 1 with hx | hx
  · rw [zeroProfile_eq_one ρ hx, norm_one]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
    rw [← div_eq_mul_inv, le_div_iff₀ hsq]
    nlinarith [le_max_left 1 (‖spectralKappa ρ‖ / 2 + C)]
  · have hx1 : 1 ≤ |x| := hx.le
    have ht := zeroProfile_tail hz h0 h1 hx1
    have hx2' : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    set y := |x| with hy
    have hy0 : 0 < y := by linarith
    have hmain : ‖spectralKappa ρ * (bernoulliTwo y : ℂ) / (2 * ((y : ℝ) : ℂ) ^ 2)‖ ≤
        ‖spectralKappa ρ‖ / 2 * y ^ (-2 : ℝ) := by
      have hB : abs (bernoulliTwo y) ≤ 1 := abs_bernoulliTwo_le _
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy0, Real.rpow_neg hy0.le, Real.rpow_two, h2]
      rw [div_le_iff₀ (by positivity)]
      calc ‖spectralKappa ρ‖ * abs (bernoulliTwo y) ≤ ‖spectralKappa ρ‖ * 1 :=
            mul_le_mul_of_nonneg_left hB (norm_nonneg _)
        _ = ‖spectralKappa ρ‖ / 2 * (y ^ 2)⁻¹ * (2 * y ^ 2) := by field_simp
    have h32 : y ^ (-3 : ℝ) ≤ y ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hbound : ‖zeroProfile ρ x‖ ≤ (‖spectralKappa ρ‖ / 2 + C) * y ^ (-2 : ℝ) := by
      calc ‖zeroProfile ρ x‖ ≤ ‖spectralKappa ρ * (bernoulliTwo y : ℂ) / (2 * ((y : ℝ) : ℂ) ^ 2)‖ +
            ‖zeroProfile ρ x - spectralKappa ρ * (bernoulliTwo y : ℂ) / (2 * ((y : ℝ) : ℂ) ^ 2)‖ :=
            norm_le_insert' _ _
        _ ≤ ‖spectralKappa ρ‖ / 2 * y ^ (-2 : ℝ) + C * y ^ (-2 : ℝ) := by
            gcongr; exact ht.trans (mul_le_mul_of_nonneg_left h32 hC0)
        _ = _ := by ring
    have hx2 : y ^ (-2 : ℝ) ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [Real.rpow_neg hy0.le, Real.rpow_two, hx2']
      have hy2 : 0 < y ^ 2 := by positivity
      rw [inv_le_iff_one_le_mul₀ hy2]
      rw [show 2 * (1 + y ^ 2)⁻¹ * y ^ 2 = 2 * y ^ 2 / (1 + y ^ 2) by ring]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    calc ‖zeroProfile ρ x‖ ≤ (‖spectralKappa ρ‖ / 2 + C) * y ^ (-2 : ℝ) := hbound
      _ ≤ M * (2 * (1 + x ^ 2)⁻¹) := by
          gcongr
          · exact le_max_right _ _
      _ = 2 * M * (1 + x ^ 2)⁻¹ := by ring

theorem integrable_zeroProfile {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    Integrable (zeroProfile ρ) := by
  obtain ⟨K, -, hK⟩ := zeroProfile_norm_le hz h0 h1
  refine (integrable_inv_one_add_sq.const_mul K).mono' (continuous_zeroProfile ρ).aestronglyMeasurable
    (Eventually.of_forall hK)

theorem memLp_two_zeroProfile {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    MemLp (zeroProfile ρ) 2 := by
  obtain ⟨K, hK0, hK⟩ := zeroProfile_norm_le hz h0 h1
  have hg : MemLp (fun x : ℝ => K * (1 + x ^ 2)⁻¹) 2 := by
    have hm : AEStronglyMeasurable (fun x : ℝ => K * (1 + x ^ 2)⁻¹) volume := by
      fun_prop
    refine (memLp_two_iff_integrable_sq hm).mpr ?_
    refine (integrable_inv_one_add_sq.const_mul (K ^ 2)).mono' (by fun_prop)
      (Eventually.of_forall (fun x => ?_))
    have hsq : 0 < 1 + x ^ 2 := by positivity
    have hinv : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
    have hinv0 : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (K * (1 + x ^ 2)⁻¹) ^ 2 = K ^ 2 * ((1 + x ^ 2)⁻¹ * (1 + x ^ 2)⁻¹) := by ring
      _ ≤ K ^ 2 * ((1 + x ^ 2)⁻¹ * 1) := by gcongr
      _ = K ^ 2 * (1 + x ^ 2)⁻¹ := by ring
  refine hg.of_le (continuous_zeroProfile ρ).aestronglyMeasurable (Eventually.of_forall (fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hK x

/-- x h'(x) ∈ L²(0, ∞) at an actual zero. -/
theorem memLp_two_mul_deriv_zeroProfile {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    MemLp (fun x : ℝ => (x : ℂ) * deriv (zeroProfile ρ) x) 2 (volume.restrict (Ioi 0)) := by
  set C := (‖2 * ρ - 1‖ + srhoDerivRemainderConst ρ) / ‖normalizationBrho ρ‖ with hC
  have hC0 : 0 ≤ C := by
    have : 0 ≤ srhoDerivRemainderConst ρ := by unfold srhoDerivRemainderConst; positivity
    positivity
  set g : ℝ → ℝ := (Ici (1 : ℝ)).indicator (fun x => C * x ^ (-1 : ℝ)) with hg
  have hgm : Measurable g := (Measurable.const_mul (by fun_prop) C).indicator measurableSet_Ici
  have hgL : MemLp g 2 (volume.restrict (Ioi 0)) := by
    refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr ?_
    have heq : (fun x => g x ^ 2) = (Ici (1 : ℝ)).indicator (fun x => C ^ 2 * x ^ (-2 : ℝ)) := by
      funext x
      by_cases hx : x ∈ Ici (1 : ℝ)
      · have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
        rw [hg, indicator_of_mem hx, indicator_of_mem hx, mul_pow,
          ← Real.rpow_natCast (x ^ (-1 : ℝ)) 2, ← Real.rpow_mul hx0.le]
        norm_num
      · rw [hg, indicator_of_notMem hx, indicator_of_notMem hx]; simp
    rw [heq]
    refine (Integrable.mono_measure ?_ Measure.restrict_le_self)
    refine (integrable_indicator_iff measurableSet_Ici).mpr ?_
    exact ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)).const_mul _
  refine hgL.of_le ((Complex.measurable_ofReal.mul (measurable_deriv _)).aestronglyMeasurable) ?_
  have hnull : volume (Set.range (fun n : ℕ => (n : ℝ))) = 0 :=
    (Set.countable_range _).measure_zero _
  have hae : ∀ᵐ x ∂(volume.restrict (Ioi 0)), x ∉ Set.range (fun n : ℕ => (n : ℝ)) :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hnull)
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with x hxn hx0
  have hx0' : 0 < x := hx0
  have hcell := mem_cell_of_not_nat hx0' hxn
  rw [(hasDerivAt_zeroProfile_cell ρ hcell).deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx0', norm_neg]
  rcases lt_or_ge x 1 with hx1 | hx1
  · have hf : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
    rw [hf, srhoCellDeriv_zero, zero_div, norm_zero, mul_zero]
    exact norm_nonneg _
  · have hb := zeroProfile_deriv_bound hz h0 h1 (Ioo_subset_Ico_self hcell) hx1
    have hgx : g x = C * x ^ (-1 : ℝ) := by rw [hg, indicator_of_mem (show x ∈ Ici 1 from hx1)]
    rw [hgx, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc x * ‖srhoCellDeriv ρ ⌊x⌋₊ x / normalizationBrho ρ‖ ≤ x * (C * x ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hb hx0'.le
      _ = C * x ^ (-1 : ℝ) := by
          rw [mul_left_comm, ← Real.rpow_one_add' hx0'.le (by norm_num)]
          norm_num

end Integrability

section SelfDual

lemma zeroProfile_eq_one_sub_density {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (x : ℝ) :
    zeroProfile ρ x = 1 - coPoissonComplexDensity ρ x := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  rw [zeroProfile, coPoissonComplexDensity, coPoissonOriginNormalizer_eq_brho hρ0 hρ1]

lemma integrable_zeroProfile_mul {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : 𝓢(ℝ, ℂ)) : Integrable (fun x => zeroProfile ρ x * φ x) := by
  obtain ⟨K, hK0, hK⟩ := zeroProfile_norm_le hz h0 h1
  refine (φ.integrable.norm.const_mul K).mono'
    ((continuous_zeroProfile ρ).aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable)
    (Eventually.of_forall (fun x => ?_))
  rw [norm_mul]
  have hinv : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
  have hb : ‖zeroProfile ρ x‖ ≤ K :=
    (hK x).trans (by nlinarith [inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 1 + x ^ 2)])
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- The profile pairing through the actual zero measure, the Lebesgue functional and the comb. -/
lemma zeroProfile_pairing {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : 𝓢(ℝ, ℂ)) : (∫ x, zeroProfile ρ x * φ x) =
      (∫ x, φ x) - (zeroMeasure ρ).integral φ - dilatedCombDistribution 0 φ + φ 0 := by
  have hI := integrable_zeroProfile_mul hz h0 h1 φ
  have hsplit : (fun x => coPoissonComplexDensity ρ x * φ x) =
      fun x => φ x - zeroProfile ρ x * φ x := by
    funext x; rw [zeroProfile_eq_one_sub_density h0 h1]; ring
  have hg : (∫ x, coPoissonComplexDensity ρ x * φ x) = (∫ x, φ x) - ∫ x, zeroProfile ρ x * φ x := by
    rw [hsplit, integral_sub φ.integrable hI]
  have hD : dilatedCombDistribution 0 φ = φ 0 + ∑' n : ℤ, if n = 0 then (0 : ℂ) else φ n := by
    have hA := coPoissonA_apply 0 φ
    rw [coPoissonA, sub_apply, smul_apply, TemperedDistribution.delta_apply] at hA
    simp only [zero_div, Real.exp_zero, Complex.ofReal_one, one_smul, one_mul] at hA
    rw [← hA]; ring
  rw [zeroMeasure_integral h0 h1, hg, hD]
  ring

/-- Pairing-level Fourier self-duality of the profile. -/
theorem zeroProfile_pairing_fourier {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : 𝓢(ℝ, ℂ)) : (∫ x, zeroProfile ρ x * (𝓕 φ : 𝓢(ℝ, ℂ)) x) = ∫ x, zeroProfile ρ x * φ x := by
  have hh := zero_ne_half hz
  rw [zeroProfile_pairing hz h0 h1, zeroProfile_pairing hz h0 h1, schwartz_integral_fourier,
    zeroMeasure_integral_fourier hz h0 h1 hh, dilatedCombDistribution_zero_fourier,
    schwartz_fourier_zero]
  ring

lemma integral_fourier_mul_eq_of_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ x, 𝓕 f x * g x = ∫ x, f x * 𝓕 g x := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ)
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hg

/-- Ordinary Fourier self-duality 𝓕h = h of the L¹ continuous profile. -/
theorem fourier_zeroProfile {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    𝓕 (zeroProfile ρ) = zeroProfile ρ := by
  have hI := integrable_zeroProfile hz h0 h1
  have hFc : Continuous (𝓕 (zeroProfile ρ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hI
  have hc := continuous_zeroProfile ρ
  have key : ∀ φ : 𝓢(ℝ, ℂ), ∫ x, (𝓕 (zeroProfile ρ) x - zeroProfile ρ x) * φ x = 0 := by
    intro φ
    have hm := integral_fourier_mul_eq_of_integrable hI φ.integrable
    have hp := zeroProfile_pairing_fourier hz h0 h1 φ
    have hint1 : Integrable (fun x => 𝓕 (zeroProfile ρ) x * φ x) := by
      have hb : ∀ x, ‖𝓕 (zeroProfile ρ) x‖ ≤ ∫ y, ‖zeroProfile ρ y‖ := fun x => by
        rw [Real.fourier_real_eq]
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        simp_rw [Circle.norm_smul]
      refine (φ.integrable.norm.const_mul (∫ y, ‖zeroProfile ρ y‖)).mono'
        (hFc.aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable)
        (Eventually.of_forall (fun x => ?_))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
    rw [show (fun x => (𝓕 (zeroProfile ρ) x - zeroProfile ρ x) * φ x) =
        fun x => 𝓕 (zeroProfile ρ) x * φ x - zeroProfile ρ x * φ x by funext x; ring,
      integral_sub hint1 (integrable_zeroProfile_mul hz h0 h1 φ), hm]
    rw [← hp]
    simp [SchwartzMap.fourier_coe]
  have hae : ∀ᵐ x, 𝓕 (zeroProfile ρ) x - zeroProfile ρ x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (hFc.sub hc).locallyIntegrable
      (fun g hg hgs => ?_)
    have hgc : HasCompactSupport (fun x => (g x : ℂ)) := hgs.comp_left Complex.ofReal_zero
    have hgd : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have := key (hgc.toSchwartzMap hgd)
    calc ∫ x, g x • (𝓕 (zeroProfile ρ) x - zeroProfile ρ x) =
          ∫ x, (𝓕 (zeroProfile ρ) x - zeroProfile ρ x) * (hgc.toSchwartzMap hgd) x := by
          congr 1; funext x; rw [Complex.real_smul, mul_comm]; rfl
      _ = 0 := this
  have hfun : (fun x => 𝓕 (zeroProfile ρ) x - zeroProfile ρ x) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq volume (hFc.sub hc) continuous_const).mp hae
  funext x
  have := congrFun hfun x
  exact sub_eq_zero.mp this

theorem integral_zeroProfile {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∫ x, zeroProfile ρ x = 1 := by
  have h := congrFun (fourier_zeroProfile hz h0 h1) 0
  rw [Real.fourier_real_eq] at h
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul] at h
  rw [h, zeroProfile_eq_one ρ (by simp)]

theorem integral_Ioi_zeroProfile {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∫ x in Ioi (0 : ℝ), zeroProfile ρ x = 1 / 2 := by
  have hI := integrable_zeroProfile hz h0 h1
  have hsum := intervalIntegral.integral_Iic_add_Ioi (b := 0) hI.integrableOn hI.integrableOn
  have hneg : (∫ x in Iic (0 : ℝ), zeroProfile ρ x) = ∫ x in Ioi (0 : ℝ), zeroProfile ρ x := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    simp only [neg_zero, zeroProfile_neg]
  rw [hneg, integral_zeroProfile hz h0 h1] at hsum
  linear_combination hsum / 2

end SelfDual

section Roots

/-- R2-S1a: the zero profile h = 1 - S_ρ/b_ρ at an actual zero 0 < Re ρ < 1 is even, continuous,
in L¹ ∩ L², equal to 1 on [-1, 1], Fourier self-dual (ordinarily and on Schwartz pairings), with
∫ h = h(0) = 1 and half-line integral 1/2; ν_ρ = (dx + δ₀ - D₀) - h dx on Schwartz tests. -/
theorem zero_profile_regular_selfdual (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    (∀ x : ℝ, zeroProfile ρ (-x) = zeroProfile ρ x) ∧
    Continuous (zeroProfile ρ) ∧
    Integrable (zeroProfile ρ) ∧ MemLp (zeroProfile ρ) 2 ∧
    (∀ x : ℝ, |x| ≤ 1 → zeroProfile ρ x = 1) ∧
    𝓕 (zeroProfile ρ) = zeroProfile ρ ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∫ x, zeroProfile ρ x * (𝓕 φ : 𝓢(ℝ, ℂ)) x) = ∫ x, zeroProfile ρ x * φ x) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (zeroMeasure ρ).integral φ =
      (∫ x, φ x) + φ 0 - dilatedCombDistribution 0 φ - ∫ x, zeroProfile ρ x * φ x) ∧
    (∫ x, zeroProfile ρ x) = 1 ∧
    (∫ x in Ioi (0 : ℝ), zeroProfile ρ x) = 1 / 2 := by
  refine ⟨zeroProfile_neg ρ, continuous_zeroProfile ρ, integrable_zeroProfile hz h0 h1,
    memLp_two_zeroProfile hz h0 h1, fun x hx => zeroProfile_eq_one ρ hx,
    fourier_zeroProfile hz h0 h1, zeroProfile_pairing_fourier hz h0 h1, fun φ => ?_,
    integral_zeroProfile hz h0 h1, integral_Ioi_zeroProfile hz h0 h1⟩
  rw [zeroProfile_pairing hz h0 h1]; ring

/-- R2-S1a: at an actual zero, h = κ B₂({x})/(2x²) + O(x⁻³); the exact differentiated finite sums
give h' inside every cell, h' = O(x⁻²) between integers (with leading term κ B₁({x})/x² and
remainder O(x⁻⁴)), the one-sided derivatives jump by -κ/n² at every integer n ≥ 1 with
h'(1-) = 0, and x h' ∈ L²(0, ∞). -/
theorem zero_profile_tail_and_jumps (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖zeroProfile ρ x - spectralKappa ρ * (bernoulliTwo |x| : ℂ) / (2 * ((|x| : ℝ) : ℂ) ^ 2)‖ ≤
        C * |x| ^ (-3 : ℝ)) ∧
    (∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) →
      HasDerivAt (zeroProfile ρ) (-(srhoCellDeriv ρ n x / normalizationBrho ρ)) x) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) → 1 ≤ x →
      ‖deriv (zeroProfile ρ) x‖ ≤ C * x ^ (-2 : ℝ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) → 1 ≤ x →
      ‖deriv (zeroProfile ρ) x - spectralKappa ρ * (bernoulliOneRight x : ℂ) / (x : ℂ) ^ 2‖ ≤
        C * x ^ (-4 : ℝ)) ∧
    (∀ n : ℕ, ∃ dR dL : ℂ,
      HasDerivWithinAt (zeroProfile ρ) dR (Ici ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) ∧
      HasDerivWithinAt (zeroProfile ρ) dL (Iic ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) ∧
      dR - dL = -spectralKappa ρ / ((n + 1 : ℕ) : ℂ) ^ 2) ∧
    HasDerivWithinAt (zeroProfile ρ) 0 (Iic (1 : ℝ)) 1 ∧
    MemLp (fun x : ℝ => (x : ℂ) * deriv (zeroProfile ρ) x) 2 (volume.restrict (Ioi 0)) := by
  have hh := zero_ne_half hz
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
  have hDn : 0 ≤ srhoDerivRemainderConst ρ := by unfold srhoDerivRemainderConst; positivity
  refine ⟨⟨_, div_nonneg (srhoRemainderConst_nonneg ρ) (norm_nonneg _),
      fun x hx => zeroProfile_tail hz h0 h1 hx⟩,
    fun n x hx => hasDerivAt_zeroProfile_cell ρ hx,
    ⟨(‖2 * ρ - 1‖ + srhoDerivRemainderConst ρ) / ‖normalizationBrho ρ‖, by positivity,
      fun n x hx hx1 => ?_⟩,
    ⟨srhoDerivRemainderConst ρ / ‖normalizationBrho ρ‖, by positivity, fun n x hx hx1 => ?_⟩,
    fun n => ⟨_, _, hasDerivWithinAt_zeroProfile_right ρ (by omega),
      hasDerivWithinAt_zeroProfile_left ρ n, zeroProfile_deriv_jump h0 h1 hh n⟩, ?_,
    memLp_two_mul_deriv_zeroProfile hz h0 h1⟩
  · rw [(hasDerivAt_zeroProfile_cell ρ hx).deriv, norm_neg]
    exact zeroProfile_deriv_bound hz h0 h1 (Ioo_subset_Ico_self hx) hx1
  · have hz' : riemannZeta (1 - ρ) = 0 := by
      have hn : ∀ n : ℕ, ρ ≠ -n := fun n h => by
        have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [riemannZeta_one_sub hn hρ1, hz, mul_zero]
    have hk := kappa_div_brho h0 h1 hh
    rw [(hasDerivAt_zeroProfile_cell ρ hx).deriv,
      srhoCellDeriv_expansion h0 h1 (Ioo_subset_Ico_self hx) hx1, hz, hz']
    have he : -((-ρ * 0 * (x : ℂ) ^ (-ρ - 1) - (ρ - 1) * 0 * (x : ℂ) ^ (ρ - 1 - 1) +
        (2 * ρ - 1) * (bernoulliOneRight x : ℂ) / (x : ℂ) ^ 2 + srhoDerivRemainder ρ x) /
          normalizationBrho ρ) - spectralKappa ρ * (bernoulliOneRight x : ℂ) / (x : ℂ) ^ 2 =
        -(srhoDerivRemainder ρ x / normalizationBrho ρ) := by
      rw [show spectralKappa ρ = -((2 * ρ - 1) / normalizationBrho ρ) by rw [hk]; ring]
      field_simp
      ring
    rw [he, norm_neg, norm_div, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (srhoDerivRemainder_norm_le h0 h1 (by linarith))
      (norm_nonneg _)
  · have h := hasDerivWithinAt_zeroProfile_left ρ 0
    simp only [srhoCellDeriv_zero, zero_div, neg_zero, zero_add, Nat.cast_one] at h
    exact h

end Roots

end Zeta23.OPICAFollowup
