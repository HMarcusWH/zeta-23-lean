import Zeta23.CCM.CanonicalContactOverlapSign
import Zeta23.CCM.CanonicalGroundContinuity

noncomputable section

/-!
# M31 (Step 66): Grönwall contact barrier, abstract and canonical (CONDITIONAL)

**Abstract Grönwall lower bound.**  If `y` is continuous on `[a, b]`,
differentiable inside, `C` is continuous, and `y' ≥ -C y` inside, then
`y(t) ≥ y(a) exp(-∫ₐᵗ C)` on `[a, b]`; in particular `y > 0` throughout when
`y(a) > 0`.

**Canonical barrier.**  For `K = N + 1 ≥ 2`, on an aperture interval
`[L₀, L₁] ⊂ (0, ∞)` where the odd bottom is positive and the even bottom is
positive at `L₀`, suppose a real function `y` satisfies the determinant relation
`det A_L = det B_L · y(L)` (so `y = 1 - T_L`, the secular margin) and the
Grönwall inequality `y' ≥ -C y` for a continuous `C`.  Then the even bottom stays
positive on `[L₀, L₁]`: there is no strict-even contact in the interval.

**This is a conditional theorem.**  The inequality `y' ≥ -C y`, i.e. the plan's
(67.1) `T' ≤ C (1 - T)`, is a hypothesis.  It is OPEN for the canonical
operator (M32), and `C` must be built independently of `T'/(1-T)`, of
`det A_L`, of the absence of contacts, of F04-only shortcuts and of RH, with
integrability through any hypothetical contact.  Nothing here proves such a
`C` exists, and nothing here is an unconditional exclusion.  Firewalls: the
operator start `A_{L₀} ≻ 0` is a separate hypothesis (it is not inferred from a
physical-test positivity); `T ≤ 1` is never used to infer positivity; `D` is not
assumed unitary; `A_L` is not the scalar `𝓐_L`.
-/

namespace Zeta23.CCM

open Set MeasureTheory

/-! ## Abstract Grönwall lower bound -/

/-- **M31, abstract.**  `y' ≥ -C y` on `(a, b)` with `C` continuous gives
`y(t) ≥ y(a) exp(-∫ₐᵗ C)` on `[a, b]`. -/
theorem gronwall_lower_bound {y y' C : ℝ → ℝ} {a b : ℝ} (hC : Continuous C)
    (hy : ContinuousOn y (Icc a b)) (hderiv : ∀ t ∈ Ioo a b, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Ioo a b, -(C t * y t) ≤ y' t) :
    ∀ t ∈ Icc a b, y a * Real.exp (-∫ s in a..t, C s) ≤ y t := by
  set G : ℝ → ℝ := fun t => ∫ s in a..t, C s with hG
  have hGd : ∀ t, HasDerivAt G (C t) t := fun t => (hC.integral_hasStrictDerivAt a t).hasDerivAt
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun t => (hGd t).continuousAt
  set φ : ℝ → ℝ := fun t => y t * Real.exp (G t) with hφ
  have hφd : ∀ t ∈ Ioo a b,
      HasDerivAt φ (y' t * Real.exp (G t) + y t * (Real.exp (G t) * C t)) t := fun t ht =>
    (hderiv t ht).mul ((hGd t).exp)
  have hmono : MonotoneOn φ (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact hy.mul (Real.continuous_exp.comp hGc).continuousOn
    · rw [interior_Icc]
      exact fun t ht => (hφd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hφd t ht).deriv]
      have he := Real.exp_pos (G t)
      have h := hineq t ht
      nlinarith
  intro t ht
  have hat : a ≤ t := ht.1
  have h := hmono ⟨le_rfl, hat.trans ht.2⟩ ht hat
  simp only [hφ, hG, intervalIntegral.integral_same, Real.exp_zero, mul_one] at h
  have he := Real.exp_pos (∫ s in a..t, C s)
  rw [Real.exp_neg]
  rw [← div_le_iff₀ he] at h
  simpa [div_eq_mul_inv] using h

/-- Positivity propagates: `y(a) > 0` and `y' ≥ -C y` give `y > 0` on `[a, b]`. -/
theorem gronwall_pos {y y' C : ℝ → ℝ} {a b : ℝ} (hC : Continuous C)
    (hy : ContinuousOn y (Icc a b)) (hderiv : ∀ t ∈ Ioo a b, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Ioo a b, -(C t * y t) ≤ y' t) (ha : 0 < y a) :
    ∀ t ∈ Icc a b, 0 < y t := fun t ht =>
  lt_of_lt_of_le (mul_pos ha (Real.exp_pos _)) (gronwall_lower_bound hC hy hderiv hineq t ht)

/-! ## Canonical barrier (conditional on the Grönwall inequality) -/

section Canonical

variable {N : ℕ}

theorem oddCompressedCanonical_det_ne_zero {L : ℝ} {K : ℕ}
    (hpos : 0 < parityRayleighBottom .odd L K) :
    LinearMap.det (oddCompressedCanonical L K) ≠ 0 := by
  obtain ⟨r, hr, hdet⟩ := exists_det_eq_ofReal_pos_of_coercive
    (T := oddCompressedCanonical L K) (parityCompressedCanonical_isSymmetric .odd L K) hpos
    (oddCompressedCanonical_coercive L K)
  rw [hdet]
  exact_mod_cast hr.ne'

theorem evenCompressedCanonical_det_eq_zero_of_bottom_eq_zero {L : ℝ} (hN : 1 ≤ N)
    (h0 : parityRayleighBottom .even L (N + 1) = 0) :
    LinearMap.det (evenCompressedCanonical L (N + 1)) = 0 := by
  obtain ⟨v, hv, hAv⟩ := exists_eigenmode_at_parityRayleighBottom_succ .even L N hN
  rw [h0, Complex.ofReal_zero, zero_smul] at hAv
  by_contra hdet
  have hunit : IsUnit (evenCompressedCanonical L (N + 1)) :=
    LinearMap.isUnit_iff_isUnit_det _ |>.mpr (Ne.isUnit hdet)
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot'] at hunit
  exact hv (hunit v hAv)

/-- **M31, canonical barrier (CONDITIONAL).**  With the odd bottom positive on
`[L₀, L₁]`, the even bottom positive at `L₀`, and a real secular margin `y`
(`det A_L = det B_L · y(L)`) obeying the Grönwall inequality `y' ≥ -C y` for a
continuous `C`, the even bottom stays positive on `[L₀, L₁]`.  The inequality is
the OPEN (67.1); this theorem does not assert it. -/
theorem canonical_evenBottom_pos_of_gronwall (hN : 1 ≤ N) {L₀ L₁ : ℝ} (hL₀ : 0 < L₀)
    (hodd : ∀ L ∈ Icc L₀ L₁, 0 < parityRayleighBottom .odd L (N + 1))
    (heven : 0 < parityRayleighBottom .even L₀ (N + 1))
    {y y' C : ℝ → ℝ} (hC : Continuous C)
    (hdet : ∀ L ∈ Icc L₀ L₁, LinearMap.det (evenCompressedCanonical L (N + 1)) =
      LinearMap.det (oddCompressedCanonical L (N + 1)) * (y L : ℂ))
    (hy : ContinuousOn y (Icc L₀ L₁)) (hderiv : ∀ L ∈ Ioo L₀ L₁, HasDerivAt y (y' L) L)
    (hineq : ∀ L ∈ Ioo L₀ L₁, -(C L * y L) ≤ y' L) :
    ∀ L ∈ Icc L₀ L₁, 0 < parityRayleighBottom .even L (N + 1) := by
  by_cases hL : L₀ ≤ L₁
  swap
  · intro L hL'
    exact absurd (hL'.1.trans hL'.2) hL
  -- the margin starts positive: both determinants are real and positive at `L₀`
  have hy0 : 0 < y L₀ := by
    obtain ⟨a, ha, hA⟩ := exists_det_eq_ofReal_pos_of_coercive
      (T := evenCompressedCanonical L₀ (N + 1))
      (parityCompressedCanonical_isSymmetric .even L₀ (N + 1)) heven
      (evenCompressedCanonical_coercive L₀ (N + 1))
    obtain ⟨b, hb, hB⟩ := exists_det_eq_ofReal_pos_of_coercive
      (T := oddCompressedCanonical L₀ (N + 1))
      (parityCompressedCanonical_isSymmetric .odd L₀ (N + 1)) (hodd L₀ ⟨le_rfl, hL⟩)
      (oddCompressedCanonical_coercive L₀ (N + 1))
    have h := hdet L₀ ⟨le_rfl, hL⟩
    rw [hA, hB] at h
    have hy : (y L₀ : ℂ) = ((a / b : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hb.ne'), mul_comm]
      exact h.symm
    have := Complex.ofReal_injective hy
    rw [this]
    exact div_pos ha hb
  have hypos := gronwall_pos hC hy hderiv hineq hy0
  -- an interior zero of the even bottom would make `det A_L = 0`
  intro L hLI
  by_contra hnot
  push Not at hnot
  have hcont : ContinuousOn (fun L => parityRayleighBottom .even L (N + 1)) (Icc L₀ L) :=
    (continuousOn_parityRayleighBottom_succ_Ioi .even N hN).mono fun t ht =>
      lt_of_lt_of_le hL₀ ht.1
  obtain ⟨L', hL', hzero⟩ := intermediate_value_Icc' hLI.1 hcont ⟨hnot, heven.le⟩
  have hL'I : L' ∈ Icc L₀ L₁ := ⟨hL'.1, hL'.2.trans hLI.2⟩
  have hA0 := evenCompressedCanonical_det_eq_zero_of_bottom_eq_zero hN hzero
  have hB0 := oddCompressedCanonical_det_ne_zero (hodd L' hL'I)
  have h := hdet L' hL'I
  rw [hA0] at h
  have hy' : (y L' : ℂ) ≠ 0 := by exact_mod_cast (hypos L' hL'I).ne'
  exact mul_ne_zero hB0 hy' h.symm

end Canonical

end Zeta23.CCM

#print axioms Zeta23.CCM.gronwall_lower_bound
#print axioms Zeta23.CCM.gronwall_pos
#print axioms Zeta23.CCM.evenCompressedCanonical_det_eq_zero_of_bottom_eq_zero
#print axioms Zeta23.CCM.canonical_evenBottom_pos_of_gronwall
