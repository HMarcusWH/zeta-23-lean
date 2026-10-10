import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace Zeta23.CCM

open Finset
open scoped BigOperators

/-!
# POST284-M11: local strict-even prime-seam dichotomy (abstract form)

Abstract crossing classification for a frozen background `s₋` with a degree-9
expansion `∑_{k<10} c_k h^k + O(h^10)` near the seam `h = 0`, and the entering
continuation `s₊(h) = s₋(h) - α h^9 + O(h^10)` with `α > 0` (the sign supplied by
the entering prime at a strict-even contact, M10).

Hypotheses: contact `c₀ = 0`, stationarity `c₁ = 0`, left nonnegativity of
`s₋` and right negativity of `s₊` at arbitrarily small `h > 0`.

* LOW: if some `c_k ≠ 0` with `k < 9`, the first such `k` lies in `{3,5,7}`
  and `c_k < 0`.
* HIGH: if `c_k = 0` for every `k < 9`, then `c₉ ≤ 0`, `c₉ - α < 0`, and `s₊`
  is negative on a full right interval.

This classifies possible crossing mechanisms; it does not exclude them, and the
expansion/continuation hypotheses are premises (real analyticity of the frozen
canonical branch and the M10 ninth-order perturbation are OPEN).
-/

/-- Degree-9 polynomial part. -/
def seamPoly (c : ℕ → ℝ) (h : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 10, c k * h ^ k

/-- Below `|h| ≤ 1`, the part of `seamPoly` above a vanishing prefix is
`O(|h|^(k+1))` after removing the leading term. -/
theorem abs_seamPoly_sub_leading_le (c : ℕ → ℝ) {k : ℕ} (hk : k < 10)
    (hlow : ∀ j, j < k → c j = 0) {h : ℝ} (h1 : |h| ≤ 1) :
    |seamPoly c h - c k * h ^ k| ≤
      (∑ j ∈ Finset.range 10, |c j|) * |h| ^ (k + 1) := by
  unfold seamPoly
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hk), add_sub_cancel_left]
  calc |∑ j ∈ (Finset.range 10).erase k, c j * h ^ j|
      ≤ ∑ j ∈ (Finset.range 10).erase k, |c j * h ^ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ (Finset.range 10).erase k, |c j| * |h| ^ (k + 1) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_pow]
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hjk | hjk
        · rw [hlow j hjk]
          simp
        · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact pow_le_pow_of_le_one (abs_nonneg h) h1 (by omega)
    _ ≤ ∑ j ∈ Finset.range 10, |c j| * |h| ^ (k + 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro j _ _
        positivity
    _ = (∑ j ∈ Finset.range 10, |c j|) * |h| ^ (k + 1) := by
        rw [Finset.sum_mul]

/-- Leading-term domination: near `0` the first nonzero coefficient controls
the sign of any function with the expansion. -/
theorem abs_sub_leading_lt (c : ℕ → ℝ) {k : ℕ} (hk : k < 10) (hck : c k ≠ 0)
    (hlow : ∀ j, j < k → c j = 0) {C : ℝ} (hC : 0 ≤ C) {f h : ℝ}
    (hh0 : h ≠ 0) (h1 : |h| ≤ 1)
    (hsmall : (C + ∑ j ∈ Finset.range 10, |c j|) * |h| < |c k|)
    (hf : |f - seamPoly c h| ≤ C * |h| ^ 10) :
    |f - c k * h ^ k| < |c k| * |h| ^ k := by
  have hpoly := abs_seamPoly_sub_leading_le c hk hlow h1
  have hhpos : 0 < |h| := abs_pos.mpr hh0
  have hpow10 : |h| ^ 10 ≤ |h| ^ (k + 1) :=
    pow_le_pow_of_le_one (abs_nonneg h) h1 (by omega)
  have htri : |f - c k * h ^ k| ≤ |f - seamPoly c h| + |seamPoly c h - c k * h ^ k| := by
    have := abs_sub_le f (seamPoly c h) (c k * h ^ k)
    linarith
  have hkpos : 0 < |h| ^ k := pow_pos hhpos k
  have hbound : |f - c k * h ^ k| ≤
      (C + ∑ j ∈ Finset.range 10, |c j|) * |h| * |h| ^ k := by
    have hC10 : C * |h| ^ 10 ≤ C * |h| ^ (k + 1) := mul_le_mul_of_nonneg_left hpow10 hC
    have heq : (C + ∑ j ∈ Finset.range 10, |c j|) * |h| * |h| ^ k =
        C * |h| ^ (k + 1) + (∑ j ∈ Finset.range 10, |c j|) * |h| ^ (k + 1) := by
      rw [pow_succ]; ring
    linarith
  calc |f - c k * h ^ k| ≤ (C + ∑ j ∈ Finset.range 10, |c j|) * |h| * |h| ^ k := hbound
    _ < |c k| * |h| ^ k := mul_lt_mul_of_pos_right hsmall hkpos

/-- Sign transfer: `f` has the strict sign of `c_k h^k`. -/
theorem sign_of_leading {f a b : ℝ} (hab : |f - a| < b) (hb : b = |a|) :
    (0 < a → 0 < f) ∧ (a < 0 → f < 0) := by
  rw [hb] at hab
  constructor
  · intro ha
    rw [abs_of_pos ha] at hab
    have := neg_abs_le (f - a)
    linarith [abs_lt.mp hab]
  · intro ha
    rw [abs_of_neg ha] at hab
    linarith [abs_lt.mp hab]

/-- Coefficients of the entering continuation `s₋ - α h^9`. -/
def enteringCoeff (c : ℕ → ℝ) (α : ℝ) (k : ℕ) : ℝ :=
  if k = 9 then c k - α else c k

theorem seamPoly_enteringCoeff (c : ℕ → ℝ) (α h : ℝ) :
    seamPoly (enteringCoeff c α) h = seamPoly c h - α * h ^ 9 := by
  unfold seamPoly enteringCoeff
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp
  ring

/-- Existence of a uniform small interval on which leading-term domination
holds. -/
theorem exists_leading_radius (c : ℕ → ℝ) {k : ℕ} (hck : c k ≠ 0) {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ ε > 0, ε ≤ δ ∧ ε ≤ 1 ∧ ∀ h, |h| < ε →
      (C + ∑ j ∈ Finset.range 10, |c j|) * |h| < |c k| := by
  set M := C + ∑ j ∈ Finset.range 10, |c j| with hM
  have hMnn : 0 ≤ M := by
    rw [hM]
    exact add_nonneg hC (Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hck' : 0 < |c k| := abs_pos.mpr hck
  refine ⟨min δ (min 1 (|c k| / (M + 1))), ?_, min_le_left _ _,
    le_trans (min_le_right _ _) (min_le_left _ _), ?_⟩
  · apply lt_min hδ (lt_min one_pos (div_pos hck' (by linarith)))
  · intro h hh
    have h3 : |h| < |c k| / (M + 1) :=
      lt_of_lt_of_le hh (le_trans (min_le_right _ _) (min_le_right _ _))
    have hM1 : 0 < M + 1 := by linarith
    rw [lt_div_iff₀ hM1] at h3
    nlinarith [abs_nonneg h]

/-- **Abstract strict-even prime-seam dichotomy (M11).** -/
theorem strictEven_seam_dichotomy
    (sm sp : ℝ → ℝ) (c : ℕ → ℝ) {α C δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hc0 : c 0 = 0) (hc1 : c 1 = 0)
    (hm : ∀ h, |h| ≤ δ → |sm h - seamPoly c h| ≤ C * |h| ^ 10)
    (hp : ∀ h, 0 ≤ h → h ≤ δ → |sp h - (seamPoly c h - α * h ^ 9)| ≤ C * |h| ^ 10)
    (hleft : ∀ h, -δ ≤ h → h < 0 → 0 ≤ sm h)
    (hright : ∀ ε > 0, ∃ h, 0 < h ∧ h < ε ∧ sp h < 0) :
    (∀ k, k < 9 → c k ≠ 0 → (∀ j, j < k → c j = 0) →
        (k = 3 ∨ k = 5 ∨ k = 7) ∧ c k < 0) ∧
      ((∀ k, k < 9 → c k = 0) →
        c 9 ≤ 0 ∧ c 9 - α < 0 ∧ ∃ ε > 0, ∀ h, 0 < h → h < ε → sp h < 0) := by
  constructor
  · intro k hk9 hck hlow
    -- the entering coefficients agree with `c` below `9`
    have hck' : enteringCoeff c α k = c k := by simp [enteringCoeff, show k ≠ 9 by omega]
    have hlow' : ∀ j, j < k → enteringCoeff c α j = 0 := by
      intro j hj
      simp [enteringCoeff, show j ≠ 9 by omega, hlow j hj]
    -- right side: c_k < 0
    obtain ⟨εp, hεp, hεpδ, hεp1, hεpM⟩ :=
      exists_leading_radius (enteringCoeff c α) (k := k) (by rw [hck']; exact hck) hC hδ
    have hneg : c k < 0 := by
      by_contra hnn
      push_neg at hnn
      have hpos : 0 < c k := lt_of_le_of_ne hnn (Ne.symm hck)
      obtain ⟨h, hh0, hhε, hsp⟩ := hright εp hεp
      have habs : |h| < εp := by rw [abs_of_pos hh0]; exact hhε
      have hdom := abs_sub_leading_lt (enteringCoeff c α) (k := k) (by omega)
        (by rw [hck']; exact hck) hlow' hC (f := sp h) hh0.ne' (by linarith [abs_of_pos hh0])
        (hεpM h habs)
        (by rw [seamPoly_enteringCoeff]; exact hp h hh0.le (by linarith))
      rw [hck'] at hdom
      have := (sign_of_leading hdom (by rw [abs_mul, abs_pow, abs_of_pos hh0])).1
        (mul_pos hpos (pow_pos hh0 k))
      linarith
    -- left side: k is odd
    obtain ⟨εm, hεm, hεmδ, hεm1, hεmM⟩ := exists_leading_radius c (k := k) hck hC hδ
    have hodd : Odd k := by
      by_contra hev
      have hev' : Even k := Nat.not_odd_iff_even.mp hev
      set h := -(εm / 2) with hh
      have hhneg : h < 0 := by rw [hh]; linarith
      have habs : |h| < εm := by rw [abs_of_neg hhneg, hh]; linarith
      have hdom := abs_sub_leading_lt c (k := k) (by omega) hck hlow hC (f := sm h)
        hhneg.ne (by rw [abs_of_neg hhneg, hh]; linarith) (hεmM h habs)
        (hm h (by rw [abs_of_neg hhneg, hh]; linarith))
      have hpowpos : 0 < h ^ k := hev'.pow_pos hhneg.ne
      have := (sign_of_leading hdom (by rw [abs_mul, abs_pow, abs_of_pos hpowpos])).2
        (mul_neg_of_neg_of_pos hneg hpowpos)
      have := hleft h (by rw [hh]; linarith) hhneg
      linarith
    refine ⟨?_, hneg⟩
    have hk0 : k ≠ 0 := by rintro rfl; exact hck hc0
    have hk1 : k ≠ 1 := by rintro rfl; exact hck hc1
    obtain ⟨m, rfl⟩ := hodd
    omega
  · intro hall
    have hlow9 : ∀ j, j < 9 → c j = 0 := hall
    have hc9 : c 9 ≤ 0 := by
      by_contra hpos
      push_neg at hpos
      obtain ⟨εm, hεm, hεmδ, hεm1, hεmM⟩ := exists_leading_radius c (k := 9) hpos.ne' hC hδ
      set h := -(εm / 2) with hh
      have hhneg : h < 0 := by rw [hh]; linarith
      have habs : |h| < εm := by rw [abs_of_neg hhneg, hh]; linarith
      have hdom := abs_sub_leading_lt c (k := 9) (by omega) hpos.ne' hlow9 hC (f := sm h)
        hhneg.ne (by rw [abs_of_neg hhneg, hh]; linarith) (hεmM h habs)
        (hm h (by rw [abs_of_neg hhneg, hh]; linarith))
      have hpowneg : h ^ 9 < 0 := Odd.pow_neg ⟨4, by norm_num⟩ hhneg
      have := (sign_of_leading hdom (by rw [abs_mul])).2
        (mul_neg_of_pos_of_neg hpos hpowneg)
      have := hleft h (by rw [hh]; linarith) hhneg
      linarith
    have hc9α : c 9 - α < 0 := by linarith
    refine ⟨hc9, hc9α, ?_⟩
    have hk9 : enteringCoeff c α 9 = c 9 - α := by simp [enteringCoeff]
    have hlow' : ∀ j, j < 9 → enteringCoeff c α j = 0 := by
      intro j hj
      simp [enteringCoeff, show j ≠ 9 by omega, hlow9 j hj]
    obtain ⟨εp, hεp, hεpδ, hεp1, hεpM⟩ :=
      exists_leading_radius (enteringCoeff c α) (k := 9) (by rw [hk9]; exact hc9α.ne) hC hδ
    refine ⟨εp, hεp, ?_⟩
    intro h hh0 hhε
    have habs : |h| < εp := by rw [abs_of_pos hh0]; exact hhε
    have hdom := abs_sub_leading_lt (enteringCoeff c α) (k := 9) (by omega)
      (by rw [hk9]; exact hc9α.ne) hlow' hC (f := sp h) hh0.ne'
      (by rw [abs_of_pos hh0]; linarith) (hεpM h habs)
      (by rw [seamPoly_enteringCoeff]; exact hp h hh0.le (by linarith))
    rw [hk9] at hdom
    exact (sign_of_leading hdom (by rw [abs_mul])).2
      (mul_neg_of_neg_of_pos hc9α (pow_pos hh0 9))

/-! ## Regression toy cases -/

/-- LOW toy: `s₋ = -h^3`, `s₊ = -h^3 - α h^9`. -/
theorem seam_toy_low {α : ℝ} (hα : 0 < α) :
    let c : ℕ → ℝ := fun k => if k = 3 then -1 else 0
    (∀ h, seamPoly c h = -h ^ 3) ∧
      (∀ h, h < 0 → 0 ≤ -h ^ 3) ∧ (∀ h, 0 < h → -h ^ 3 - α * h ^ 9 < 0) := by
  intro c
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp [seamPoly, c, Finset.sum_range_succ]
  · intro h hh
    have : h ^ 3 < 0 := Odd.pow_neg ⟨1, by norm_num⟩ hh
    linarith
  · intro h hh
    have h3 : 0 < h ^ 3 := pow_pos hh 3
    have h9 : 0 < h ^ 9 := pow_pos hh 9
    nlinarith

/-- HIGH toy: `s₋ = h^10`, `s₊ = h^10 - α h^9`, negative on `(0, α)`. -/
theorem seam_toy_high {α : ℝ} (hα : 0 < α) :
    (∀ h, h < 0 → 0 ≤ h ^ 10) ∧ (∀ h, 0 < h → h < α → h ^ 10 - α * h ^ 9 < 0) := by
  refine ⟨fun h _ => by positivity, ?_⟩
  intro h hh hhα
  have h9 : 0 < h ^ 9 := pow_pos hh 9
  have : h ^ 10 = h * h ^ 9 := by ring
  nlinarith

end Zeta23.CCM

#print axioms Zeta23.CCM.abs_sub_leading_lt
#print axioms Zeta23.CCM.strictEven_seam_dichotomy
#print axioms Zeta23.CCM.seam_toy_low
#print axioms Zeta23.CCM.seam_toy_high
