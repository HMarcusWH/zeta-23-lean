import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
namespace OPICAExtractionR1

def rampG (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (⌊y⌋₊ + 1),
    ArithmeticFunction.vonMangoldt n * max (y / (n : ℝ) - 1) 0) -
  y * Real.log y + (1 + Real.eulerMascheroniConstant) * y

def discreteG (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
    ArithmeticFunction.vonMangoldt n * (y / (n : ℝ) - 1)) -
  y * Real.log y + (1 + Real.eulerMascheroniConstant) * y

/-- Same all-prime-power source, including zero coefficient and exact endpoint. -/
theorem discreteG_eq_rampG (y : ℝ) : discreteG y = rampG y := by
  have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.range (⌊y⌋₊ + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
  have hsum : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      ArithmeticFunction.vonMangoldt n * max (y / (n : ℝ) - 1) 0) =
      ∑ n ∈ Finset.range (⌊y⌋₊ + 1),
        ArithmeticFunction.vonMangoldt n * max (y / (n : ℝ) - 1) 0 := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hn' := Finset.mem_range.mp hn
    have hz : n = 0 := by
      by_contra hne
      apply hnot
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne, Nat.le_of_lt_succ hn'⟩
    subst n
    simp
  have hterm : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      ArithmeticFunction.vonMangoldt n * (y / (n : ℝ) - 1)) =
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt n * max (y / (n : ℝ) - 1) 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
    have hn_pos : 0 < n := Nat.zero_lt_of_lt hn₁
    have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' hn_pos.ne').mp hn₂
    have hnonneg : 0 ≤ y / (n : ℝ) - 1 := by
      rw [sub_nonneg, le_div_iff₀ (Nat.cast_pos.mpr hn_pos), one_mul]
      exact hny
    rw [max_eq_left hnonneg]
  unfold discreteG rampG
  rw [hterm, hsum]

def OneSidedWindows (g : ℝ → ℝ) : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ C : ℝ,
    ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
      ∀ y ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)), g y ≤ C * y ^ θ

def RampWindows : Prop := OneSidedWindows rampG

theorem windows_congr {g h : ℝ → ℝ} (heq : ∀ y, g y = h y) :
    OneSidedWindows g → OneSidedWindows h := by
  rw [funext heq]
  exact id
end OPICAExtractionR1

#print axioms OPICAExtractionR1.discreteG_eq_rampG
#print axioms OPICAExtractionR1.windows_congr
