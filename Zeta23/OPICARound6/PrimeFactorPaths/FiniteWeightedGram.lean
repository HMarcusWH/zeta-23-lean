import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram

variable {ι : Type*}

abbrev energy (s : Finset ι) (w l : ι → ℝ) : ℝ := ∑ i ∈ s, w i * l i ^ 2

abbrev cross (s : Finset ι) (w l h : ι → ℝ) : ℝ := ∑ i ∈ s, w i * (l i * h i)

theorem scalar_factorization (A B g : ℝ) :
    (A - B)^2 + 4 * (A * B - g^2) = (A + B + 2*g) * (A + B - 2*g) := by
  ring

theorem signed_energy (s : Finset ι) (w l h : ι → ℝ) (c : ℝ) :
    energy s w (fun i => l i + c * h i) =
      energy s w l + c^2 * energy s w h + (2*c) * cross s w l h := by
  unfold energy cross
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- All ordered pairs are retained and no sign restriction on the weights is needed. -/
theorem ordered_minors (s : Finset ι) (w l h : ι → ℝ) :
    2 * (energy s w l * energy s w h - (cross s w l h)^2) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (l i * h j - l j * h i)^2 := by
  let a := fun i => w i * l i ^ 2
  let b := fun i => w i * h i ^ 2
  let g := fun i => w i * (l i * h i)
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s, (a i * b j + b i * a j - (g i * g j + g i * g j)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul]
      change 2 * ((∑ i ∈ s, a i) * (∑ i ∈ s, b i) - (∑ i ∈ s, g i)^2) = _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [a, b, g]
      ring

theorem determinant_nonneg (s : Finset ι) (w l h : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ energy s w l * energy s w h - (cross s w l h)^2 := by
  have he := ordered_minors s w l h
  have hpos : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * (l i * h j - l j * h i)^2 := by
    exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj =>
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)))
  rw [← he] at hpos
  exact nonneg_of_mul_nonneg_right hpos (zero_lt_two : (0 : ℝ) < 2)

end Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram
