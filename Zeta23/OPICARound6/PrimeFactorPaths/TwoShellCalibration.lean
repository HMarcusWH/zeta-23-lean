import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Zeta23.OPICARound6.PrimeFactorPaths.TwoShellCalibration

abbrev normSq (x y : ℝ) : ℝ := x^2 + y^2

abbrev det (x y z t : ℝ) : ℝ := x*t - y*z

abbrev traceEnergy (p₁ a₁ p₂ a₂ : ℝ) : ℝ := normSq p₁ a₁ + normSq p₂ a₂

abbrev residual (p a f u pi ai : ℝ) : ℝ :=
  normSq (pi*f-p*u) (ai*f-a*u)

private theorem normSq_nonneg (x y : ℝ) : 0 ≤ normSq x y :=
  add_nonneg (sq_nonneg x) (sq_nonneg y)

private theorem det_le (x y z t : ℝ) :
    (det x y z t)^2 ≤ normSq x y * normSq z t := by
  unfold det normSq
  nlinarith only [sq_nonneg (x*z + y*t)]

theorem two_shell (p₁ a₁ p₂ a₂ p a f u₁ u₂ : ℝ) :
    (det p₁ a₁ p₂ a₂)^2 * f^2 ≤
    traceEnergy p₁ a₁ p₂ a₂ * (residual p a f u₁ p₁ a₁ + residual p a f u₂ p₂ a₂) := by
  let b₁ := det p a p₁ a₁
  let b₂ := det p a p₂ a₂
  have ht : 0 ≤ traceEnergy p₁ a₁ p₂ a₂ :=
    add_nonneg (normSq_nonneg _ _) (normSq_nonneg _ _)
  by_cases hn : 0 < normSq p a
  · have hd : (det p₁ a₁ p₂ a₂)^2 * normSq p a ≤
        traceEnergy p₁ a₁ p₂ a₂ * normSq b₁ b₂ := by
      calc
        _ = (det p₁ p₂ b₁ b₂)^2 + (det a₁ a₂ b₁ b₂)^2 := by
          dsimp only [b₁, b₂, det, normSq]
          ring
        _ ≤ normSq p₁ p₂ * normSq b₁ b₂ + normSq a₁ a₂ * normSq b₁ b₂ :=
          add_le_add (det_le _ _ _ _) (det_le _ _ _ _)
        _ = _ := by unfold traceEnergy normSq; ring
    have hr : f^2 * normSq b₁ b₂ ≤ normSq p a *
        (residual p a f u₁ p₁ a₁ + residual p a f u₂ p₂ a₂) := by
      calc
        _ = (det p a (p₁*f-p*u₁) (a₁*f-a*u₁))^2 +
            (det p a (p₂*f-p*u₂) (a₂*f-a*u₂))^2 := by
          dsimp only [b₁, b₂, det, normSq]
          ring
        _ ≤ normSq p a * residual p a f u₁ p₁ a₁ +
              normSq p a * residual p a f u₂ p₂ a₂ :=
          add_le_add (det_le _ _ _ _) (det_le _ _ _ _)
        _ = _ := by ring
    apply (mul_le_mul_iff_of_pos_right hn).mp
    calc
      _ = ((det p₁ a₁ p₂ a₂)^2 * normSq p a) * f^2 := by ring
      _ ≤ (traceEnergy p₁ a₁ p₂ a₂ * normSq b₁ b₂) * f^2 :=
        mul_le_mul_of_nonneg_right hd (sq_nonneg f)
      _ = traceEnergy p₁ a₁ p₂ a₂ * (f^2 * normSq b₁ b₂) := by ring
      _ ≤ traceEnergy p₁ a₁ p₂ a₂ * (normSq p a *
          (residual p a f u₁ p₁ a₁ + residual p a f u₂ p₂ a₂)) :=
        mul_le_mul_of_nonneg_left hr ht
      _ = _ := by ring
  · have hp : p = 0 := by
      by_contra hp
      exact hn (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hp) (sq_nonneg a))
    have ha : a = 0 := by
      by_contra ha
      exact hn (add_pos_of_nonneg_of_pos (sq_nonneg p) (sq_pos_of_ne_zero ha))
    subst p
    subst a
    have hd : (det p₁ a₁ p₂ a₂)^2 ≤ (traceEnergy p₁ a₁ p₂ a₂)^2 := by
      apply (det_le _ _ _ _).trans
      unfold traceEnergy
      nlinarith only [sq_nonneg (normSq p₁ a₁), sq_nonneg (normSq p₂ a₂),
        mul_nonneg (normSq_nonneg p₁ a₁) (normSq_nonneg p₂ a₂)]
    calc
      _ ≤ (traceEnergy p₁ a₁ p₂ a₂)^2 * f^2 := mul_le_mul_of_nonneg_right hd (sq_nonneg f)
      _ = _ := by unfold traceEnergy residual normSq; ring

theorem weighted_finite {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (p₁ a₁ p₂ a₂ : ℝ) (p a f u₁ u₂ : ι → ℝ) :
    (det p₁ a₁ p₂ a₂)^2 * (∑ i ∈ s, w i * (f i)^2) ≤
      traceEnergy p₁ a₁ p₂ a₂ * ∑ i ∈ s, w i *
        (residual (p i) (a i) (f i) (u₁ i) p₁ a₁ +
         residual (p i) (a i) (f i) (u₂ i) p₂ a₂) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left (two_shell p₁ a₁ p₂ a₂
    (p i) (a i) (f i) (u₁ i) (u₂ i)) (hw i hi)
  simpa only [mul_left_comm] using h

end Zeta23.OPICARound6.PrimeFactorPaths.TwoShellCalibration
