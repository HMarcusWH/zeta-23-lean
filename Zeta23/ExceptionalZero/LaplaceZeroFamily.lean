import Zeta23.ExceptionalZero.LaplacePole
import Zeta23.XiPrime.ExplicitFormula.ZeroFree

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.XiPrime

/-- Difference of reciprocal zero-distance kernels at two evaluation points. -/
def reciprocalDiff (p q ρ : ℂ) : ℂ :=
  1 / (p - ρ) - 1 / (q - ρ)

/-- Algebraic form exhibiting the extra inverse-distance factor. -/
theorem reciprocalDiff_eq {p q ρ : ℂ} (hp : p ≠ ρ) (hq : q ≠ ρ) :
    reciprocalDiff p q ρ = (q - p) / ((p - ρ) * (q - ρ)) := by
  unfold reciprocalDiff
  field_simp [sub_ne_zero.mpr hp, sub_ne_zero.mpr hq]
  ring

/-- Generic version of the inverse-square zero-tail estimate used by Anthropic's reflected
weight: any reciprocal difference between two points off the zeta zero set is
`O((1+|gamma_rho|^2)^-1)` on nontrivial zeros. -/
theorem norm_reciprocalDiff_le_zero {p q : ℂ} (hpXi : xi p ≠ 0) (hqXi : xi q ≠ 0) :
    ∃ C : ℝ, ∀ ρ : ℂ, IsNontrivialZero ρ →
      ‖reciprocalDiff p q ρ‖ ≤ C / (1 + Complex.normSq (gammaOf ρ)) := by
  obtain ⟨c, hc, hpdist⟩ := Zeta23.XiPrime.ZeroFree.exists_normSq_sub_ge hpXi
  obtain ⟨c', hc', hqdist⟩ := Zeta23.XiPrime.ZeroFree.exists_normSq_sub_ge hqXi
  refine ⟨‖q - p‖ / 2 * (1 / c + 1 / c'), fun ρ hρ => ?_⟩
  have hzero : xi ρ = 0 := (xi_eq_zero_iff ρ).mpr hρ
  have hp : p - ρ ≠ 0 := sub_ne_zero.mpr (fun e => hpXi (e ▸ hzero))
  have hq : q - ρ ≠ 0 := sub_ne_zero.mpr (fun e => hqXi (e ▸ hzero))
  set N : ℝ := 1 + Complex.normSq (gammaOf ρ) with hNdef
  have hN : 0 < N := by rw [hNdef]; linarith [Complex.normSq_nonneg (gammaOf ρ)]
  have ha : c * N ≤ ‖p - ρ‖ ^ 2 := by
    rw [Complex.sq_norm]
    exact hpdist ρ hρ
  have hb : c' * N ≤ ‖q - ρ‖ ^ 2 := by
    rw [Complex.sq_norm]
    exact hqdist ρ hρ
  have ha0 : 0 < ‖p - ρ‖ := norm_pos_iff.mpr hp
  have hb0 : 0 < ‖q - ρ‖ := norm_pos_iff.mpr hq
  rw [reciprocalDiff_eq (sub_ne_zero.mp hp) (sub_ne_zero.mp hq), norm_div, norm_mul]
  have key : 1 / (‖p - ρ‖ * ‖q - ρ‖) ≤
      (1 / (c * N) + 1 / (c' * N)) / 2 := by
    have hab : 1 / (‖p - ρ‖ * ‖q - ρ‖) ≤
        (1 / ‖p - ρ‖ ^ 2 + 1 / ‖q - ρ‖ ^ 2) / 2 := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (‖p - ρ‖ - ‖q - ρ‖), mul_pos ha0 hb0]
    have h3 : 1 / ‖p - ρ‖ ^ 2 ≤ 1 / (c * N) :=
      one_div_le_one_div_of_le (by positivity) ha
    have h4 : 1 / ‖q - ρ‖ ^ 2 ≤ 1 / (c' * N) :=
      one_div_le_one_div_of_le (by positivity) hb
    linarith
  calc
    ‖q - p‖ / (‖p - ρ‖ * ‖q - ρ‖)
        = ‖q - p‖ * (1 / (‖p - ρ‖ * ‖q - ρ‖)) := by ring
    _ ≤ ‖q - p‖ * ((1 / (c * N) + 1 / (c' * N)) / 2) :=
      mul_le_mul_of_nonneg_left key (norm_nonneg _)
    _ = ‖q - p‖ / 2 * (1 / c + 1 / c') / N := by field_simp

/-- The Laplace zero kernel is a scaled reciprocal difference between `s` and `s+z/2`. -/
theorem laplaceZeroKernel_eq_reciprocalDiff {s z ρ : ℂ}
    (hz : z ≠ 0) (hs : s ≠ ρ) (ht : s + z / 2 ≠ ρ) :
    laplaceZeroKernel (ρ - s) z =
      -(1 / z) * reciprocalDiff s (s + z / 2) ρ := by
  unfold laplaceZeroKernel reciprocalDiff
  field_simp [hz, sub_ne_zero.mpr hs, sub_ne_zero.mpr ht, sub_ne_zero.mpr (Ne.symm hs)]
  ring

/-- Away from the two evaluation-point zero sets, the full multiplicity-weighted transformed
zero family is absolutely summable.  This is the infinite-family convergence seam needed by
the Laplace pole route. -/
theorem summable_laplaceZeroKernel {s z : ℂ} (hz : z ≠ 0)
    (hsXi : xi s ≠ 0) (htXi : xi (s + z / 2) ≠ 0) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      (zeroMult ρ : ℂ) * laplaceZeroKernel ((ρ : ℂ) - s) z) := by
  obtain ⟨C, hC⟩ := norm_reciprocalDiff_le_zero hsXi htXi
  apply Zeta23.XiPrime.ZeroFree.summable_mult_mul
    (C := ‖(1 / z : ℂ)‖ * C)
  intro ρ hρ
  have hzero : xi ρ = 0 := (xi_eq_zero_iff ρ).mpr hρ
  have hs : s ≠ ρ := fun e => hsXi (e ▸ hzero)
  have ht : s + z / 2 ≠ ρ := fun e => htXi (e ▸ hzero)
  rw [laplaceZeroKernel_eq_reciprocalDiff hz hs ht, norm_mul, norm_neg]
  calc
    ‖(1 / z : ℂ)‖ * ‖reciprocalDiff s (s + z / 2) ρ‖
        ≤ ‖(1 / z : ℂ)‖ * (C / (1 + Complex.normSq (gammaOf ρ))) :=
      mul_le_mul_of_nonneg_left (hC ρ hρ) (norm_nonneg _)
    _ = (‖(1 / z : ℂ)‖ * C) / (1 + Complex.normSq (gammaOf ρ)) := by ring

end Zeta23.ExceptionalZero
