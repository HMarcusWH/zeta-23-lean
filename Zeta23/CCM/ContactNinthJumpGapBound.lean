import Zeta23.CCM.CanonicalSourceMomentJets
import Mathlib.Algebra.Order.Chebyshev

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate

/-!
# POST284-M19: quantitative strict-even ninth-order jump (conditional algebra)

Unconditional content:

* index-mass inequality: if `∑ u = 0` then
  `∑ |u_i|^2 ≤ (2K+1) ∑ n_i^2 |u_i|^2`; hence a normalized vector with
  `M_0 = 0` satisfies `‖D z‖^2 ≥ 1/(2K+1)` for the centered index action `D`.

Conditional content (premises are explicit hypotheses, NOT proved here):

* the parity-ground gap inequality `δ ‖Dz‖^2 ≤ B |M_4(z)|` (the handoff's M19
  identity `Re(conj(H z) M_4 z) = ⟨F_- Dz, Dz⟩` with odd ground gap `δ` and
  `B = ‖H‖ > 0`);
* the optimized ninth-derivative seam jump of M10,
  `Δ₉ = -κ |M_4(z)|^2` with `κ = 2Λ(q)(2π)^8 / (√q (log q)^9) > 0`.

Under these premises `|M_4(z)| ≥ δ/((2K+1)B)` and
`Δ₉ ≤ -κ δ^2 / ((2K+1)^2 B^2) < 0`.  This quantifies a potentially negative
entering-prime perturbation; it cannot by itself exclude a first crossing.
M10 is OPEN, so the jump statement is conditional.
-/

/-- Index-mass inequality on centered coefficients with vanishing sum. -/
theorem sum_normSq_le_index_weighted {K : ℕ} (u : Fin (2 * K + 1) → ℂ)
    (h0 : ∑ i, u i = 0) :
    ∑ i, Complex.normSq (u i) ≤
      (2 * K + 1 : ℝ) * ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (u i) := by
  classical
  let c : Fin (2 * K + 1) := ⟨K, by omega⟩
  have hc : centeredIndex K c = 0 := by simp [centeredIndex, c]
  set S := (Finset.univ : Finset (Fin (2 * K + 1))).erase c with hS
  have hcard : S.card = 2 * K := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
    omega
  have hsplit : ∀ g : Fin (2 * K + 1) → ℝ, ∑ i, g i = g c + ∑ i ∈ S, g i := by
    intro g
    rw [hS, Finset.add_sum_erase _ _ (Finset.mem_univ c)]
  have huc : u c = -∑ i ∈ S, u i := by
    have h := h0
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c)] at h
    rw [← hS] at h
    linear_combination h
  have hcs : Complex.normSq (u c) ≤ (2 * K : ℝ) * ∑ i ∈ S, Complex.normSq (u i) := by
    rw [huc, Complex.normSq_neg, Complex.normSq_eq_norm_sq]
    have h1 : ‖∑ i ∈ S, u i‖ ≤ ∑ i ∈ S, ‖u i‖ := norm_sum_le _ _
    have h2 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => ‖u i‖)
    rw [hcard] at h2
    calc ‖∑ i ∈ S, u i‖ ^ 2 ≤ (∑ i ∈ S, ‖u i‖) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ ((2 * K : ℕ) : ℝ) * ∑ i ∈ S, ‖u i‖ ^ 2 := h2
      _ = (2 * K : ℝ) * ∑ i ∈ S, Complex.normSq (u i) := by
          push_cast
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [Complex.normSq_eq_norm_sq]
  have hweight : ∀ i ∈ S, Complex.normSq (u i) ≤
      ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (u i) := by
    intro i hi
    have hne : i ≠ c := Finset.ne_of_mem_erase hi
    have hidx : centeredIndex K i ≠ 0 := by
      intro h
      apply hne
      apply centeredIndex_injective K
      rw [h, hc]
    have h1 : (1 : ℝ) ≤ ((centeredIndex K i : ℤ) : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ (centeredIndex K i) ^ 2 := by
        have := sq_pos_of_ne_zero hidx
        omega
      exact_mod_cast this
    have h2 := Complex.normSq_nonneg (u i)
    nlinarith
  have hSum : ∑ i ∈ S, Complex.normSq (u i) ≤
      ∑ i ∈ S, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (u i) :=
    Finset.sum_le_sum hweight
  have hfull : ∑ i ∈ S, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (u i) ≤
      ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (u i) := by
    rw [hsplit (fun i => ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (u i))]
    have := Complex.normSq_nonneg (u c)
    rw [hc]
    simp
  rw [hsplit (fun i => Complex.normSq (u i))]
  have hnn : 0 ≤ ∑ i ∈ S, Complex.normSq (u i) :=
    Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  nlinarith

/-- Normalized vectors with vanishing coefficient sum have
`‖D z‖^2 ≥ 1/(2K+1)` for the centered index action `D`. -/
theorem one_div_le_norm_sq_sourceIndexAction (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) (hx : ‖x‖ = 1)
    (h0 : centeredMoment K 0 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) = 0) :
    1 / (2 * K + 1 : ℝ) ≤ ‖sourceIndexAction K x‖ ^ 2 := by
  set u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  have hsum : ∑ i, u i = 0 := by simpa [centeredMoment] using h0
  have hnorm : ‖x‖ ^ 2 = ∑ i, Complex.normSq (u i) := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.normSq_eq_norm_sq]
    rfl
  have hD : ‖sourceIndexAction K x‖ ^ 2 =
      ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (u i) := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    have hcoord : (sourceIndexAction K x) i = ((centeredIndex K i : ℤ) : ℂ) * u i := by
      change ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) (sourceIndexAction K x)) i = _
      rw [sourceIndexAction_coordinates]
      simp [indexMatrix, Matrix.mulVec_diagonal, u]
    rw [hcoord, norm_mul, mul_pow, ← Complex.normSq_eq_norm_sq]
    congr 1
    rw [Complex.norm_intCast]
    simp [sq_abs]
  have hineq := sum_normSq_le_index_weighted u hsum
  rw [← hnorm, hx, ← hD] at hineq
  have hpos : (0 : ℝ) < 2 * K + 1 := by positivity
  rw [div_le_iff₀ hpos]
  linarith

/-- Conditional lower bound on the fourth moment from an explicit
parity-ground gap premise `δ ‖Dz‖^2 ≤ B |M_4|`. -/
theorem fourthMoment_lower_bound_of_gap {K : ℕ} {δ B D2 M4 : ℝ}
    (hδ : 0 ≤ δ) (hB : 0 < B)
    (hD2 : 1 / (2 * K + 1 : ℝ) ≤ D2) (hgap : δ * D2 ≤ B * M4) :
    δ / ((2 * K + 1) * B) ≤ M4 := by
  have hpos : (0 : ℝ) < 2 * K + 1 := by positivity
  have h1 : δ * (1 / (2 * K + 1)) ≤ δ * D2 := mul_le_mul_of_nonneg_left hD2 hδ
  rw [div_le_iff₀ (mul_pos hpos hB)]
  have h2 : δ = δ * (1 / (2 * K + 1)) * (2 * K + 1) := by field_simp
  nlinarith

/-- **Conditional quantitative strict-even ninth-order jump (M19).**
Premises: normalized contact mode `x` with `M_0 = 0`, explicit gap premise
`δ ‖Dx‖^2 ≤ B |M_4(x)|` with `δ > 0`, `B > 0`, and the (OPEN, M10) optimized
ninth-derivative jump formula `Δ₉ = -κ |M_4(x)|^2` with `κ > 0`.
Conclusion: `Δ₉ ≤ -κ δ^2/((2K+1)^2 B^2) < 0`. -/
theorem ninthJump_le_of_gap_conditional (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) (hx : ‖x‖ = 1)
    (h0 : centeredMoment K 0 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) = 0)
    {δ B κ Δ9 : ℝ} (hδ : 0 < δ) (hB : 0 < B) (hκ : 0 < κ)
    (hgap : δ * ‖sourceIndexAction K x‖ ^ 2 ≤
      B * ‖centeredMoment K 4 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)‖)
    (hjump : Δ9 = -κ *
      ‖centeredMoment K 4 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)‖ ^ 2) :
    δ / ((2 * K + 1) * B) ≤
        ‖centeredMoment K 4 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)‖ ∧
      Δ9 ≤ -κ * δ ^ 2 / ((2 * K + 1) ^ 2 * B ^ 2) ∧ Δ9 < 0 := by
  have hD2 := one_div_le_norm_sq_sourceIndexAction K x hx h0
  have hM4 := fourthMoment_lower_bound_of_gap hδ.le hB hD2 hgap
  set M := ‖centeredMoment K 4 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)‖
  have hpos : (0 : ℝ) < 2 * K + 1 := by positivity
  have hq : 0 < δ / ((2 * K + 1) * B) := div_pos hδ (mul_pos hpos hB)
  have hsq : (δ / ((2 * K + 1) * B)) ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ hq.le hM4 2
  have hrw : -κ * δ ^ 2 / ((2 * K + 1) ^ 2 * B ^ 2) = -κ * (δ / ((2 * K + 1) * B)) ^ 2 := by
    field_simp
  refine ⟨hM4, ?_, ?_⟩
  · rw [hrw, hjump]
    nlinarith
  · rw [hjump]
    have : 0 < M ^ 2 := by nlinarith
    nlinarith

end Zeta23.CCM

#print axioms Zeta23.CCM.sum_normSq_le_index_weighted
#print axioms Zeta23.CCM.one_div_le_norm_sq_sourceIndexAction
#print axioms Zeta23.CCM.fourthMoment_lower_bound_of_gap
#print axioms Zeta23.CCM.ninthJump_le_of_gap_conditional
