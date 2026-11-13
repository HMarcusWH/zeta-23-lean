import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

/-!
# Soundness of the finite certificate kernel for exact data

The acceptance kernel `certificates.py` decides `A ≻ 0` by a shifted-factor
certificate: for an exact factor proposal `R` and a shift `τ`, it checks
`‖A - τ I - R Rᵀ‖²_F < τ²`. This module proves that this decision is sound for
exact real data:

* `posDef_of_shifted_factor`: `0 < τ` and `‖A - τ I - R Rᵀ‖²_F < τ²` imply
  `0 < xᵀ A x` for every `x ≠ 0`; no symmetry of `A` is needed;
* `shifted_factor_requires_positive_shift`: the `0 < τ` precondition cannot be
  dropped (a `1 × 1` counterexample with `τ = -1`);
* `not_nonneg_of_negative_witness`: one exact vector with `xᵀ A x < 0` refutes
  `A ⪰ 0`, which is the meaning of `FALSIFIED_BOUND`;
* `pencil_checkpoint_of_posDef`: a positive pencil `F + ε G` gives the
  checkpoint inequality `xᵀ F x ≥ -ε xᵀ G x`.

Scope: exact data only. That the kernel's Arb ball enclosures contain the true
transcendental native entries (the native enclosure bridge) is not proved here
and remains OPEN, so a numerical certificate is still not a Lean fact about the
actual canonical source.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

/-- The quadratic form `xᵀ A x`. -/
def quad (A : Matrix n n ℝ) (x : n → ℝ) : ℝ := ∑ i, ∑ j, x i * A i j * x j

/-- The squared Frobenius norm `‖E‖²_F`. -/
def froSq (E : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, E i j ^ 2

/-- The squared Euclidean norm `xᵀ x`. -/
def normSq (x : n → ℝ) : ℝ := ∑ i, x i ^ 2

theorem quad_add (A B : Matrix n n ℝ) (x : n → ℝ) : quad (A + B) x = quad A x + quad B x := by
  simp only [quad, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem quad_sub (A B : Matrix n n ℝ) (x : n → ℝ) : quad (A - B) x = quad A x - quad B x := by
  simp only [quad, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem quad_smul (c : ℝ) (A : Matrix n n ℝ) (x : n → ℝ) : quad (c • A) x = c * quad A x := by
  simp only [quad, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem quad_one [DecidableEq n] (x : n → ℝ) : quad (1 : Matrix n n ℝ) x = normSq x := by
  simp only [quad, normSq, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `xᵀ (R Rᵀ) x = ‖Rᵀ x‖² ≥ 0`. -/
theorem quad_mul_transpose_nonneg (R : Matrix n m ℝ) (x : n → ℝ) : 0 ≤ quad (R * Rᵀ) x := by
  have e1 : quad (R * Rᵀ) x = ∑ i, ∑ j, ∑ k, (x i * R i k) * (x j * R j k) := by
    unfold quad
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.transpose_apply]
    ring
  have e2 : (∑ i, ∑ j, ∑ k, (x i * R i k) * (x j * R j k)) = ∑ k, (∑ i, x i * R i k) ^ 2 := by
    calc (∑ i, ∑ j, ∑ k, (x i * R i k) * (x j * R j k))
        = ∑ i, ∑ k, ∑ j, (x i * R i k) * (x j * R j k) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, (x i * R i k) * (x j * R j k) := Finset.sum_comm
      _ = ∑ k, (∑ i, x i * R i k) ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sq, Finset.sum_mul_sum]
  rw [e1, e2]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- Cauchy–Schwarz for the form: `(xᵀ E x)² ≤ ‖E‖²_F (xᵀ x)²`. -/
theorem quad_sq_le (E : Matrix n n ℝ) (x : n → ℝ) : quad E x ^ 2 ≤ froSq E * normSq x ^ 2 := by
  have hq : quad E x = ∑ p : n × n, E p.1 p.2 * (x p.1 * x p.2) := by
    rw [quad, ← Finset.univ_product_univ, Finset.sum_product]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hf : froSq E = ∑ p : n × n, E p.1 p.2 ^ 2 := by
    rw [froSq, ← Finset.univ_product_univ, Finset.sum_product]
  have hn : normSq x ^ 2 = ∑ p : n × n, (x p.1 * x p.2) ^ 2 := by
    rw [normSq, sq, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hq, hf, hn]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem normSq_pos {x : n → ℝ} (hx : x ≠ 0) : 0 < normSq x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  have hle : x i ^ 2 ≤ normSq x :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le (by positivity) hle

/-- **Shifted-factor soundness.** If `0 < τ` and `‖A - τ I - R Rᵀ‖²_F < τ²`, then `xᵀ A x > 0`
for every nonzero `x`. This is the decision rule of `certify_shifted` on exact data. -/
theorem posDef_of_shifted_factor [DecidableEq n] (A : Matrix n n ℝ) (R : Matrix n m ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hfro : froSq (A - τ • (1 : Matrix n n ℝ) - R * Rᵀ) < τ ^ 2) {x : n → ℝ} (hx : x ≠ 0) :
    0 < quad A x := by
  set E := A - τ • (1 : Matrix n n ℝ) - R * Rᵀ with hEdef
  have hA : A = E + τ • (1 : Matrix n n ℝ) + R * Rᵀ := by rw [hEdef]; abel
  have hsplit : quad A x = quad E x + τ * normSq x + quad (R * Rᵀ) x := by
    rw [hA, quad_add, quad_add, quad_smul, quad_one]
  have ht := normSq_pos hx
  have hcs := quad_sq_le E x
  have hR := quad_mul_transpose_nonneg R x
  -- |xᵀ E x| < τ ‖x‖²
  have hlt : quad E x ^ 2 < (τ * normSq x) ^ 2 := by
    calc quad E x ^ 2 ≤ froSq E * normSq x ^ 2 := hcs
      _ < τ ^ 2 * normSq x ^ 2 := by
          exact mul_lt_mul_of_pos_right hfro (by positivity)
      _ = (τ * normSq x) ^ 2 := by ring
  have habs : |quad E x| < τ * normSq x := by
    have h0 : 0 ≤ τ * normSq x := by positivity
    exact abs_lt_of_sq_lt_sq hlt h0
  have hneg : -(τ * normSq x) < quad E x := (abs_lt.mp habs).1
  rw [hsplit]
  linarith

/-- Scalar-shift residual bound: `(xᵀ A x - τ xᵀ x)² ≤ ‖A - τ I‖²_F (xᵀ x)²`. -/
theorem quad_near_shift [DecidableEq n] (A : Matrix n n ℝ) (τ : ℝ) (x : n → ℝ) :
    (quad A x - τ * normSq x) ^ 2 ≤ froSq (A - τ • (1 : Matrix n n ℝ)) * normSq x ^ 2 := by
  have h := quad_sq_le (A - τ • (1 : Matrix n n ℝ)) x
  rwa [quad_sub, quad_smul, quad_one] at h

/-- `FALSIFIED_BOUND` semantics: one exact vector with a negative value refutes `A ⪰ 0`. -/
theorem not_nonneg_of_negative_witness (A : Matrix n n ℝ) {x : n → ℝ} (hx : quad A x < 0) :
    ¬ ∀ y : n → ℝ, 0 ≤ quad A y :=
  fun h => absurd (h x) (not_le.mpr hx)

/-- A positive shifted pencil gives the checkpoint inequality `xᵀ F x ≥ -ε xᵀ G x`. -/
theorem pencil_checkpoint_of_posDef (F G : Matrix n n ℝ) (ε : ℝ)
    (hpos : ∀ x : n → ℝ, x ≠ 0 → 0 < quad (F + ε • G) x) (x : n → ℝ) :
    -ε * quad G x ≤ quad F x := by
  by_cases hx : x = 0
  · subst hx
    simp [quad]
  · have h := hpos x hx
    rw [quad_add, quad_smul] at h
    linarith

/-- **The `0 < τ` precondition cannot be dropped.** With `A = -1`, `τ = -1`, `R = 0` the residual
vanishes, `0 < τ²`, and yet `A` is negative. -/
theorem shifted_factor_requires_positive_shift :
    ∃ (A : Matrix (Fin 1) (Fin 1) ℝ) (R : Matrix (Fin 1) (Fin 1) ℝ) (τ : ℝ),
      froSq (A - τ • (1 : Matrix (Fin 1) (Fin 1) ℝ) - R * Rᵀ) < τ ^ 2 ∧ quad A (fun _ => 1) < 0 := by
  refine ⟨-1, 0, -1, ?_, ?_⟩
  · simp [froSq]
  · simp [quad]

end Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness
