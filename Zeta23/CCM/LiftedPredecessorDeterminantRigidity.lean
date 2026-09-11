import Zeta23.CCM.FrozenIntrinsicPredecessorComplex
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Charpoly.Basic

noncomputable section

namespace Zeta23.CCM

open Complex Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4R2: deck-forced determinant nonidentity

The lifted frozen intrinsic predecessor satisfies the exact deck law

  B(z + 2*pi*i) = B(z) - (2*pi*i) id.

This module extracts the finite-dimensional algebraic consequence that the
lifted determinant cannot vanish at every deck translate of one point.  The
argument is independent of holomorphy: if all scalar shifts of one finite
endomorphism had zero determinant, its characteristic polynomial would have
infinitely many distinct roots.

This is deliberately separated from the analytic-density step.  Holomorphy is
still required later to turn determinant nonidentity into local/dense real
regularity.

No source sign, successor positivity, negative-root exclusion, finite-to-
infinite closure, or RH theorem is claimed here.
-/

/-- A finite-dimensional complex endomorphism cannot have singular scalar
shifts along every natural multiple of one nonzero complex step. -/
theorem exists_nat_det_sub_smul_id_ne_zero
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    [Module.Free ℂ E] [Module.Finite ℂ E]
    (A : E →ₗ[ℂ] E) {c : ℂ} (hc : c ≠ 0) :
    ∃ k : ℕ,
      LinearMap.det (A - (((k : ℂ) * c) • LinearMap.id)) ≠ 0 := by
  by_contra h
  push Not at h
  let f : ℕ → ℂ := fun k => (k : ℂ) * c
  have hf : Function.Injective f := by
    intro m n hmn
    have hcast : (m : ℂ) = (n : ℂ) := by
      exact mul_right_cancel₀ hc hmn
    exact_mod_cast hcast
  have hrange : (Set.range f).Infinite :=
    Set.infinite_range_of_injective hf
  have hroot : Set.range f ⊆ {z : ℂ | Polynomial.IsRoot A.charpoly z} := by
    rintro z ⟨k, rfl⟩
    change Polynomial.IsRoot A.charpoly (f k)
    rw [Polynomial.IsRoot.def]
    rw [LinearMap.eval_charpoly]
    have hshift :
        algebraMap ℂ (Module.End ℂ E) (f k) - A =
          -(A - (f k) • LinearMap.id) := by
      ext x
      simp [sub_eq_add_neg]
    rw [hshift]
    have hneg :
        -(A - (f k) • LinearMap.id) =
          (-1 : ℂ) • (A - (f k) • LinearMap.id) := by
      ext x
      simp
    rw [hneg, LinearMap.det_smul, h k, mul_zero]
  have hroots : {z : ℂ | Polynomial.IsRoot A.charpoly z}.Infinite :=
    hrange.mono hroot
  have hzero : A.charpoly = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot A.charpoly hroots
  exact (LinearMap.charpoly_monic A).ne_zero hzero

/-- Natural-iterate form of the exact lifted deck law. -/
theorem liftedFrozenIntrinsicPredecessorBlock_add_nat_two_pi_I
    (Q : ℕ) (p : ReversalParity) (N k : ℕ) (z : ℂ) :
    liftedFrozenIntrinsicPredecessorBlock Q p N
        (z + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      liftedFrozenIntrinsicPredecessorBlock Q p N z -
        ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) • LinearMap.id := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have harg :
          z + ((Nat.succ k : ℕ) : ℂ) *
              (2 * (Real.pi : ℂ) * Complex.I) =
            (z + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
              2 * (Real.pi : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg,
        liftedFrozenIntrinsicPredecessorBlock_add_two_pi_I,
        ih]
      module

/-- At the deck orbit of every point, at least one lifted predecessor block is
regular.  This is the exact finite-dimensional rigidity supplied by the deck
shift; no analyticity assumption is used. -/
theorem exists_nat_deck_translate_liftedFrozenIntrinsicPredecessor_det_ne_zero
    (Q : ℕ) (p : ReversalParity) (N : ℕ) (z : ℂ) :
    ∃ k : ℕ,
      LinearMap.det
          (liftedFrozenIntrinsicPredecessorBlock Q p N
            (z + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) ≠ 0 := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  obtain ⟨k, hk⟩ :=
    exists_nat_det_sub_smul_id_ne_zero
      (liftedFrozenIntrinsicPredecessorBlock Q p N z) hc
  refine ⟨k, ?_⟩
  rw [liftedFrozenIntrinsicPredecessorBlock_add_nat_two_pi_I]
  exact hk

/-- In particular, the lifted predecessor determinant is not the zero function.
The witness is produced on the deck orbit of the origin. -/
theorem liftedFrozenIntrinsicPredecessor_det_not_identically_zero
    (Q : ℕ) (p : ReversalParity) (N : ℕ) :
    ∃ z : ℂ,
      LinearMap.det (liftedFrozenIntrinsicPredecessorBlock Q p N z) ≠ 0 := by
  obtain ⟨k, hk⟩ :=
    exists_nat_deck_translate_liftedFrozenIntrinsicPredecessor_det_ne_zero
      Q p N 0
  exact ⟨(k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I), by simpa using hk⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_nat_det_sub_smul_id_ne_zero
#print axioms Zeta23.CCM.liftedFrozenIntrinsicPredecessorBlock_add_nat_two_pi_I
#print axioms Zeta23.CCM.exists_nat_deck_translate_liftedFrozenIntrinsicPredecessor_det_ne_zero
#print axioms Zeta23.CCM.liftedFrozenIntrinsicPredecessor_det_not_identically_zero
