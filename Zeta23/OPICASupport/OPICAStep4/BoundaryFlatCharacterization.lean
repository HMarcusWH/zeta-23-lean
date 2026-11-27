import Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor

/-!
Round 20 structural audit. These are equivalences and conditional consequences;
none supplies C1 or RH. The reverse direction below restricts the literal full
boundary-flat quadratic form to the native even carrier, without using RH.
-/

noncomputable section

open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4.ArithmeticFrontier

namespace Zeta23.OPICARound20

/-- All legal native finite vectors, retaining the physical coefficient space. -/
def AllBoundaryFlatNonnegative : Prop :=
  ∀ L : ℝ, 0 < L → ∀ K : ℕ, ∀ u : Fin (2 * K + 1) → ℂ,
    BoundaryFlatCoefficients K u →
      0 ≤ Complex.re (quadraticForm (canonicalSourceMatrix L K) u)

theorem even_zero_bound_of_all_boundary_flat_nonnegative
    (h : AllBoundaryFlatNonnegative) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    EvenMomentSliceLowerBound L K 0 := by
  intro u _
  have hflat : BoundaryFlatCoefficients K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) :=
    (mem_boundaryFlatSubspace_iff K _).mp
      (Submodule.mem_inf.mp ((mem_euclideanEvenBoundaryFlatSubspace_iff K _).mp u.val.property)).1
  have henergy := h L hL K _ hflat
  have hE : (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re =
      Complex.re (quadraticForm (canonicalSourceMatrix L K)
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))) :=
    (matrixRealEnergy_eq_re_inner_apply_self (canonicalSourceMatrix L K) _).symm
  unfold evenNativeEnergy
  rw [inner_poleNeutralEvenCompressedCanonical_self, hE, neg_zero, zero_mul]
  exact henergy

/-- The cofinal approximate slice contract is exactly full boundary-flat
positivity. Forward uses the proved C1 -> RH reduction. Reverse is a direct
restriction to an even carrier followed by weakening zero to 1/n. -/
theorem c1_iff_all_boundary_flat_nonnegative :
    CofinalMomentSliceVanishingErrorBounds ↔ AllBoundaryFlatNonnegative := by
  constructor
  · intro hC1 L hL K u hflat
    apply canonicalSourceQuadraticForm_re_nonnegative_of_criticalLine ?_ K u hL hflat
    intro ρ hρ
    exact RH_implies_on_line
      (riemannHypothesis_of_cofinal_moment_slice_bounds hC1) hρ
  · intro h n _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    refine ⟨(n : ℝ) + 2, le_rfl, Or.inl ?_⟩
    exact (even_zero_bound_of_all_boundary_flat_nonnegative h (by linarith) _).mono
      (by positivity)

theorem riemannHypothesis_iff_all_boundary_flat_nonnegative :
    RiemannHypothesis ↔ AllBoundaryFlatNonnegative :=
  riemannHypothesis_iff_cofinal_moment_slice_bounds.trans
    c1_iff_all_boundary_flat_nonnegative

/-- A rigorously negative single legal finite vector would refute C1.
The hypotheses require the actual complete source, exact boundary flatness,
and a strict energy inequality; an approximate numerical matrix is insufficient. -/
theorem finite_negative_boundary_flat_witness_refutes_c1
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients K u)
    (hnegative : Complex.re (quadraticForm (canonicalSourceMatrix L K) u) < 0) :
    ¬ CofinalMomentSliceVanishingErrorBounds := by
  intro hC1
  exact (not_lt_of_ge ((c1_iff_all_boundary_flat_nonnegative.mp hC1) L hL K u hflat))
    hnegative

end Zeta23.OPICARound20

set_option pp.fullNames true
set_option pp.universes false
set_option pp.maxSteps 100000

#check @Zeta23.OPICARound20.even_zero_bound_of_all_boundary_flat_nonnegative
#print axioms Zeta23.OPICARound20.even_zero_bound_of_all_boundary_flat_nonnegative
#check @Zeta23.OPICARound20.c1_iff_all_boundary_flat_nonnegative
#print axioms Zeta23.OPICARound20.c1_iff_all_boundary_flat_nonnegative
#check @Zeta23.OPICARound20.riemannHypothesis_iff_all_boundary_flat_nonnegative
#print axioms Zeta23.OPICARound20.riemannHypothesis_iff_all_boundary_flat_nonnegative
#check @Zeta23.OPICARound20.finite_negative_boundary_flat_witness_refutes_c1
#print axioms Zeta23.OPICARound20.finite_negative_boundary_flat_witness_refutes_c1
