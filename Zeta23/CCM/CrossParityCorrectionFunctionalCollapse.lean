import Zeta23.CCM.CrossParityCubicCorrectionCollapse

noncomputable section

namespace Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: generic predecessor-correction propagation

PR #226 proves that the two odd predecessor corrections are exactly collinear:
`a_N = -κ_N d_N`, with `κ_N = (2N-1)/6`.

This module exposes the linear-map consequence once, so later secular,
zero-shift, and kernel constructions do not each re-prove the same algebra.

No sign, branch exclusion, negative-root exclusion, or RH claim is made here.
-/

/-- Any complex-linear construction sends the odd cubic-generator predecessor
correction to the same exact scalar multiple of the transported even-shell
predecessor correction. -/
theorem map_oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul
    {V : Type*}
    [AddCommMonoid V]
    [Module ℂ V]
    (N : ℕ) (hN : 1 ≤ N)
    (T : intrinsicParityPredecessorSubspace .odd N →ₗ[ℂ] V) :
    T (oddCubicGeneratorPredecessorPart N) =
      -(crossParityCubicCorrectionKappa N) •
        T (oddIndexCubicShellPredecessorPart N) := by
  rw [oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul N hN]
  exact T.map_smul _ _

/-- Denominator-free form of the exact one-step correction coefficient. -/
theorem six_mul_crossParityCubicCorrectionKappa
    (N : ℕ) :
    (6 : ℂ) * crossParityCubicCorrectionKappa N =
      2 * (N : ℂ) - 1 := by
  unfold crossParityCubicCorrectionKappa
  field_simp

/-- Closed form for `1 + κ_N`, useful in one-coefficient transfer formulas. -/
theorem one_add_crossParityCubicCorrectionKappa
    (N : ℕ) :
    1 + crossParityCubicCorrectionKappa N =
      (2 * (N : ℂ) + 5) / 6 := by
  unfold crossParityCubicCorrectionKappa
  field_simp
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.map_oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul
#print axioms Zeta23.CCM.six_mul_crossParityCubicCorrectionKappa
#print axioms Zeta23.CCM.one_add_crossParityCubicCorrectionKappa
