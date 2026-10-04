import Zeta23.CCM.FirstCrossingGeneratedStrictEvenFrontier
import Zeta23.CCM.FirstCrossingInheritedStationarity

noncomputable section

namespace Zeta23.RHRC

open Zeta23.CCM

/-!
# Post-#282 contact-calculus contract

This module is a compiler-facing premise firewall.  The exported examples must
typecheck without caller-supplied legacy realization, curvature/arithmetic
identity, zero-curvature equality, endpoint barrier, RH, or RH-equivalent
positivity premise.
-/


example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFirstVariation .even L K z =
      productionArithmeticRealValue L
        (productionFirstDerivativePhysicalTest L K z) :=
  canonicalFirstVariation_eq_physical hL K hK z

example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFixedSecondVariation .even L K z +
        2 * productionContactFirstVariation .even L K z / L =
      productionArithmeticRealValue L
        (productionSecondDerivativePhysicalTest L K z) :=
  canonicalFixedSecondEuler_eq_physical hL K hK z

example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    Complex.re (inner ℂ z (canonicalEvenApertureFirst L K w)) =
      productionArithmeticRealValue L
        (productionMixedDerivativePhysicalTest L K z w) :=
  canonicalMixedFirstVariation_eq_physical hL K hK z w

example (c : GeneratedStrictEvenContact) :
    Nonempty (GeneratedStrictEvenProductionBranch c) :=
  c.production_frontier

example (c : GeneratedStrictEvenContact)
    (hinh : c.generated.shell.n < c.generated.shell.k) :
    productionContactFirstVariation .even
      c.generated.shell.Lstar (c.generated.shell.k + 1) c.z = 0 :=
  c.firstVariation_eq_zero_of_inherited hinh

example (c : GeneratedStrictEvenContact)
    (hstationary :
      productionContactFirstVariation .even
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z = 0) :
    canonicalOptimizedContactCurvature
      c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary = 0 :=
  c.actual_stationary_curvature_eq_zero hstationary

example (c : GeneratedStrictEvenContact)
    (hstationary :
      productionContactFirstVariation .even
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z = 0) :
    productionContactRemainderValue c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z
        (canonicalStationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) =
      (2 * Real.pi)^2 / c.generated.shell.Lstar^2 *
        productionStrictEvenSourceValue c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z :=
  c.production_stationary_saturation hstationary

example (c : GeneratedStrictEvenContact) :
    Nonempty (GeneratedStrictEvenCompletedProductionBranch c) :=
  c.completed_production_frontier

example (c : GeneratedStrictEvenContact)
    (hinh : c.generated.shell.n < c.generated.shell.k) :
    ∃ b : GeneratedStrictEvenCompletedProductionBranch c,
      match b with
      | .firstOrder _ _ => False
      | .stationary hzero _ _ _ _ _ _ _ =>
          hzero = c.firstVariation_eq_zero_of_inherited hinh :=
  c.inherited_completed_production_frontier hinh

example (c : GeneratedStrictEvenContact)
    (hinh : c.generated.shell.n < c.generated.shell.k) :
    productionContactRemainderValue c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z
        (canonicalStationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive
          (c.firstVariation_eq_zero_of_inherited hinh)) =
      (2 * Real.pi)^2 / c.generated.shell.Lstar^2 *
        productionStrictEvenSourceValue c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z :=
  c.inherited_production_saturation hinh

example (c : GeneratedStrictEvenContact)
    (hstationary :
      productionContactFirstVariation .even
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z = 0) :
    0 < productionContactRemainderValue
      c.generated.shell.Lstar (c.generated.shell.k + 1) c.z
      (canonicalStationaryEvenResponse
        c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) :=
  c.production_stationary_remainder_pos hstationary

end Zeta23.RHRC

#print axioms Zeta23.CCM.canonicalFirstVariation_eq_physical
#print axioms Zeta23.CCM.canonicalFixedSecondEuler_eq_physical
#print axioms Zeta23.CCM.canonicalMixedFirstVariation_eq_physical
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.actual_stationary_curvature_eq_zero
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.production_stationary_saturation
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.completed_production_frontier
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.inherited_production_saturation
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.inherited_completed_production_frontier
