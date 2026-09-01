import Zeta23.ExceptionalZero.WeilZeroSideEvenization
import Zeta23.CCM.BoundaryFlatFiniteSpace
import Zeta23.CCM.SourceNormalizationRepair

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex

/-!
# F0-B1A: genuine Weil form on the boundary-flat finite sector

Once the hard zero extension is globally C², PR #83 identifies the genuine
concrete-zeta diagonal Weil form with the repository localized additive RHS.
G1-A already identifies that RHS with the cutoff-free/canonical finite matrix.

This module composes those existing theorems.  It does not prove approximation
or density of the boundary-flat sector, continuity of W on a family, strict
finite negativity, F1, or RH.
-/

/-- On every legal boundary-flat finite vector, the genuine concrete-zeta Weil
form is exactly the cutoff-free finite CCM quadratic form. -/
theorem zeta_W_boundaryFlatFiniteVector_eq_cutoffFreeQuadraticForm
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ}
    (hL : 0 < L)
    (hflat : Zeta23.CCM.BoundaryFlatCoefficients N u) :
    zetaZeroConfig.W
        (Zeta23.CCM.localizedFiniteVector L N u)
        (Zeta23.CCM.localizedFiniteVector L N u) =
      Zeta23.CCM.quadraticForm
        (Zeta23.CCM.cutoffFreeMatrix L N) u := by
  have hC2 :
      ContDiff ℝ 2 (Zeta23.CCM.localizedFiniteVector L N u) :=
    Zeta23.CCM.contDiff_localizedFiniteVector_of_boundaryFlat
      N u hL hflat
  have hcompact :
      HasCompactSupport (Zeta23.CCM.localizedFiniteVector L N u) :=
    Zeta23.CCM.localizedFiniteVector_hasCompactSupport L N u
  calc
    zetaZeroConfig.W
        (Zeta23.CCM.localizedFiniteVector L N u)
        (Zeta23.CCM.localizedFiniteVector L N u) =
      Zeta23.CCM.localizedWeilAdditiveRHS
        (Zeta23.CCM.localizedFiniteVector L N u)
        (Zeta23.CCM.localizedFiniteVector L N u) :=
          zeta_W_self_eq_localizedWeilAdditiveRHS hC2 hcompact
    _ =
      Zeta23.CCM.quadraticForm
        (Zeta23.CCM.cutoffFreeMatrix L N) u :=
          Zeta23.CCM.localizedWeilAdditiveRHS_finiteVector_eq_cutoffFreeQuadraticForm
            N u hL

/-- **F0-B1A composition endpoint.**

On the boundary-flat finite sector the genuine concrete-zeta Weil form, the
localized additive RHS, and the canonical direct-source finite matrix quadratic
form are the same scalar.  This is a carrier-identification theorem only. -/
theorem zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ}
    (hL : 0 < L)
    (hflat : Zeta23.CCM.BoundaryFlatCoefficients N u) :
    zetaZeroConfig.W
        (Zeta23.CCM.localizedFiniteVector L N u)
        (Zeta23.CCM.localizedFiniteVector L N u) =
      Zeta23.CCM.quadraticForm
        (Zeta23.CCM.canonicalSourceMatrix L N) u := by
  simpa [Zeta23.CCM.canonicalSourceMatrix] using
    zeta_W_boundaryFlatFiniteVector_eq_cutoffFreeQuadraticForm
      N u hL hflat

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.zeta_W_boundaryFlatFiniteVector_eq_cutoffFreeQuadraticForm
#print axioms Zeta23.ExceptionalZero.zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm
