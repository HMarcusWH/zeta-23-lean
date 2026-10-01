import Zeta23.CCM.CanonicalParityFirstCrossingShell
import Zeta23.CCM.FirstCrossingSourceDynamics
import Zeta23.CCM.CanonicalApertureLocation
import Zeta23.CCM.LiftedPredecessorRegularity
import Zeta23.CCM.HermitianSchurEnvelopeDerivative

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#278 interior first-crossing barrier target

This module isolates the exact OPEN production theorem for contacts lying
strictly inside one fixed physical cutoff cell.

Generic Hermitian contact geometry is not enough: the repository already
contains exact countermodels and mixed Schur-derivative evidence.  The missing
input must therefore constrain the actual production regular zero-shift Schur
endpoint through the canonical source family.

No barrier is assumed or proved here.
-/

/-- OPEN target: no canonical parity first-crossing shell can have its contact
strictly inside a fixed physical cutoff cell. -/
def CanonicalInteriorFirstCrossingBarrier : Prop :=
  ∀ c : CanonicalParityFirstCrossingShell,
    ∀ Q : ℕ, 1 ≤ Q →
      c.Lstar ∈ fixedCanonicalCutoffCell Q →
        False

/-- Scalar production target for the interior route.

On a first-crossing state inside one frozen cutoff cell, every sufficiently
nearby regular one-step state with nonnegative predecessor should have a
nonnegative canonical regular zero-shift Schur endpoint.  Together with regular
bad-state density this contradicts the already-proved negative endpoint at a
bad regular successor.

This proposition is intentionally not promoted as theorem authority. -/
def CanonicalInteriorRegularEndpointBarrier : Prop :=
  ∀ c : CanonicalParityFirstCrossingShell,
    ∀ Q : ℕ, 1 ≤ Q →
      c.Lstar ∈ fixedCanonicalCutoffCell Q →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ L : ℝ,
            c.Lstar < L →
            L < c.Lstar + δ →
            L ∈ fixedCanonicalCutoffCell Q →
            ∀ hreg : IntrinsicPredecessorRegular c.p L c.k,
              PredecessorSectorNonnegative c.p L c.k →
              0 ≤ Complex.re
                (regularZeroShiftSchurEndpoint c.p L c.k hreg)

/-- The scalar regular-endpoint barrier is sufficient for the full interior
first-crossing exclusion.  The proof spends the arbitrarily-close regular
negative endpoint theorem and only elementary distance to the right edge of the
current cutoff cell. -/
theorem canonicalInteriorFirstCrossingBarrier_of_regularEndpointBarrier
    (hendpoint : CanonicalInteriorRegularEndpointBarrier) :
    CanonicalInteriorFirstCrossingBarrier := by
  intro c Q hQ hcell
  obtain ⟨δ, hδ, hnonneg⟩ := hendpoint c Q hQ hcell
  let δcell : ℝ :=
    (Real.log ((Q + 1 : ℕ) : ℝ) - c.Lstar) / 2
  have hδcell : 0 < δcell := by
    dsimp [δcell]
    linarith [hcell.2]
  let ε : ℝ := min δ δcell
  have hε : 0 < ε := lt_min hδ hδcell
  obtain ⟨L, hLlo, hLhi, hprev, hreg, hneg⟩ :=
    c.exists_arbitrarilyClose_regularZeroShiftEndpoint_neg ε hε
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεδcell : ε ≤ δcell := min_le_right _ _
  have hLhiδ : L < c.Lstar + δ := by
    linarith
  have hLcell : L ∈ fixedCanonicalCutoffCell Q := by
    constructor
    · exact lt_trans hcell.1 hLlo
    · dsimp [δcell] at hεδcell
      linarith [hcell.2]
  have hge :=
    hnonneg L hLlo hLhiδ hLcell hreg hprev
  linarith


end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalInteriorFirstCrossingBarrier_of_regularEndpointBarrier
