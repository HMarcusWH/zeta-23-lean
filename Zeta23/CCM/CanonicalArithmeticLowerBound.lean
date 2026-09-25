import Zeta23.CCM.CofinalLowerBound
import Zeta23.CCM.CanonicalPrimeRemainder

noncomputable section

namespace Zeta23.CCM

/-!
# Exact arithmetic form of a lower certificate

This file fixes the signs and Euclidean norm in the remaining estimate.
It does not construct any certificate. The error must bound ALL legal vectors
at the same size, not just a computed trial vector.
-/

/-- The signed arithmetic estimate is equivalent to a canonical energy lower
bound, without an absolute-value relaxation or normalization loss. -/
theorem canonicalSourceChannelEnergy_lowerBound_iff
    {L : ℝ} (hL : 0 < L) (K : ℕ) (ε : ℝ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    -ε * ‖x‖ ^ 2 ≤ canonicalSourceChannelEnergy L K x ↔
      canonicalPrimeFreeBudget L K x + canonicalPrimeRemainderEnergy L K x ≤
        ε * ‖x‖ ^ 2 := by
  rw [canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget hL K x]
  constructor <;> intro h <;> linarith

/-- All-vector lower-bound obligation on the existing Euclidean boundary-flat
subspace. This is not satisfied by a finite vector sample. -/
def CanonicalArithmeticLowerBound (L : ℝ) (K : ℕ) (ε : ℝ) : Prop :=
  ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
    x ∈ euclideanBoundaryFlatSubspace K →
      canonicalPrimeFreeBudget L K x + canonicalPrimeRemainderEnergy L K x ≤
        ε * ‖x‖ ^ 2

/-- Exact equivalence of the two all-vector formulations. -/
theorem canonicalArithmeticLowerBound_iff_energy
    {L : ℝ} (hL : 0 < L) (K : ℕ) (ε : ℝ) :
    CanonicalArithmeticLowerBound L K ε ↔
      ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
        x ∈ euclideanBoundaryFlatSubspace K →
          -ε * ‖x‖ ^ 2 ≤ canonicalSourceChannelEnergy L K x := by
  constructor
  · intro h x hx
    exact (canonicalSourceChannelEnergy_lowerBound_iff hL K ε x).mpr (h x hx)
  · intro h x hx
    exact (canonicalSourceChannelEnergy_lowerBound_iff hL K ε x).mp (h x hx)

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalSourceChannelEnergy_lowerBound_iff
#print axioms Zeta23.CCM.canonicalArithmeticLowerBound_iff_energy
