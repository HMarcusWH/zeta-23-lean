import Zeta23.CCM.CanonicalSourceEnergy
import Zeta23.CCM.DictionaryArchLift

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A1: archimedean small-aperture obligations

The full-space inequality remains a useful stronger target, but the RH-relevant
critical path only needs the legal boundary-flat carrier.  Neither proposition
is asserted here; they are explicit proof obligations.
-/

/-- Stronger full-space canonical archimedean upper bound. -/
def CanonicalArchSmallApertureUpperBound : Prop :=
  ∀ L : ℝ, 0 < L → L ≤ (1 : ℝ) / 512 →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      matrixRealEnergy (canonicalArchMatrix L K) x ≤
        (L - 2) * ‖x‖ ^ 2

/-- Critical-path version restricted to the exact legal boundary-flat carrier.
This is weaker than the full-space target and is sufficient for the terminal
finite-Weil positivity route. -/
def CanonicalBoundaryFlatArchSmallApertureUpperBound : Prop :=
  ∀ L : ℝ, 0 < L → L ≤ (1 : ℝ) / 512 →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      BoundaryFlatCoefficients K
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) →
      matrixRealEnergy (canonicalArchMatrix L K) x ≤
        (L - 2) * ‖x‖ ^ 2

/-- Any future full-space proof immediately discharges the weaker legal-carrier
obligation. -/
theorem canonicalBoundaryFlatArchSmallApertureUpperBound_of_full
    (h : CanonicalArchSmallApertureUpperBound) :
    CanonicalBoundaryFlatArchSmallApertureUpperBound := by
  intro L hL hsmall K x _hflat
  exact h L hL hsmall K x


/-!
## Exact dictionary/canonical archimedean bridge

The already-proved dictionary archimedean functional uses the historical
printed component together with the exact diagonal correction.  The
source-normalization repair identifies that coefficient entrywise with the
negative direct equation-(4.4) canonical archimedean matrix.  This bridge is
pure finite algebra; it adds no sign assumption.
-/

/-- The finite dictionary archimedean functional is exactly the negative
canonical archimedean quadratic form in the repaired source normalization. -/
theorem dictionaryArchRHS_dictionaryTest_eq_neg_canonicalArchQuadraticForm
    (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryArchRHS (dictionaryTest K u L) =
      -quadraticForm (canonicalArchMatrix L K) u := by
  rw [dictionaryArchRHS_dictionaryTest K u hL]
  unfold quadraticForm
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [canonicalArchMatrix_apply,
    sourceEq44ArchComponent_eq_cutoffFreeArchComponent,
    cutoffFreeArchComponent_eq_archComponent_sub_two_correction]
  by_cases hij : i = j
  · subst j
    simp
    ring
  · have hidx : centeredIndex K i ≠ centeredIndex K j := by
      intro h
      exact hij (centeredIndex_injective K h)
    simp [hij, hidx]
    ring

/-- Real-energy form of the exact dictionary/canonical bridge. -/
theorem matrixRealEnergy_canonicalArchMatrix_eq_neg_re_dictionaryArchRHS
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalArchMatrix L K) x =
      -Complex.re
        (dictionaryArchRHS
          (dictionaryTest K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) L)) := by
  unfold matrixRealEnergy
  rw [dictionaryArchRHS_dictionaryTest_eq_neg_canonicalArchQuadraticForm
    K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) hL]
  simp

/-- Minimal analytic target beneath the boundary-flat matrix inequality:
the dictionary archimedean functional must have the corresponding positive
real-part lower bound on the legal carrier. -/
def CanonicalBoundaryFlatDictionaryArchLowerBound : Prop :=
  ∀ L : ℝ, 0 < L → L ≤ (1 : ℝ) / 512 →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      BoundaryFlatCoefficients K
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) →
      (2 - L) * ‖x‖ ^ 2 ≤
        Complex.re
          (dictionaryArchRHS
            (dictionaryTest K
              ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) L))

/-- The scalar/function-space dictionary lower bound is exactly sufficient for
the critical boundary-flat canonical archimedean upper bound. -/
theorem canonicalBoundaryFlatArchSmallApertureUpperBound_of_dictionaryLower
    (h : CanonicalBoundaryFlatDictionaryArchLowerBound) :
    CanonicalBoundaryFlatArchSmallApertureUpperBound := by
  intro L hL hsmall K x hflat
  have hd := h L hL hsmall K x hflat
  rw [matrixRealEnergy_canonicalArchMatrix_eq_neg_re_dictionaryArchRHS
    hL K x]
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalBoundaryFlatArchSmallApertureUpperBound_of_full
#print axioms Zeta23.CCM.dictionaryArchRHS_dictionaryTest_eq_neg_canonicalArchQuadraticForm
#print axioms Zeta23.CCM.matrixRealEnergy_canonicalArchMatrix_eq_neg_re_dictionaryArchRHS
#print axioms Zeta23.CCM.canonicalBoundaryFlatArchSmallApertureUpperBound_of_dictionaryLower
