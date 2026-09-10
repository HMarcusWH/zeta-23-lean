import Zeta23.CCM.CanonicalApertureContinuity
import Zeta23.CCM.CanonicalApertureComplexSource
import Zeta23.CCM.CanonicalSourceChannels

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1b: frozen canonical source analytic scaffold

This module starts the exact source-side input for the analytic regular-aperture
route.  It freezes the prime-power cutoff, separates only the production
`wCorrection` scalar from the direct equation-(4.4) archimedean channel, and
proves the resulting full frozen source has the exact real-axis form

`M_Q(L) = -log(L) * I + R_Q(L)`.

The point of separating only `wCorrection` is that PR #140 already proved its
exact scalar extraction.  No legacy printed-(4.11) correction is used.

This file deliberately makes no holomorphy, determinant-nonidentity, dense
regularity, positivity, negative-root-exclusion, or RH claim.
-/

/-- Production direct equation-(4.4) archimedean entry with the sole
index-independent `wCorrection` diagonal scalar removed. -/
def canonicalArchWithoutWComponent (n m : ℤ) (L : ℝ) : ℝ :=
  if n = m then
    2 * (sourceEq44GammaL n L - wCorrection L) - 2 * betaL n L
  else
    (alphaL m L - alphaL n L) / ((n - m : ℤ) : ℝ)

/-- Exact entrywise recovery of the production archimedean channel from its
`wCorrection`-free part. -/
theorem sourceEq44ArchComponent_eq_withoutW_add_scalar
    (n m : ℤ) (L : ℝ) :
    sourceEq44ArchComponent n m L =
      canonicalArchWithoutWComponent n m L +
        if n = m then 2 * wCorrection L else 0 := by
  by_cases hnm : n = m
  · subst m
    simp [sourceEq44ArchComponent, canonicalArchWithoutWComponent]
    ring
  · simp [sourceEq44ArchComponent, canonicalArchWithoutWComponent, hnm]

/-- Matrix form of the direct archimedean channel with `wCorrection` removed. -/
def canonicalArchWithoutWMatrix (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    (canonicalArchWithoutWComponent
      (centeredIndex K i) (centeredIndex K j) L : ℂ)

/-- The production archimedean matrix is its `wCorrection`-free part plus the
scalar diagonal `2*wCorrection(L)`. -/
theorem canonicalArchMatrix_eq_withoutW_add_scalar
    (L : ℝ) (K : ℕ) :
    canonicalArchMatrix L K =
      canonicalArchWithoutWMatrix L K +
        ((2 * wCorrection L : ℝ) : ℂ) •
          (1 : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ) := by
  ext i j
  change
    (sourceEq44ArchComponent (centeredIndex K i) (centeredIndex K j) L : ℂ) =
      (canonicalArchWithoutWComponent
        (centeredIndex K i) (centeredIndex K j) L : ℂ) +
        ((2 * wCorrection L : ℝ) : ℂ) * (if i = j then 1 else 0)
  rw [sourceEq44ArchComponent_eq_withoutW_add_scalar]
  by_cases hij : i = j
  · subst j
    simp
  · have hidx : centeredIndex K i ≠ centeredIndex K j := by
      exact fun h => hij ((centeredIndex_injective K) h)
    simp [hij, hidx]

/-- Full canonical source with the finite prime-power horizon frozen at `Q`.
Outside the physical cutoff cell this is only an auxiliary frozen family. -/
def frozenCanonicalSourceMatrix
    (Q : ℕ) (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  canonicalPoleMatrix L K -
    canonicalArchMatrix L K -
      frozenCanonicalPrimeMatrix Q L K

/-- On its physical cutoff cell, the frozen source is exactly the actual
production `canonicalSourceMatrix`. -/
theorem frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_fixedCell
    {Q : ℕ} (hQ : 1 ≤ Q)
    {L : ℝ} (hL : L ∈ fixedCanonicalCutoffCell Q)
    (K : ℕ) :
    frozenCanonicalSourceMatrix Q L K = canonicalSourceMatrix L K := by
  have hfloor : ⌊Real.exp L⌋₊ = Q :=
    natFloor_exp_eq_on_fixedCanonicalCutoffCell hQ hL
  rw [frozenCanonicalSourceMatrix,
    canonicalSourceMatrix_eq_pole_sub_arch_sub_prime,
    frozenCanonicalPrimeMatrix_eq_canonicalPrimeMatrix L K hfloor]

/-- Real frozen-source remainder after extracting the exact scalar `-log L`.
This is the object to be complexified in the next analytic layer. -/
def frozenCanonicalSourceRemainderReal
    (Q : ℕ) (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  canonicalPoleMatrix L K -
    canonicalArchWithoutWMatrix L K -
      frozenCanonicalPrimeMatrix Q L K +
        (canonicalApertureScalarRemainder L : ℂ) •
          (1 : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)

/-- Exact real-axis scalar decomposition of the full frozen production source.
The scalar coefficient is exactly `-1`; no projected/basis Gram matrix appears
at the ambient source level. -/
theorem frozenCanonicalSourceMatrix_eq_neg_log_identity_add_remainder
    (Q K : ℕ) {L : ℝ} (hL : 0 < L) :
    frozenCanonicalSourceMatrix Q L K =
      (-(Real.log L : ℂ)) •
          (1 : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ) +
        frozenCanonicalSourceRemainderReal Q L K := by
  rw [frozenCanonicalSourceMatrix,
    canonicalArchMatrix_eq_withoutW_add_scalar,
    frozenCanonicalSourceRemainderReal]
  have hsR := neg_two_wCorrection_eq_neg_log_add_remainder hL
  have hsC := congrArg (fun x : ℝ => (x : ℂ)) hsR
  push_cast at hsC
  ext i j
  by_cases hij : i = j
  · subst j
    simp
    linear_combination hsC
  · simp [hij]

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceEq44ArchComponent_eq_withoutW_add_scalar
#print axioms Zeta23.CCM.canonicalArchMatrix_eq_withoutW_add_scalar
#print axioms Zeta23.CCM.frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_fixedCell
#print axioms Zeta23.CCM.frozenCanonicalSourceMatrix_eq_neg_log_identity_add_remainder
