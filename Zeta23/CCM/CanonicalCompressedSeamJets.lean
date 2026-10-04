import Zeta23.CCM.CanonicalPrimeSeamTaylor
import Zeta23.CCM.CanonicalGroundContinuity
import Zeta23.CCM.ConstrainedParitySpectrum
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#282 compressed seam jets

This file isolates the exact reason the production cutoff staircase is smoother
after legal compression than it is entrywise.

At a new logarithmic integer threshold the entering source atom has source
coordinate zero.  Its raw first source-coordinate derivative is the rank-one
matrix `2 * 1 1^*`; hence it annihilates every zero-sum legal vector.  Its
second source-coordinate derivative is zero entrywise.  The corresponding
fixed-vector energy therefore has zero first and second *aperture* jets at the
threshold.

These are seam facts about the genuine production source atom.  They do not
assert a higher-order barrier or any sign away from the seam.
-/

def sourceFirstJetMatrix (K : ℕ) (ω : ℝ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    (sourceEntryDerivative ω (centeredIndex K i) (centeredIndex K j) : ℂ)

def sourceSecondJetMatrix (K : ℕ) (ω : ℝ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    (sourceEntrySecondDerivative ω
      (centeredIndex K i) (centeredIndex K j) : ℂ)

theorem sourceFirstJetMatrix_zero_apply
    (K : ℕ) (i j : Fin (2 * K + 1)) :
    sourceFirstJetMatrix K 0 i j = 2 := by
  simp [sourceFirstJetMatrix]

theorem sourceFirstJetMatrix_zero_mulVec_of_sum_zero
    (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (hsum : ∑ j, u j = 0) :
    sourceFirstJetMatrix K 0 *ᵥ u = 0 := by
  funext i
  unfold Matrix.mulVec dotProduct
  simp only [sourceFirstJetMatrix_zero_apply]
  rw [← Finset.mul_sum, hsum]
  simp

theorem sourceSecondJetMatrix_zero
    (K : ℕ) :
    sourceSecondJetMatrix K 0 = 0 := by
  ext i j
  simp [sourceSecondJetMatrix]

theorem hasDerivAt_primeSourceCoordinate
    (q : ℕ) {L : ℝ} (hL : L ≠ 0) :
    HasDerivAt (primeSourceCoordinate q)
      (Real.log q / L ^ 2) L := by
  unfold primeSourceCoordinate
  convert
    (hasDerivAt_const L (1 : ℝ)).sub
      ((hasDerivAt_const L (Real.log q)).div
        (hasDerivAt_id L) hL) using 1 <;> ring

theorem hasDerivAt_primeSourceCoordinate_first
    (q : ℕ) {L : ℝ} (hL : L ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.log q / s ^ 2)
      (-2 * Real.log q / L ^ 3) L := by
  fun_prop (disch := assumption)

theorem sourceAtomRealEnergyDerivative_zero_of_boundaryFlat
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    sourceAtomRealEnergyDerivative K x 0 = 0 := by
  have hjet :=
    sourceAtomRealEnergy_boundaryFlat_jets_through_six
      K x hflat 1 (by omega) (by omega)
  rw [iteratedDeriv_one,
    (hasDerivAt_sourceAtomRealEnergy_transport K x 0).deriv] at hjet
  exact hjet

theorem sourceAtomRealEnergySecondDerivative_zero
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceAtomRealEnergySecondDerivative K x 0 = 0 := by
  unfold sourceAtomRealEnergySecondDerivative
  simp [sourceContractRealSecondDerivative_zero]

def enteringPrimeSourceEnergy
    (q K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (L : ℝ) : ℝ :=
  (Λ q / Real.sqrt q : ℝ) *
    sourceAtomRealEnergy K x (primeSourceCoordinate q L)

theorem enteringPrimeSourceEnergy_firstJet_zero
    (q K : ℕ) (hq : 2 ≤ q)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    deriv (enteringPrimeSourceEnergy q K x) (Real.log q) = 0 := by
  have hlog : Real.log (q : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast hq))
  have hcoord := hasDerivAt_primeSourceCoordinate q hlog
  have hcoord0 := primeSourceCoordinate_log_self q hq
  have hsource := hasDerivAt_sourceAtomRealEnergy_transport K x 0
  have hcomp :
      HasDerivAt
        (fun L : ℝ =>
          sourceAtomRealEnergy K x (primeSourceCoordinate q L))
        (sourceAtomRealEnergyDerivative K x 0 *
          (Real.log q / (Real.log q) ^ 2))
        (Real.log q) := by
    simpa [hcoord0] using hsource.comp (Real.log q) hcoord
  have hscaled := hcomp.const_mul (Λ q / Real.sqrt q : ℝ)
  unfold enteringPrimeSourceEnergy
  rw [hscaled.deriv,
    sourceAtomRealEnergyDerivative_zero_of_boundaryFlat K x hflat]
  ring

theorem enteringPrimeSourceEnergy_secondJet_zero
    (q K : ℕ) (hq : 2 ≤ q)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    deriv (fun L : ℝ => deriv (enteringPrimeSourceEnergy q K x) L)
      (Real.log q) = 0 := by
  have hlog : Real.log (q : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast hq))
  let omega := primeSourceCoordinate q
  let omega' := fun L : ℝ => Real.log q / L ^ 2
  let g' := sourceAtomRealEnergyDerivative K x
  have hfirstFun :
      (fun L : ℝ => deriv (enteringPrimeSourceEnergy q K x) L) =
        fun L : ℝ =>
          (Λ q / Real.sqrt q : ℝ) *
            (g' (omega L) * omega' L) := by
    funext L
    by_cases hL : L = 0
    · subst L
      simp [enteringPrimeSourceEnergy, omega, omega']
    · have hc := hasDerivAt_primeSourceCoordinate q hL
      have hg := hasDerivAt_sourceAtomRealEnergy_transport K x (omega L)
      unfold enteringPrimeSourceEnergy
      rw [(hg.comp L hc).const_mul (Λ q / Real.sqrt q : ℝ) |>.deriv]
      rfl
  rw [hfirstFun]
  have hcoord0 : omega (Real.log q) = 0 := by
    simpa [omega] using primeSourceCoordinate_log_self q hq
  have hg' := hasDerivAt_sourceAtomRealEnergyDerivative_transport K x 0
  have homega := hasDerivAt_primeSourceCoordinate q hlog
  have hleft :
      HasDerivAt (fun L : ℝ => g' (omega L))
        (sourceAtomRealEnergySecondDerivative K x 0 *
          (Real.log q / (Real.log q) ^ 2))
        (Real.log q) := by
    simpa [g', omega, hcoord0] using hg'.comp (Real.log q) homega
  have hright := hasDerivAt_primeSourceCoordinate_first q hlog
  have hscaled := (hleft.mul hright).const_mul (Λ q / Real.sqrt q : ℝ)
  rw [hscaled.deriv,
    sourceAtomRealEnergySecondDerivative_zero K x,
    sourceAtomRealEnergyDerivative_zero_of_boundaryFlat K x hflat]
  simp [g', omega, omega', hcoord0]

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceFirstJetMatrix_zero_mulVec_of_sum_zero
#print axioms Zeta23.CCM.sourceSecondJetMatrix_zero
#print axioms Zeta23.CCM.enteringPrimeSourceEnergy_firstJet_zero
#print axioms Zeta23.CCM.enteringPrimeSourceEnergy_secondJet_zero
