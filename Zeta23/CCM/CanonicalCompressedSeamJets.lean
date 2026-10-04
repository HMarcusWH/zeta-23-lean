import Zeta23.CCM.CanonicalPrimeSeamTaylor
import Zeta23.CCM.CanonicalGroundContinuity
import Zeta23.CCM.ConstrainedParitySpectrum
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate ArithmeticFunction

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
  simpa [primeSourceCoordinate] using
    (hasDerivAt_const L (1 : ℝ)).sub
      ((hasDerivAt_const L (Real.log q)).div
        (hasDerivAt_id L) hL)

theorem hasDerivAt_primeSourceCoordinate_first
    (q : ℕ) {L : ℝ} (hL : L ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.log q / s ^ 2)
      (-2 * Real.log q / L ^ 3) L := by
  have hden : HasDerivAt (fun s : ℝ => s ^ 2) (2 * L) L := by
    simpa [pow_two] using (hasDerivAt_id L).mul (hasDerivAt_id L)
  have h :=
    (hasDerivAt_const L (Real.log q)).div hden (pow_ne_zero 2 hL)
  convert h using 1 <;> field_simp [hL] <;> ring

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

/-! ## Matrix-valued source jets -/

/-- The elementary source matrix has the entrywise first jet packaged as a
genuine real derivative in the finite matrix space. -/
theorem hasDerivAt_sourceMatrix_sourceCoordinate
    (K : ℕ) (ω : ℝ) :
    HasDerivAt (fun t : ℝ => sourceMatrix t K)
      (sourceFirstJetMatrix K ω) ω := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  have hreal :=
    hasDerivAt_sourceEntryReal
      ω (centeredIndex K i) (centeredIndex K j)
  have hcomplex :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt ω hreal
  simpa [sourceMatrix_apply, sourceEntry_eq_ofReal, sourceFirstJetMatrix] using
    hcomplex

/-- The first source-matrix jet has the exact second source jet as derivative. -/
theorem hasDerivAt_sourceFirstJetMatrix
    (K : ℕ) (ω : ℝ) :
    HasDerivAt (fun t : ℝ => sourceFirstJetMatrix K t)
      (sourceSecondJetMatrix K ω) ω := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  have hreal :=
    hasDerivAt_sourceEntryDerivative
      ω (centeredIndex K i) (centeredIndex K j)
  have hcomplex :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt ω hreal
  simpa [sourceFirstJetMatrix, sourceSecondJetMatrix] using hcomplex

/-- First aperture jet of one frozen entering source atom. -/
def primeSourceMatrixFirstApertureJet
    (q : ℕ) (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  (Real.log q / L ^ 2) •
    sourceFirstJetMatrix K (primeSourceCoordinate q L)

/-- Second aperture jet of one frozen entering source atom. -/
def primeSourceMatrixSecondApertureJet
    (q : ℕ) (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  (-2 * Real.log q / L ^ 3) •
      sourceFirstJetMatrix K (primeSourceCoordinate q L) +
    (Real.log q / L ^ 2) ^ 2 •
      sourceSecondJetMatrix K (primeSourceCoordinate q L)

theorem hasDerivAt_sourceMatrix_primeSourceCoordinate
    (q K : ℕ) {L : ℝ} (hL : L ≠ 0) :
    HasDerivAt
      (fun s : ℝ => sourceMatrix (primeSourceCoordinate q s) K)
      (primeSourceMatrixFirstApertureJet q L K) L := by
  have hs :=
    hasDerivAt_sourceMatrix_sourceCoordinate K (primeSourceCoordinate q L)
  have hc := hasDerivAt_primeSourceCoordinate q hL
  simpa [primeSourceMatrixFirstApertureJet] using hs.comp L hc

theorem hasDerivAt_primeSourceMatrixFirstApertureJet
    (q K : ℕ) {L : ℝ} (hL : L ≠ 0) :
    HasDerivAt
      (fun s : ℝ => primeSourceMatrixFirstApertureJet q s K)
      (primeSourceMatrixSecondApertureJet q L K) L := by
  have hc := hasDerivAt_primeSourceCoordinate q hL
  have hcoeff := hasDerivAt_primeSourceCoordinate_first q hL
  have hjet :=
    (hasDerivAt_sourceFirstJetMatrix K (primeSourceCoordinate q L)).comp L hc
  have hprod := hcoeff.smul hjet
  simpa [primeSourceMatrixFirstApertureJet,
    primeSourceMatrixSecondApertureJet, add_comm, add_left_comm, add_assoc,
    smul_smul, mul_comm, mul_left_comm, mul_assoc] using hprod

/-- Every parity-boundary-flat legal vector has zero coefficient sum. -/
theorem parityBoundaryFlat_coordinateSum_zero
    (p : ReversalParity) (K : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p K) :
    ∑ i,
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
        (x : EuclideanSpace ℂ (Fin (2 * K + 1)))) i = 0 := by
  have hx :=
    (mem_euclideanParityBoundaryFlatSubspace_iff
      p K (x : EuclideanSpace ℂ (Fin (2 * K + 1)))).mp x.property
  cases p with
  | even =>
      rcases hx with ⟨hflat, _⟩
      exact sum_eq_zero_of_boundaryFlat
        ((mem_boundaryFlatSubspace_iff K _).mp hflat)
  | odd =>
      rcases hx with ⟨hflat, _⟩
      exact sum_eq_zero_of_boundaryFlat
        ((mem_boundaryFlatSubspace_iff K _).mp hflat)

/-- At entry, the first aperture source jet annihilates every legal parity
carrier vector. -/
theorem primeSourceMatrixFirstApertureJet_log_mulVec_zero
    (q K : ℕ) (hq : 2 ≤ q)
    (p : ReversalParity)
    (x : euclideanParityBoundaryFlatSubspace p K) :
    primeSourceMatrixFirstApertureJet q (Real.log q) K *ᵥ
        (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (x : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
  have hcoord := primeSourceCoordinate_log_self q hq
  rw [primeSourceMatrixFirstApertureJet, hcoord]
  simp only [Matrix.smul_mulVec]
  rw [sourceFirstJetMatrix_zero_mulVec_of_sum_zero K _
    (parityBoundaryFlat_coordinateSum_zero p K x)]
  simp

/-- At entry, the second aperture source jet also annihilates every legal
parity carrier vector.  The source-coordinate acceleration only multiplies the
same rank-one first jet, while the genuine second source jet is zero. -/
theorem primeSourceMatrixSecondApertureJet_log_mulVec_zero
    (q K : ℕ) (hq : 2 ≤ q)
    (p : ReversalParity)
    (x : euclideanParityBoundaryFlatSubspace p K) :
    primeSourceMatrixSecondApertureJet q (Real.log q) K *ᵥ
        (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (x : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
  have hcoord := primeSourceCoordinate_log_self q hq
  rw [primeSourceMatrixSecondApertureJet, hcoord, sourceSecondJetMatrix_zero]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.zero_mulVec,
    smul_zero, add_zero]
  rw [sourceFirstJetMatrix_zero_mulVec_of_sum_zero K _
    (parityBoundaryFlat_coordinateSum_zero p K x)]
  simp


end Zeta23.CCM

#print axioms Zeta23.CCM.sourceFirstJetMatrix_zero_mulVec_of_sum_zero
#print axioms Zeta23.CCM.sourceSecondJetMatrix_zero
#print axioms Zeta23.CCM.hasDerivAt_sourceMatrix_sourceCoordinate
#print axioms Zeta23.CCM.hasDerivAt_sourceFirstJetMatrix
#print axioms Zeta23.CCM.hasDerivAt_sourceMatrix_primeSourceCoordinate
#print axioms Zeta23.CCM.hasDerivAt_primeSourceMatrixFirstApertureJet
#print axioms Zeta23.CCM.primeSourceMatrixFirstApertureJet_log_mulVec_zero
#print axioms Zeta23.CCM.primeSourceMatrixSecondApertureJet_log_mulVec_zero
#print axioms Zeta23.CCM.enteringPrimeSourceEnergy_firstJet_zero
#print axioms Zeta23.CCM.enteringPrimeSourceEnergy_secondJet_zero
