import Zeta23.CCM.CanonicalPrimeSeamTaylor
import Zeta23.CCM.CanonicalGroundContinuity
import Zeta23.CCM.ConstrainedParitySpectrum
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set Filter
open scoped BigOperators ComplexConjugate ArithmeticFunction Topology

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
  have h :=
    (hasDerivAt_const L (1 : ℝ)).sub
      ((hasDerivAt_const L (Real.log q)).div
        (hasDerivAt_id L) hL)
  simpa only [primeSourceCoordinate, Pi.sub_apply, Pi.div_apply, id_eq,
    zero_mul, mul_one, zero_sub, sub_neg_eq_add, zero_add] using h

theorem hasDerivAt_primeSourceCoordinate_first
    (q : ℕ) {L : ℝ} (hL : L ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.log q / s ^ 2)
      (-2 * Real.log q / L ^ 3) L := by
  have hden := (hasDerivAt_id L).pow 2
  have h :=
    (hasDerivAt_const L (Real.log q)).div hden (pow_ne_zero 2 hL)
  simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one, zero_mul, zero_sub, sub_neg_eq_add, zero_add] using h

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
  have hsource0 := hasDerivAt_sourceAtomRealEnergy_transport K x 0
  have hsource :
      HasDerivAt (sourceAtomRealEnergy K x)
        (sourceAtomRealEnergyDerivative K x 0)
        (primeSourceCoordinate q (Real.log q)) := by
    simpa [hcoord0] using hsource0
  have hcomp :
      HasDerivAt
        (fun L : ℝ =>
          sourceAtomRealEnergy K x (primeSourceCoordinate q L))
        (sourceAtomRealEnergyDerivative K x 0 *
          (Real.log q / (Real.log q) ^ 2))
        (Real.log q) := by
    exact hsource.comp (Real.log q) hcoord
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
  let omega : ℝ → ℝ := primeSourceCoordinate q
  let omega' : ℝ → ℝ := fun L : ℝ => Real.log q / L ^ 2
  let g' : ℝ → ℝ := sourceAtomRealEnergyDerivative K x
  let c : ℝ := Λ q / Real.sqrt q
  have hfirstFun :
      (fun L : ℝ => deriv (enteringPrimeSourceEnergy q K x) L) =ᶠ[nhds (Real.log q)]
        fun L : ℝ => c * (g' (omega L) * omega' L) := by
    filter_upwards [eventually_ne_nhds hlog] with L hL
    have hc := hasDerivAt_primeSourceCoordinate q hL
    have hg := hasDerivAt_sourceAtomRealEnergy_transport K x (omega L)
    have hcomp :
        HasDerivAt
          (fun t : ℝ => sourceAtomRealEnergy K x (omega t))
          (g' (omega L) * omega' L) L := by
      simpa only [g', omega, omega'] using hg.comp L hc
    have hscaled :
        HasDerivAt
          (fun t : ℝ => c * sourceAtomRealEnergy K x (omega t))
          (c * (g' (omega L) * omega' L)) L :=
      hcomp.const_mul c
    have hd := hscaled.deriv
    simpa only [enteringPrimeSourceEnergy, c, omega] using hd
  rw [Filter.EventuallyEq.deriv_eq hfirstFun]
  have hcoord0 : omega (Real.log q) = 0 := by
    simpa only [omega] using primeSourceCoordinate_log_self q hq
  have hg'0 := hasDerivAt_sourceAtomRealEnergyDerivative_transport K x 0
  have hg' :
      HasDerivAt (sourceAtomRealEnergyDerivative K x)
        (sourceAtomRealEnergySecondDerivative K x 0)
        (omega (Real.log q)) := by
    simpa only [hcoord0] using hg'0
  have homega := hasDerivAt_primeSourceCoordinate q hlog
  have hleft :
      HasDerivAt (fun L : ℝ => g' (omega L))
        (sourceAtomRealEnergySecondDerivative K x 0 *
          (Real.log q / (Real.log q) ^ 2))
        (Real.log q) := by
    have hc := hg'.comp (Real.log q) homega
    simpa only [Function.comp_apply, g', omega] using hc
  have hright : HasDerivAt omega' (-2 * Real.log q / (Real.log q) ^ 3)
      (Real.log q) := by
    simpa only [omega'] using hasDerivAt_primeSourceCoordinate_first q hlog
  have hscaled :
      HasDerivAt
        (fun L : ℝ => c * (g' (omega L) * omega' L))
        (c * (
          (sourceAtomRealEnergySecondDerivative K x 0 *
              (Real.log q / (Real.log q) ^ 2)) * omega' (Real.log q) +
            g' (omega (Real.log q)) *
              (-2 * Real.log q / (Real.log q) ^ 3)))
        (Real.log q) :=
    (hleft.mul hright).const_mul c
  rw [hscaled.deriv]
  rw [sourceAtomRealEnergySecondDerivative_zero K x,
    sourceAtomRealEnergyDerivative_zero_of_boundaryFlat K x hflat]
  simp [g', omega, omega', hcoord0]

/-! ## Matrix-valued source jets -/

/-- The elementary source matrix has the entrywise first jet packaged as a
genuine real derivative in the finite matrix space. -/
theorem hasDerivAt_sourceMatrix_sourceCoordinate
    (K : ℕ) (ω : ℝ) :
    HasDerivAt (fun t : ℝ => sourceMatrix t K)
      (sourceFirstJetMatrix K ω) ω := by
  change HasDerivAt
    (fun t : ℝ => fun i j => sourceMatrix t K i j)
    (fun i j => sourceFirstJetMatrix K ω i j) ω
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hreal :=
    hasDerivAt_sourceEntryReal
      ω (centeredIndex K i) (centeredIndex K j)
  simpa [sourceMatrix_apply, sourceEntry_eq_ofReal, sourceFirstJetMatrix] using
    hreal.ofReal_comp

/-- The first source-matrix jet has the exact second source jet as derivative. -/
theorem hasDerivAt_sourceFirstJetMatrix
    (K : ℕ) (ω : ℝ) :
    HasDerivAt (fun t : ℝ => sourceFirstJetMatrix K t)
      (sourceSecondJetMatrix K ω) ω := by
  change HasDerivAt
    (fun t : ℝ => fun i j => sourceFirstJetMatrix K t i j)
    (fun i j => sourceSecondJetMatrix K ω i j) ω
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hreal :=
    hasDerivAt_sourceEntryDerivative
      ω (centeredIndex K i) (centeredIndex K j)
  simpa [sourceFirstJetMatrix, sourceSecondJetMatrix] using
    hreal.ofReal_comp

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
  change HasDerivAt
    (fun s : ℝ => fun i j =>
      sourceMatrix (primeSourceCoordinate q s) K i j)
    (fun i j => primeSourceMatrixFirstApertureJet q L K i j) L
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hc := hasDerivAt_primeSourceCoordinate q hL
  have he :=
    hasDerivAt_sourceEntryReal
      (primeSourceCoordinate q L) (centeredIndex K i) (centeredIndex K j)
  have hcomp := he.comp L hc
  have hcomplex := hcomp.ofReal_comp
  simpa [sourceMatrix_apply, sourceEntry_eq_ofReal,
    primeSourceMatrixFirstApertureJet, sourceFirstJetMatrix,
    real_smul, mul_comm] using hcomplex

theorem hasDerivAt_primeSourceMatrixFirstApertureJet
    (q K : ℕ) {L : ℝ} (hL : L ≠ 0) :
    HasDerivAt
      (fun s : ℝ => primeSourceMatrixFirstApertureJet q s K)
      (primeSourceMatrixSecondApertureJet q L K) L := by
  change HasDerivAt
    (fun s : ℝ => fun i j => primeSourceMatrixFirstApertureJet q s K i j)
    (fun i j => primeSourceMatrixSecondApertureJet q L K i j) L
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hc := hasDerivAt_primeSourceCoordinate q hL
  have hcoeff := hasDerivAt_primeSourceCoordinate_first q hL
  have he :=
    hasDerivAt_sourceEntryDerivative
      (primeSourceCoordinate q L) (centeredIndex K i) (centeredIndex K j)
  have hentry := he.comp L hc
  have hprod := hcoeff.mul hentry
  have hcomplex := hprod.ofReal_comp
  simpa [primeSourceMatrixFirstApertureJet,
    primeSourceMatrixSecondApertureJet, sourceFirstJetMatrix,
    sourceSecondJetMatrix, real_smul, mul_add, add_mul,
    mul_comm, mul_left_comm, mul_assoc, pow_two] using hcomplex

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
