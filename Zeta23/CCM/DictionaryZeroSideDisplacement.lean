import Zeta23.CCM.DictionaryZeroSideBridge
import Zeta23.CCM.Displacement

noncomputable section

namespace Zeta23.CCM

open Matrix

/-!
# Actual zero-side displacement closure

The exact production bridge identifies the actual finite zeta zero-side matrix
with the formal CCM matrix plus the scalar correction
`2*cCorrection(L) * I`.  The already-proved generic displacement-transfer
theorem removes scalar matrices from the commutator.  Consequently the actual
zero-side matrix inherits the exact formal CCM displacement identity with no
extra factor two.

This is a structural finite-matrix theorem only.  Rank-two displacement is
generic divided-difference structure and is not a positivity, zero-location,
finite-to-infinite, or RH statement.
-/

/-- The actual finite zeta zero-side matrix has exactly the production CCM
index displacement.  The scalar correction commutes with the index diagonal,
so the displacement vector is not rescaled. -/
theorem zeroSideMatrix_displacement
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    indexMatrix N * zeroSideMatrix hs N L -
        zeroSideMatrix hs N L * indexMatrix N =
      vecMulVec (displacementVector L N) (fun _ => 1) -
        vecMulVec (fun _ => 1) (displacementVector L N) := by
  have hA :
      zeroSideMatrix hs N L =
        (1 : ℂ) • finiteMatrix L N +
          ((2 * cCorrection L : ℝ) : ℂ) •
            (1 : Matrix
              (Fin (2 * N + 1))
              (Fin (2 * N + 1)) ℂ) := by
    simpa using
      zeroSideMatrix_eq_finiteMatrix_add_correction hs N hL
  have hM :
      Zeta23.ExceptionalZero.displacement
          (indexMatrix N) (finiteMatrix L N) =
        vecMulVec (displacementVector L N) (fun _ => 1) -
          vecMulVec (fun _ => 1) (displacementVector L N) := by
    simpa [Zeta23.ExceptionalZero.displacement] using
      finiteMatrix_displacement hL N
  have h :=
    Zeta23.ExceptionalZero.displacement_eq_of_eq_smul_add_scalar
      (D := indexMatrix N)
      (M := finiteMatrix L N)
      (A := zeroSideMatrix hs N L)
      (g := displacementVector L N)
      (u := fun _ => (1 : ℂ))
      (k := (1 : ℂ))
      (c := ((2 * cCorrection L : ℝ) : ℂ))
      hA hM
  simpa [Zeta23.ExceptionalZero.displacement] using h

/-- Rank form of the actual zero-side displacement theorem. -/
theorem rank_zeroSideMatrix_displacement_le_two
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    (indexMatrix N * zeroSideMatrix hs N L -
      zeroSideMatrix hs N L * indexMatrix N).rank ≤ 2 := by
  have hA :
      zeroSideMatrix hs N L =
        (1 : ℂ) • finiteMatrix L N +
          ((2 * cCorrection L : ℝ) : ℂ) •
            (1 : Matrix
              (Fin (2 * N + 1))
              (Fin (2 * N + 1)) ℂ) := by
    simpa using
      zeroSideMatrix_eq_finiteMatrix_add_correction hs N hL
  have hM :
      Zeta23.ExceptionalZero.displacement
          (indexMatrix N) (finiteMatrix L N) =
        vecMulVec (displacementVector L N) (fun _ => 1) -
          vecMulVec (fun _ => 1) (displacementVector L N) := by
    simpa [Zeta23.ExceptionalZero.displacement] using
      finiteMatrix_displacement hL N
  have h :=
    Zeta23.ExceptionalZero.rank_displacement_le_two_of_eq_smul_add_scalar
      (D := indexMatrix N)
      (M := finiteMatrix L N)
      (A := zeroSideMatrix hs N L)
      (g := displacementVector L N)
      (u := fun _ => (1 : ℂ))
      (k := (1 : ℂ))
      (c := ((2 * cCorrection L : ℝ) : ℂ))
      hA hM
  simpa [Zeta23.ExceptionalZero.displacement] using h

end Zeta23.CCM

#print axioms Zeta23.CCM.zeroSideMatrix_displacement
#print axioms Zeta23.CCM.rank_zeroSideMatrix_displacement_le_two
