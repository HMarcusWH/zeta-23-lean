import Zeta23.CCM.DictionaryZeroSideMatrix
import Zeta23.CCM.CodimOneMatrixCompletion

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators

/-!
# H2b completion: localize the actual zero-side discrepancy

The actual finite zero-side matrix is available entrywise with absolute
summability. H1 identifies its pivoted basis-difference pairings with the
production dictionary matrix on the coefficient-sum-zero hyperplane. The
minimum-input H2a theorem then forces the whole discrepancy into the unique
two-sided coefficient-sum seam.

This does not prove that the discrepancy vanishes.
-/

/-- Real matrix pairing is additive under matrix subtraction. -/
theorem realMatrixPairing_sub
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (u v : ι → ℝ) :
    realMatrixPairing (A - B) u v =
      realMatrixPairing A u v - realMatrixPairing B u v := by
  unfold realMatrixPairing
  simp_rw [Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- H2a's pairing notation is additive under matrix subtraction. -/
theorem codimOneRealPairing_sub
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (u v : ι → ℝ) :
    codimOneRealPairing (A - B) u v =
      codimOneRealPairing A u v - codimOneRealPairing B u v := by
  rw [codimOneRealPairing_eq_realMatrixPairing,
    codimOneRealPairing_eq_realMatrixPairing,
    codimOneRealPairing_eq_realMatrixPairing,
    realMatrixPairing_sub]

/-- The actual finite zero-side discrepancy from the deterministic production
matrix. -/
def zeroSideDiscrepancy
    (hs : ZetaSeam) (N : ℕ) (L : ℝ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  zeroSideMatrix hs N L - dictionaryMatrix L N

/-- The actual discrepancy is symmetric. -/
theorem zeroSideDiscrepancy_apply_comm
    (hs : ZetaSeam) (N : ℕ) (L : ℝ)
    (i j : Fin (2 * N + 1)) :
    zeroSideDiscrepancy hs N L i j =
      zeroSideDiscrepancy hs N L j i := by
  unfold zeroSideDiscrepancy
  simp only [Matrix.sub_apply]
  rw [zeroSideMatrix_apply_comm hs N L i j,
    dictionaryMatrix_apply_comm L N i j]

/-- H1 on exactly the probes needed by H2a: every pivoted basis-difference
pairing of the actual discrepancy vanishes. -/
theorem zeroSideDiscrepancy_basisDiff_pairing_eq_zero
    (hs : ZetaSeam)
    (N : ℕ)
    (p i j : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    codimOneRealPairing (zeroSideDiscrepancy hs N L)
        (codimOneBasisDiff p i) (codimOneBasisDiff p j) = 0 := by
  let u : Fin (2 * N + 1) → ℝ := codimOneBasisDiff p i
  let v : Fin (2 * N + 1) → ℝ := codimOneBasisDiff p j
  have hu : coefficientSumReal N u = 0 := by
    simp [coefficientSumReal, u]
  have hv : coefficientSumReal N v = 0 := by
    simp [coefficientSumReal, v]
  have hZ :=
    zeroSideMatrix_basisDiff_pairing_eq_smoothCoreZeroPolarization
      hs N p i j hL
  have hH1 :=
    smoothCoreZeroPolarization_eq_realMatrixPairing
      hs N u v hL hu hv
  unfold zeroSideDiscrepancy
  rw [codimOneRealPairing_sub]
  rw [show
      codimOneRealPairing (zeroSideMatrix hs N L) u v =
        smoothCoreZeroPolarization hs N L u v by
      simpa [u, v] using hZ]
  rw [hH1]
  rw [codimOneRealPairing_eq_realMatrixPairing]
  exact sub_self _

/-- Canonical H2b seam vector. It is explicit in the pivot column of the actual
discrepancy and is the object to be tested by H2+ parity/displacement arguments. -/
def zeroSideCompletionVector
    (hs : ZetaSeam) (N : ℕ) (L : ℝ) :
    Fin (2 * N + 1) → ℂ :=
  codimOneCompletionVector
    (zeroSideDiscrepancy hs N L) (0 : Fin (2 * N + 1))

/-- H2b endpoint: the actual finite zeta zero-side discrepancy is exactly a
two-sided coefficient-sum seam. -/
theorem zeroSideDiscrepancy_eq_completion
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    zeroSideDiscrepancy hs N L =
      vecMulVec (fun _ => (1 : ℂ)) (zeroSideCompletionVector hs N L) +
        vecMulVec (zeroSideCompletionVector hs N L) (fun _ => (1 : ℂ)) := by
  simpa [zeroSideCompletionVector] using
    codimOneMatrixCompletion_of_basisDiff
      (zeroSideDiscrepancy hs N L)
      (0 : Fin (2 * N + 1))
      (zeroSideDiscrepancy_apply_comm hs N L)
      (fun i j =>
        zeroSideDiscrepancy_basisDiff_pairing_eq_zero
          hs N (0 : Fin (2 * N + 1)) i j hL)

/-- H2b rank consequence for the actual zeta-dependent discrepancy. -/
theorem rank_zeroSideDiscrepancy_le_two
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    (zeroSideDiscrepancy hs N L).rank ≤ 2 := by
  exact rank_codimOneMatrixCompletion_of_basisDiff_le_two
    (zeroSideDiscrepancy hs N L)
    (0 : Fin (2 * N + 1))
    (zeroSideDiscrepancy_apply_comm hs N L)
    (fun i j =>
      zeroSideDiscrepancy_basisDiff_pairing_eq_zero
        hs N (0 : Fin (2 * N + 1)) i j hL)

/-- Equivalent additive presentation: the actual zero-side matrix is the
production dictionary matrix plus the canonical two-sided seam. -/
theorem zeroSideMatrix_eq_dictionaryMatrix_add_completion
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    zeroSideMatrix hs N L =
      dictionaryMatrix L N +
        (vecMulVec (fun _ => (1 : ℂ)) (zeroSideCompletionVector hs N L) +
          vecMulVec (zeroSideCompletionVector hs N L) (fun _ => (1 : ℂ))) := by
  have h := zeroSideDiscrepancy_eq_completion hs N hL
  unfold zeroSideDiscrepancy at h
  have h' := sub_eq_iff_eq_add.mp h
  simpa [add_comm, add_left_comm, add_assoc] using h'

end Zeta23.CCM

#print axioms Zeta23.CCM.zeroSideDiscrepancy_basisDiff_pairing_eq_zero
#print axioms Zeta23.CCM.zeroSideDiscrepancy_eq_completion
#print axioms Zeta23.CCM.rank_zeroSideDiscrepancy_le_two
