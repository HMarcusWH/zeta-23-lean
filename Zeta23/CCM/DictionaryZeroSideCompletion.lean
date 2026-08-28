import Zeta23.CCM.DictionaryZeroSideMatrix
import Zeta23.CCM.CodimOneMatrixCompletion

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators

/-!
# H2b completion: localize the actual zero-side discrepancy

The actual finite zero-side matrix is now available entrywise.  H1 identifies
its real pairing with the production dictionary matrix on the coefficient-sum
zero hyperplane.  H2a then forces the whole discrepancy into the unique
two-sided coefficient-sum seam.

This does not prove that the discrepancy vanishes.
-/

/-- Compatibility between the H1 pairing notation and the H2a pairing notation. -/
theorem codimOneRealPairing_eq_realMatrixPairing
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (u v : ι → ℝ) :
    codimOneRealPairing A u v = realMatrixPairing A u v := by
  unfold codimOneRealPairing realMatrixPairing Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Real matrix pairing is additive in the matrix argument. -/
theorem realMatrixPairing_sub
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (u v : ι → ℝ) :
    realMatrixPairing (A - B) u v =
      realMatrixPairing A u v - realMatrixPairing B u v := by
  unfold realMatrixPairing
  simp_rw [Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

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

/-- H1 instantiated on the legally constructed zero-side matrix: the actual
discrepancy pairing vanishes on the coefficient-sum-zero hyperplane. -/
theorem zeroSideDiscrepancy_pairing_eq_zero
    (hs : ZetaSeam)
    (N : ℕ)
    (u v : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L)
    (hu : coefficientSumReal N u = 0)
    (hv : coefficientSumReal N v = 0) :
    codimOneRealPairing (zeroSideDiscrepancy hs N L) u v = 0 := by
  rw [codimOneRealPairing_eq_realMatrixPairing,
    zeroSideDiscrepancy, realMatrixPairing_sub,
    realMatrixPairing_zeroSideMatrix_eq_smoothCoreZeroPolarization hs N u v hL,
    smoothCoreZeroPolarization_eq_realMatrixPairing hs N u v hL hu hv,
    sub_self]

/-- Canonical H2b seam vector.  It is explicit in the pivot column of the
actual discrepancy and is the object to be tested by H2+ parity/displacement
arguments. -/
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
    ccmCodimOneMatrixCompletion N
      (zeroSideDiscrepancy hs N L)
      (zeroSideDiscrepancy_apply_comm hs N L)
      (fun u v hu hv =>
        zeroSideDiscrepancy_pairing_eq_zero hs N u v hL hu hv)

/-- H2b rank consequence for the actual zeta-dependent discrepancy. -/
theorem rank_zeroSideDiscrepancy_le_two
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    (zeroSideDiscrepancy hs N L).rank ≤ 2 := by
  exact rank_ccmCodimOneMatrixCompletion_le_two N
    (zeroSideDiscrepancy hs N L)
    (zeroSideDiscrepancy_apply_comm hs N L)
    (fun u v hu hv =>
      zeroSideDiscrepancy_pairing_eq_zero hs N u v hL hu hv)

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
  apply sub_eq_iff_eq_add.mp at h
  simpa [add_comm, add_left_comm, add_assoc] using h

end Zeta23.CCM

#print axioms Zeta23.CCM.zeroSideDiscrepancy_pairing_eq_zero
#print axioms Zeta23.CCM.zeroSideDiscrepancy_eq_completion
#print axioms Zeta23.CCM.rank_zeroSideDiscrepancy_le_two
