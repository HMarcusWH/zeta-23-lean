import Zeta23.CCM.DictionaryAnalysis
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators

/-!
# Codimension-one matrix completion

This module is the pure finite-linear-algebra H2a step of Route R003.

If a symmetric complex matrix has zero real-coefficient bilinear pairing on the
codimension-one hyperplane of coefficient-sum-zero vectors, then the whole
matrix is forced into the two-sided coefficient-sum channel

```text
A = 1 aᵀ + a 1ᵀ.
```

The witness is canonical after choosing a pivot coordinate `p`:

```text
aᵢ = Aᵢₚ - Aₚₚ / 2.
```

Consequently the matrix has rank at most two.

This file contains no zeta zeros, no explicit-formula limit passage, no
positivity statement, and no finite-to-infinite claim.
-/

/-- Real-coefficient bilinear pairing against a complex matrix. -/
def codimOneRealPairing {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (u v : ι → ℝ) : ℂ :=
  ∑ i, ∑ j, (u i : ℂ) * A i j * (v j : ℂ)

/-- The zero-sum probe `e_i - e_p` based at a chosen pivot coordinate `p`. -/
def codimOneBasisDiff {ι : Type*} [DecidableEq ι]
    (p i : ι) : ι → ℝ :=
  fun k => (if k = i then 1 else 0) - (if k = p then 1 else 0)

/-- Every pivoted basis-difference probe has coefficient sum zero. -/
@[simp] theorem sum_codimOneBasisDiff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p i : ι) :
    (∑ k, codimOneBasisDiff p i k) = 0 := by
  simp [codimOneBasisDiff, Finset.sum_sub_distrib]

/-- Pairing two pivoted basis-difference probes extracts the corresponding
four-entry second difference of the matrix. -/
theorem codimOneRealPairing_basisDiff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (p i j : ι) :
    codimOneRealPairing A (codimOneBasisDiff p i) (codimOneBasisDiff p j) =
      A i j - A i p - A p j + A p p := by
  unfold codimOneRealPairing codimOneBasisDiff
  push_cast
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp
  ring

/-- Vanishing on the coefficient-sum-zero hyperplane forces the entry identity
`Aᵢⱼ = Aᵢₚ + Aₚⱼ - Aₚₚ`.  No symmetry is used yet. -/
theorem codimOne_entry_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (p : ι)
    (hzero :
      ∀ u v : ι → ℝ,
        (∑ k, u k) = 0 →
        (∑ k, v k) = 0 →
        codimOneRealPairing A u v = 0)
    (i j : ι) :
    A i j = A i p + A p j - A p p := by
  have h := hzero
    (codimOneBasisDiff p i) (codimOneBasisDiff p j)
    (sum_codimOneBasisDiff p i) (sum_codimOneBasisDiff p j)
  rw [codimOneRealPairing_basisDiff] at h
  linear_combination h

/-- Canonical completion vector associated with a pivot coordinate. -/
def codimOneCompletionVector
    {ι : Type*} (A : Matrix ι ι ℂ) (p : ι) : ι → ℂ :=
  fun i => A i p - A p p / 2

/-- Under symmetry, the entry identity becomes `Aᵢⱼ = aᵢ + aⱼ` for the
canonical completion vector. -/
theorem codimOne_entry_eq_completionVector_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (p : ι)
    (hA : ∀ i j, A i j = A j i)
    (hzero :
      ∀ u v : ι → ℝ,
        (∑ k, u k) = 0 →
        (∑ k, v k) = 0 →
        codimOneRealPairing A u v = 0)
    (i j : ι) :
    A i j =
      codimOneCompletionVector A p i + codimOneCompletionVector A p j := by
  rw [codimOne_entry_identity A p hzero i j, hA p j]
  unfold codimOneCompletionVector
  ring

/-- H2a representation theorem: a symmetric matrix invisible on the
coefficient-sum-zero hyperplane is exactly a two-sided coefficient-sum channel. -/
theorem codimOneMatrixCompletion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (p : ι)
    (hA : ∀ i j, A i j = A j i)
    (hzero :
      ∀ u v : ι → ℝ,
        (∑ k, u k) = 0 →
        (∑ k, v k) = 0 →
        codimOneRealPairing A u v = 0) :
    A =
      vecMulVec (fun _ => (1 : ℂ)) (codimOneCompletionVector A p) +
        vecMulVec (codimOneCompletionVector A p) (fun _ => (1 : ℂ)) := by
  ext i j
  have h := codimOne_entry_eq_completionVector_add A p hA hzero i j
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, one_mul, mul_one]
  simpa [add_comm] using h

/-- A two-column factor whose product with `codimOneRankRight` realizes
`1 aᵀ + a 1ᵀ`. -/
private def codimOneRankLeft
    {ι : Type*} (a : ι → ℂ) : Matrix ι (Fin 2) ℂ :=
  fun i k => if k = 0 then 1 else a i

/-- A two-row factor whose product with `codimOneRankLeft` realizes
`1 aᵀ + a 1ᵀ`. -/
private def codimOneRankRight
    {ι : Type*} (a : ι → ℂ) : Matrix (Fin 2) ι ℂ :=
  fun k j => if k = 0 then a j else 1

private theorem codimOneRankLeft_mul_right
    {ι : Type*} [Fintype ι]
    (a : ι → ℂ) :
    codimOneRankLeft a * codimOneRankRight a =
      vecMulVec (fun _ => (1 : ℂ)) a + vecMulVec a (fun _ => (1 : ℂ)) := by
  ext i j
  simp [Matrix.mul_apply, codimOneRankLeft, codimOneRankRight,
    Fin.sum_univ_two, Matrix.vecMulVec_apply]

/-- Rank consequence of H2a: the invisible symmetric discrepancy has rank at
most two.  The proof factors the matrix through a two-dimensional space rather
than importing the zero-side rank infrastructure. -/
theorem rank_codimOneMatrixCompletion_le_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (p : ι)
    (hA : ∀ i j, A i j = A j i)
    (hzero :
      ∀ u v : ι → ℝ,
        (∑ k, u k) = 0 →
        (∑ k, v k) = 0 →
        codimOneRealPairing A u v = 0) :
    A.rank ≤ 2 := by
  let a := codimOneCompletionVector A p
  have hrepr :
      A = vecMulVec (fun _ => (1 : ℂ)) a + vecMulVec a (fun _ => (1 : ℂ)) := by
    simpa [a] using codimOneMatrixCompletion A p hA hzero
  have hfactor :
      A = codimOneRankLeft a * codimOneRankRight a := by
    rw [hrepr, codimOneRankLeft_mul_right]
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width (codimOneRankLeft a))

/-- Production wrapper on the centered CCM coefficient type.  It accepts the
existing `coefficientSumReal` interface used by H0/H1 and fixes the canonical
pivot at coordinate zero. -/
theorem ccmCodimOneMatrixCompletion
    (N : ℕ)
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)
    (hA : ∀ i j, A i j = A j i)
    (hzero :
      ∀ u v : Fin (2 * N + 1) → ℝ,
        coefficientSumReal N u = 0 →
        coefficientSumReal N v = 0 →
        codimOneRealPairing A u v = 0) :
    A =
      vecMulVec (fun _ => (1 : ℂ))
          (codimOneCompletionVector A (0 : Fin (2 * N + 1))) +
        vecMulVec
          (codimOneCompletionVector A (0 : Fin (2 * N + 1)))
          (fun _ => (1 : ℂ)) := by
  apply codimOneMatrixCompletion A (0 : Fin (2 * N + 1)) hA
  intro u v hu hv
  exact hzero u v
    (by simpa [coefficientSumReal] using hu)
    (by simpa [coefficientSumReal] using hv)

/-- Production H2a rank endpoint on `Fin (2N+1)`. -/
theorem rank_ccmCodimOneMatrixCompletion_le_two
    (N : ℕ)
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)
    (hA : ∀ i j, A i j = A j i)
    (hzero :
      ∀ u v : Fin (2 * N + 1) → ℝ,
        coefficientSumReal N u = 0 →
        coefficientSumReal N v = 0 →
        codimOneRealPairing A u v = 0) :
    A.rank ≤ 2 := by
  apply rank_codimOneMatrixCompletion_le_two
    A (0 : Fin (2 * N + 1)) hA
  intro u v hu hv
  exact hzero u v
    (by simpa [coefficientSumReal] using hu)
    (by simpa [coefficientSumReal] using hv)

end Zeta23.CCM

#print axioms Zeta23.CCM.codimOneMatrixCompletion
#print axioms Zeta23.CCM.rank_ccmCodimOneMatrixCompletion_le_two
