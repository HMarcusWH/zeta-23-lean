import Zeta23.CCM.DictionaryZeroSideSummability
import Zeta23.CCM.DictionaryFiniteExpansion
import Zeta23.CCM.DictionarySmoothCorePolarization

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators

/-!
# The actual finite zeta zero-side matrix

The matrix is defined entrywise from absolutely convergent zero sums of the
finite dictionary basis transforms.  Entrywise summability is proved before the
matrix is used.

No positivity statement is made.  The name is deliberately
`zeroSideMatrix`, not `Gram`.
-/

/-- Spectral matrix of one finite dictionary evaluation. -/
def dictionarySpectralMatrix
    (N : ℕ) (L : ℝ) (z : ℂ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  fun i j =>
    Zeta23.paperFT
      (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L) z

/-- Production basis tests are symmetric in their two centered indices. -/
theorem dictionaryBasisTest_comm
    (n m : ℤ) (L : ℝ) :
    dictionaryBasisTest n m L = dictionaryBasisTest m n L := by
  funext y
  unfold dictionaryBasisTest kernel
  by_cases hy : |y| ≤ L
  · simp [hy, qBasis_comm]
  · simp [hy]

/-- The spectral matrix is symmetric entrywise. -/
theorem dictionarySpectralMatrix_apply_comm
    (N : ℕ) (L : ℝ) (z : ℂ)
    (i j : Fin (2 * N + 1)) :
    dictionarySpectralMatrix N L z i j =
      dictionarySpectralMatrix N L z j i := by
  unfold dictionarySpectralMatrix
  rw [dictionaryBasisTest_comm]

/-- The full dictionary transform is exactly the quadratic form of its spectral
matrix.  This is finite algebra; it is not linearity in the coefficient vector. -/
theorem dictionaryTransform_eq_quadraticForm_spectralMatrix
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    dictionaryTransform N u L z =
      quadraticForm (dictionarySpectralMatrix N L z) u := by
  rw [dictionaryTransform, paperFT_dictionaryTest_eq_basis_sum N u hL z]
  rfl

/-- Real coordinate basis vector used only for finite polarization. -/
def dictionaryRealUnit
    {ι : Type*} [DecidableEq ι] (i : ι) : ι → ℝ :=
  fun k => if k = i then 1 else 0

/-- A real matrix pairing on coordinate vectors reads off one entry. -/
@[simp] theorem realMatrixPairing_dictionaryRealUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) :
    realMatrixPairing A (dictionaryRealUnit i) (dictionaryRealUnit j) =
      A i j := by
  unfold realMatrixPairing dictionaryRealUnit
  simp

/-- Pointwise real polarization of the finite spectral quadratic form. -/
theorem dictionarySpectralMatrix_real_polarization
    (N : ℕ)
    (u v : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    (1 / 4 : ℂ) *
        (dictionaryTransform N (fun i => ((u i + v i : ℝ) : ℂ)) L z -
          dictionaryTransform N (fun i => ((u i - v i : ℝ) : ℂ)) L z) =
      realMatrixPairing (dictionarySpectralMatrix N L z) u v := by
  rw [dictionaryTransform_eq_quadraticForm_spectralMatrix N
        (fun i => ((u i + v i : ℝ) : ℂ)) hL z,
      dictionaryTransform_eq_quadraticForm_spectralMatrix N
        (fun i => ((u i - v i : ℝ) : ℂ)) hL z]
  calc
    (1 / 4 : ℂ) *
        (quadraticForm (dictionarySpectralMatrix N L z)
            (fun i => ((u i + v i : ℝ) : ℂ)) -
          quadraticForm (dictionarySpectralMatrix N L z)
            (fun i => ((u i - v i : ℝ) : ℂ))) =
        (1 / 2 : ℂ) *
          (realMatrixPairing (dictionarySpectralMatrix N L z) u v +
            realMatrixPairing (dictionarySpectralMatrix N L z) v u) :=
      quadraticForm_real_polarization (dictionarySpectralMatrix N L z) u v
    _ = realMatrixPairing (dictionarySpectralMatrix N L z) u v := by
      rw [realMatrixPairing_comm_of_symmetric
        (dictionarySpectralMatrix N L z)
        (dictionarySpectralMatrix_apply_comm N L z) v u]
      ring

/-- Each spectral matrix entry is a real polarization of two full dictionary
transforms. -/
theorem dictionarySpectralMatrix_apply_eq_realPolarization
    (N : ℕ) (i j : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    dictionarySpectralMatrix N L z i j =
      (1 / 4 : ℂ) *
        (dictionaryTransform N
            (fun k =>
              ((dictionaryRealUnit i k + dictionaryRealUnit j k : ℝ) : ℂ))
            L z -
          dictionaryTransform N
            (fun k =>
              ((dictionaryRealUnit i k - dictionaryRealUnit j k : ℝ) : ℂ))
            L z) := by
  symm
  simpa using
    dictionarySpectralMatrix_real_polarization N
      (dictionaryRealUnit i) (dictionaryRealUnit j) hL z

/-- Entrywise legality theorem: every matrix-entry zero series is absolutely
summable.  The proof uses polarization of already-summable full dictionaries;
it never applies the C² explicit-formula theorem directly to a nonsmooth basis
test. -/
theorem dictionarySpectralMatrix_zero_entry_summable
    (hs : ZetaSeam)
    (N : ℕ) (i j : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    Summable (fun ρ : (zetaZeros hs).carrier =>
      ((zetaZeros hs).mult ρ : ℂ) *
        dictionarySpectralMatrix N L (gammaOf ρ) i j) := by
  let up : Fin (2 * N + 1) → ℝ :=
    fun k => dictionaryRealUnit i k + dictionaryRealUnit j k
  let um : Fin (2 * N + 1) → ℝ :=
    fun k => dictionaryRealUnit i k - dictionaryRealUnit j k
  have hp := dictionaryTransform_zero_sum_summable hs N up hL
  have hm := dictionaryTransform_zero_sum_summable hs N um hL
  have h := (hp.sub hm).mul_left (1 / 4 : ℂ)
  convert h using 1
  funext ρ
  rw [dictionarySpectralMatrix_apply_eq_realPolarization N i j hL]
  simp only [up, um]
  ring

/-- The actual finite zeta zero-side dictionary matrix, defined only after
entrywise absolute summability has been established above. -/
def zeroSideMatrix
    (hs : ZetaSeam) (N : ℕ) (L : ℝ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  fun i j =>
    ∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        dictionarySpectralMatrix N L (gammaOf ρ) i j

/-- The actual zero-side matrix is symmetric entrywise. -/
theorem zeroSideMatrix_apply_comm
    (hs : ZetaSeam) (N : ℕ) (L : ℝ)
    (i j : Fin (2 * N + 1)) :
    zeroSideMatrix hs N L i j = zeroSideMatrix hs N L j i := by
  unfold zeroSideMatrix
  apply tsum_congr
  intro ρ
  rw [dictionarySpectralMatrix_apply_comm]

/-- The quadratic form of the zero-side matrix on a real coefficient vector is
the absolutely convergent full-dictionary zero sum. -/
theorem quadraticForm_zeroSideMatrix_eq_zeroSum
    (hs : ZetaSeam)
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) :
    quadraticForm (zeroSideMatrix hs N L) (fun i => (u i : ℂ)) =
      ∑' ρ : (zetaZeros hs).carrier,
        ((zetaZeros hs).mult ρ : ℂ) *
          dictionaryTransform N (fun i => (u i : ℂ)) L (gammaOf ρ) := by
  have hentry :
      ∀ i j : Fin (2 * N + 1),
        Summable (fun ρ : (zetaZeros hs).carrier =>
          ((u i : ℂ) *
            (((zetaZeros hs).mult ρ : ℂ) *
              dictionarySpectralMatrix N L (gammaOf ρ) i j)) *
            (u j : ℂ)) := by
    intro i j
    exact ((dictionarySpectralMatrix_zero_entry_summable hs N i j hL).mul_left
      (u i : ℂ)).mul_right (u j : ℂ)
  unfold quadraticForm zeroSideMatrix
  simp only [Complex.conj_ofReal]
  rw [show
      (∑ i, ∑ j,
        (u i : ℂ) *
          (∑' ρ : (zetaZeros hs).carrier,
            ((zetaZeros hs).mult ρ : ℂ) *
              dictionarySpectralMatrix N L (gammaOf ρ) i j) *
          (u j : ℂ)) =
      ∑ i, ∑ j,
        ∑' ρ : (zetaZeros hs).carrier,
          (u i : ℂ) *
            (((zetaZeros hs).mult ρ : ℂ) *
              dictionarySpectralMatrix N L (gammaOf ρ) i j) *
            (u j : ℂ) by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [tsum_mul_left, tsum_mul_right]
        rfl]
  have hswap1 :
      (∑ i, ∑ j,
        ∑' ρ : (zetaZeros hs).carrier,
          (u i : ℂ) *
            (((zetaZeros hs).mult ρ : ℂ) *
              dictionarySpectralMatrix N L (gammaOf ρ) i j) *
            (u j : ℂ)) =
      ∑' ρ : (zetaZeros hs).carrier,
        ∑ i, ∑ j,
          (u i : ℂ) *
            (((zetaZeros hs).mult ρ : ℂ) *
              dictionarySpectralMatrix N L (gammaOf ρ) i j) *
            (u j : ℂ)) := by
    rw [← (Summable.tsum_finsetSum
      (s := Finset.univ)
      (fun i _ =>
        Summable.tsum_finsetSum
          (s := Finset.univ)
          (fun j _ => hentry i j)))]
    simp
  rw [hswap1]
  apply tsum_congr
  intro ρ
  rw [dictionaryTransform_eq_quadraticForm_spectralMatrix N
      (fun i => (u i : ℂ)) hL (gammaOf ρ)]
  unfold quadraticForm realMatrixPairing
  simp only [Complex.conj_ofReal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact unrestricted real-pairing realization of the zero-side polarization.
This is a finite-dimensional consequence of the entrywise construction, not an
extra explicit-formula assertion. -/
theorem realMatrixPairing_zeroSideMatrix_eq_smoothCoreZeroPolarization
    (hs : ZetaSeam)
    (N : ℕ)
    (u v : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) :
    realMatrixPairing (zeroSideMatrix hs N L) u v =
      smoothCoreZeroPolarization hs N L u v := by
  have hpol :=
    quadraticForm_real_polarization (zeroSideMatrix hs N L) u v
  have hsym :=
    realMatrixPairing_comm_of_symmetric
      (zeroSideMatrix hs N L)
      (zeroSideMatrix_apply_comm hs N L) v u
  have hpol' :
      realMatrixPairing (zeroSideMatrix hs N L) u v =
        (1 / 4 : ℂ) *
          (quadraticForm (zeroSideMatrix hs N L)
              (fun i => ((u i + v i : ℝ) : ℂ)) -
            quadraticForm (zeroSideMatrix hs N L)
              (fun i => ((u i - v i : ℝ) : ℂ))) := by
    rw [hsym] at hpol
    linear_combination hpol
  rw [hpol',
    quadraticForm_zeroSideMatrix_eq_zeroSum hs N (fun i => u i + v i) hL,
    quadraticForm_zeroSideMatrix_eq_zeroSum hs N (fun i => u i - v i) hL]
  rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.dictionarySpectralMatrix_zero_entry_summable
#print axioms Zeta23.CCM.quadraticForm_zeroSideMatrix_eq_zeroSum
#print axioms Zeta23.CCM.realMatrixPairing_zeroSideMatrix_eq_smoothCoreZeroPolarization
