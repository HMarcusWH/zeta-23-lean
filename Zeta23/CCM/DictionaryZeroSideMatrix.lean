import Zeta23.CCM.DictionaryZeroSideSummability
import Zeta23.CCM.DictionaryFiniteExpansion
import Zeta23.CCM.DictionarySmoothCorePolarization
import Zeta23.CCM.CodimOneMatrixCompletion

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators

/-!
# The actual finite zeta zero-side matrix

The matrix is defined entrywise from absolutely convergent zero sums of the
finite dictionary basis transforms. Entrywise summability is proved before the
matrix is used.

H2b deliberately needs only pivoted basis-difference pairings. This avoids an
unnecessary general finite-sum/tsum interchange theorem while still supplying
the exact minimum input consumed by the strengthened H2a interface.

No positivity statement is made. The name is deliberately
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
matrix. This is finite algebra; it is not linearity in the coefficient vector. -/
theorem dictionaryTransform_eq_quadraticForm_spectralMatrix
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    dictionaryTransform N u L z =
      quadraticForm (dictionarySpectralMatrix N L z) u := by
  rw [dictionaryTransform, paperFT_dictionaryTest_eq_basis_sum N u hL z]
  rfl

/-- Compatibility of the two real matrix-pairing notations used by H1 and H2a. -/
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
summable. The proof uses polarization of already-summable full dictionaries;
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

/-- Minimum H2b realization theorem. For pivoted basis-difference probes, the
pairing of the legally constructed zero-side matrix is exactly the H1 zero-side
polarization.

This uses only four entrywise absolutely convergent series and the two full
dictionary series appearing in the polarization. No unrestricted
finite-sum/tsum interchange is required. -/
theorem zeroSideMatrix_basisDiff_pairing_eq_smoothCoreZeroPolarization
    (hs : ZetaSeam)
    (N : ℕ)
    (p i j : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    codimOneRealPairing (zeroSideMatrix hs N L)
        (codimOneBasisDiff p i) (codimOneBasisDiff p j) =
      smoothCoreZeroPolarization hs N L
        (codimOneBasisDiff p i) (codimOneBasisDiff p j) := by
  let u : Fin (2 * N + 1) → ℝ := codimOneBasisDiff p i
  let v : Fin (2 * N + 1) → ℝ := codimOneBasisDiff p j
  let up : Fin (2 * N + 1) → ℝ := fun k => u k + v k
  let um : Fin (2 * N + 1) → ℝ := fun k => u k - v k
  let F := fun (a b : Fin (2 * N + 1)) (ρ : (zetaZeros hs).carrier) =>
    ((zetaZeros hs).mult ρ : ℂ) *
      dictionarySpectralMatrix N L (gammaOf ρ) a b

  have hij := dictionarySpectralMatrix_zero_entry_summable hs N i j hL
  have hip := dictionarySpectralMatrix_zero_entry_summable hs N i p hL
  have hpj := dictionarySpectralMatrix_zero_entry_summable hs N p j hL
  have hpp := dictionarySpectralMatrix_zero_entry_summable hs N p p hL

  have hentries :
      HasSum (fun ρ => F i j ρ - F i p ρ - F p j ρ + F p p ρ)
        (zeroSideMatrix hs N L i j -
          zeroSideMatrix hs N L i p -
          zeroSideMatrix hs N L p j +
          zeroSideMatrix hs N L p p) := by
    simpa [F, zeroSideMatrix] using
      (((hij.hasSum.sub hip.hasSum).sub hpj.hasSum).add hpp.hasSum)

  have hplus := dictionaryTransform_zero_sum_summable hs N up hL
  have hminus := dictionaryTransform_zero_sum_summable hs N um hL
  have hpolar :
      HasSum
        (fun ρ : (zetaZeros hs).carrier =>
          (1 / 4 : ℂ) *
            ((((zetaZeros hs).mult ρ : ℂ) *
                dictionaryTransform N (fun k => (up k : ℂ)) L (gammaOf ρ)) -
              (((zetaZeros hs).mult ρ : ℂ) *
                dictionaryTransform N (fun k => (um k : ℂ)) L (gammaOf ρ))))
        (smoothCoreZeroPolarization hs N L u v) := by
    unfold smoothCoreZeroPolarization
    simpa [up, um, u, v] using
      (hplus.hasSum.sub hminus.hasSum).mul_left (1 / 4 : ℂ)

  have hpoint :
      ∀ ρ : (zetaZeros hs).carrier,
        F i j ρ - F i p ρ - F p j ρ + F p p ρ =
          (1 / 4 : ℂ) *
            ((((zetaZeros hs).mult ρ : ℂ) *
                dictionaryTransform N (fun k => (up k : ℂ)) L (gammaOf ρ)) -
              (((zetaZeros hs).mult ρ : ℂ) *
                dictionaryTransform N (fun k => (um k : ℂ)) L (gammaOf ρ))) := by
    intro ρ
    have hpol :=
      dictionarySpectralMatrix_real_polarization N u v hL (gammaOf ρ)
    have hentry :
        dictionarySpectralMatrix N L (gammaOf ρ) i j -
          dictionarySpectralMatrix N L (gammaOf ρ) i p -
          dictionarySpectralMatrix N L (gammaOf ρ) p j +
          dictionarySpectralMatrix N L (gammaOf ρ) p p =
        (1 / 4 : ℂ) *
          (dictionaryTransform N (fun k => (up k : ℂ)) L (gammaOf ρ) -
            dictionaryTransform N (fun k => (um k : ℂ)) L (gammaOf ρ)) := by
      rw [← codimOneRealPairing_basisDiff
        (dictionarySpectralMatrix N L (gammaOf ρ)) p i j,
        codimOneRealPairing_eq_realMatrixPairing]
      simpa [u, v, up, um] using hpol.symm
    unfold F
    rw [hentry]
    ring

  have hentries' :
      HasSum
        (fun ρ : (zetaZeros hs).carrier =>
          (1 / 4 : ℂ) *
            ((((zetaZeros hs).mult ρ : ℂ) *
                dictionaryTransform N (fun k => (up k : ℂ)) L (gammaOf ρ)) -
              (((zetaZeros hs).mult ρ : ℂ) *
                dictionaryTransform N (fun k => (um k : ℂ)) L (gammaOf ρ))))
        (zeroSideMatrix hs N L i j -
          zeroSideMatrix hs N L i p -
          zeroSideMatrix hs N L p j +
          zeroSideMatrix hs N L p p) := by
    convert hentries using 1
    funext ρ
    exact hpoint ρ

  rw [codimOneRealPairing_basisDiff]
  exact hentries'.unique hpolar

end Zeta23.CCM

#print axioms Zeta23.CCM.dictionarySpectralMatrix_zero_entry_summable
#print axioms Zeta23.CCM.zeroSideMatrix_basisDiff_pairing_eq_smoothCoreZeroPolarization
