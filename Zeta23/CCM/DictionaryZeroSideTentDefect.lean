import Zeta23.CCM.DictionaryZeroSideCompletion

noncomputable section

namespace Zeta23.CCM

open Matrix Set MeasureTheory
open scoped BigOperators ArithmeticFunction

/-!
# H2+ collapse to the universal tent defect

H2b localizes the actual finite zero-side discrepancy to the symmetric
coefficient-sum seam
`1 aᵀ + a 1ᵀ`.  This file tests the strongest cheap consequence available
without assuming any zero-side displacement law.

The key observation is that diagonal dictionary basis tests all have the same
universal tent seam.  Their difference from the centered zero-frequency
diagonal basis test is exactly a globally `C_c^2` residual, so the inherited
explicit formula applies to that difference.  This forces all diagonal entries
of the H2b discrepancy to agree.  Combined with the H2b seam representation,
the whole discrepancy therefore collapses to one scalar multiple of
`J = 1 1ᵀ`.

The scalar is then identified with the literal tent explicit-formula defect.
No claim that this scalar vanishes is made here.
-/

/-- The coordinate representing Fourier index zero on the centered
`-N,...,N` grid. -/
def dictionaryCenterIndex (N : ℕ) : Fin (2 * N + 1) :=
  ⟨N, by omega⟩

@[simp] theorem centeredIndex_dictionaryCenterIndex (N : ℕ) :
    centeredIndex N (dictionaryCenterIndex N) = 0 := by
  simp [centeredIndex, dictionaryCenterIndex]

/-- The zero-frequency diagonal production basis test is exactly the canonical
literal tent.  This is the normalization smoke test for H2+. -/
theorem dictionaryBasisTest_zero_zero_eq_tent
    {L : ℝ} (hL : 0 < L) :
    dictionaryBasisTest 0 0 L = dictionaryTent L := by
  funext y
  by_cases hy : |y| ≤ L
  · have hnonneg : 0 ≤ 1 - |y| / L :=
      sub_nonneg.mpr ((div_le_one hL).2 hy)
    simp [dictionaryBasisTest, kernel, qBasis, dictionaryTent,
      dictionaryApertureCoord, hy, max_eq_right hnonneg]
  · have hlt : L < |y| := lt_of_not_ge hy
    have hnonpos : 1 - |y| / L ≤ 0 :=
      le_of_lt (sub_neg.mpr ((one_lt_div hL).2 hlt))
    simp [dictionaryBasisTest, kernel, qBasis, dictionaryTent,
      dictionaryApertureCoord, hy, max_eq_left hnonpos]

/-- A real coordinate unit has coefficient sum one. -/
@[simp] theorem coefficientSumReal_dictionaryRealUnit
    (N : ℕ) (i : Fin (2 * N + 1)) :
    coefficientSumReal N (dictionaryRealUnit i) = 1 := by
  simp [coefficientSumReal, dictionaryRealUnit]

/-- A coordinate unit selects the corresponding diagonal dictionary basis
test. -/
theorem dictionaryTest_dictionaryRealUnit_eq_basisTest
    (N : ℕ) (i : Fin (2 * N + 1)) (L : ℝ) :
    dictionaryTest N (fun k => (dictionaryRealUnit i k : ℂ)) L =
      dictionaryBasisTest (centeredIndex N i) (centeredIndex N i) L := by
  funext y
  rw [dictionaryTest_eq_basis_sum]
  push_cast
  simp [dictionaryRealUnit]

/-- Physical test obtained by subtracting the common zero-frequency diagonal
basis test from one diagonal basis test. -/
def dictionaryDiagonalDifferenceTest
    (N : ℕ) (i : Fin (2 * N + 1)) (L : ℝ) : ℝ → ℂ :=
  fun y =>
    dictionaryBasisTest (centeredIndex N i) (centeredIndex N i) L y -
      dictionaryBasisTest 0 0 L y

/-- The diagonal difference is exactly the already-proved smooth residual of a
coordinate unit.  Hence no new regularity argument is needed. -/
theorem dictionaryDiagonalDifferenceTest_eq_residual
    (N : ℕ) (i : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    dictionaryDiagonalDifferenceTest N i L =
      dictionaryResidualTest N (dictionaryRealUnit i) L := by
  have hdec :=
    dictionaryTest_ofReal_eq_tent_smul_add_residual
      N (dictionaryRealUnit i) hL
  funext y
  have h := congrFun hdec y
  rw [dictionaryTest_dictionaryRealUnit_eq_basisTest] at h
  simp at h
  unfold dictionaryDiagonalDifferenceTest
  rw [dictionaryBasisTest_zero_zero_eq_tent hL]
  rw [h, dictionaryTent_apply]
  ring

/-- Fourier transform is linear on the subtraction of two continuous compactly
supported tests.  Kept local to H2+ rather than widening the central EF API. -/
private theorem paperFT_sub_of_continuous_compactSupport
    (k l : ℝ → ℂ)
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hl : Continuous l) (hlc : HasCompactSupport l)
    (z : ℂ) :
    Zeta23.paperFT (fun y => k y - l y) z =
      Zeta23.paperFT k z - Zeta23.paperFT l z := by
  rw [Zeta23.paperFT_def, Zeta23.paperFT_def, Zeta23.paperFT_def]
  have hik : Integrable
      (fun y : ℝ => k y * Complex.exp (Complex.I * z * y)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hil : Integrable
      (fun y : ℝ => l y * Complex.exp (Complex.I * z * y)) :=
    (hl.mul (by fun_prop)).integrable_of_hasCompactSupport hlc.mul_right
  have hpoint :
      (fun y : ℝ =>
        (k y - l y) * Complex.exp (Complex.I * z * y)) =
      fun y =>
        k y * Complex.exp (Complex.I * z * y) -
          l y * Complex.exp (Complex.I * z * y) := by
    funext y
    ring
  rw [hpoint, integral_sub hik hil]

/-- The von-Mangoldt series appearing in the literature RHS is summable for any
compactly supported physical test.  Compact support makes the sequence finitely
supported. -/
private theorem summable_dictionaryPrimeSeries_of_hasCompactSupport
    (k : ℝ → ℂ) (hkc : HasCompactSupport k) :
    Summable (fun n : ℕ =>
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) := by
  obtain ⟨B, hB⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  have hsummable_gen :
      ∀ (g : ℝ → ℂ),
        (∀ u, g u ≠ 0 → |u| ≤ max B 0) →
        Summable (fun n : ℕ =>
          ((Λ n / Real.sqrt n : ℝ) : ℂ) * g (Real.log n)) := by
    intro g hg
    refine summable_of_hasFiniteSupport ?_
    have hsub :
        Function.support
            (fun n : ℕ =>
              ((Λ n / Real.sqrt n : ℝ) : ℂ) * g (Real.log n))
          ⊆ Set.Iic ⌈Real.exp (max B 0)⌉₊ := by
      intro n hn
      rw [Function.mem_support] at hn
      have hgne : g (Real.log n) ≠ 0 := by
        intro hzero
        rw [hzero, mul_zero] at hn
        exact hn rfl
      have hlog := hg _ hgne
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hnexp : (n : ℝ) ≤ Real.exp (max B 0) := by
        have hlog' : Real.log n ≤ max B 0 :=
          (le_abs_self _).trans hlog
        calc
          (n : ℝ) = Real.exp (Real.log n) :=
            (Real.exp_log (by linarith)).symm
          _ ≤ Real.exp (max B 0) := Real.exp_le_exp.mpr hlog'
      rw [Set.mem_Iic]
      exact_mod_cast hnexp.trans (Nat.le_ceil _)
    exact (Set.finite_Iic _).subset hsub
  have hp :
      Summable (fun n : ℕ =>
        ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n)) :=
    hsummable_gen k (fun u hu => (hB u hu).trans (le_max_left _ _))
  have hm :
      Summable (fun n : ℕ =>
        ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n)) := by
    have hneg :
        Summable (fun n : ℕ =>
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            (fun u => k (-u)) (Real.log n)) :=
      hsummable_gen (fun u => k (-u)) (by
        intro u hu
        have h : |u| ≤ B := by
          simpa [abs_neg] using hB (-u) hu
        exact h.trans (le_max_left _ _))
    simpa using hneg
  simpa [mul_add] using hp.add hm

/-- Prime-channel subtraction for two compactly supported tests. -/
private theorem dictionaryPrimeRHS_sub_of_compactSupport
    (k l : ℝ → ℂ)
    (hkc : HasCompactSupport k) (hlc : HasCompactSupport l) :
    dictionaryPrimeRHS (fun y => k y - l y) =
      dictionaryPrimeRHS k - dictionaryPrimeRHS l := by
  have hk := summable_dictionaryPrimeSeries_of_hasCompactSupport k hkc
  have hl := summable_dictionaryPrimeSeries_of_hasCompactSupport l hlc
  unfold dictionaryPrimeRHS
  have hpoint :
      (fun n : ℕ =>
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
          ((k (Real.log n) - l (Real.log n)) +
            (k (-Real.log n) - l (-Real.log n)))) =
      fun n =>
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            (k (Real.log n) + k (-Real.log n)) -
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            (l (Real.log n) + l (-Real.log n)) := by
    funext n
    ring
  rw [hpoint, hk.tsum_sub hl]
  ring

/-- Pole-channel subtraction for two dictionary basis tests. -/
private theorem dictionaryPoleRHS_dictionaryBasisTest_sub
    {L : ℝ} (hL : 0 < L)
    (n m p q : ℤ) :
    dictionaryPoleRHS
        (fun y =>
          dictionaryBasisTest n m L y -
            dictionaryBasisTest p q L y) =
      dictionaryPoleRHS (dictionaryBasisTest n m L) -
        dictionaryPoleRHS (dictionaryBasisTest p q L) := by
  unfold dictionaryPoleRHS
  rw [
    paperFT_sub_of_continuous_compactSupport
      (dictionaryBasisTest n m L) (dictionaryBasisTest p q L)
      (continuous_dictionaryBasisTest hL n m)
      (dictionaryBasisTest_hasCompactSupport n m)
      (continuous_dictionaryBasisTest hL p q)
      (dictionaryBasisTest_hasCompactSupport p q)
      (Complex.I / 2),
    paperFT_sub_of_continuous_compactSupport
      (dictionaryBasisTest n m L) (dictionaryBasisTest p q L)
      (continuous_dictionaryBasisTest hL n m)
      (dictionaryBasisTest_hasCompactSupport n m)
      (continuous_dictionaryBasisTest hL p q)
      (dictionaryBasisTest_hasCompactSupport p q)
      (-Complex.I / 2)]
  ring

/-- Archimedean-channel subtraction for two dictionary basis tests. -/
private theorem dictionaryArchRHS_dictionaryBasisTest_sub
    {L : ℝ} (hL : 0 < L)
    (n m p q : ℤ) :
    dictionaryArchRHS
        (fun y =>
          dictionaryBasisTest n m L y -
            dictionaryBasisTest p q L y) =
      dictionaryArchRHS (dictionaryBasisTest n m L) -
        dictionaryArchRHS (dictionaryBasisTest p q L) := by
  rw [dictionaryArchRHS_eq_integral_mu,
    dictionaryArchRHS_eq_integral_mu,
    dictionaryArchRHS_eq_integral_mu]
  have hnm := integrable_paperFT_dictionaryBasisTest_mul_mu hL n m
  have hpq := integrable_paperFT_dictionaryBasisTest_mul_mu hL p q
  have hpoint :
      (fun τ : ℝ =>
        Zeta23.paperFT
            (fun y =>
              dictionaryBasisTest n m L y -
                dictionaryBasisTest p q L y) (τ : ℂ) *
          (Zeta23.mu τ : ℂ)) =
      fun τ : ℝ =>
        Zeta23.paperFT (dictionaryBasisTest n m L) (τ : ℂ) *
            (Zeta23.mu τ : ℂ) -
          Zeta23.paperFT (dictionaryBasisTest p q L) (τ : ℂ) *
            (Zeta23.mu τ : ℂ) := by
    funext τ
    rw [paperFT_sub_of_continuous_compactSupport
      (dictionaryBasisTest n m L) (dictionaryBasisTest p q L)
      (continuous_dictionaryBasisTest hL n m)
      (dictionaryBasisTest_hasCompactSupport n m)
      (continuous_dictionaryBasisTest hL p q)
      (dictionaryBasisTest_hasCompactSupport p q)
      (τ : ℂ)]
    ring
  rw [hpoint, integral_sub hnm hpq]

/-- The full literature RHS is linear on the one subtraction used by H2+.
This is intentionally local: no unrestricted linearity API is introduced. -/
theorem literatureRHS_dictionaryBasisTest_sub
    {L : ℝ} (hL : 0 < L)
    (n m p q : ℤ) :
    Zeta23.EF.literatureRHS
        (fun y =>
          dictionaryBasisTest n m L y -
            dictionaryBasisTest p q L y) =
      Zeta23.EF.literatureRHS (dictionaryBasisTest n m L) -
        Zeta23.EF.literatureRHS (dictionaryBasisTest p q L) := by
  rw [literatureRHS_eq_dictionaryChannels,
    literatureRHS_eq_dictionaryChannels,
    literatureRHS_eq_dictionaryChannels,
    dictionaryPoleRHS_dictionaryBasisTest_sub hL n m p q,
    dictionaryPrimeRHS_sub_of_compactSupport
      (dictionaryBasisTest n m L) (dictionaryBasisTest p q L)
      (dictionaryBasisTest_hasCompactSupport n m)
      (dictionaryBasisTest_hasCompactSupport p q),
    dictionaryArchRHS_dictionaryBasisTest_sub hL n m p q]
  ring

/-- Entrywise deterministic RHS theorem for one production basis test. -/
theorem literatureRHS_dictionaryBasisTest_eq_dictionaryMatrix_apply
    (N : ℕ) (i j : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    Zeta23.EF.literatureRHS
        (dictionaryBasisTest
          (centeredIndex N i) (centeredIndex N j) L) =
      dictionaryMatrix L N i j := by
  rw [literatureRHS_eq_dictionaryChannels,
    dictionaryPoleRHS_basis hL,
    dictionaryPrimeRHS_basis hL,
    dictionaryArchRHS_basis hL,
    dictionaryMatrix_apply,
    finiteMatrix_apply]
  unfold entry
  by_cases hij : i = j
  · subst j
    simp
    ring
  · have hidx : centeredIndex N i ≠ centeredIndex N j :=
      fun h => hij ((centeredIndex_injective N) h)
    simp [hij, hidx]
    ring

/-- The smooth diagonal difference satisfies the inherited explicit formula. -/
theorem dictionaryDiagonalDifferenceTest_zero_sum_eq_literatureRHS
    (hs : ZetaSeam)
    (N : ℕ) (i : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    (∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        Zeta23.paperFT (dictionaryDiagonalDifferenceTest N i L) (gammaOf ρ)) =
      Zeta23.EF.literatureRHS
        (dictionaryDiagonalDifferenceTest N i L) := by
  rw [dictionaryDiagonalDifferenceTest_eq_residual N i hL]
  have hEF := Zeta23.WeilEF.EF_lit_zeta hs
  exact
    (hEF
      (dictionaryResidualTest N (dictionaryRealUnit i) L)
      (contDiff_two_dictionaryResidualTest N (dictionaryRealUnit i) hL)
      (dictionaryResidualTest_hasCompactSupport N (dictionaryRealUnit i) hL)).2

/-- Fourier transform of a diagonal difference is the corresponding spectral
matrix-entry difference. -/
theorem paperFT_dictionaryDiagonalDifferenceTest
    (N : ℕ) (i : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    Zeta23.paperFT (dictionaryDiagonalDifferenceTest N i L) z =
      dictionarySpectralMatrix N L z i i -
        dictionarySpectralMatrix N L z
          (dictionaryCenterIndex N) (dictionaryCenterIndex N) := by
  unfold dictionaryDiagonalDifferenceTest dictionarySpectralMatrix
  rw [paperFT_sub_of_continuous_compactSupport
    (dictionaryBasisTest (centeredIndex N i) (centeredIndex N i) L)
    (dictionaryBasisTest 0 0 L)
    (continuous_dictionaryBasisTest hL _ _)
    (dictionaryBasisTest_hasCompactSupport _ _)
    (continuous_dictionaryBasisTest hL 0 0)
    (dictionaryBasisTest_hasCompactSupport 0 0)
    z]
  simp

/-- Zero-side diagonal difference equals the literature RHS of the smooth
physical diagonal difference. -/
theorem zeroSideMatrix_diagonal_sub_center_eq_literatureRHS
    (hs : ZetaSeam)
    (N : ℕ) (i : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    zeroSideMatrix hs N L i i -
        zeroSideMatrix hs N L
          (dictionaryCenterIndex N) (dictionaryCenterIndex N) =
      Zeta23.EF.literatureRHS
        (dictionaryDiagonalDifferenceTest N i L) := by
  let c := dictionaryCenterIndex N
  have hi :=
    dictionarySpectralMatrix_zero_entry_summable hs N i i hL
  have hc :=
    dictionarySpectralMatrix_zero_entry_summable hs N c c hL
  unfold zeroSideMatrix
  rw [← hi.tsum_sub hc]
  calc
    (∑' ρ : (zetaZeros hs).carrier,
      (((zetaZeros hs).mult ρ : ℂ) *
          dictionarySpectralMatrix N L (gammaOf ρ) i i -
        ((zetaZeros hs).mult ρ : ℂ) *
          dictionarySpectralMatrix N L (gammaOf ρ) c c)) =
      ∑' ρ : (zetaZeros hs).carrier,
        ((zetaZeros hs).mult ρ : ℂ) *
          Zeta23.paperFT
            (dictionaryDiagonalDifferenceTest N i L) (gammaOf ρ) := by
          apply tsum_congr
          intro ρ
          rw [paperFT_dictionaryDiagonalDifferenceTest N i hL]
          simp only [c]
          ring
    _ = Zeta23.EF.literatureRHS
          (dictionaryDiagonalDifferenceTest N i L) :=
      dictionaryDiagonalDifferenceTest_zero_sum_eq_literatureRHS
        hs N i hL

/-- Deterministic side of the same diagonal difference. -/
theorem literatureRHS_dictionaryDiagonalDifferenceTest_eq_dictionaryMatrix_sub
    (N : ℕ) (i : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    Zeta23.EF.literatureRHS
        (dictionaryDiagonalDifferenceTest N i L) =
      dictionaryMatrix L N i i -
        dictionaryMatrix L N
          (dictionaryCenterIndex N) (dictionaryCenterIndex N) := by
  unfold dictionaryDiagonalDifferenceTest
  rw [literatureRHS_dictionaryBasisTest_sub hL]
  rw [literatureRHS_dictionaryBasisTest_eq_dictionaryMatrix_apply N i i hL]
  have hc :=
    literatureRHS_dictionaryBasisTest_eq_dictionaryMatrix_apply
      N (dictionaryCenterIndex N) (dictionaryCenterIndex N) hL
  simp only [centeredIndex_dictionaryCenterIndex] at hc
  rw [hc]

/-- H2+ diagonal rigidity: the actual zero-side discrepancy has one common
value on the entire diagonal. -/
theorem zeroSideDiscrepancy_diagonal_eq_center
    (hs : ZetaSeam)
    (N : ℕ) (i : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    zeroSideDiscrepancy hs N L i i =
      zeroSideDiscrepancy hs N L
        (dictionaryCenterIndex N) (dictionaryCenterIndex N) := by
  have hz :=
    zeroSideMatrix_diagonal_sub_center_eq_literatureRHS
      hs N i hL
  have hM :=
    literatureRHS_dictionaryDiagonalDifferenceTest_eq_dictionaryMatrix_sub
      N i hL
  have hdiff :
      zeroSideMatrix hs N L i i -
          zeroSideMatrix hs N L
            (dictionaryCenterIndex N) (dictionaryCenterIndex N) =
        dictionaryMatrix L N i i -
          dictionaryMatrix L N
            (dictionaryCenterIndex N) (dictionaryCenterIndex N) :=
    hz.trans hM
  unfold zeroSideDiscrepancy
  simp only [Matrix.sub_apply]
  linear_combination hdiff

/-- The H2b completion vector is forced to be constant once its diagonal is
constant. -/
theorem zeroSideCompletionVector_eq_center
    (hs : ZetaSeam)
    (N : ℕ) (i : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    zeroSideCompletionVector hs N L i =
      zeroSideCompletionVector hs N L (dictionaryCenterIndex N) := by
  let A := zeroSideDiscrepancy hs N L
  let a := zeroSideCompletionVector hs N L
  let c := dictionaryCenterIndex N
  have hrepr := zeroSideDiscrepancy_eq_completion hs N hL
  have hentry (r s : Fin (2 * N + 1)) :
      A r s = a s + a r := by
    have h := congrArg (fun M => M r s) hrepr
    simpa [A, a, Matrix.vecMulVec_apply] using h
  have hdiag := zeroSideDiscrepancy_diagonal_eq_center hs N i hL
  change A i i = A c c at hdiag
  rw [hentry i i, hentry c c] at hdiag
  have htwo : (2 : ℂ) * a i = (2 : ℂ) * a c := by
    simpa [two_mul] using hdiag
  exact (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)) htwo

/-- All entries of the H2b discrepancy are therefore equal to its centered
diagonal entry. -/
theorem zeroSideDiscrepancy_apply_eq_center
    (hs : ZetaSeam)
    (N : ℕ) (i j : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    zeroSideDiscrepancy hs N L i j =
      zeroSideDiscrepancy hs N L
        (dictionaryCenterIndex N) (dictionaryCenterIndex N) := by
  let A := zeroSideDiscrepancy hs N L
  let a := zeroSideCompletionVector hs N L
  let c := dictionaryCenterIndex N
  have hrepr := zeroSideDiscrepancy_eq_completion hs N hL
  have hentry (r s : Fin (2 * N + 1)) :
      A r s = a s + a r := by
    have h := congrArg (fun M => M r s) hrepr
    simpa [A, a, Matrix.vecMulVec_apply] using h
  have hai := zeroSideCompletionVector_eq_center hs N i hL
  have haj := zeroSideCompletionVector_eq_center hs N j hL
  change a i = a c at hai
  change a j = a c at haj
  change A i j = A c c
  rw [hentry i j, hentry c c, hai, haj]

/-- Constant-one matrix `J = 1 1ᵀ` on the finite dictionary coordinates. -/
def dictionaryOnesMatrix (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  vecMulVec (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))

/-- H2+ structural endpoint before identifying the scalar: the discrepancy is
one scalar multiple of `J`. -/
theorem zeroSideDiscrepancy_eq_center_smul_ones
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    zeroSideDiscrepancy hs N L =
      zeroSideDiscrepancy hs N L
          (dictionaryCenterIndex N) (dictionaryCenterIndex N) •
        dictionaryOnesMatrix N := by
  ext i j
  rw [zeroSideDiscrepancy_apply_eq_center hs N i j hL]
  simp [dictionaryOnesMatrix, Matrix.vecMulVec_apply]

/-- The one remaining scalar obstruction: literal tent zero side minus the
literal tent deterministic literature RHS. -/
def dictionaryTentDefect
    (hs : ZetaSeam) (L : ℝ) : ℂ :=
  (∑' ρ : (zetaZeros hs).carrier,
    ((zetaZeros hs).mult ρ : ℂ) *
      Zeta23.paperFT (dictionaryTent L) (gammaOf ρ)) -
    Zeta23.EF.literatureRHS (dictionaryTent L)

/-- The centered diagonal discrepancy is exactly the literal tent defect. -/
theorem zeroSideDiscrepancy_center_eq_dictionaryTentDefect
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    zeroSideDiscrepancy hs N L
        (dictionaryCenterIndex N) (dictionaryCenterIndex N) =
      dictionaryTentDefect hs L := by
  let c := dictionaryCenterIndex N
  have hZ :
      zeroSideMatrix hs N L c c =
        ∑' ρ : (zetaZeros hs).carrier,
          ((zetaZeros hs).mult ρ : ℂ) *
            Zeta23.paperFT (dictionaryTent L) (gammaOf ρ) := by
    unfold zeroSideMatrix
    apply tsum_congr
    intro ρ
    unfold dictionarySpectralMatrix
    simp only [c, centeredIndex_dictionaryCenterIndex]
    rw [dictionaryBasisTest_zero_zero_eq_tent hL]
  have hM :
      dictionaryMatrix L N c c =
        Zeta23.EF.literatureRHS (dictionaryTent L) := by
    have h :=
      literatureRHS_dictionaryBasisTest_eq_dictionaryMatrix_apply
        N c c hL
    simp only [c, centeredIndex_dictionaryCenterIndex] at h
    rw [dictionaryBasisTest_zero_zero_eq_tent hL] at h
    exact h.symm
  unfold zeroSideDiscrepancy dictionaryTentDefect
  simp only [Matrix.sub_apply]
  rw [hZ, hM]

/-- H2+ main endpoint: the entire actual finite zeta zero-side discrepancy is
exactly the universal literal-tent defect times `J`. -/
theorem zeroSideDiscrepancy_eq_tentDefect_smul_ones
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    zeroSideDiscrepancy hs N L =
      dictionaryTentDefect hs L • dictionaryOnesMatrix N := by
  rw [zeroSideDiscrepancy_eq_center_smul_ones hs N hL,
    zeroSideDiscrepancy_center_eq_dictionaryTentDefect hs N hL]

private def dictionaryOnesColumn (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin 1) ℂ :=
  fun _ _ => 1

private def dictionaryScaledOnesRow (N : ℕ) (δ : ℂ) :
    Matrix (Fin 1) (Fin (2 * N + 1)) ℂ :=
  fun _ _ => δ

private theorem dictionaryOnesColumn_mul_scaledOnesRow
    (N : ℕ) (δ : ℂ) :
    dictionaryOnesColumn N * dictionaryScaledOnesRow N δ =
      δ • dictionaryOnesMatrix N := by
  ext i j
  simp [Matrix.mul_apply, dictionaryOnesColumn, dictionaryScaledOnesRow,
    dictionaryOnesMatrix, Matrix.vecMulVec_apply]

/-- Rank consequence of the scalar collapse: the discrepancy has rank at most
one. -/
theorem rank_zeroSideDiscrepancy_le_one
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    (zeroSideDiscrepancy hs N L).rank ≤ 1 := by
  rw [zeroSideDiscrepancy_eq_tentDefect_smul_ones hs N hL,
    ← dictionaryOnesColumn_mul_scaledOnesRow
      N (dictionaryTentDefect hs L)]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width (dictionaryOnesColumn N))

/-- Fixed-finite bridge reduction: full matrix equality is now exactly the
vanishing of the one literal-tent defect scalar. -/
theorem zeroSideMatrix_eq_dictionaryMatrix_iff_tentDefect_eq_zero
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    zeroSideMatrix hs N L = dictionaryMatrix L N ↔
      dictionaryTentDefect hs L = 0 := by
  constructor
  · intro hEq
    have hdisc :
        zeroSideDiscrepancy hs N L
            (dictionaryCenterIndex N) (dictionaryCenterIndex N) = 0 := by
      unfold zeroSideDiscrepancy
      simp only [Matrix.sub_apply]
      rw [hEq]
      simp
    rw [zeroSideDiscrepancy_center_eq_dictionaryTentDefect hs N hL] at hdisc
    exact hdisc
  · intro hδ
    have hdisc := zeroSideDiscrepancy_eq_tentDefect_smul_ones hs N hL
    rw [hδ] at hdisc
    simp at hdisc
    unfold zeroSideDiscrepancy at hdisc
    exact sub_eq_zero.mp hdisc

end Zeta23.CCM

#print axioms Zeta23.CCM.zeroSideDiscrepancy_diagonal_eq_center
#print axioms Zeta23.CCM.zeroSideDiscrepancy_eq_tentDefect_smul_ones
#print axioms Zeta23.CCM.rank_zeroSideDiscrepancy_le_one
#print axioms Zeta23.CCM.zeroSideMatrix_eq_dictionaryMatrix_iff_tentDefect_eq_zero
