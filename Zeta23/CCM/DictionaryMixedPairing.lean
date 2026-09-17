import Zeta23.CCM.DictionaryRHSIdentity

noncomputable section

namespace Zeta23.CCM

open Complex Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: mixed finite-dictionary pairing

The deterministic R003 dictionary theorem is stated as a quadratic identity.
For Pair D we need the corresponding mixed left/right contraction because the
active observable pairs the quadratic normal with an even boundary-flat trial.

This module proves that mixed identity directly from the already validated
basis/channel lifts. No new explicit-formula normalization is introduced.
-/

/-- Raw mixed coefficient pairing with the repository's conjugate-left,
linear-right convention. -/
def matrixCoefficientPairing
    {N : ℕ}
    (M : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)
    (x y : Fin (2 * N + 1) → ℂ) : ℂ :=
  ∑ i, ∑ j, star (x i) * M i j * y j

/-- Mixed physical dictionary test assembled from the theorem-authoritative
basis tests. -/
def dictionaryMixedTest
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    (L : ℝ) : ℝ → ℂ :=
  fun t =>
    ∑ i, ∑ j,
      star (x i) *
        dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L t *
        y j

/-- The mixed test vanishes outside the common physical aperture. -/
theorem dictionaryMixedTest_eq_zero_of_lt_abs
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    (L t : ℝ) (ht : L < |t|) :
    dictionaryMixedTest N x y L t = 0 := by
  unfold dictionaryMixedTest
  simp [dictionaryBasisTest_eq_zero_of_lt_abs ht]

/-- Support of the mixed test is contained in the common aperture. -/
theorem dictionaryMixedTest_support_subset
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    (L : ℝ) :
    Function.support (dictionaryMixedTest N x y L) ⊆ Icc (-L) L := by
  intro t ht
  have habs : |t| ≤ L := by
    by_contra hnot
    have hlt : L < |t| := lt_of_not_ge hnot
    exact ht (dictionaryMixedTest_eq_zero_of_lt_abs N x y L t hlt)
  exact abs_le.mp habs

/-- Topological support of the mixed test is contained in the common aperture. -/
theorem dictionaryMixedTest_tsupport_subset
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    (L : ℝ) :
    tsupport (dictionaryMixedTest N x y L) ⊆ Icc (-L) L := by
  exact closure_minimal (dictionaryMixedTest_support_subset N x y L) isClosed_Icc

/-- Fourier transform of the mixed finite dictionary as the corresponding
finite basis-transform contraction. -/
theorem paperFT_dictionaryMixedTest_eq_basis_sum
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    Zeta23.paperFT (dictionaryMixedTest N x y L) z =
      ∑ i, ∑ j,
        star (x i) *
          Zeta23.paperFT
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L) z *
          y j := by
  rw [Zeta23.paperFT_def]
  have hfun :
      (fun t : ℝ =>
        dictionaryMixedTest N x y L t * Complex.exp (Complex.I * z * t)) =
      fun t : ℝ => ∑ i, ∑ j,
        star (x i) *
          (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L t *
            Complex.exp (Complex.I * z * t)) *
          y j := by
    funext t
    unfold dictionaryMixedTest
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun]
  have hint (i j : Fin (2 * N + 1)) : Integrable
      (fun t : ℝ =>
        star (x i) *
          (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L t *
            Complex.exp (Complex.I * z * t)) *
          y j) := by
    have hcont : Continuous
        (fun t : ℝ =>
          star (x i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L t *
              Complex.exp (Complex.I * z * t)) *
            y j) := by
      exact (continuous_const.mul
        ((continuous_dictionaryBasisTest hL _ _).mul (by fun_prop))).mul
          continuous_const
    have hcs : HasCompactSupport
        (fun t : ℝ =>
          star (x i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L t *
              Complex.exp (Complex.I * z * t)) *
            y j) := by
      exact (((dictionaryBasisTest_hasCompactSupport
        (centeredIndex N i) (centeredIndex N j)).mul_right).mul_left).mul_right
    exact hcont.integrable_of_hasCompactSupport hcs
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Zeta23.integral_mul_const_C, Zeta23.integral_const_mul_C,
    Zeta23.paperFT_def]

/-- Pole channel of the mixed finite dictionary. -/
theorem dictionaryPoleRHS_dictionaryMixedTest
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryPoleRHS (dictionaryMixedTest N x y L) =
      ∑ i, ∑ j,
        star (x i) *
          ((poleComponent (centeredIndex N i) (centeredIndex N j) L : ℝ) : ℂ) *
          y j := by
  unfold dictionaryPoleRHS
  rw [paperFT_dictionaryMixedTest_eq_basis_sum N x y hL (Complex.I / 2),
    paperFT_dictionaryMixedTest_eq_basis_sum N x y hL (-Complex.I / 2),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← dictionaryPoleRHS_basis hL
    (centeredIndex N i) (centeredIndex N j)]
  unfold dictionaryPoleRHS
  ring

/-- Prime channel of the mixed finite dictionary. The raw prime `tsum` is
truncated before any coefficient sums are reordered. -/
theorem dictionaryPrimeRHS_dictionaryMixedTest
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryPrimeRHS (dictionaryMixedTest N x y L) =
      ∑ i, ∑ j,
        star (x i) *
          (-((primeComponent (centeredIndex N i) (centeredIndex N j) L : ℝ) : ℂ)) *
          y j := by
  let S := Finset.Icc 2 ⌊Real.exp L⌋₊
  let w : ℕ → ℂ := fun q => ((Λ q / Real.sqrt q : ℝ) : ℂ)
  have hmixedFinite :
      dictionaryPrimeRHS (dictionaryMixedTest N x y L) =
        -(∑ q ∈ S, w q *
          (dictionaryMixedTest N x y L (Real.log q) +
            dictionaryMixedTest N x y L (-Real.log q))) := by
    simpa only [S, w] using dictionaryPrimeRHS_eq_finset
      (dictionaryMixedTest_tsupport_subset N x y L)
  have hpair (q : ℕ) :
      dictionaryMixedTest N x y L (Real.log q) +
          dictionaryMixedTest N x y L (-Real.log q) =
        ∑ i, ∑ j,
          star (x i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                (Real.log q) +
              dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                (-Real.log q)) * y j := by
    unfold dictionaryMixedTest
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hbasisFinite (i j : Fin (2 * N + 1)) :
      dictionaryPrimeRHS
          (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L) =
        -(∑ q ∈ S, w q *
          (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
              (Real.log q) +
            dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
              (-Real.log q))) := by
    simpa only [S, w] using dictionaryPrimeRHS_eq_finset
      (dictionaryBasisTest_tsupport_subset
        (centeredIndex N i) (centeredIndex N j))
  rw [hmixedFinite]
  simp_rw [hpair]
  calc
    -(∑ q ∈ S, w q *
        ∑ i, ∑ j,
          star (x i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                (Real.log q) +
              dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                (-Real.log q)) * y j) =
        ∑ q ∈ S, ∑ i, ∑ j,
          star (x i) *
            (-(w q *
              (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (Real.log q) +
                dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (-Real.log q)))) * y j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, ∑ j, ∑ q ∈ S,
          star (x i) *
            (-(w q *
              (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (Real.log q) +
                dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (-Real.log q)))) * y j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j,
          star (x i) *
            (-(∑ q ∈ S, w q *
              (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (Real.log q) +
                dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (-Real.log q)))) * y j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ j,
          star (x i) *
            dictionaryPrimeRHS
              (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L) *
            y j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hbasisFinite i j]
    _ = ∑ i, ∑ j,
          star (x i) *
            (-((primeComponent (centeredIndex N i) (centeredIndex N j) L : ℝ) : ℂ)) *
            y j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [dictionaryPrimeRHS_basis hL]

/-- Archimedean channel of the mixed finite dictionary. -/
theorem dictionaryArchRHS_dictionaryMixedTest
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryArchRHS (dictionaryMixedTest N x y L) =
      ∑ i, ∑ j,
        star (x i) *
          ((-archComponent (centeredIndex N i) (centeredIndex N j) L +
            (if i = j then 2 * cCorrection L else 0) : ℝ) : ℂ) *
          y j := by
  rw [dictionaryArchRHS_eq_integral_mu]
  have hpaper (tau : ℝ) :
      Zeta23.paperFT (dictionaryMixedTest N x y L) (tau : ℂ) =
        ∑ i, ∑ j,
          star (x i) *
            Zeta23.paperFT
              (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
              (tau : ℂ) * y j :=
    paperFT_dictionaryMixedTest_eq_basis_sum N x y hL (tau : ℂ)
  rw [show
    (fun tau : ℝ =>
      Zeta23.paperFT (dictionaryMixedTest N x y L) (tau : ℂ) *
        (Zeta23.mu tau : ℂ)) =
      fun tau : ℝ => ∑ i, ∑ j,
        star (x i) *
          (Zeta23.paperFT
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
            (tau : ℂ) * (Zeta23.mu tau : ℂ)) * y j by
      funext tau
      rw [hpaper tau]
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring]
  have hint (i j : Fin (2 * N + 1)) : Integrable (fun tau : ℝ =>
      star (x i) *
        (Zeta23.paperFT
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
            (tau : ℂ) * (Zeta23.mu tau : ℂ)) * y j) :=
    ((integrable_paperFT_dictionaryBasisTest_mul_mu hL
      (centeredIndex N i) (centeredIndex N j)).const_mul _).mul_const _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Zeta23.integral_mul_const_C, Zeta23.integral_const_mul_C,
    ← dictionaryArchRHS_eq_integral_mu,
    dictionaryArchRHS_basis hL
      (centeredIndex N i) (centeredIndex N j)]
  simp only [(centeredIndex_injective N).eq_iff]

/-- Mixed deterministic assembly theorem. This is the bilinear/sesquilinear
extension of the existing quadratic R003 endpoint. -/
theorem literatureRHS_dictionaryMixedTest_eq_matrixCoefficientPairing
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    Zeta23.EF.literatureRHS (dictionaryMixedTest N x y L) =
      matrixCoefficientPairing (dictionaryMatrix L N) x y := by
  rw [literatureRHS_eq_dictionaryChannels,
    dictionaryPoleRHS_dictionaryMixedTest N x y hL,
    dictionaryPrimeRHS_dictionaryMixedTest N x y hL,
    dictionaryArchRHS_dictionaryMixedTest N x y hL]
  unfold matrixCoefficientPairing
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dictionaryMatrix_apply, finiteMatrix_apply]
  unfold entry
  by_cases hij : i = j <;> simp [hij] <;> ring

end Zeta23.CCM

#print axioms Zeta23.CCM.literatureRHS_dictionaryMixedTest_eq_matrixCoefficientPairing