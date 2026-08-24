import Zeta23.CCM.DictionaryPoleSource
import Zeta23.CCM.DictionaryArchOffDiagonal

noncomputable section

namespace Zeta23.CCM

open Matrix Set MeasureTheory
open scoped BigOperators ComplexConjugate ArithmeticFunction

theorem probe_dictionaryTest_eq_basis_sum
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (L y : ℝ) :
    dictionaryTest N u L y =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L y * u j := by
  by_cases hy : |y| ≤ L
  · rw [dictionaryTest_eq_qBasisContract_of_abs_le N u hy]
    simp only [dictionaryBasisTest, kernel, hy, if_pos]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · have hylt : L < |y| := lt_of_not_ge hy
    rw [dictionaryTest_eq_zero_of_lt_abs N u L y hylt]
    simp [dictionaryBasisTest_eq_zero_of_lt_abs hylt]

theorem probe_continuous_dictionaryBasisTest
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    Continuous (dictionaryBasisTest n m L) := by
  unfold dictionaryBasisTest
  exact continuous_const.mul (kernel_continuous hL n m)

theorem probe_dictionaryBasisTest_hasCompactSupport
    {L : ℝ} (n m : ℤ) :
    HasCompactSupport (dictionaryBasisTest n m L) := by
  unfold dictionaryBasisTest
  exact (kernel_hasCompactSupport n m).mul_left

theorem probe_dictionaryTest_tsupport_subset
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (L : ℝ) :
    tsupport (dictionaryTest N u L) ⊆ Icc (-L) L := by
  exact closure_minimal (dictionaryTest_support_subset N u L) isClosed_Icc

theorem probe_paperFT_dictionaryTest_eq_basis_sum
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    Zeta23.paperFT (dictionaryTest N u L) z =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          Zeta23.paperFT
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L) z *
          u j := by
  rw [Zeta23.paperFT_def]
  have hfun :
      (fun y : ℝ => dictionaryTest N u L y * Complex.exp (Complex.I * z * y)) =
        fun y : ℝ => ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L y *
              Complex.exp (Complex.I * z * y)) * u j := by
    funext y
    rw [probe_dictionaryTest_eq_basis_sum N u L y]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun]
  have hint (i j : Fin (2 * N + 1)) : Integrable
      (fun y : ℝ =>
        (starRingEnd ℂ) (u i) *
          (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L y *
            Complex.exp (Complex.I * z * y)) * u j) := by
    have hcont : Continuous
        (fun y : ℝ =>
          (starRingEnd ℂ) (u i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L y *
              Complex.exp (Complex.I * z * y)) * u j) := by
      exact (continuous_const.mul
        ((probe_continuous_dictionaryBasisTest hL _ _).mul (by fun_prop))).mul
          continuous_const
    have hcs : HasCompactSupport
        (fun y : ℝ =>
          (starRingEnd ℂ) (u i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L y *
              Complex.exp (Complex.I * z * y)) * u j) := by
      exact (((probe_dictionaryBasisTest_hasCompactSupport
        (centeredIndex N i) (centeredIndex N j)).mul_right).mul_left).mul_right
    exact hcont.integrable_of_hasCompactSupport hcs
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Zeta23.integral_mul_const_C, Zeta23.integral_const_mul_C]

theorem probe_dictionaryPoleRHS_dictionaryTest
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryPoleRHS (dictionaryTest N u L) =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          ((poleComponent (centeredIndex N i) (centeredIndex N j) L : ℝ) : ℂ) *
          u j := by
  unfold dictionaryPoleRHS
  rw [probe_paperFT_dictionaryTest_eq_basis_sum N u hL (Complex.I / 2),
    probe_paperFT_dictionaryTest_eq_basis_sum N u hL (-Complex.I / 2),
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

private theorem probe_dictionaryPrimeRHS_eq_finset
    {k : ℝ → ℂ} {L : ℝ}
    (hks : tsupport k ⊆ Icc (-L) L) :
    dictionaryPrimeRHS k =
      -(∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        ((Λ q / Real.sqrt q : ℝ) : ℂ) *
          (k (Real.log q) + k (-Real.log q))) := by
  unfold dictionaryPrimeRHS
  let S := Finset.Icc 2 ⌊Real.exp L⌋₊
  rw [tsum_eq_sum (s := S)]
  intro q hq
  by_cases hsmall : q < 2
  · interval_cases q <;> simp
  · have hq2 : 2 ≤ q := Nat.le_of_not_gt hsmall
    have hqgt : ⌊Real.exp L⌋₊ < q := by
      by_contra hnot
      have hqle : q ≤ ⌊Real.exp L⌋₊ := Nat.le_of_not_gt hnot
      exact hq (by simpa [S, Finset.mem_Icc] using And.intro hq2 hqle)
    apply Zeta23.EF.prime_summand_eq_zero hks
    simp only [Finset.mem_Ioc, not_and, not_le]
    intro _
    exact hqgt

theorem probe_dictionaryPrimeRHS_dictionaryTest
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryPrimeRHS (dictionaryTest N u L) =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          (-((primeComponent (centeredIndex N i) (centeredIndex N j) L : ℝ) : ℂ)) *
          u j := by
  let S := Finset.Icc 2 ⌊Real.exp L⌋₊
  let w : ℕ → ℂ := fun q => ((Λ q / Real.sqrt q : ℝ) : ℂ)
  -- First truncate the production dictionary's raw `tsum` using only support.
  have hdictFinite :
      dictionaryPrimeRHS (dictionaryTest N u L) =
        -(∑ q ∈ S, w q *
          (dictionaryTest N u L (Real.log q) +
            dictionaryTest N u L (-Real.log q))) := by
    simpa only [S, w] using probe_dictionaryPrimeRHS_eq_finset
      (probe_dictionaryTest_tsupport_subset N u L)
  -- Do not apply this coefficient expansion until `hdictFinite` has replaced
  -- the infinite sum by the finite prime-power range.
  have hpair (q : ℕ) :
      dictionaryTest N u L (Real.log q) +
          dictionaryTest N u L (-Real.log q) =
        ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                (Real.log q) +
              dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                (-Real.log q)) * u j := by
    rw [probe_dictionaryTest_eq_basis_sum N u L (Real.log q),
      probe_dictionaryTest_eq_basis_sum N u L (-Real.log q),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  -- Truncate every basis channel independently as well; only after both sides
  -- are finite do the coefficient sums commute with the prime-power sum.
  have hbasisFinite (i j : Fin (2 * N + 1)) :
      dictionaryPrimeRHS
          (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L) =
        -(∑ q ∈ S, w q *
          (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
              (Real.log q) +
            dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
              (-Real.log q))) := by
    simpa only [S, w] using probe_dictionaryPrimeRHS_eq_finset
      (dictionaryBasisTest_tsupport_subset
        (centeredIndex N i) (centeredIndex N j))
  rw [hdictFinite]
  simp_rw [hpair]
  calc
    -(∑ q ∈ S, w q *
        ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                (Real.log q) +
              dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                (-Real.log q)) * u j) =
        ∑ q ∈ S, ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            (-(w q *
              (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (Real.log q) +
                dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (-Real.log q)))) * u j := by
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
          (starRingEnd ℂ) (u i) *
            (-(w q *
              (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (Real.log q) +
                dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (-Real.log q)))) * u j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            (-(∑ q ∈ S, w q *
              (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (Real.log q) +
                dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                  (-Real.log q)))) * u j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            dictionaryPrimeRHS
              (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L) *
            u j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hbasisFinite i j]
    _ = ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            (-((primeComponent (centeredIndex N i) (centeredIndex N j) L : ℝ) : ℂ)) *
            u j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [dictionaryPrimeRHS_basis hL]

/- These two packaging lemmas are the exact Phase-G contract consumed by the
finite archimedean lift.  Their only remaining inputs are the diagonal value
and diagonal full-`mu` integrability certificates supplied by Phase F. -/
theorem probe_integrable_paperFT_dictionaryBasisTest_mul_mu
    {L : ℝ} (hL : 0 < L)
    (hdiag : ∀ n : ℤ, Integrable (fun τ : ℝ =>
      Zeta23.paperFT (dictionaryBasisTest n n L) (τ : ℂ) *
        (Zeta23.mu τ : ℂ)))
    (n m : ℤ) :
    Integrable (fun τ : ℝ =>
      Zeta23.paperFT (dictionaryBasisTest n m L) (τ : ℂ) *
        (Zeta23.mu τ : ℂ)) := by
  by_cases hnm : n = m
  · subst m
    exact hdiag n
  · exact integrable_paperFT_dictionaryBasisTest_mul_mu_of_ne hL hnm

theorem probe_dictionaryArchRHS_basis
    {L : ℝ} (hL : 0 < L)
    (hdiag : ∀ n : ℤ,
      dictionaryArchRHS (dictionaryBasisTest n n L) =
        -((archComponent n n L : ℝ) : ℂ) +
          ((2 * cCorrection L : ℝ) : ℂ))
    (n m : ℤ) :
    dictionaryArchRHS (dictionaryBasisTest n m L) =
      ((-archComponent n m L +
        (if n = m then 2 * cCorrection L else 0) : ℝ) : ℂ) := by
  by_cases hnm : n = m
  · subst m
    simpa using hdiag n
  · simpa [hnm] using dictionaryArchRHS_basis_of_ne hL hnm

theorem probe_dictionaryArchRHS_dictionaryTest
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L)
    (hintBasis : ∀ n m : ℤ, Integrable (fun τ : ℝ =>
      Zeta23.paperFT (dictionaryBasisTest n m L) (τ : ℂ) *
        (Zeta23.mu τ : ℂ)))
    (hBasis : ∀ n m : ℤ,
      dictionaryArchRHS (dictionaryBasisTest n m L) =
        ((-archComponent n m L +
          (if n = m then 2 * cCorrection L else 0) : ℝ) : ℂ)) :
    dictionaryArchRHS (dictionaryTest N u L) =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          ((-archComponent (centeredIndex N i) (centeredIndex N j) L +
            (if i = j then 2 * cCorrection L else 0) : ℝ) : ℂ) *
          u j := by
  rw [dictionaryArchRHS_eq_integral_mu]
  have hfun :
      (fun τ : ℝ =>
        Zeta23.paperFT (dictionaryTest N u L) (τ : ℂ) *
          (Zeta23.mu τ : ℂ)) =
        fun τ : ℝ => ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            (Zeta23.paperFT
                (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
                (τ : ℂ) * (Zeta23.mu τ : ℂ)) * u j := by
    funext τ
    rw [probe_paperFT_dictionaryTest_eq_basis_sum N u hL (τ : ℂ)]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun]
  have hint (i j : Fin (2 * N + 1)) : Integrable (fun τ : ℝ =>
      (starRingEnd ℂ) (u i) *
        (Zeta23.paperFT
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
            (τ : ℂ) * (Zeta23.mu τ : ℂ)) * u j) :=
    ((hintBasis (centeredIndex N i) (centeredIndex N j)).const_mul _).mul_const _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Zeta23.integral_mul_const_C, Zeta23.integral_const_mul_C,
    ← dictionaryArchRHS_eq_integral_mu,
    hBasis (centeredIndex N i) (centeredIndex N j)]
  simp only [(centeredIndex_injective N).eq_iff]

theorem probe_final_assembly
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) {L : ℝ}
    (hPole : dictionaryPoleRHS (dictionaryTest N u L) =
      ∑ i, ∑ j, (starRingEnd ℂ) (u i) *
        ((poleComponent (centeredIndex N i) (centeredIndex N j) L : ℝ) : ℂ) * u j)
    (hPrime : dictionaryPrimeRHS (dictionaryTest N u L) =
      ∑ i, ∑ j, (starRingEnd ℂ) (u i) *
        (-((primeComponent (centeredIndex N i) (centeredIndex N j) L : ℝ) : ℂ)) * u j)
    (hArch : dictionaryArchRHS (dictionaryTest N u L) =
      ∑ i, ∑ j, (starRingEnd ℂ) (u i) *
        ((-archComponent (centeredIndex N i) (centeredIndex N j) L +
          (if i = j then 2 * cCorrection L else 0) : ℝ) : ℂ) * u j) :
    Zeta23.EF.literatureRHS (dictionaryTest N u L) =
      quadraticForm (dictionaryMatrix L N) u := by
  rw [literatureRHS_eq_dictionaryChannels, hPole, hPrime, hArch,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  unfold quadraticForm
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dictionaryMatrix_apply, finiteMatrix_apply]
  unfold entry
  push_cast
  ring

theorem probe_advertised_endpoint_with_basis_contract
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L)
    (hintBasis : ∀ n m : ℤ, Integrable (fun τ : ℝ =>
      Zeta23.paperFT (dictionaryBasisTest n m L) (τ : ℂ) *
        (Zeta23.mu τ : ℂ)))
    (hBasis : ∀ n m : ℤ,
      dictionaryArchRHS (dictionaryBasisTest n m L) =
        ((-archComponent n m L +
          (if n = m then 2 * cCorrection L else 0) : ℝ) : ℂ)) :
    Zeta23.EF.literatureRHS
        (dictionaryTest N (fun i => (u i : ℂ)) L) =
      quadraticForm (dictionaryMatrix L N) (fun i => (u i : ℂ)) := by
  apply probe_final_assembly N (fun i => (u i : ℂ))
  · exact probe_dictionaryPoleRHS_dictionaryTest N (fun i => (u i : ℂ)) hL
  · exact probe_dictionaryPrimeRHS_dictionaryTest N (fun i => (u i : ℂ)) hL
  · exact probe_dictionaryArchRHS_dictionaryTest N (fun i => (u i : ℂ)) hL
      hintBasis hBasis

/- Exact production endpoint.  This wrapper intentionally has no analytic or
finite-support proof in its body: those obligations are discharged by the
preceding channel lifts and the two Phase-G all-entry exports. -/
theorem literatureRHS_dictionaryTest_eq_quadraticForm
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) :
  Zeta23.EF.literatureRHS
    (dictionaryTest N (fun i => (u i : ℂ)) L)
    =
  quadraticForm
    (dictionaryMatrix L N)
    (fun i => (u i : ℂ)) := by
  apply probe_final_assembly N (fun i => (u i : ℂ))
  · exact probe_dictionaryPoleRHS_dictionaryTest N (fun i => (u i : ℂ)) hL
  · exact probe_dictionaryPrimeRHS_dictionaryTest N (fun i => (u i : ℂ)) hL
  · exact probe_dictionaryArchRHS_dictionaryTest N (fun i => (u i : ℂ)) hL
      (integrable_paperFT_dictionaryBasisTest_mul_mu hL)
      (dictionaryArchRHS_basis hL)

end Zeta23.CCM
