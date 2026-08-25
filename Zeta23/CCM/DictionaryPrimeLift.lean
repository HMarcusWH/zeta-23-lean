import Zeta23.CCM.DictionaryPoleLift

noncomputable section

namespace Zeta23.CCM

open Matrix Set MeasureTheory
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-! # Finite dictionary prime-channel lift

Phase J2 of the deterministic R003 completion.  The raw prime `tsum` is first
truncated independently for the full dictionary and for every basis channel.
Only after both sides are finite are coefficient sums reordered.
-/

private theorem dictionaryPrimeRHS_eq_finset
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

/-- The prime channel of the full finite dictionary is the coefficient
contraction of minus the fork-owned prime component.  Infinite and coefficient
sums are never interchanged. -/
theorem dictionaryPrimeRHS_dictionaryTest
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryPrimeRHS (dictionaryTest N u L) =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          (-((primeComponent (centeredIndex N i) (centeredIndex N j) L : ℝ) : ℂ)) *
          u j := by
  let S := Finset.Icc 2 ⌊Real.exp L⌋₊
  let w : ℕ → ℂ := fun q => ((Λ q / Real.sqrt q : ℝ) : ℂ)
  have hdictFinite :
      dictionaryPrimeRHS (dictionaryTest N u L) =
        -(∑ q ∈ S, w q *
          (dictionaryTest N u L (Real.log q) +
            dictionaryTest N u L (-Real.log q))) := by
    simpa only [S, w] using dictionaryPrimeRHS_eq_finset
      (dictionaryTest_tsupport_subset N u L)
  have hpair (q : ℕ) :
      dictionaryTest N u L (Real.log q) +
          dictionaryTest N u L (-Real.log q) =
        ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                (Real.log q) +
              dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L
                (-Real.log q)) * u j := by
    rw [dictionaryTest_eq_basis_sum N u L (Real.log q),
      dictionaryTest_eq_basis_sum N u L (-Real.log q),
      ← Finset.sum_add_distrib]
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

end Zeta23.CCM
