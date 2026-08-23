import Zeta23.CCM.FiniteDictionary
import Zeta23.CCM.FiniteMatrix
import Zeta23.CCM.KernelAnalysis
import Zeta23.ExplicitFormula

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# Deterministic explicit-formula side of the finite dictionary

This file starts the zero-free normalization step after the merged tent-analytics
package.  It introduces the production half-normalized basis test and the neutral
matrix target.  The proof order is deliberately channelwise:

`prime -> pole -> archimedean -> quadratic lift`.

No zero sum and no explicit-formula hypothesis is used in this file.
-/

/-- One production-normalized matrix-entry test.  This is literally one half of the
existing two-sided CCM kernel, matching the `1/2` in `dictionaryTest`. -/
def dictionaryBasisTest (n m : ℤ) (L : ℝ) : ℝ → ℂ :=
  fun y => (1 / 2 : ℂ) * kernel n m L y

@[simp] theorem dictionaryBasisTest_neg (n m : ℤ) (L y : ℝ) :
    dictionaryBasisTest n m L (-y) = dictionaryBasisTest n m L y := by
  simp [dictionaryBasisTest]

/-- Outside the aperture the production basis test vanishes. -/
theorem dictionaryBasisTest_eq_zero_of_lt_abs
    {n m : ℤ} {L y : ℝ} (hy : L < |y|) :
    dictionaryBasisTest n m L y = 0 := by
  simp [dictionaryBasisTest, kernel_eq_zero_of_lt_abs hy]

/-- Pointwise support of the production basis test stays inside the same aperture. -/
theorem dictionaryBasisTest_support_subset {L : ℝ} (n m : ℤ) :
    Function.support (dictionaryBasisTest n m L) ⊆ Icc (-L) L := by
  intro y hy
  apply kernel_support_subset n m
  intro hzero
  exact hy (by simp [dictionaryBasisTest, hzero])

/-- Topological support of the production basis test stays inside the closed aperture. -/
theorem dictionaryBasisTest_tsupport_subset {L : ℝ} (n m : ℤ) :
    tsupport (dictionaryBasisTest n m L) ⊆ Icc (-L) L := by
  exact closure_minimal (dictionaryBasisTest_support_subset n m) isClosed_Icc

/-- The factor-two smoke test for the prime channel: evenness contributes a factor
`2`, which cancels the production `1/2` exactly. -/
theorem dictionaryBasisTest_pair_of_mem_aperture
    (n m : ℤ) {L y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    dictionaryBasisTest n m L y + dictionaryBasisTest n m L (-y) =
      (qBasis n m y L : ℂ) := by
  simp [dictionaryBasisTest, kernel, abs_of_nonneg hy0, hyL]
  ring

/-- The same normalization smoke test specialized to a prime-power logarithm once
that logarithm is known to lie in the aperture. -/
theorem dictionaryBasisTest_prime_pair_of_log_mem
    (n m : ℤ) (q : ℕ) {L : ℝ}
    (hlog0 : 0 ≤ Real.log q) (hlogL : Real.log q ≤ L) :
    dictionaryBasisTest n m L (Real.log q) +
        dictionaryBasisTest n m L (-Real.log q) =
      (qBasis n m (Real.log q) L : ℂ) :=
  dictionaryBasisTest_pair_of_mem_aperture n m hlog0 hlogL

/-- Production finite matrix target locked by the external normalization audit.
The scalar correction is an identity-matrix channel, not the rank-one seam channel. -/
def dictionaryMatrix (L : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  finiteMatrix L N + ((2 * cCorrection L : ℝ) : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)

@[simp] theorem dictionaryMatrix_apply (L : ℝ) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    dictionaryMatrix L N i j =
      finiteMatrix L N i j +
        (if i = j then ((2 * cCorrection L : ℝ) : ℂ) else 0) := by
  by_cases h : i = j
  · subst j
    simp [dictionaryMatrix]
  · simp [dictionaryMatrix, h]

/-- Pole channel of the literature RHS, split out for normalization proofs. -/
def dictionaryPoleRHS (k : ℝ → ℂ) : ℂ :=
  Zeta23.paperFT k (Complex.I / 2) + Zeta23.paperFT k (-Complex.I / 2)

/-- Prime channel of the literature RHS, including its minus sign. -/
def dictionaryPrimeRHS (k : ℝ → ℂ) : ℂ :=
  -(∑' q : ℕ, ((Λ q / Real.sqrt q : ℝ) : ℂ) *
      (k (Real.log q) + k (-Real.log q)))

/-- Archimedean channel of the literature RHS. -/
def dictionaryArchRHS (k : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ)

/-- Exact bookkeeping decomposition of the inherited literature RHS. -/
theorem literatureRHS_eq_dictionaryChannels (k : ℝ → ℂ) :
    Zeta23.EF.literatureRHS k =
      dictionaryPoleRHS k + dictionaryPrimeRHS k + dictionaryArchRHS k := by
  rfl

/-- The production prime channel is exactly minus the fork-owned `primeComponent`.
This is the normalization crash test: evenness contributes `2` and the dictionary
basis contributes `1/2`, leaving no residual factor. -/
theorem dictionaryPrimeRHS_basis
    {L : ℝ} (_hL : 0 < L) (n m : ℤ) :
    dictionaryPrimeRHS (dictionaryBasisTest n m L) =
      -((primeComponent n m L : ℝ) : ℂ) := by
  unfold dictionaryPrimeRHS primeComponent
  let S := Finset.Icc 2 ⌊Real.exp L⌋₊
  have hks : tsupport (dictionaryBasisTest n m L) ⊆ Icc (-L) L :=
    dictionaryBasisTest_tsupport_subset n m
  rw [tsum_eq_sum (s := S)]
  · simp only [S]
    push_cast
    congr 1
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hqmem := Finset.mem_Icc.mp hq
    have hqposNat : 0 < q := lt_of_lt_of_le (by norm_num : 0 < 2) hqmem.1
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposNat
    have hqexp : (q : ℝ) ≤ Real.exp L :=
      (Nat.le_floor_iff (Real.exp_pos L).le).mp hqmem.2
    have hlogL : Real.log q ≤ L := by
      rw [← Real.log_exp L]
      exact Real.log_le_log hqpos hqexp
    rw [dictionaryBasisTest_prime_pair_of_log_mem n m q
      (Real.log_natCast_nonneg q) hlogL]
  · intro q hq
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

end Zeta23.CCM
