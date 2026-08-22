import Zeta23.CCM.FiniteDictionary
import Zeta23.CCM.FiniteMatrix
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

/-- The factor-two smoke test for the prime channel: evenness contributes a factor
`2`, which cancels the production `1/2` exactly. -/
theorem dictionaryBasisTest_pair_of_mem_aperture
    (n m : ℤ) {L y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    dictionaryBasisTest n m L y + dictionaryBasisTest n m L (-y) =
      (qBasis n m y L : ℂ) := by
  simp [dictionaryBasisTest, kernel, abs_of_nonneg hy0, hyL]

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

end Zeta23.CCM
