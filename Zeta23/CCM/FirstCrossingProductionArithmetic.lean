import Zeta23.CCM.CanonicalQuadraticNormalSourceKernel
import Zeta23.CCM.FirstCrossingStrictEvenSourceEnergy

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate ArithmeticFunction Interval

/-!
# Post-#280 production arithmetic frontier

PR #280 theoremized the source/remainder algebra through an abstract real-linear
functional. This module exposes the exact theorem-authoritative physical
pole/archimedean/von-Mangoldt evaluation already used by the canonical source.

The physical RHS is intentionally reused from
`DictionaryCompletePhysicalRHS`; no pole, archimedean, prime, cutoff, or
normalization constant is retyped here.

This file does **not** prove that the optimized contact curvature equals this
production evaluation on the handoff remainder. That derivative/integrability
bridge remains the active frontier.
-/

/-- Exact complete physical production evaluation of one complex source test. -/
def productionArithmeticComplexValue
    (L : ℝ) (f : ℝ → ℂ) : ℂ :=
  dictionaryCompletePhysicalRHS f L

/-- Physical lift of the exact quadratic-normal source atom without a new
normalization. The source coordinate is the production value `1 - t/L`. -/
def productionQuadraticNormalPhysicalSource
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    ℝ → ℂ :=
  fun t => quadraticNormalSourceAtom K v (1 - t / L)

/-- The production physical evaluation of the quadratic-normal source is
definitionally the already-proved source-kernel RHS. -/
theorem productionArithmeticComplexValue_quadraticNormal_eq_sourceKernelRHS
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    productionArithmeticComplexValue L
        (productionQuadraticNormalPhysicalSource L K v) =
      quadraticNormalSourceKernelRHS L K v := by
  rfl

/-- Consequently the exact canonical source moment is the production
pole/archimedean/von-Mangoldt evaluation of the same physical source test. -/
theorem explicitCanonicalSourceMoment_eq_productionArithmeticComplexValue
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    explicitCanonicalSourceMoment L K v =
      productionArithmeticComplexValue L
        (productionQuadraticNormalPhysicalSource L K v) := by
  calc
    explicitCanonicalSourceMoment L K v =
        quadraticNormalSourceKernelRHS L K v :=
      explicitCanonicalSourceMoment_eq_sourceKernelRHS hL K hK v
    _ =
        productionArithmeticComplexValue L
          (productionQuadraticNormalPhysicalSource L K v) :=
      (productionArithmeticComplexValue_quadraticNormal_eq_sourceKernelRHS
        L K v).symm

/-- Real restriction of the exact complete physical production evaluation.
This is a value-level interface, not an unrestricted linear map: the
archimedean density is singular at the physical origin, so admissibility of a
particular source/remainder test must be established separately. -/
def productionArithmeticRealValue
    (L : ℝ) (f : ℝ → ℝ) : ℝ :=
  Complex.re
    (productionArithmeticComplexValue L (fun t => (f t : ℂ)))

/-- The production source value entering the strict-even saturation balance. -/
def productionStrictEvenSourceValue
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) : ℝ :=
  Complex.re
    (star
        (productionArithmeticComplexValue L
          (productionQuadraticNormalPhysicalSource L K v)) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v))

/-- The production source value is exactly the PR #280 source/M4 pairing. -/
theorem productionStrictEvenSourceValue_eq_pairing
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    productionStrictEvenSourceValue L K v =
      strictEvenSourceMomentPairing L K v := by
  unfold productionStrictEvenSourceValue strictEvenSourceMomentPairing
  rw [← explicitCanonicalSourceMoment_eq_productionArithmeticComplexValue
    hL K hK v]

/-- At an exact even zero eigenmode, the theorem-authoritative production
pole/archimedean/von-Mangoldt source value is exactly the opposite-parity
energy of the centered-index image. -/
theorem productionStrictEvenSourceValue_eq_oddEnergy_of_even_zero_eigenmode
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig : evenCompressedCanonical L K v = 0) :
    productionStrictEvenSourceValue L K v =
      Complex.re
        (inner ℂ
          (oddCompressedCanonical L K
            (euclideanEvenToOddIndexLinearMap K v))
          (euclideanEvenToOddIndexLinearMap K v)) := by
  rw [productionStrictEvenSourceValue_eq_pairing hL K (by omega) v]
  exact
    strictEvenSourceMomentPairing_eq_oddEnergy_of_even_zero_eigenmode
      hL K hK v hveig

/-- In the strict-even zero-ground branch, the exact production source value is
strictly positive.  This is a production-arithmetic statement about the source
channel, not a sign theorem for the unresolved remainder. -/
theorem productionStrictEvenSourceValue_pos_of_even_zero_ground_strict
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hvne : v ≠ 0)
    (hground : parityRayleighBottom .even L K = 0)
    (hveig : evenCompressedCanonical L K v = 0)
    (hodd : 0 < parityRayleighBottom .odd L K) :
    0 < productionStrictEvenSourceValue L K v := by
  rw [productionStrictEvenSourceValue_eq_pairing hL K (by omega) v]
  exact
    strictEvenSourceMomentPairing_pos_of_even_zero_ground_strict
      hL K hK v hvne hground hveig hodd

end Zeta23.CCM

#print axioms Zeta23.CCM.explicitCanonicalSourceMoment_eq_productionArithmeticComplexValue
#print axioms Zeta23.CCM.productionStrictEvenSourceValue_eq_pairing
#print axioms Zeta23.CCM.productionStrictEvenSourceValue_eq_oddEnergy_of_even_zero_eigenmode
#print axioms Zeta23.CCM.productionStrictEvenSourceValue_pos_of_even_zero_ground_strict
