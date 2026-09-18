import Zeta23.CCM.DictionaryCompletePhysicalRHS
import Zeta23.CCM.CanonicalQuadraticNormalSourceFunctional

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate ArithmeticFunction Interval

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: canonical quadratic-normal source kernel

This module specializes the generic complete physical RHS to the exact
quadratic-normal source observable used by Pair D.
-/

/-- Exact source-coordinate kernel expression for the complete Pair-D functional. -/
def quadraticNormalSourceKernelRHS
    (L : ℝ)
    (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) : ℂ :=
  (∫ x in (0 : ℝ)..L,
      quadraticNormalSourceAtom K v (1 - x / L) *
        (completeSourcePoleWeight x : ℂ))
    -
  (∫ x in (0 : ℝ)..L,
      quadraticNormalSourceAtom K v (1 - x / L) *
        (archDensity x : ℂ))
    -
  ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
      primeSourceWeight q *
        quadraticNormalSourceAtom K v (primeSourceCoordinate q L)

/-- Inside a positive aperture, the canonical physical lift is the unclamped
source coordinate `1-x/L`. -/
theorem canonicalSourcePhysicalLift_eq_one_sub_of_mem
    {L x : ℝ} (hL : 0 < L)
    (hx0 : 0 ≤ x) (hxL : x ≤ L)
    (h : ℝ → ℂ) :
    canonicalSourcePhysicalLift L h x = h (1 - x / L) := by
  unfold canonicalSourcePhysicalLift
  have habs : |x| ≤ L := by
    simpa [abs_of_nonneg hx0] using hxL
  rw [dictionaryApertureCoord_eq_one_sub_of_abs_le hL habs,
    abs_of_nonneg hx0]

/-- Prime samples inside the finite aperture map to the exact canonical prime
source coordinate. -/
theorem canonicalSourcePhysicalLift_log_eq_primeSourceCoordinate
    {L : ℝ} (hL : 0 < L)
    {q : ℕ}
    (hq : q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊)
    (h : ℝ → ℂ) :
    canonicalSourcePhysicalLift L h (Real.log q) =
      h (primeSourceCoordinate q L) := by
  have hqmem := Finset.mem_Icc.mp hq
  have hqposNat : 0 < q :=
    lt_of_lt_of_le (by norm_num : 0 < 2) hqmem.1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposNat
  have hqexp : (q : ℝ) ≤ Real.exp L :=
    (Nat.le_floor_iff (Real.exp_pos L).le).mp hqmem.2
  have hlog0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hlogL : Real.log q ≤ L := by
    rw [← Real.log_exp L]
    exact Real.log_le_log hqpos hqexp
  rw [canonicalSourcePhysicalLift_eq_one_sub_of_mem hL hlog0 hlogL]
  rfl

/-- The active physical lift vanishes at physical center because source
coordinate one is scalar identity and the quadratic normal annihilates it. -/
@[simp] theorem canonicalSourcePhysicalLift_quadraticNormalSourceAtom_zero
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    canonicalSourcePhysicalLift L
      (quadraticNormalSourceAtom K v) 0 = 0 := by
  unfold canonicalSourcePhysicalLift
  rw [dictionaryApertureCoord_zero]
  exact quadraticNormalSourceAtom_one K v

/-- The complete functional on the active source atom is exactly the explicit
source-coordinate integral-plus-prime expression. -/
theorem canonicalQuadraticNormalSourceFunctional_eq_sourceKernelRHS
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    canonicalQuadraticNormalSourceFunctional L
        (quadraticNormalSourceAtom K v) =
      quadraticNormalSourceKernelRHS L K v := by
  let xvec : Fin (2 * K + 1) → ℂ :=
    fun i => centeredQuadraticNormal K i
  let yvec : Fin (2 * K + 1) → ℂ :=
    fun j =>
      (2 / inner ℂ (centeredQuadraticNormal K)
              (centeredQuadraticNormal K)) *
        evenBoundaryFlatRawCoefficients K v j
  have hlift :
      canonicalSourcePhysicalLift L (quadraticNormalSourceAtom K v) =
        dictionaryMixedTest K xvec yvec L := by
    simpa [xvec, yvec] using
      canonicalSourcePhysicalLift_quadraticNormalSourceAtom_eq_mixedTest
        hL K hK v
  have hzero : dictionaryMixedTest K xvec yvec L 0 = 0 := by
    rw [← congrFun hlift 0]
    exact canonicalSourcePhysicalLift_quadraticNormalSourceAtom_zero hL K v
  unfold canonicalQuadraticNormalSourceFunctional
  rw [hlift]
  rw [half_literatureRHS_dictionaryMixedTest_eq_completePhysicalRHS_of_zero
    K xvec yvec hL hzero]
  unfold dictionaryCompletePhysicalRHS quadraticNormalSourceKernelRHS
  have hinterval (w : ℝ → ℂ) :
      (∫ x in (0 : ℝ)..L,
        dictionaryMixedTest K xvec yvec L x * w x) =
      ∫ x in (0 : ℝ)..L,
        quadraticNormalSourceAtom K v (1 - x / L) * w x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hL.le] at hx
    change
      dictionaryMixedTest K xvec yvec L x * w x =
        quadraticNormalSourceAtom K v (1 - x / L) * w x
    rw [← congrFun hlift x]
    rw [canonicalSourcePhysicalLift_eq_one_sub_of_mem hL hx.1 hx.2]
  rw [hinterval (fun x => (completeSourcePoleWeight x : ℂ))]
  rw [hinterval (fun x => (archDensity x : ℂ))]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [← congrFun hlift (Real.log q)]
  rw [canonicalSourcePhysicalLift_log_eq_primeSourceCoordinate hL hq]

/-- Headline source-kernel theorem: the exact production source moment is the
same explicit continuous-plus-prime source-coordinate functional. -/
theorem explicitCanonicalSourceMoment_eq_sourceKernelRHS
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    explicitCanonicalSourceMoment L K v =
      quadraticNormalSourceKernelRHS L K v := by
  rw [explicitCanonicalSourceMoment_eq_completeSourceFunctional hL K hK v]
  exact canonicalQuadraticNormalSourceFunctional_eq_sourceKernelRHS
    hL K hK v

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalQuadraticNormalSourceFunctional_eq_sourceKernelRHS
#print axioms Zeta23.CCM.explicitCanonicalSourceMoment_eq_sourceKernelRHS
