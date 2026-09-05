import Zeta23.CCM.FirstBadShiftedSchur
import Zeta23.CCM.ParityCubicFactorization
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E1: cubic-shell incidence

PR #113 gives the canonical intrinsic decomposition `V = W ⊕ S` at one
centered N-flow step and proves

  intrinsicShellPart p N v = 0 ↔ v ∈ W.

PR #112 gives the explicit nonzero odd cubic compression channel and its
algebraic pullback to the even carrier.  This module proves that the cubic
channel is not inherited from the centered predecessor image.  Consequently
its canonical intrinsic shell coordinate is nonzero in either parity.

The proof deliberately avoids making the stronger closed-form projection
formula `g_K = d^3 - α_K d` with an explicit power-sum value for `α_K` a
prerequisite.  Instead, if the new outer coordinate vanished, exact odd-normal
geometry would force the candidate `d^3 - K^2 d` to be boundary-flat.  Its
first centered moment is strictly negative for `K >= 2`, a contradiction.

Firewalls:
* the cubic vector is not proved to lie purely in the shell;
* the shell is not proved invariant under the compressed canonical operator;
* D is used only algebraically, never as a unitary/isometric transport;
* no nonzeroness of `cubicDefectFunctional` is claimed;
* no Schur contradiction, positivity theorem, finite-to-infinite closure, or
  RH theorem is claimed.
-/

/-- The rightmost grid coordinate has centered index equal to the grid
radius.  The generic helper keeps endpoint arithmetic out of downstream
projection arguments. -/
@[simp] theorem centeredIndex_finLast (K : ℕ) :
    centeredIndex K (Fin.last (2 * K)) = (K : ℤ) := by
  simp [centeredIndex] <;> omega

/-- Rightmost coordinate in the successor grid for a one-step centered
extension from size `N` to size `N+1`. -/
def successorRightOuterIndex (N : ℕ) : Fin (2 * (N + 1) + 1) :=
  Fin.last (2 * (N + 1))

@[simp] theorem centeredIndex_successorRightOuterIndex (N : ℕ) :
    centeredIndex (N + 1) (successorRightOuterIndex N) = (N + 1 : ℤ) := by
  simpa [successorRightOuterIndex] using centeredIndex_finLast (N + 1)

/-- The new right outer coordinate is not in the range of the one-step
centered predecessor embedding. -/
theorem successorRightOuterIndex_not_mem_centeredEmbedding_range
    (N : ℕ) :
    successorRightOuterIndex N ∉
      Set.range (centeredEmbedding N (N + 1) (Nat.le_succ N)) := by
  rintro ⟨i, hi⟩
  have hval := congrArg Fin.val hi
  simp [successorRightOuterIndex, centeredEmbedding] at hval
  omega

/-- Exact one-step centered Euclidean zero extension vanishes at the new right
outer coordinate. -/
theorem euclideanCenteredZeroExtend_succ_rightOuter_eq_zero
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    euclideanCenteredZeroExtend (Nat.le_succ N) x
      (successorRightOuterIndex N) = 0 := by
  exact euclideanCenteredZeroExtendLinearMap_apply_of_not_mem_range
    (Nat.le_succ N) x (successorRightOuterIndex N)
      (successorRightOuterIndex_not_mem_centeredEmbedding_range N)

/-- Every vector in the intrinsic centered predecessor has zero value at the
new right outer coordinate. -/
theorem intrinsicPredecessor_rightOuter_eq_zero
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p (N + 1))
    (hv : v ∈ intrinsicParityPredecessorSubspace p N) :
    ((v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
        (successorRightOuterIndex N) = 0 := by
  have hv' := hv
  change
    ((v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanParityEmbeddedSuccSubspace p N at hv'
  rcases hv' with ⟨x, hx, hxv⟩
  rw [← hxv]
  exact euclideanCenteredZeroExtend_succ_rightOuter_eq_zero N x

/-- Raw cubic-minus-outer-slope vector.  If the projected cubic channel had
zero outer coordinate, exact odd-normal geometry would force it to equal this
vector with `K` equal to the current grid radius. -/
def cubicOuterVanishingRaw (K : ℕ) : Fin (2 * K + 1) → ℂ :=
  fun i =>
    (centeredIndex K i : ℂ) ^ 3 -
      (K : ℂ) ^ 2 * (centeredIndex K i : ℂ)

/-- Real summand in the first centered moment of
`cubicOuterVanishingRaw K`. -/
def cubicOuterMomentTerm
    (K : ℕ) (i : Fin (2 * K + 1)) : ℝ :=
  let x : ℝ := (centeredIndex K i : ℝ)
  x ^ 2 * (x ^ 2 - (K : ℝ) ^ 2)

/-- Every centered grid index has square at most the square of the radius. -/
theorem centeredIndex_sq_le_radius_sq
    (K : ℕ) (i : Fin (2 * K + 1)) :
    ((centeredIndex K i : ℝ) ^ 2) ≤ (K : ℝ) ^ 2 := by
  have hloZ : -(K : ℤ) ≤ centeredIndex K i := by
    dsimp [centeredIndex]
    omega
  have hhiZ : centeredIndex K i ≤ (K : ℤ) := by
    dsimp [centeredIndex]
    omega
  have hlo : -(K : ℝ) ≤ (centeredIndex K i : ℝ) := by
    exact_mod_cast hloZ
  have hhi : (centeredIndex K i : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hhiZ
  nlinarith

/-- Every first-moment summand of the outer-vanishing cubic candidate is
nonpositive. -/
theorem cubicOuterMomentTerm_nonpos
    (K : ℕ) (i : Fin (2 * K + 1)) :
    cubicOuterMomentTerm K i ≤ 0 := by
  unfold cubicOuterMomentTerm
  exact mul_nonpos_of_nonneg_of_nonpos
    (sq_nonneg (centeredIndex K i : ℝ))
    (sub_nonpos.mpr (centeredIndex_sq_le_radius_sq K i))

/-- For `K>=2`, the first centered moment of the outer-vanishing cubic
candidate is strictly negative.  The strict summand is the grid point with
centered index `1`. -/
theorem sum_cubicOuterMomentTerm_neg
    (K : ℕ) (hK : 2 ≤ K) :
    (∑ i : Fin (2 * K + 1), cubicOuterMomentTerm K i) < 0 := by
  let i1 : Fin (2 * K + 1) := ⟨K + 1, by omega⟩
  have hi1 : centeredIndex K i1 = 1 := by
    dsimp [i1, centeredIndex]
    omega
  have hstrict : cubicOuterMomentTerm K i1 < 0 := by
    simp [cubicOuterMomentTerm, hi1]
    have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  calc
    (∑ i : Fin (2 * K + 1), cubicOuterMomentTerm K i) <
        ∑ i : Fin (2 * K + 1), (0 : ℝ) := by
      refine Finset.sum_lt_sum
        (fun i _ => cubicOuterMomentTerm_nonpos K i) ?_
      exact ⟨i1, Finset.mem_univ i1, hstrict⟩
    _ = 0 := by simp

/-- Pointwise real-part normalization for the first moment of
`cubicOuterVanishingRaw`.  Keeping the complex-to-real coercion step local
prevents the finite-sum proof from depending on fragile simplifier behavior. -/
theorem re_cubicOuterVanishing_summand
    (K : ℕ) (i : Fin (2 * K + 1)) :
    Complex.re
        ((centeredIndex K i : ℂ) *
          ((centeredIndex K i : ℂ) ^ 3 -
            (K : ℂ) ^ 2 * (centeredIndex K i : ℂ))) =
      cubicOuterMomentTerm K i := by
  simp [cubicOuterMomentTerm, Complex.mul_re, pow_succ] <;> ring

/-- The raw vector `d^3-K^2 d` cannot satisfy the first boundary-flat moment
when `K>=2`.  This is the arithmetic obstruction used instead of a stronger
closed-form projection coefficient. -/
theorem centeredMoment_one_cubicOuterVanishingRaw_ne_zero
    (K : ℕ) (hK : 2 ≤ K) :
    centeredMoment K 1 (cubicOuterVanishingRaw K) ≠ 0 := by
  have hsum := sum_cubicOuterMomentTerm_neg K hK
  have hre :
      Complex.re (centeredMoment K 1 (cubicOuterVanishingRaw K)) =
        ∑ i : Fin (2 * K + 1), cubicOuterMomentTerm K i := by
    unfold centeredMoment cubicOuterVanishingRaw
    change
      Complex.reCLM
          (∑ i : Fin (2 * K + 1),
            (centeredIndex K i : ℂ) ^ 1 *
              ((centeredIndex K i : ℂ) ^ 3 -
                (K : ℂ) ^ 2 * (centeredIndex K i : ℂ))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Complex.reCLM_apply, pow_one] using
      re_cubicOuterVanishing_summand K i
  intro hzero
  have hz : (∑ i : Fin (2 * K + 1), cubicOuterMomentTerm K i) = 0 := by
    rw [← hre, hzero]
    simp
  exact (ne_of_lt hsum) hz

/-- The residual between `d^3` and its odd constrained projection lies in the
exact odd normal line `span{d}`. -/
theorem cubicProjectionResidual_mem_oddNormalSubspace
    (K : ℕ) :
    centeredPowerVector K 3 -
        ((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
          EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
      oddNormalSubspace K := by
  let V := euclideanOddBoundaryFlatSubspace K
  have horth :
      centeredPowerVector K 3 - V.starProjection (centeredPowerVector K 3) ∈
        Vᗮ :=
    V.sub_starProjection_mem_orthogonal (centeredPowerVector K 3)
  have horth' :
      centeredPowerVector K 3 -
          ((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
            EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
        (euclideanOddBoundaryFlatSubspace K)ᗮ := by
    simpa [V, oddCubicCompressionVector] using horth
  have hgCoeff :
      ((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
        EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
      euclideanOddCoefficientSubspace K := by
    exact
      ((mem_euclideanOddBoundaryFlatSubspace_iff K _).mp
        (oddCubicCompressionVector K).property).2
  have hcoeff :
      centeredPowerVector K 3 -
          ((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
            EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
        euclideanOddCoefficientSubspace K :=
    (euclideanOddCoefficientSubspace K).sub_mem
      (centeredPowerVector_three_mem_oddCoefficient K) hgCoeff
  have hi :
      centeredPowerVector K 3 -
          ((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
            EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
        (euclideanOddBoundaryFlatSubspace K)ᗮ ⊓
          euclideanOddCoefficientSubspace K :=
    ⟨horth', hcoeff⟩
  rw [oddBoundaryFlat_normal_eq_oddNormalSubspace K] at hi
  exact hi

/-- For `K>=2`, the odd cubic compression vector has a nonzero right outer
coordinate.  No explicit closed form for the projection coefficient is used. -/
theorem oddCubicCompressionVector_rightOuter_ne_zero
    (K : ℕ) (hK : 2 ≤ K) :
    ((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
      EuclideanSpace ℂ (Fin (2 * K + 1)))
        (Fin.last (2 * K)) ≠ 0 := by
  intro houter
  have hnormal := cubicProjectionResidual_mem_oddNormalSubspace K
  rw [oddNormalSubspace, Submodule.mem_span_singleton] at hnormal
  rcases hnormal with ⟨a, ha⟩
  let ir : Fin (2 * K + 1) := Fin.last (2 * K)
  have hir : centeredIndex K ir = (K : ℤ) := by
    simpa [ir] using centeredIndex_finLast K
  have hcoord := congrArg
    (fun x : EuclideanSpace ℂ (Fin (2 * K + 1)) => x ir) ha
  have houter' :
      ((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
        EuclideanSpace ℂ (Fin (2 * K + 1))) ir = 0 := by
    simpa [ir] using houter
  simp [centeredPowerVector_apply, hir, houter', smul_eq_mul] at hcoord
  have hKneNat : K ≠ 0 := by omega
  have hKne : (K : ℂ) ≠ 0 := by exact_mod_cast hKneNat
  have haK : a = (K : ℂ) ^ 2 := by
    apply (mul_right_cancel₀ hKne)
    simpa [pow_succ, mul_assoc] using hcoord
  rw [haK] at ha
  have hgEq :
      ((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
        EuclideanSpace ℂ (Fin (2 * K + 1))) =
        centeredPowerVector K 3 -
          (K : ℂ) ^ 2 • centeredPowerVector K 1 := by
    apply (eq_sub_iff_add_eq).2
    have hadd := (eq_sub_iff_add_eq).1 ha
    simpa [add_comm] using hadd
  have hgFlat :
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
            EuclideanSpace ℂ (Fin (2 * K + 1)))) ∈
        boundaryFlatSubspace K := by
    exact
      ((mem_euclideanOddBoundaryFlatSubspace_iff K _).mp
        (oddCubicCompressionVector K).property).1
  have hm1 :
      centeredMoment K 1
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
            EuclideanSpace ℂ (Fin (2 * K + 1))))) = 0 :=
    ((mem_boundaryFlatSubspace_iff K _).mp hgFlat).2.1
  have hrawEq :
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
            EuclideanSpace ℂ (Fin (2 * K + 1)))) =
        cubicOuterVanishingRaw K := by
    funext i
    have hcoord' := congrArg
      (fun x : EuclideanSpace ℂ (Fin (2 * K + 1)) => x i) hgEq
    simpa [cubicOuterVanishingRaw, centeredPowerVector_apply, smul_eq_mul] using hcoord'
  rw [hrawEq] at hm1
  exact centeredMoment_one_cubicOuterVanishingRaw_ne_zero K hK hm1

/-- At successor size `N+1`, the odd cubic generator cannot be inherited from
the centered predecessor image. -/
theorem oddCubicCompressionVector_not_mem_intrinsicPredecessor
    (N : ℕ) (hN : 1 ≤ N) :
    (oddCubicCompressionVector (N + 1) :
      euclideanParityBoundaryFlatSubspace .odd (N + 1)) ∉
        intrinsicParityPredecessorSubspace .odd N := by
  intro hmem
  have hzero := intrinsicPredecessor_rightOuter_eq_zero
    .odd N
    (oddCubicCompressionVector (N + 1) :
      euclideanParityBoundaryFlatSubspace .odd (N + 1)) hmem
  have hne := oddCubicCompressionVector_rightOuter_ne_zero
    (N + 1) (by omega)
  apply hne
  simpa [successorRightOuterIndex] using hzero

/-- Exact Euclidean D/N-flow compatibility: centered-index action commutes
with centered zero extension. -/
theorem euclideanIndexLinearMap_centeredZeroExtend
    {N M : ℕ} (hNM : N ≤ M)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    euclideanIndexLinearMap M (euclideanCenteredZeroExtend hNM x) =
      euclideanCenteredZeroExtend hNM (euclideanIndexLinearMap N x) := by
  apply (EuclideanSpace.equiv (Fin (2 * M + 1)) ℂ).injective
  rw [euclideanIndexLinearMap_coordinates,
    euclideanCenteredZeroExtend_coordinates,
    euclideanCenteredZeroExtend_coordinates,
    euclideanIndexLinearMap_coordinates]
  exact indexMatrix_mulVec_centeredZeroExtend hNM
    ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x)

/-- Algebraic D transport sends the native even predecessor image into the
native odd predecessor image.  The theorem is deliberately stated in ambient
Euclidean membership so no parity-subtype coercion is needed at the D API
boundary.  No metric property of D is used. -/
theorem evenIndex_mem_oddIntrinsicPredecessor_of_mem_evenIntrinsicPredecessor
    (N : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace (N + 1))
    (hv :
      (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanParityEmbeddedSuccSubspace .even N) :
    ((euclideanEvenToOddIndexLinearMap (N + 1) v :
        euclideanOddBoundaryFlatSubspace (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanParityEmbeddedSuccSubspace .odd N := by
  rcases hv with ⟨x, hx, hxv⟩
  have hxEven : x ∈ euclideanEvenBoundaryFlatSubspace N := by
    simpa using hx
  let xEven : euclideanEvenBoundaryFlatSubspace N := ⟨x, hxEven⟩
  let yOdd : euclideanOddBoundaryFlatSubspace N :=
    euclideanEvenToOddIndexLinearMap N xEven
  have hyOdd :
      (yOdd : EuclideanSpace ℂ (Fin (2 * N + 1))) ∈
        euclideanParityBoundaryFlatSubspace .odd N := by
    exact yOdd.property
  refine ⟨(yOdd : EuclideanSpace ℂ (Fin (2 * N + 1))), hyOdd, ?_⟩
  rw [coe_euclideanEvenToOddIndexLinearMap]
  rw [coe_euclideanEvenToOddIndexLinearMap]
  rw [← hxv]
  exact (euclideanIndexLinearMap_centeredZeroExtend
    (Nat.le_succ N) x).symm

/-- Cubic generator pulled back algebraically to the even successor carrier.
Unlike the older helper carrying an explicit `2≤K` proof parameter, this
one-step form is proof-term-free at the interface. -/
def successorPulledBackCubicCompressionVector
    (N : ℕ) : euclideanEvenBoundaryFlatSubspace (N + 1) :=
  (euclideanEvenOddBoundaryFlatLinearEquiv (N + 1) (by omega)).symm
    (oddCubicCompressionVector (N + 1))

/-- Applying D to the one-step even pullback recovers the odd cubic generator. -/
theorem evenIndex_successorPulledBackCubicCompressionVector
    (N : ℕ) :
    euclideanEvenToOddIndexLinearMap (N + 1)
        (successorPulledBackCubicCompressionVector N) =
      oddCubicCompressionVector (N + 1) := by
  let E := euclideanEvenOddBoundaryFlatLinearEquiv (N + 1) (by omega)
  change E (E.symm (oddCubicCompressionVector (N + 1))) =
    oddCubicCompressionVector (N + 1)
  exact E.apply_symm_apply _

/-- The algebraically pulled-back even cubic channel is also not inherited from
the centered predecessor. -/
theorem successorPulledBackCubicCompressionVector_not_mem_intrinsicPredecessor
    (N : ℕ) (hN : 1 ≤ N) :
    (successorPulledBackCubicCompressionVector N :
      euclideanParityBoundaryFlatSubspace .even (N + 1)) ∉
        intrinsicParityPredecessorSubspace .even N := by
  intro hmem
  have hmem' := hmem
  change
    ((successorPulledBackCubicCompressionVector N :
        euclideanEvenBoundaryFlatSubspace (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanParityEmbeddedSuccSubspace .even N at hmem'
  have htransport :=
    evenIndex_mem_oddIntrinsicPredecessor_of_mem_evenIntrinsicPredecessor
      N (successorPulledBackCubicCompressionVector N) hmem'
  have hmap := evenIndex_successorPulledBackCubicCompressionVector N
  rw [hmap] at htransport
  apply oddCubicCompressionVector_not_mem_intrinsicPredecessor N hN
  change
    ((oddCubicCompressionVector (N + 1) :
        euclideanOddBoundaryFlatSubspace (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanParityEmbeddedSuccSubspace .odd N
  exact htransport

/-- Parity-uniform cubic vector at a one-step successor.  Odd parity uses the
native cubic generator; even parity uses only the algebraic D-pullback. -/
def successorParityCubicVector
    (p : ReversalParity) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p (N + 1) :=
  match p with
  | .odd => oddCubicCompressionVector (N + 1)
  | .even => successorPulledBackCubicCompressionVector N

/-- The parity-uniform successor cubic vector is not inherited from the
centered predecessor. -/
theorem successorParityCubicVector_not_mem_intrinsicPredecessor
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    successorParityCubicVector p N ∉
      intrinsicParityPredecessorSubspace p N := by
  cases p with
  | odd =>
      exact oddCubicCompressionVector_not_mem_intrinsicPredecessor N hN
  | even =>
      exact successorPulledBackCubicCompressionVector_not_mem_intrinsicPredecessor
        N hN

/-- Canonical shell coordinate of the parity-uniform cubic channel. -/
def intrinsicCubicShellPart
    (p : ReversalParity) (N : ℕ) : intrinsicParitySuccShell p N :=
  intrinsicShellPart p N (successorParityCubicVector p N)

/-- E1 endpoint: for every nontrivial predecessor size, the canonical cubic
channel has a genuinely nonzero coordinate in the one-dimensional intrinsic
N-flow shell. -/
theorem intrinsicCubicShellPart_ne_zero
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    intrinsicCubicShellPart p N ≠ 0 := by
  intro hzero
  apply successorParityCubicVector_not_mem_intrinsicPredecessor p N hN
  exact (intrinsicShellPart_eq_zero_iff p N).mp hzero

end Zeta23.CCM

#print axioms Zeta23.CCM.oddCubicCompressionVector_rightOuter_ne_zero
#print axioms Zeta23.CCM.oddCubicCompressionVector_not_mem_intrinsicPredecessor
#print axioms Zeta23.CCM.successorPulledBackCubicCompressionVector_not_mem_intrinsicPredecessor
#print axioms Zeta23.CCM.intrinsicCubicShellPart_ne_zero
