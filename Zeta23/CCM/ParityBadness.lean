import Zeta23.CCM.ConstrainedParityGeometry
import Mathlib.Data.Nat.Find

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Parity-resolved badness and one-dimensional successor shells

This module packages the exact even/odd constrained sectors behind a single
parity index, proves parity-resolved persistence under centered N-flow, defines
least bad sizes, and theorem-locks the one-dimensional Euclidean successor
shell implied by the N-1 parity dimension formula.

The badness predicate is deliberately finite and quadratic.  No compressed
operator, eigenvalue, KKT equation, positivity theorem, or RH claim is made.
-/

inductive ReversalParity
| even
| odd
deriving DecidableEq, Repr

def parityBoundaryFlatSubspace
    (p : ReversalParity) (N : ℕ) :
    Submodule ℂ (Fin (2 * N + 1) → ℂ) :=
  match p with
  | .even => evenBoundaryFlatSubspace N
  | .odd => oddBoundaryFlatSubspace N

def euclideanParityBoundaryFlatSubspace
    (p : ReversalParity) (N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 1))) :=
  match p with
  | .even => euclideanEvenBoundaryFlatSubspace N
  | .odd => euclideanOddBoundaryFlatSubspace N

@[simp] theorem parityBoundaryFlatSubspace_even
    (N : ℕ) :
    parityBoundaryFlatSubspace .even N = evenBoundaryFlatSubspace N := rfl

@[simp] theorem parityBoundaryFlatSubspace_odd
    (N : ℕ) :
    parityBoundaryFlatSubspace .odd N = oddBoundaryFlatSubspace N := rfl

@[simp] theorem euclideanParityBoundaryFlatSubspace_even
    (N : ℕ) :
    euclideanParityBoundaryFlatSubspace .even N =
      euclideanEvenBoundaryFlatSubspace N := rfl

@[simp] theorem euclideanParityBoundaryFlatSubspace_odd
    (N : ℕ) :
    euclideanParityBoundaryFlatSubspace .odd N =
      euclideanOddBoundaryFlatSubspace N := rfl

theorem finrank_parityBoundaryFlatSubspace
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (parityBoundaryFlatSubspace p N) = N - 1 := by
  cases p with
  | even => exact finrank_evenBoundaryFlatSubspace N hN
  | odd => exact finrank_oddBoundaryFlatSubspace N hN

theorem finrank_euclideanParityBoundaryFlatSubspace
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (euclideanParityBoundaryFlatSubspace p N) = N - 1 := by
  cases p with
  | even => exact finrank_euclideanEvenBoundaryFlatSubspace N hN
  | odd => exact finrank_euclideanOddBoundaryFlatSubspace N hN

theorem centeredZeroExtend_mem_parityBoundaryFlatSubspace
    (p : ReversalParity)
    {N M : ℕ} (hNM : N ≤ M)
    {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ parityBoundaryFlatSubspace p N) :
    centeredZeroExtend hNM u ∈ parityBoundaryFlatSubspace p M := by
  cases p with
  | even =>
      rcases hu with ⟨hflat, heven⟩
      refine ⟨centeredZeroExtend_mem_boundaryFlatSubspace hNM hflat, ?_⟩
      have heven' : reverseCoefficients N u = u :=
        (mem_evenCoefficientSubspace_iff N u).1 heven
      apply (mem_evenCoefficientSubspace_iff M _).2
      rw [← centeredZeroExtend_reverseCoefficients hNM, heven']
  | odd =>
      rcases hu with ⟨hflat, hodd⟩
      refine ⟨centeredZeroExtend_mem_boundaryFlatSubspace hNM hflat, ?_⟩
      have hodd' : reverseCoefficients N u = -u :=
        (mem_oddCoefficientSubspace_iff N u).1 hodd
      apply (mem_oddCoefficientSubspace_iff M _).2
      rw [← centeredZeroExtend_reverseCoefficients hNM, hodd']
      change centeredZeroExtendLinearMap hNM (-u) =
        -centeredZeroExtendLinearMap hNM u
      exact (centeredZeroExtendLinearMap hNM).map_neg u

theorem euclideanCenteredZeroExtend_mem_euclideanParityBoundaryFlatSubspace
    (p : ReversalParity)
    {N M : ℕ} (hNM : N ≤ M)
    {x : EuclideanSpace ℂ (Fin (2 * N + 1))}
    (hx : x ∈ euclideanParityBoundaryFlatSubspace p N) :
    euclideanCenteredZeroExtend hNM x ∈
      euclideanParityBoundaryFlatSubspace p M := by
  cases p with
  | even =>
      exact euclideanCenteredZeroExtend_mem_euclideanEvenBoundaryFlatSubspace
        hNM hx
  | odd =>
      exact euclideanCenteredZeroExtend_mem_euclideanOddBoundaryFlatSubspace
        hNM hx

theorem centeredZeroExtend_ne_zero
    {N M : ℕ} (hNM : N ≤ M)
    {u : Fin (2 * N + 1) → ℂ}
    (hu : u ≠ 0) :
    centeredZeroExtend hNM u ≠ 0 := by
  intro hz
  apply hu
  funext i
  have hi := congrFun hz (centeredEmbedding N M hNM i)
  simpa using hi


/-- The centered-index operator commutes exactly with centered zero extension.
This is the raw D/N-flow compatibility needed to make the #103 parity
equivalence coherent across truncation sizes. -/
theorem indexMatrix_mulVec_centeredZeroExtend
    {N M : ℕ} (hNM : N ≤ M)
    (u : Fin (2 * N + 1) → ℂ) :
    indexMatrix M *ᵥ centeredZeroExtend hNM u =
      centeredZeroExtend hNM (indexMatrix N *ᵥ u) := by
  ext j
  rw [indexMatrix_mulVec_apply]
  by_cases hj : j ∈ Set.range (centeredEmbedding N M hNM)
  · obtain ⟨i, rfl⟩ := hj
    rw [centeredZeroExtend_apply_centeredEmbedding]
    rw [centeredZeroExtend_apply_centeredEmbedding]
    rw [indexMatrix_mulVec_apply]
    rw [centeredIndex_centeredEmbedding]
  · rw [centeredZeroExtend_apply_of_not_mem_range hNM u j hj]
    rw [centeredZeroExtend_apply_of_not_mem_range
      hNM (indexMatrix N *ᵥ u) j hj]
    simp

/-- The canonical quadratic form is invariant under simultaneous coefficient
reversal.  This is the scalar quadratic counterpart of the #102 matrix-action
reversal theorem. -/
theorem quadraticForm_canonicalSourceMatrix_reverseCoefficients
    (L : ℝ) (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    quadraticForm (canonicalSourceMatrix L N) (reverseCoefficients N u) =
      quadraticForm (canonicalSourceMatrix L N) u := by
  unfold quadraticForm
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [reverseCoefficients]

/-- Algebraic parallelogram identity for the project's sesquilinear quadratic
form.  No Hermitianity hypothesis is needed. -/
theorem quadraticForm_add_add_sub
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ)
    (u v : ι → ℂ) :
    quadraticForm A (u + v) + quadraticForm A (u - v) =
      2 * quadraticForm A u + 2 * quadraticForm A v := by
  unfold quadraticForm
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.add_apply, Pi.sub_apply, map_add, map_sub, starRingEnd_apply]
  ring

/-- Exact even/odd energy splitting for the canonical quadratic form. -/
theorem quadraticForm_evenPart_add_oddPart
    (L : ℝ) (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    quadraticForm (canonicalSourceMatrix L N) (evenPart N u) +
        quadraticForm (canonicalSourceMatrix L N) (oddPart N u) =
      quadraticForm (canonicalSourceMatrix L N) u := by
  have heven :
      evenPart N u =
        (1 / 2 : ℂ) • (u + reverseCoefficients N u) := by
    ext i
    simp [evenPart, reverseCoefficients, Pi.smul_apply, smul_eq_mul]
  have hodd :
      oddPart N u =
        (1 / 2 : ℂ) • (u - reverseCoefficients N u) := by
    ext i
    simp [oddPart, reverseCoefficients, Pi.smul_apply, smul_eq_mul]
  rw [heven, hodd]
  rw [quadraticForm_smul, quadraticForm_smul]
  have hpar :=
    quadraticForm_add_add_sub
      (canonicalSourceMatrix L N) u (reverseCoefficients N u)
  rw [quadraticForm_canonicalSourceMatrix_reverseCoefficients L N u] at hpar
  norm_num at hpar ⊢
  linear_combination (1 / 4 : ℂ) * hpar

/-- Any negative boundary-flat canonical witness has a negative component in
one of the two exact reversal parity sectors. -/
theorem parityBad_even_or_odd_of_negative
    {L : ℝ} {N : ℕ}
    {u : Fin (2 * N + 1) → ℂ}
    (hmem : u ∈ boundaryFlatSubspace N)
    (hneg : (quadraticForm (canonicalSourceMatrix L N) u).re < 0) :
    ParityBad .even L N ∨ ParityBad .odd L N := by
  have hsplit :=
    congrArg Complex.re
      (quadraticForm_evenPart_add_oddPart L N u)
  have hsplitRe :
      (quadraticForm (canonicalSourceMatrix L N) (evenPart N u)).re +
          (quadraticForm (canonicalSourceMatrix L N) (oddPart N u)).re =
        (quadraticForm (canonicalSourceMatrix L N) u).re := by
    simpa only [Complex.add_re] using hsplit
  by_cases hevenneg :
      (quadraticForm (canonicalSourceMatrix L N) (evenPart N u)).re < 0
  · left
    have hene : evenPart N u ≠ 0 := by
      intro hz
      rw [hz, quadraticForm_zero] at hevenneg
      norm_num at hevenneg
    exact ⟨evenPart N u, hene,
      evenPart_mem_evenBoundaryFlatSubspace hmem, hevenneg⟩
  · right
    have hevennonneg :
        0 ≤ (quadraticForm
          (canonicalSourceMatrix L N) (evenPart N u)).re :=
      le_of_not_gt hevenneg
    have hoddneg :
        (quadraticForm (canonicalSourceMatrix L N) (oddPart N u)).re < 0 := by
      linarith
    have hone : oddPart N u ≠ 0 := by
      intro hz
      rw [hz, quadraticForm_zero] at hoddneg
      norm_num at hoddneg
    exact ⟨oddPart N u, hone,
      oddPart_mem_oddBoundaryFlatSubspace hmem, hoddneg⟩

/-- A negative canonical quadratic direction in one fixed parity sector. -/
def ParityBad
    (p : ReversalParity) (L : ℝ) (N : ℕ) : Prop :=
  ∃ u : Fin (2 * N + 1) → ℂ,
    u ≠ 0 ∧
    u ∈ parityBoundaryFlatSubspace p N ∧
    (quadraticForm (canonicalSourceMatrix L N) u).re < 0


/-- A nonzero vector in a parity-constrained sector cannot occur at N=0. -/
theorem one_le_of_ne_zero_mem_parityBoundaryFlatSubspace
    (p : ReversalParity)
    {N : ℕ}
    {u : Fin (2 * N + 1) → ℂ}
    (hne : u ≠ 0)
    (hmem : u ∈ parityBoundaryFlatSubspace p N) :
    1 ≤ N := by
  by_contra hN
  have hN0 : N = 0 := by omega
  subst N
  have hflat : u ∈ boundaryFlatSubspace 0 := by
    cases p with
    | even => exact hmem.1
    | odd => exact hmem.1
  have hmoment0 :=
    ((mem_boundaryFlatSubspace_iff 0 u).mp hflat).1
  apply hne
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simpa [centeredMoment] using hmoment0

/-- Every parity-bad finite problem occurs at size N>=2. -/
theorem two_le_of_parityBad
    {p : ReversalParity} {L : ℝ} {N : ℕ}
    (hbad : ParityBad p L N) :
    2 ≤ N := by
  obtain ⟨u, hne, hmem, hneg⟩ := hbad
  have hN1 :=
    one_le_of_ne_zero_mem_parityBoundaryFlatSubspace p hne hmem
  have hflat : u ∈ boundaryFlatSubspace N := by
    cases p with
    | even => exact hmem.1
    | odd => exact hmem.1
  exact two_le_of_ne_zero_mem_boundaryFlatSubspace hN1 hflat hne

/-- Parity-resolved finite badness is upward closed under the exact centered
N-flow at fixed positive aperture. -/
theorem parityBad_persists_of_le
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hNM : N ≤ M)
    (hbad : ParityBad p L N) :
    ParityBad p L M := by
  obtain ⟨u, hune, humem, huneg⟩ := hbad
  refine ⟨centeredZeroExtend hNM u,
    centeredZeroExtend_ne_zero hNM hune,
    centeredZeroExtend_mem_parityBoundaryFlatSubspace p hNM humem, ?_⟩
  rw [quadraticForm_canonicalSourceMatrix_centeredZeroExtend hL hNM u]
  exact huneg

/-- Every nonempty parity-bad size set has a least bad size. -/
theorem exists_least_parityBad
    (p : ReversalParity) (L : ℝ)
    (hex : ∃ N : ℕ, ParityBad p L N) :
    ∃ Nstar : ℕ,
      ParityBad p L Nstar ∧
      ∀ N : ℕ, N < Nstar → ¬ ParityBad p L N := by
  classical
  let Nstar := Nat.find hex
  refine ⟨Nstar, Nat.find_spec hex, ?_⟩
  intro N hN
  exact Nat.find_min hex hN


/-- A nonempty parity-bad size set has a least bad size, and that least size is
automatically at least two. -/
theorem exists_least_parityBad_two_le
    (p : ReversalParity) (L : ℝ)
    (hex : ∃ N : ℕ, ParityBad p L N) :
    ∃ Nstar : ℕ,
      2 ≤ Nstar ∧
      ParityBad p L Nstar ∧
      ∀ N : ℕ, N < Nstar → ¬ ParityBad p L N := by
  obtain ⟨Nstar, hbad, hmin⟩ := exists_least_parityBad p L hex
  exact ⟨Nstar, two_le_of_parityBad hbad, hbad, hmin⟩

/-- At a least bad size, every smaller parity sector is nonnegative. -/
theorem nonnegative_of_lt_least_parityBad
    (p : ReversalParity) (L : ℝ)
    {Nstar : ℕ}
    (hmin : ∀ N : ℕ, N < Nstar → ¬ ParityBad p L N)
    {N : ℕ} (hN : N < Nstar)
    (u : Fin (2 * N + 1) → ℂ)
    (humem : u ∈ parityBoundaryFlatSubspace p N) :
    0 ≤ (quadraticForm (canonicalSourceMatrix L N) u).re := by
  by_contra hnonneg
  have hneg : (quadraticForm (canonicalSourceMatrix L N) u).re < 0 :=
    lt_of_not_ge hnonneg
  have hune : u ≠ 0 := by
    intro hu
    subst u
    simpa using hneg
  exact (hmin N hN) ⟨u, hune, humem, hneg⟩

/-- Image of the previous Euclidean parity sector inside the successor size. -/
def euclideanParityEmbeddedSuccSubspace
    (p : ReversalParity) (N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) :=
  (euclideanParityBoundaryFlatSubspace p N).map
    (euclideanCenteredZeroExtend (Nat.le_succ N)).toLinearMap

theorem euclideanParityEmbeddedSuccSubspace_le
    (p : ReversalParity) (N : ℕ) :
    euclideanParityEmbeddedSuccSubspace p N ≤
      euclideanParityBoundaryFlatSubspace p (N + 1) := by
  rintro y ⟨x, hx, rfl⟩
  exact euclideanCenteredZeroExtend_mem_euclideanParityBoundaryFlatSubspace
    p (Nat.le_succ N) hx

theorem finrank_euclideanParityEmbeddedSuccSubspace
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (euclideanParityEmbeddedSuccSubspace p N) = N - 1 := by
  let f :=
    (euclideanCenteredZeroExtend (Nat.le_succ N)).toLinearMap
  have he :=
    Submodule.equivMapOfInjective
      f (euclideanCenteredZeroExtend (Nat.le_succ N)).injective
      (euclideanParityBoundaryFlatSubspace p N)
  change
    Module.finrank ℂ
      ((euclideanParityBoundaryFlatSubspace p N).map f) = N - 1
  rw [← he.finrank_eq]
  exact finrank_euclideanParityBoundaryFlatSubspace p N hN

/-- One new orthogonal direction in a fixed parity sector when N increases by
one. -/
def euclideanParitySuccShell
    (p : ReversalParity) (N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) :=
  (euclideanParityEmbeddedSuccSubspace p N)ᗮ ⊓
    euclideanParityBoundaryFlatSubspace p (N + 1)

/-- Exact one-dimensional successor shell in each parity sector. -/
theorem finrank_euclideanParitySuccShell
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (euclideanParitySuccShell p N) = 1 := by
  have hle := euclideanParityEmbeddedSuccSubspace_le p N
  have hdim :=
    Submodule.finrank_add_inf_finrank_orthogonal hle
  rw [finrank_euclideanParityEmbeddedSuccSubspace p N hN,
    finrank_euclideanParityBoundaryFlatSubspace p (N + 1) (by omega)] at hdim
  change
    N - 1 + Module.finrank ℂ (euclideanParitySuccShell p N) =
      N + 1 - 1 at hdim
  omega

end Zeta23.CCM

#print axioms Zeta23.CCM.indexMatrix_mulVec_centeredZeroExtend
#print axioms Zeta23.CCM.quadraticForm_canonicalSourceMatrix_reverseCoefficients
#print axioms Zeta23.CCM.quadraticForm_add_add_sub
#print axioms Zeta23.CCM.quadraticForm_evenPart_add_oddPart
#print axioms Zeta23.CCM.parityBad_even_or_odd_of_negative
#print axioms Zeta23.CCM.two_le_of_parityBad
#print axioms Zeta23.CCM.finrank_parityBoundaryFlatSubspace
#print axioms Zeta23.CCM.parityBad_persists_of_le
#print axioms Zeta23.CCM.exists_least_parityBad
#print axioms Zeta23.CCM.nonnegative_of_lt_least_parityBad
#print axioms Zeta23.CCM.finrank_euclideanParitySuccShell
