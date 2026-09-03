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

/-- A negative canonical quadratic direction in one fixed parity sector. -/
def ParityBad
    (p : ReversalParity) (L : ℝ) (N : ℕ) : Prop :=
  ∃ u : Fin (2 * N + 1) → ℂ,
    u ≠ 0 ∧
    u ∈ parityBoundaryFlatSubspace p N ∧
    (quadraticForm (canonicalSourceMatrix L N) u).re < 0

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

#print axioms Zeta23.CCM.finrank_parityBoundaryFlatSubspace
#print axioms Zeta23.CCM.parityBad_persists_of_le
#print axioms Zeta23.CCM.exists_least_parityBad
#print axioms Zeta23.CCM.nonnegative_of_lt_least_parityBad
#print axioms Zeta23.CCM.finrank_euclideanParitySuccShell
