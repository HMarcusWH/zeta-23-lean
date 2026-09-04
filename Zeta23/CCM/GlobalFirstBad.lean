import Zeta23.CCM.ParityBadness

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-D1: global parity badness

PR #105 introduced least badness after fixing one reversal parity.  PR #110
then linked the even and odd compressed operators at the same finite size.
For that comparison the more useful minimum is the first size at which either
parity is bad.

At a least global bad size, both parity sectors at every smaller size are
nonnegative.  No spectral comparison, Schur/Feshbach formula, positivity
result, finite-to-infinite theorem, or RH theorem is claimed here.
-/

/-- A finite canonical problem is globally parity-bad when at least one exact
reversal parity sector contains a strictly negative constrained direction. -/
def AnyParityBad (L : ℝ) (N : ℕ) : Prop :=
  ParityBad .even L N ∨ ParityBad .odd L N

/-- Any negative boundary-flat canonical direction makes the corresponding
finite problem globally parity-bad. -/
theorem anyParityBad_of_negative
    {L : ℝ} {N : ℕ}
    {u : Fin (2 * N + 1) → ℂ}
    (hmem : u ∈ boundaryFlatSubspace N)
    (hneg : (quadraticForm (canonicalSourceMatrix L N) u).re < 0) :
    AnyParityBad L N :=
  parityBad_even_or_odd_of_negative hmem hneg

/-- Global parity badness persists under the exact centered N-flow. -/
theorem anyParityBad_persists_of_le
    {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hNM : N ≤ M)
    (hbad : AnyParityBad L N) :
    AnyParityBad L M := by
  rcases hbad with heven | hodd
  · exact Or.inl (parityBad_persists_of_le .even hL hNM heven)
  · exact Or.inr (parityBad_persists_of_le .odd hL hNM hodd)

/-- Every globally bad finite problem occurs at size at least two. -/
theorem two_le_of_anyParityBad
    {L : ℝ} {N : ℕ}
    (hbad : AnyParityBad L N) :
    2 ≤ N := by
  rcases hbad with heven | hodd
  · exact two_le_of_parityBad heven
  · exact two_le_of_parityBad hodd

/-- Every nonempty globally-bad size set has a least bad size, automatically
at least two. -/
theorem exists_least_anyParityBad_two_le
    (L : ℝ)
    (hex : ∃ N : ℕ, AnyParityBad L N) :
    ∃ Nstar : ℕ,
      2 ≤ Nstar ∧
      AnyParityBad L Nstar ∧
      ∀ N : ℕ, N < Nstar → ¬ AnyParityBad L N := by
  classical
  let Nstar := Nat.find hex
  have hbad : AnyParityBad L Nstar := Nat.find_spec hex
  exact ⟨Nstar, two_le_of_anyParityBad hbad, hbad,
    fun N hN => Nat.find_min hex hN⟩

/-- At a least globally-bad size, each chosen parity sector at every smaller
size is nonnegative. -/
theorem parity_nonnegative_of_lt_least_anyParityBad
    (L : ℝ)
    {Nstar : ℕ}
    (hmin : ∀ N : ℕ, N < Nstar → ¬ AnyParityBad L N)
    (p : ReversalParity)
    {N : ℕ} (hN : N < Nstar)
    (u : Fin (2 * N + 1) → ℂ)
    (humem : u ∈ parityBoundaryFlatSubspace p N) :
    0 ≤ (quadraticForm (canonicalSourceMatrix L N) u).re := by
  by_contra hnonneg
  have hneg :
      (quadraticForm (canonicalSourceMatrix L N) u).re < 0 :=
    lt_of_not_ge hnonneg
  have hune : u ≠ 0 := by
    intro hu
    subst u
    simpa using hneg
  have hpbad : ParityBad p L N := ⟨u, hune, humem, hneg⟩
  apply hmin N hN
  cases p with
  | even => exact Or.inl hpbad
  | odd => exact Or.inr hpbad

/-- Euclidean form of global-minimality nonnegativity.  In particular, at the
predecessor of a first globally-bad size this applies to both parities. -/
theorem euclideanParity_nonnegative_of_lt_least_anyParityBad
    (L : ℝ)
    {Nstar : ℕ}
    (hmin : ∀ N : ℕ, N < Nstar → ¬ AnyParityBad L N)
    (p : ReversalParity)
    {N : ℕ} (hN : N < Nstar)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1)))
    (hx : x ∈ euclideanParityBoundaryFlatSubspace p N) :
    0 ≤ Complex.re
      (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x) := by
  have hxraw :
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x ∈
        parityBoundaryFlatSubspace p N := by
    cases p with
    | even =>
        exact (mem_euclideanEvenBoundaryFlatSubspace_iff N x).mp hx
    | odd =>
        exact (mem_euclideanOddBoundaryFlatSubspace_iff N x).mp hx
  have hraw :=
    parity_nonnegative_of_lt_least_anyParityBad
      L hmin p hN
      ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x) hxraw
  simpa only [quadraticForm_re_eq_re_inner_apply_self] using hraw

end Zeta23.CCM

#print axioms Zeta23.CCM.anyParityBad_of_negative
#print axioms Zeta23.CCM.anyParityBad_persists_of_le
#print axioms Zeta23.CCM.exists_least_anyParityBad_two_le
#print axioms Zeta23.CCM.parity_nonnegative_of_lt_least_anyParityBad
#print axioms Zeta23.CCM.euclideanParity_nonnegative_of_lt_least_anyParityBad
