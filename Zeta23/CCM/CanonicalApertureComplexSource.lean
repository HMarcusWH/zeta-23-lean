import Zeta23.CCM.CanonicalApertureAnalyticPrimitives
import Zeta23.CCM.CanonicalApertureRegularityScaffold

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ArithmeticFunction

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1b: complex finite source channels

This file complexifies only source channels whose aperture dependence is
already explicit after the prime cutoff is frozen.  Every auxiliary complex
object is theorem-locked back to the exact production real-axis object before
it is used downstream.

No holomorphic determinant, determinant nonidentity, dense regularity,
positivity, negative-root exclusion, or RH claim is made here.
-/

/-- Complex source potential extending the production real source potential. -/
def complexSourcePotential (ω : ℂ) (n : ℤ) : ℂ :=
  Complex.sin (2 * (Real.pi : ℂ) * (n : ℂ) * ω) / (Real.pi : ℂ)

/-- Complex diagonal derivative data extending the production source diagonal. -/
def complexSourceDiagonal (ω : ℂ) (n : ℤ) : ℂ :=
  2 * ω * Complex.cos (2 * (Real.pi : ℂ) * (n : ℂ) * ω)

/-- Complex elementary divided-difference source entry. -/
def complexSourceEntry (ω : ℂ) (n m : ℤ) : ℂ :=
  dividedDifferenceEntry (complexSourcePotential ω) (complexSourceDiagonal ω) n m

/-- Complex elementary source matrix. -/
def complexSourceMatrix (ω : ℂ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  dividedDifferenceMatrix (complexSourcePotential ω) (complexSourceDiagonal ω) N

@[simp] theorem complexSourcePotential_ofReal (ω : ℝ) (n : ℤ) :
    complexSourcePotential (ω : ℂ) n = sourcePotential ω n := by
  unfold complexSourcePotential sourcePotential
  norm_cast

@[simp] theorem complexSourceDiagonal_ofReal (ω : ℝ) (n : ℤ) :
    complexSourceDiagonal (ω : ℂ) n = sourceDiagonal ω n := by
  unfold complexSourceDiagonal sourceDiagonal
  norm_cast

@[simp] theorem complexSourceEntry_ofReal (ω : ℝ) (n m : ℤ) :
    complexSourceEntry (ω : ℂ) n m = sourceEntry ω n m := by
  unfold complexSourceEntry sourceEntry dividedDifferenceEntry
  by_cases hnm : n = m
  · simp [hnm]
  · simp [hnm]

@[simp] theorem complexSourceMatrix_ofReal (ω : ℝ) (N : ℕ) :
    complexSourceMatrix (ω : ℂ) N = sourceMatrix ω N := by
  ext i j
  change complexSourceEntry (ω : ℂ) (centeredIndex N i) (centeredIndex N j) =
    sourceEntry ω (centeredIndex N i) (centeredIndex N j)
  exact complexSourceEntry_ofReal ω _ _

/-- Complex aperture coordinate of one frozen prime-power source atom. -/
def complexPrimeSourceCoordinate (q : ℕ) (z : ℂ) : ℂ :=
  1 - (Real.log q : ℂ) / z

@[simp] theorem complexPrimeSourceCoordinate_ofReal (q : ℕ) (L : ℝ) :
    complexPrimeSourceCoordinate q (L : ℂ) =
      (primeSourceCoordinate q L : ℂ) := by
  unfold complexPrimeSourceCoordinate primeSourceCoordinate
  norm_cast

/-- Frozen complex prime-power matrix.  The finite set is literally `Icc 2 Q`;
there is no complexified floor or moving cutoff. -/
def complexFrozenCanonicalPrimeMatrix
    (Q : ℕ) (z : ℂ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  ∑ q ∈ Finset.Icc 2 Q,
    primeSourceWeight q • complexSourceMatrix (complexPrimeSourceCoordinate q z) K

/-- Exact real-axis agreement of the frozen prime channel. -/
@[simp] theorem complexFrozenCanonicalPrimeMatrix_ofReal
    (Q : ℕ) (L : ℝ) (K : ℕ) :
    complexFrozenCanonicalPrimeMatrix Q (L : ℂ) K =
      frozenCanonicalPrimeMatrix Q L K := by
  classical
  unfold complexFrozenCanonicalPrimeMatrix frozenCanonicalPrimeMatrix
  apply Finset.sum_congr rfl
  intro q hq
  rw [complexPrimeSourceCoordinate_ofReal, complexSourceMatrix_ofReal]

/-- Literal complexification of the production pole entry. -/
def complexPoleComponent (n m : ℤ) (z : ℂ) : ℂ :=
  let κ : ℂ := 16 * (Real.pi : ℂ) ^ 2
  let C : ℂ := 32 * z * Complex.sinh (z / 4) ^ 2
  C * (z ^ 2 - κ * ((m * n : ℤ) : ℂ)) /
    ((z ^ 2 + κ * (m : ℂ) ^ 2) * (z ^ 2 + κ * (n : ℂ) ^ 2))

/-- Exact real-axis agreement of the literal pole continuation. -/
@[simp] theorem complexPoleComponent_ofReal
    (n m : ℤ) (L : ℝ) :
    complexPoleComponent n m (L : ℂ) = (poleComponent n m L : ℂ) := by
  unfold complexPoleComponent poleComponent
  dsimp
  norm_cast

/-- Centered finite complex pole matrix. -/
def complexCanonicalPoleMatrix (z : ℂ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j => complexPoleComponent (centeredIndex K i) (centeredIndex K j) z

/-- Exact real-axis agreement of the finite pole matrix. -/
@[simp] theorem complexCanonicalPoleMatrix_ofReal (L : ℝ) (K : ℕ) :
    complexCanonicalPoleMatrix (L : ℂ) K = canonicalPoleMatrix L K := by
  ext i j
  simp [complexCanonicalPoleMatrix, canonicalPoleMatrix]

end Zeta23.CCM

#print axioms Zeta23.CCM.complexSourceMatrix_ofReal
#print axioms Zeta23.CCM.complexFrozenCanonicalPrimeMatrix_ofReal
#print axioms Zeta23.CCM.complexPoleComponent_ofReal
#print axioms Zeta23.CCM.complexCanonicalPoleMatrix_ofReal