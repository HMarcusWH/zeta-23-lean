import Zeta23.CCM.CanonicalSourceMomentAtoms
import Zeta23.CCM.FirstBadShiftedSchur
import Zeta23.CCM.SourceNormalizationRepair
import Mathlib.LinearAlgebra.Determinant

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# FIRST-BAD-RIGIDITY-E4-A4R0: canonical aperture regularity scaffold

This module theorem-locks the algebraic interfaces needed by the regular-
aperture route before any complex analytic continuation is attempted.

It deliberately separates four facts:

* regularity means nonzero determinant of the actual projected predecessor
  block `A = P_W T|_W`;
* finite-dimensional determinant nonvanishing is exactly injectivity and gives
  a unique zero-shift preimage;
* the finite prime channel can be frozen at a prescribed cutoff, and a source
  atom enters with zero matrix value at its logarithmic threshold;
* the explicit scalar correction contains an exact `-log L` contribution on
  the positive real aperture axis.

No holomorphic extension, periodic log lift, dense regularity theorem,
successor positivity, or RH theorem is claimed.
-/

/-- Determinant of the actual intrinsic predecessor block used by the Schur
machinery. -/
noncomputable def intrinsicPredecessorDet
    (p : ReversalParity) (L : ℝ) (N : ℕ) : ℂ :=
  LinearMap.det (intrinsicPredecessorBlock p L N)

/-- A predecessor block is regular exactly when its determinant is nonzero. -/
def IntrinsicPredecessorRegular
    (p : ReversalParity) (L : ℝ) (N : ℕ) : Prop :=
  intrinsicPredecessorDet p L N ≠ 0

/-- Determinant nonvanishing is exactly injectivity of the finite-dimensional
projected predecessor block. -/
theorem intrinsicPredecessorRegular_iff_injective
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    IntrinsicPredecessorRegular p L N ↔
      Function.Injective (intrinsicPredecessorBlock p L N) := by
  constructor
  · intro hdet
    have hker : LinearMap.ker (intrinsicPredecessorBlock p L N) = ⊥ := by
      by_contra hne
      apply hdet
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot).2 hne
    exact LinearMap.ker_eq_bot.mp hker
  · intro hinj
    intro hzero
    have hker : LinearMap.ker (intrinsicPredecessorBlock p L N) ≠ ⊥ :=
      (LinearMap.det_eq_zero_iff_ker_ne_bot).1 hzero
    exact hker (LinearMap.ker_eq_bot.mpr hinj)

/-- On a regular predecessor block, every target has one and only one preimage.
This is the zero-shift algebra needed later without introducing a bespoke
inverse definition. -/
theorem existsUnique_intrinsicPredecessorBlock_preimage_of_regular
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N)
    (b : intrinsicParityPredecessorSubspace p N) :
    ∃! x : intrinsicParityPredecessorSubspace p N,
      intrinsicPredecessorBlock p L N x = b := by
  have hinj : Function.Injective (intrinsicPredecessorBlock p L N) :=
    (intrinsicPredecessorRegular_iff_injective p L N).1 hreg
  have hsurj : Function.Surjective (intrinsicPredecessorBlock p L N) :=
    (LinearMap.injective_iff_surjective).1 hinj
  obtain ⟨x, hx⟩ := hsurj b
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hinj (hy.trans hx.symm)

/-- In particular the canonical shell coupling has a unique zero-shift
preimage on a regular predecessor block. -/
theorem existsUnique_cubicZeroShiftPreimage_of_regular
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) :
    ∃! x₀ : intrinsicParityPredecessorSubspace p N,
      intrinsicPredecessorBlock p L N x₀ =
        intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N) := by
  exact existsUnique_intrinsicPredecessorBlock_preimage_of_regular
    p L N hreg
      (intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N))

/-- Prime channel with a frozen finite cutoff.  This is the physical source
family on one cutoff cell before restoring `floor (exp L)`. -/
def frozenCanonicalPrimeMatrix
    (Q : ℕ) (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  ∑ q ∈ Finset.Icc 2 Q,
    primeSourceWeight q • sourceMatrix (primeSourceCoordinate q L) K

/-- On a cell where the physical prime cutoff equals `Q`, the frozen and
production prime matrices are definitionally the same finite source sum. -/
theorem frozenCanonicalPrimeMatrix_eq_canonicalPrimeMatrix
    {Q : ℕ} (L : ℝ) (K : ℕ)
    (hQ : ⌊Real.exp L⌋₊ = Q) :
    frozenCanonicalPrimeMatrix Q L K = canonicalPrimeMatrix L K := by
  rw [canonicalPrimeMatrix_eq_sum_sourceMatrix, hQ]
  rfl

/-- At its logarithmic entry threshold, a prime-power source coordinate is
exactly the zero endpoint of the elementary source family. -/
theorem primeSourceCoordinate_log_self
    (q : ℕ) (hq : 2 ≤ q) :
    primeSourceCoordinate q (Real.log q) = 0 := by
  unfold primeSourceCoordinate
  have hq1Nat : 1 < q := by omega
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1Nat
  have hlog : Real.log (q : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hq1)
  rw [div_self hlog]
  ring

/-- Consequently the full elementary source matrix vanishes exactly when that
atom enters the finite physical cutoff. -/
theorem sourceMatrix_primeSourceCoordinate_log_self
    (q K : ℕ) (hq : 2 ≤ q) :
    sourceMatrix (primeSourceCoordinate q (Real.log q)) K = 0 := by
  rw [primeSourceCoordinate_log_self q hq, sourceMatrix_zero]

/-- Regular real-aperture remainder after extracting the explicit `-log L`
part of the scalar archimedean correction. -/
def canonicalApertureScalarRemainder (L : ℝ) : ℝ :=
  Real.log (L * ((Real.exp L + 1) / (Real.exp L - 1))) -
    (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))

/-- Exact real-axis scalar extraction.  This theorem does not assert any
complex analytic continuation of the remainder. -/
theorem neg_two_wCorrection_eq_neg_log_add_remainder
    {L : ℝ} (hL : 0 < L) :
    -2 * wCorrection L =
      -Real.log L + canonicalApertureScalarRemainder L := by
  have hExp : 1 < Real.exp L := Real.one_lt_exp_iff.mpr hL
  have hnum : Real.exp L + 1 ≠ 0 := by positivity
  have hden : Real.exp L - 1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hExp)
  have hratio : (Real.exp L + 1) / (Real.exp L - 1) ≠ 0 :=
    div_ne_zero hnum hden
  unfold wCorrection canonicalApertureScalarRemainder
  rw [Real.log_mul hL.ne' hratio]
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.intrinsicPredecessorRegular_iff_injective
#print axioms Zeta23.CCM.existsUnique_cubicZeroShiftPreimage_of_regular
#print axioms Zeta23.CCM.frozenCanonicalPrimeMatrix_eq_canonicalPrimeMatrix
#print axioms Zeta23.CCM.sourceMatrix_primeSourceCoordinate_log_self
#print axioms Zeta23.CCM.neg_two_wCorrection_eq_neg_log_add_remainder
