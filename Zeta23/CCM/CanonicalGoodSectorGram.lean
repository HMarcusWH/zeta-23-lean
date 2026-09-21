import Zeta23.CCM.GoodSectorKernelAnnihilation
import Zeta23.CCM.CanonicalOneStepDomination

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: good-sector Gram control

This module extracts the two-vector Gram consequence of parity-sector goodness.

For the parity-compressed canonical operator `T`, define

  E(x) = Re <T x,x>,
  B(x,y) = <x,T y>.

On a good parity sector, `E` is nonnegative on every vector.  Symmetry of
`T` makes `B` Hermitian.  A completion-of-square argument, with the
zero-energy case discharged by the already-proved good-sector kernel
annihilation theorem, gives

  |B(x,y)|^2 <= E(x) E(y).

Specializing to the intrinsic predecessor direction and canonical cubic shell
proves nonnegativity of the existing one-step determinant and therefore the
existing `canonicalOneStepDomination` proposition.

Firewall: this does not provide independent arithmetic information beyond
`¬ ParityBad`; it records a structural consequence of sector goodness.  No
bad branch is excluded and no RH claim is made.
-/

/-- The canonical source pairing is Hermitian in the project orientation. -/
theorem star_parityCanonicalSourcePairing_eq_swap
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (x y : euclideanParityBoundaryFlatSubspace p K) :
    star (parityCanonicalSourcePairing p L K x y) =
      parityCanonicalSourcePairing p L K y x := by
  unfold parityCanonicalSourcePairing
  calc
    star (inner ℂ x (parityCompressedCanonical p L K y)) =
        inner ℂ (parityCompressedCanonical p L K y) x := by
          simp
    _ = inner ℂ y (parityCompressedCanonical p L K x) := by
          exact parityCompressedCanonical_isSymmetric p L K y x

/-- Exact completion-of-square identity for the canonical two-vector Gram
form.  The coefficient uses the energy of `y`, so the positive-energy case
can be divided without ever dividing by a complex pairing. -/
theorem parityCanonicalSourceEnergy_completion_of_square
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (x y : euclideanParityBoundaryFlatSubspace p K) :
    let Ex := parityCanonicalSourceEnergy p L K x
    let Ey := parityCanonicalSourceEnergy p L K y
    let z := parityCanonicalSourcePairing p L K x y
    parityCanonicalSourceEnergy p L K
        ((Ey : ℂ) • x - star z • y) =
      Ey * (Ex * Ey - ‖z‖ ^ 2) := by
  let T := parityCompressedCanonical p L K
  let Ex := parityCanonicalSourceEnergy p L K x
  let Ey := parityCanonicalSourceEnergy p L K y
  let z := parityCanonicalSourcePairing p L K x y
  dsimp only
  change
    Complex.re
        (inner ℂ
          (T ((Ey : ℂ) • x - star z • y))
          ((Ey : ℂ) • x - star z • y)) =
      Ey * (Ex * Ey - ‖z‖ ^ 2)
  have hxy : inner ℂ (T x) y = z := by
    change
      inner ℂ (parityCompressedCanonical p L K x) y =
        parityCanonicalSourcePairing p L K x y
    rw [parityCompressedCanonical_isSymmetric p L K x y]
    rfl
  have hyx : inner ℂ (T y) x = star z := by
    calc
      inner ℂ (T y) x =
          inner ℂ y (T x) := by
            exact parityCompressedCanonical_isSymmetric p L K y x
      _ = star (inner ℂ (T x) y) := by
            simp
      _ = star z := by rw [hxy]
  have hEx :
      Complex.re (inner ℂ (T x) x) = Ex := by
    rfl
  have hEy :
      Complex.re (inner ℂ (T y) y) = Ey := by
    rfl
  have h11 :
      inner ℂ ((Ey : ℂ) • T x) ((Ey : ℂ) • x) =
        star (Ey : ℂ) * ((Ey : ℂ) * inner ℂ (T x) x) := by
    calc
      inner ℂ ((Ey : ℂ) • T x) ((Ey : ℂ) • x) =
          star (Ey : ℂ) *
            inner ℂ (T x) ((Ey : ℂ) • x) := by
              exact inner_smul_left (𝕜 := ℂ) (T x) ((Ey : ℂ) • x) (r := (Ey : ℂ))
      _ = star (Ey : ℂ) *
          ((Ey : ℂ) * inner ℂ (T x) x) := by
            rw [inner_smul_right (𝕜 := ℂ) (T x) x (r := (Ey : ℂ))]
  have h12 :
      inner ℂ ((Ey : ℂ) • T x) (star z • y) =
        star (Ey : ℂ) * (star z * inner ℂ (T x) y) := by
    calc
      inner ℂ ((Ey : ℂ) • T x) (star z • y) =
          star (Ey : ℂ) * inner ℂ (T x) (star z • y) := by
            exact inner_smul_left (𝕜 := ℂ) (T x) (star z • y) (r := (Ey : ℂ))
      _ = star (Ey : ℂ) * (star z * inner ℂ (T x) y) := by
            rw [inner_smul_right (𝕜 := ℂ) (T x) y (r := star z)]
  have h21 :
      inner ℂ (star z • T y) ((Ey : ℂ) • x) =
        star (star z) * ((Ey : ℂ) * inner ℂ (T y) x) := by
    calc
      inner ℂ (star z • T y) ((Ey : ℂ) • x) =
          star (star z) * inner ℂ (T y) ((Ey : ℂ) • x) := by
            exact inner_smul_left (𝕜 := ℂ) (T y) ((Ey : ℂ) • x) (r := star z)
      _ = star (star z) *
          ((Ey : ℂ) * inner ℂ (T y) x) := by
            rw [inner_smul_right (𝕜 := ℂ) (T y) x (r := (Ey : ℂ))]
  have h22 :
      inner ℂ (star z • T y) (star z • y) =
        star (star z) * (star z * inner ℂ (T y) y) := by
    calc
      inner ℂ (star z • T y) (star z • y) =
          star (star z) * inner ℂ (T y) (star z • y) := by
            exact inner_smul_left (𝕜 := ℂ) (T y) (star z • y) (r := star z)
      _ = star (star z) * (star z * inner ℂ (T y) y) := by
            rw [inner_smul_right (𝕜 := ℂ) (T y) y (r := star z)]
  rw [map_sub, map_smul, map_smul]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  rw [h11, h12, h21, h22, hxy, hyx]
  simp only [map_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.mul_re, starRingEnd_apply, Complex.conj_ofReal, Complex.conj_re,
    Complex.conj_im, star_star, zero_mul, mul_zero, sub_zero, add_zero]
  rw [hEx, hEy, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Cauchy--Schwarz for the canonical pairing on a good parity sector. -/
theorem norm_sq_parityCanonicalSourcePairing_le_mul_energy_of_not_parityBad
    {p : ReversalParity} {L : ℝ} {K : ℕ}
    (hgood : ¬ ParityBad p L K)
    (x y : euclideanParityBoundaryFlatSubspace p K) :
    ‖parityCanonicalSourcePairing p L K x y‖ ^ 2 ≤
      parityCanonicalSourceEnergy p L K x *
        parityCanonicalSourceEnergy p L K y := by
  let Ex := parityCanonicalSourceEnergy p L K x
  let Ey := parityCanonicalSourceEnergy p L K y
  let z := parityCanonicalSourcePairing p L K x y
  change ‖z‖ ^ 2 ≤ Ex * Ey
  have hEx : 0 ≤ Ex := by
    simpa [Ex, parityCanonicalSourceEnergy] using
      re_inner_parityCompressedCanonical_nonnegative_of_not_parityBad hgood x
  have hEy : 0 ≤ Ey := by
    simpa [Ey, parityCanonicalSourceEnergy] using
      re_inner_parityCompressedCanonical_nonnegative_of_not_parityBad hgood y
  by_cases hEy0 : Ey = 0
  · have hTy :
        parityCompressedCanonical p L K y = 0 := by
      apply
        parityCompressedCanonical_eq_zero_of_not_parityBad_of_selfEnergy_eq_zero
          hgood y
      simpa [Ey, parityCanonicalSourceEnergy] using hEy0
    have hz : z = 0 := by
      change inner ℂ x (parityCompressedCanonical p L K y) = 0
      rw [hTy]
      simp
    simp [hz, hEy0]
  · have hEypos : 0 < Ey := lt_of_le_of_ne hEy (Ne.symm hEy0)
    let v : euclideanParityBoundaryFlatSubspace p K :=
      (Ey : ℂ) • x - star z • y
    have hvnonneg :
        0 ≤ parityCanonicalSourceEnergy p L K v := by
      simpa [parityCanonicalSourceEnergy] using
        re_inner_parityCompressedCanonical_nonnegative_of_not_parityBad hgood v
    have hcomp :=
      parityCanonicalSourceEnergy_completion_of_square p L K x y
    change
      parityCanonicalSourceEnergy p L K
          ((Ey : ℂ) • x - star z • y) =
        Ey * (Ex * Ey - ‖z‖ ^ 2) at hcomp
    change
      0 ≤ parityCanonicalSourceEnergy p L K
        ((Ey : ℂ) • x - star z • y) at hvnonneg
    rw [hcomp] at hvnonneg
    have hdiff : 0 ≤ Ex * Ey - ‖z‖ ^ 2 :=
      nonneg_of_mul_nonneg_right hvnonneg hEypos
    exact sub_nonneg.mp hdiff

/-- A good successor sector makes the canonical cubic shell energy
nonnegative. -/
theorem cubicShellRealEnergy_nonnegative_of_not_parityBad
    {p : ReversalParity} {L : ℝ} {N : ℕ}
    (hgood : ¬ ParityBad p L (N + 1)) :
    0 ≤ cubicShellRealEnergy p L N := by
  simpa [cubicShellRealEnergy, parityCanonicalSourceEnergy] using
    re_inner_parityCompressedCanonical_nonnegative_of_not_parityBad
      hgood
      (intrinsicCubicShellPart p N :
        euclideanParityBoundaryFlatSubspace p (N + 1))

/-- The existing denominator-free one-step Gram determinant is nonnegative on
a good successor sector. -/
theorem cubicOneStepDeterminant_nonnegative_of_not_parityBad
    {p : ReversalParity} {L : ℝ} {N : ℕ}
    (hgood : ¬ ParityBad p L (N + 1))
    (w : intrinsicParityPredecessorSubspace p N) :
    0 ≤ cubicOneStepDeterminant p L N w := by
  have hgram :=
    norm_sq_parityCanonicalSourcePairing_le_mul_energy_of_not_parityBad
      hgood
      (w : euclideanParityBoundaryFlatSubspace p (N + 1))
      (intrinsicCubicShellPart p N :
        euclideanParityBoundaryFlatSubspace p (N + 1))
  rw [← cubicShellCoupling_eq_parityCanonicalSourcePairing p L N w] at hgram
  rw [← intrinsicPredecessorRealEnergy_eq_parityCanonicalSourceEnergy p L N w] at hgram
  change
    ‖cubicShellCoupling p L N w‖ ^ 2 ≤
      intrinsicPredecessorRealEnergy p L N w *
        cubicShellRealEnergy p L N at hgram
  unfold cubicOneStepDeterminant
  nlinarith

/-- Sector goodness implies the already-defined one-step domination
certificate.  This is a structural consequence of `¬ ParityBad`, not an
independent arithmetic positivity hypothesis. -/
theorem canonicalOneStepDomination_of_not_parityBad
    {p : ReversalParity} {L : ℝ} {N : ℕ}
    (hgood : ¬ ParityBad p L (N + 1)) :
    canonicalOneStepDomination p L N := by
  refine ⟨cubicShellRealEnergy_nonnegative_of_not_parityBad hgood, ?_⟩
  intro w
  exact cubicOneStepDeterminant_nonnegative_of_not_parityBad hgood w

end Zeta23.CCM

#print axioms Zeta23.CCM.star_parityCanonicalSourcePairing_eq_swap
#print axioms Zeta23.CCM.parityCanonicalSourceEnergy_completion_of_square
#print axioms Zeta23.CCM.norm_sq_parityCanonicalSourcePairing_le_mul_energy_of_not_parityBad
#print axioms Zeta23.CCM.cubicShellRealEnergy_nonnegative_of_not_parityBad
#print axioms Zeta23.CCM.cubicOneStepDeterminant_nonnegative_of_not_parityBad
#print axioms Zeta23.CCM.canonicalOneStepDomination_of_not_parityBad
