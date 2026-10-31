import Zeta23.OPICARound4.NativeSpectralMeasure
import Zeta23.OPICARound4.SignedPickKernel
import Zeta23.OPICARound4.NativeVisibility
import Mathlib.LinearAlgebra.Matrix.Hermitian

noncomputable section

namespace Zeta23.OPICARound4.Validation
open scoped BigOperators Matrix

/-- The nonunitary repeated-eigenvalue control uses the actual transport. -/
def repeatedSpectrumD : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 1]
def repeatedSpectrumDinv : Matrix (Fin 2) (Fin 2) ℂ := !![1, -1; 0, 1]
def repeatedSpectrumA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 2]
def repeatedSpectrumB : Matrix (Fin 2) (Fin 2) ℂ := !![2, 0; 0, 2]
def repeatedSpectrumP₁ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ) / 2, -Complex.I / 2; Complex.I / 2, (1 : ℂ) / 2]
def repeatedSpectrumP₂ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ) / 2, Complex.I / 2; -Complex.I / 2, (1 : ℂ) / 2]

theorem repeated_spectrum_transport_inverse :
    repeatedSpectrumD * repeatedSpectrumDinv = 1 ∧
      repeatedSpectrumDinv * repeatedSpectrumD = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [repeatedSpectrumD, repeatedSpectrumDinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem repeated_spectrum_rank_one :
    repeatedSpectrumB * repeatedSpectrumD - repeatedSpectrumD * repeatedSpectrumA =
      Matrix.vecMulVec (![1, 0] : Fin 2 → ℂ) (![1, 0] : Fin 2 → ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [repeatedSpectrumA, repeatedSpectrumB, repeatedSpectrumD,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec]

/-- The two rank-one orthogonal coordinate projectors sum to the genuine
grouped eigenspace projector of `2 I`. -/
theorem repeated_spectrum_coordinate_projectors :
    repeatedSpectrumP₁ * repeatedSpectrumP₁ = repeatedSpectrumP₁ ∧
    repeatedSpectrumP₂ * repeatedSpectrumP₂ = repeatedSpectrumP₂ ∧
    repeatedSpectrumP₁ * repeatedSpectrumP₂ = 0 ∧
    repeatedSpectrumP₁ + repeatedSpectrumP₂ = 1 := by
  repeat' constructor
  all_goals ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [repeatedSpectrumP₁, repeatedSpectrumP₂, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring_nf <;> norm_num

theorem repeated_spectrum_hermitian_controls :
    repeatedSpectrumA.IsHermitian ∧ repeatedSpectrumB.IsHermitian ∧
      repeatedSpectrumP₁.IsHermitian ∧ repeatedSpectrumP₂.IsHermitian := by
  repeat' constructor
  all_goals ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.conjTranspose, repeatedSpectrumA, repeatedSpectrumB,
      repeatedSpectrumP₁, repeatedSpectrumP₂, map_ofNat, div_eq_mul_inv]

def repeatedSpectrumCoordinateCoefficient (P : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (repeatedSpectrumDinv.mulVec (P.mulVec (![1, 0] : Fin 2 → ℂ))) 0

/-- Coordinate coefficients can be non-real even though their grouped sum
is real. This rules out a basis-coordinate residue-reality assertion. -/
theorem repeated_spectrum_nonreal_coordinates :
    repeatedSpectrumCoordinateCoefficient repeatedSpectrumP₁ = (1 - Complex.I) / 2 ∧
    repeatedSpectrumCoordinateCoefficient repeatedSpectrumP₂ = (1 + Complex.I) / 2 ∧
    (repeatedSpectrumCoordinateCoefficient repeatedSpectrumP₁).im = -1 / 2 ∧
    (repeatedSpectrumCoordinateCoefficient repeatedSpectrumP₂).im = 1 / 2 ∧
    repeatedSpectrumCoordinateCoefficient repeatedSpectrumP₁ +
      repeatedSpectrumCoordinateCoefficient repeatedSpectrumP₂ = 1 := by
  repeat' constructor
  all_goals norm_num [repeatedSpectrumCoordinateCoefficient, repeatedSpectrumDinv,
    repeatedSpectrumP₁, repeatedSpectrumP₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Complex.div_re, Complex.div_im]
  <;> ring

/-- A nonzero source component can have zero residue while the eigenmode
survives on both sides of a nonunitary Hermitian rank-one transport. -/
theorem invisible_shared_mode_control :
    repeatedSpectrumA * repeatedSpectrumD - repeatedSpectrumD * repeatedSpectrumA =
      Matrix.vecMulVec (![1, 0] : Fin 2 → ℂ) (![0, -1] : Fin 2 → ℂ) ∧
    (let P : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0];
      P ≠ 0 ∧ P.mulVec (![1, 0] : Fin 2 → ℂ) ≠ 0 ∧
        -((repeatedSpectrumDinv.mulVec (P.mulVec (![1, 0] : Fin 2 → ℂ))) 1) = 0) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [repeatedSpectrumA, repeatedSpectrumD, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.vecMulVec]
  · dsimp
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hh := congrArg (fun P : Matrix (Fin 2) (Fin 2) ℂ => P 0 0) h
      norm_num at hh
    · intro h
      have hh := congrFun h 0
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
    · norm_num [repeatedSpectrumDinv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- There can be arbitrarily many negative residues in a Hermitian rank-one
family. The diagonal values are distinct, so no grouping removes them. -/
def allNegativeSpectralValue (d : ℕ) (i : Fin d) : ℝ := (i.val : ℝ) + 1

def allNegativeFamilyB (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => (allNegativeSpectralValue d i : ℂ)

def allNegativeFamilyA (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  allNegativeFamilyB d + Matrix.vecMulVec (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))

theorem all_negative_family_rank_one (d : ℕ) :
    allNegativeFamilyB d * 1 - 1 * allNegativeFamilyA d =
      Matrix.vecMulVec (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ)) := by
  simp only [mul_one, one_mul, allNegativeFamilyA]
  ext i j
  simp [Matrix.vecMulVec]

theorem all_negative_family_hermitian (d : ℕ) :
    (allNegativeFamilyA d).IsHermitian ∧ (allNegativeFamilyB d).IsHermitian := by
  have hb : (allNegativeFamilyB d).IsHermitian := by
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    ext i
    simp [allNegativeFamilyB, Complex.star_def, Complex.conj_ofReal]
  have hg : (Matrix.vecMulVec (fun _ : Fin d => (1 : ℂ))
      (fun _ : Fin d => (1 : ℂ))).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose, Matrix.vecMulVec]
  exact ⟨hb.add hg, hb⟩

theorem all_negative_family_coordinate_coefficient (d : ℕ) (i : Fin d) :
    (∑ j : Fin d, (-1 : ℂ) *
      ((Matrix.diagonal fun k : Fin d => if k = i then (1 : ℂ) else 0).mulVec
        (fun _ : Fin d => (1 : ℂ)) j)) = -1 := by
  simp [Matrix.mulVec_diagonal]

theorem allNegativeSpectralValue_injective (d : ℕ) :
    Function.Injective (allNegativeSpectralValue d) := by
  intro i j h
  apply Fin.ext
  have he : (i.val : ℝ) = j.val := by simpa [allNegativeSpectralValue] using h
  exact_mod_cast he

theorem arbitrarily_many_negative_atoms (d : ℕ) :
    Fintype.card {i : Fin d // (-1 : ℝ) < 0} = d := by
  simp

section UpperConsumers
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

theorem grouped_upper_away {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric)
    (z : ℂ) (hz : 0 < z.im) (β : GroupedSpectrum B) : (β : ℂ) - z ≠ 0 := by
  rw [← groupedEigenvalue_cast hB β]
  exact real_sub_upper_ne_zero (groupedEigenvalue hB β) hz

/-- Actual complex resolvent scalar, using the whole shifted native operator. -/
def hermitianUpperResponse {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ) (z : ℂ) (hz : 0 < z.im) : ℂ :=
  f (D.symm ((groupedShiftedEquiv hB z (grouped_upper_away hB z hz)).symm g))

theorem hermitian_upper_response_expansion {A : E →ₗ[ℂ] E} {B : F →ₗ[ℂ] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)
    (hrank : CCM.RankOneIntertwining A B D g f) (z : ℂ) (hz : 0 < z.im) :
    hermitianUpperResponse hB D g f z hz = complexSignedSpectralResponse
      (groupedEigenvalue hB) (groupedSignedResidue hB D g f) z := by
  exact grouped_signed_resolvent_expansion hA hB D g f hrank z
    (groupedShiftedEquiv hB z (grouped_upper_away hB z hz)) (fun _ => rfl)

/-- An independent consumer composes the actual resolvent bridge with the
finite signed Pick identity. It installs no positivity hypothesis. -/
theorem hermitian_rank_one_upper_pick_identity {A : E →ₗ[ℂ] E} {B : F →ₗ[ℂ] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)
    (hrank : CCM.RankOneIntertwining A B D g f) (z w : ℂ)
    (hz : 0 < z.im) (hw : 0 < w.im) :
    (hermitianUpperResponse hB D g f z hz - star (hermitianUpperResponse hB D g f w hw)) /
      (z - star w) = signedPickKernel (groupedEigenvalue hB) (groupedSignedResidue hB D g f) z w := by
  rw [hermitian_upper_response_expansion hA hB D g f hrank,
    hermitian_upper_response_expansion hA hB D g f hrank]
  exact finite_signed_pick_identity _ _ z w hz hw

end UpperConsumers

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  CCM.poleNeutralEven_innerProductSpace CCM.poleNeutralOdd_innerProductSpace
  CCM.euclideanParityBoundaryFlatSubspace

set_option backward.isDefEq.respectTransparency false

def nativeEvenUpperResponse {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (z : ℂ) (hz : 0 < z.im) : ℂ := by
  letI := CCM.poleNeutralEven_innerProductSpace L K
  letI := CCM.poleNeutralOdd_innerProductSpace L K
  exact hermitianUpperResponse
    (E := CCM.poleNeutralEvenSubspace L K) (F := CCM.poleNeutralOddSubspace L K)
    (CCM.poleNeutralOddCompressedCanonical_isSymmetric L K)
    (CCM.poleNeutralIndexEquiv hL K (by omega)) (CCM.poleNeutralCubicCompressionVector L K)
    (CCM.poleNeutralCorrectedCubicFunctional L K) z hz

def nativeOddUpperResponse {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (z : ℂ) (hz : 0 < z.im) : ℂ := by
  letI := CCM.poleNeutralEven_innerProductSpace L K
  letI := CCM.poleNeutralOdd_innerProductSpace L K
  exact hermitianUpperResponse
    (E := CCM.poleNeutralOddSubspace L K) (F := CCM.poleNeutralEvenSubspace L K)
    (CCM.poleNeutralEvenCompressedCanonical_isSymmetric L K)
    (CCM.poleNeutralIndexAdjointEquiv hL K hK) (-CCM.poleNeutralCorrectedCubicRieszVector L K)
    (CCM.poleNeutralCubicPairingFunctional L K) z hz

theorem native_even_upper_pick_identity {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) :
    (nativeEvenUpperResponse hL K hK z hz - star (nativeEvenUpperResponse hL K hK w hw)) /
      (z - star w) = signedPickKernel (nativeOddGroupedEigenvalue L K)
        (nativeEvenGroupedResidue hL K hK) z w := by
  letI := CCM.poleNeutralEven_innerProductSpace L K
  letI := CCM.poleNeutralOdd_innerProductSpace L K
  simpa only [nativeEvenUpperResponse, nativeOddGroupedEigenvalue, groupedEigenvalue,
    nativeEvenGroupedResidue] using! (hermitian_rank_one_upper_pick_identity
    (E := CCM.poleNeutralEvenSubspace L K) (F := CCM.poleNeutralOddSubspace L K)
    (CCM.poleNeutralEvenCompressedCanonical_isSymmetric L K)
    (CCM.poleNeutralOddCompressedCanonical_isSymmetric L K)
    (CCM.poleNeutralIndexEquiv hL K (by omega)) (CCM.poleNeutralCubicCompressionVector L K)
    (CCM.poleNeutralCorrectedCubicFunctional L K)
    (CCM.canonicalPoleNeutralRankOneIntertwining hL K (by omega)) z w hz hw)

theorem native_odd_upper_pick_identity {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) :
    (nativeOddUpperResponse hL K hK z hz - star (nativeOddUpperResponse hL K hK w hw)) /
      (z - star w) = signedPickKernel (nativeEvenGroupedEigenvalue L K)
        (nativeOddGroupedResidue hL K hK) z w := by
  letI := CCM.poleNeutralEven_innerProductSpace L K
  letI := CCM.poleNeutralOdd_innerProductSpace L K
  simpa only [nativeOddUpperResponse, nativeEvenGroupedEigenvalue, groupedEigenvalue,
    nativeOddGroupedResidue] using! (hermitian_rank_one_upper_pick_identity
    (E := CCM.poleNeutralOddSubspace L K) (F := CCM.poleNeutralEvenSubspace L K)
    (CCM.poleNeutralOddCompressedCanonical_isSymmetric L K)
    (CCM.poleNeutralEvenCompressedCanonical_isSymmetric L K)
    (CCM.poleNeutralIndexAdjointEquiv hL K hK) (-CCM.poleNeutralCorrectedCubicRieszVector L K)
    (CCM.poleNeutralCubicPairingFunctional L K) (native_odd_rank_one_unshifted hL K hK) z w hz hw)

/-- The independent native consumer preserves a zero-source shared mode. -/
theorem native_even_invisible_eigen_shared {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (u : CCM.poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : CCM.poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)
    (hf : CCM.poleNeutralCorrectedCubicSource L K u = 0) :
    ∃ v : CCM.poleNeutralOddSubspace L K, v ≠ 0 ∧
      CCM.poleNeutralOddCompressedCanonical L K v = (lam : ℂ) • v ∧
      v = CCM.poleNeutralIndexEquiv hL K (by omega) u := by
  rcases native_even_visible_or_shared_mode hL K hK lam u hu0 hu with h | h
  · exact False.elim (h hf)
  · exact h

theorem native_odd_invisible_eigen_shared {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (u : CCM.poleNeutralOddSubspace L K) (hu0 : u ≠ 0)
    (hu : CCM.poleNeutralOddCompressedCanonical L K u = (lam : ℂ) • u)
    (hf : CCM.poleNeutralCubicPairingFunctional L K u = 0) :
    ∃ v : CCM.poleNeutralEvenSubspace L K, v ≠ 0 ∧
      CCM.poleNeutralEvenCompressedCanonical L K v = (lam : ℂ) • v ∧
      v = CCM.poleNeutralIndexAdjointEquiv hL K hK u := by
  rcases native_odd_visible_or_shared_mode hL K hK lam u hu0 hu with h | h
  · exact False.elim (h hf)
  · exact h

#check @grouped_resolvent_expansion
#check @groupedSpectralCoefficient_star
#check @finite_signed_pick_identity
#check @finite_signed_pick_gram
#check @finite_signed_pick_negative_subspace_bound
#check @finite_signed_pick_negative_subspace_exact
#print axioms repeated_spectrum_nonreal_coordinates
#print axioms finite_signed_pick_negative_subspace_bound
#print axioms native_even_invisible_eigen_shared
#print axioms native_odd_invisible_eigen_shared
#print axioms native_even_upper_pick_identity
#print axioms native_odd_upper_pick_identity

end Zeta23.OPICARound4.Validation
