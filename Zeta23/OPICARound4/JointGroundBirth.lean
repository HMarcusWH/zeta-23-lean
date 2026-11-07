import Zeta23.OPICARound4.JointGroundConstraints
import Zeta23.OPICARound3.NewbornSource
import Zeta23.CCM.CanonicalPoleNeutralSimpleEvenTie
import Zeta23.CCM.CanonicalPoleNeutralCubicWitness
import Zeta23.CCM.CanonicalPoleNeutralTiePackage

/-!
Own-first-birth and complete tied-ground constraints for the actual native
source. The predecessor belongs to this same parity and cutoff. Full ground
complements and the entire odd ground projection are retained. These results
do not assert a parity gap, eliminate ties, or supply the closing arithmetic
estimate. Simplicity is derived at an own newborn and remains explicit when
a theorem is applied at a different cutoff.
-/
noncomputable section
namespace Zeta23.OPICARound4
open CCM OPICARound3
open scoped ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

/-- A negative eigenspace injects into the actual shell whenever its
predecessor is nonnegative. No unshifted inverse or regularity is assumed. -/
theorem negative_eigenspace_finrank_le_shell
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hPSD : ∀ x, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re)
    (lam : ℝ) (hlam : lam < 0) :
    Module.finrank ℂ (Module.End.eigenspace T (lam : ℂ)) ≤
      Module.finrank ℂ (isometricDetectorComplement J) := by
  let C := (isometricDetectorComplementCoordinate J).comp
    (Module.End.eigenspace T (lam : ℂ)).subtype
  apply LinearMap.finrank_le_finrank_of_injective (f := C)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hc : isometricDetectorComplementCoordinate J (v : F) = 0 := hv
  have hd := isometricDetector_coordinate_decomposition J (v : F)
  rw [hc, Submodule.coe_zero, add_zero] at hd
  have hp := hPSD (J.toLinearMap.adjoint (v : F))
  change 0 ≤ (inner ℂ (J.toLinearMap.adjoint
    (T (J (J.toLinearMap.adjoint (v : F))))) (J.toLinearMap.adjoint (v : F))).re at hp
  rw [inner_adjoint_isometry_left, hd] at hp
  have he : T (v : F) = (lam : ℂ) • (v : F) :=
    (Module.End.mem_eigenspace_iff).mp v.property
  rw [he] at hp
  have hs := re_inner_ofReal_smul_self lam (v : F)
  rw [hs] at hp
  have hz : (v : F) = 0 := by
    by_contra hn
    have hnorm : 0 < ‖(v : F)‖ ^ 2 := by positivity
    have hnegative := mul_neg_of_neg_of_pos hlam hnorm
    linarith
  exact Subtype.ext hz

/-- Actual newborn negative eigenspaces have dimension at most one in
both zero-shift Schur branches. -/
theorem nativeNewborn_negative_eigenspace_finrank_le_one
    (p : ReversalParity) {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness p L K hL) (lam : ℝ) (hlam : lam < 0) :
    Module.finrank ℂ (Module.End.eigenspace
      (nativePoleNeutralParityCanonical p L K) (lam : ℂ)) ≤ 1 := by
  have hc := nativePoleNeutralParity_predecessor_compression_eq p hL
    (show K - 1 ≤ K by omega)
  have hp : ∀ x, 0 ≤ (inner ℂ (predecessorBlock
      (newbornCutoffInclusion p L K) (nativePoleNeutralParityCanonical p L K) x) x).re := by
    intro x
    change predecessorBlock (newbornCutoffInclusion p L K)
      (nativePoleNeutralParityCanonical p L K) =
        nativePoleNeutralParityCanonical p L (K - 1) at hc
    rw [hc]
    cases p <;> exact s.predecessor_psd x
  have hd := negative_eigenspace_finrank_le_shell
    (newbornCutoffInclusion p L K) (nativePoleNeutralParityCanonical p L K) hp lam hlam
  simpa only [s.shell_rank] using hd

/-- A genuine even newborn's negative ground is simple, independently of
whether the odd ground is deeper, shallower, or equal. -/
theorem nativeNewborn_even_ground_simple
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .even L K hL)
    (hneg : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower < 0) :
    Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ)) = 1 := by
  have hl := nativeNewborn_negative_eigenspace_finrank_le_one .even s _ hneg
  obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralEvenRayleighBottom hL K s.cutoff_lower
  have hp : 0 < Module.finrank ℂ (Module.End.eigenspace
      (poleNeutralEvenCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ)) := by
    apply (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)
      (M := Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
        (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ))).mpr
    refine ⟨⟨u, (Module.End.mem_eigenspace_iff).mpr hu⟩, ?_⟩
    intro hz
    apply hu0
    exact congrArg Subtype.val hz
  change Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
    (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ)) ≤ 1 at hl
  omega

/-- At a tied negative ground with even newborn, its fourth moment cannot
vanish. This supplies the existing tie theorem's simplicity premise. -/
theorem nativeNewborn_even_tied_ground_momentFour_ne_zero
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .even L K hL)
    (hneg : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower < 0)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u) :
    centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) ≠ 0 :=
  poleNeutral_simpleEven_tie_momentFour_ne_zero hL K s.cutoff_lower u hu0 hu
    htie (nativeNewborn_even_ground_simple s hneg)

/-- At a simple tied native ground the even corrected source and odd cubic
pairing cannot both vanish. The centered-index correction is retained by
using the previously proved nonzero fourth moment. -/
theorem simple_native_tied_ground_not_both_silent
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (htie : poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK)
    (heSimple : Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ)) = 1)
    (hoSimple : Module.finrank ℂ (Module.End.eigenspace (poleNeutralOddCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ)) = 1)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u)
    (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • w) :
    ¬ (poleNeutralCorrectedCubicSource L K u = 0 ∧
      poleNeutralCubicPairingFunctional L K w = 0) := by
  rintro ⟨hf, hc⟩
  have hm := poleNeutral_simpleEven_tie_momentFour_ne_zero hL K hK u hu0 hu htie heSimple
  have hd := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K (by omega) u
  change poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
    poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K u) = _ at hd
  rw [hu, map_smul, hf, zero_smul] at hd
  have hdEig := sub_eq_zero.mp hd
  let we : Module.End.eigenspace (poleNeutralOddCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) :=
    ⟨w, Module.End.mem_eigenspace_iff.mpr hw⟩
  let de : Module.End.eigenspace (poleNeutralOddCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) :=
    ⟨poleNeutralIndexLinearMap hL K u, Module.End.mem_eigenspace_iff.mpr hdEig⟩
  have hwne : we ≠ 0 := fun hz => hw0 (congrArg Subtype.val hz)
  obtain ⟨c, heq⟩ := (finrank_eq_one_iff_of_nonzero' we hwne).mp hoSimple de
  have hcw : c • w = poleNeutralIndexLinearMap hL K u := congrArg Subtype.val heq
  have hzero : poleNeutralCubicPairingFunctional L K (poleNeutralIndexLinearMap hL K u) = 0 := by
    rw [← hcw, map_smul, hc, smul_zero]
  apply hm
  change inner ℂ (poleNeutralCubicCompressionVector L K) (poleNeutralIndexLinearMap hL K u) = 0 at hzero
  rw [poleNeutral_cubic_pairing_eq_momentFour hL K u] at hzero
  exact hzero


open CCM OPICARound3
open scoped ComplexConjugate
set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

section Abstract
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- Own-predecessor PSD and one shell make the entire orthogonal complement
of any negative eigenvector nonnegative. No index-one premise is supplied. -/
theorem oneShell_negative_eigen_complement_nonnegative
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) (hT : T.IsSymmetric)
    (hPSD : ∀ x, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re)
    (hshell : Module.finrank ℂ (isometricDetectorComplement J) = 1)
    (lam : ℝ) (hlam : lam < 0) (u : F) (hu0 : u ≠ 0)
    (hu : T u = (lam : ℂ) • u) (x : F) (hx : inner ℂ u x = 0) :
    0 ≤ (inner ℂ (T x) x).re := by
  have hnull (y : F) (hy : isometricDetectorComplementCoordinate J y = 0) :
      0 ≤ (inner ℂ (T y) y).re := by
    have hd := isometricDetector_coordinate_decomposition J y
    rw [hy, Submodule.coe_zero, add_zero] at hd
    have hp := hPSD (J.toLinearMap.adjoint y)
    change 0 ≤ (inner ℂ (J.toLinearMap.adjoint (T (J (J.toLinearMap.adjoint y))))
      (J.toLinearMap.adjoint y)).re at hp
    rw [inner_adjoint_isometry_left, hd] at hp
    exact hp
  have hCu : isometricDetectorComplementCoordinate J u ≠ 0 := by
    intro hz
    have hp := hnull u hz
    rw [hu, re_inner_ofReal_smul_self] at hp
    have hn : 0 < ‖u‖ ^ 2 := by positivity
    have hh := mul_neg_of_neg_of_pos hlam hn
    linarith
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero'
    (isometricDetectorComplementCoordinate J u) hCu).mp hshell
      (isometricDetectorComplementCoordinate J x)
  have hnullx : isometricDetectorComplementCoordinate J (x - a • u) = 0 := by
    rw [map_sub, map_smul, ha, sub_self]
  have hp := hnull (x - a • u) hnullx
  have hv : T (a • u) = (lam : ℂ) • (a • u) := by
    rw [map_smul, hu, smul_comm]
  have hxv : inner ℂ x (a • u) = 0 := by
    rw [inner_smul_right, (inner_eq_zero_symm).mp hx, mul_zero]
  have hvx : inner ℂ (a • u) x = 0 := (inner_eq_zero_symm).mpr hxv
  have hcross1 : inner ℂ (T x) (a • u) = 0 := by
    rw [hT x (a • u), hv, inner_smul_right, hxv, mul_zero]
  have hcross2 : inner ℂ (T (a • u)) x = 0 := by
    rw [hv, inner_smul_left, hvx, mul_zero]
  have heq : (inner ℂ (T (x - a • u)) (x - a • u)).re =
      (inner ℂ (T x) x).re + lam * ‖a • u‖ ^ 2 := by
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
      hcross1, hcross2, sub_zero, zero_sub, sub_neg_eq_add, Complex.add_re,
      hv, re_inner_ofReal_smul_self]
  rw [heq] at hp
  have hn : lam * ‖a • u‖ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hlam.le (sq_nonneg _)
  linarith

/-- The complete shifted ground complement has gap at least minus the
actual negative eigenvalue, rather than an assumed relative parity gap. -/
theorem oneShell_negative_eigen_shifted_complement_coercive
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) (hT : T.IsSymmetric)
    (hPSD : ∀ x, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re)
    (hshell : Module.finrank ℂ (isometricDetectorComplement J) = 1)
    (lam : ℝ) (hlam : lam < 0) (u : F) (hu0 : u ≠ 0)
    (hu : T u = (lam : ℂ) • u) (x : F) (hx : inner ℂ u x = 0) :
    (-lam) * ‖x‖ ^ 2 ≤ (inner ℂ (T x - (lam : ℂ) • x) x).re := by
  have hp := oneShell_negative_eigen_complement_nonnegative J T hT hPSD hshell lam hlam u hu0 hu x hx
  rw [inner_sub_left, Complex.sub_re, re_inner_ofReal_smul_self]
  linarith

/-- Every actual shifted response in the full ground complement pays at
most one over the negative depth. No inverse is constructed on the kernel. -/
theorem oneShell_negative_eigen_complement_response_norm
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) (hT : T.IsSymmetric)
    (hPSD : ∀ x, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re)
    (hshell : Module.finrank ℂ (isometricDetectorComplement J) = 1)
    (lam : ℝ) (hlam : lam < 0) (u : F) (hu0 : u ≠ 0)
    (hu : T u = (lam : ℂ) • u) (x : F) (hx : inner ℂ u x = 0) :
    ‖x‖ ≤ ‖T x - (lam : ℂ) • x‖ / (-lam) := by
  have hc := oneShell_negative_eigen_shifted_complement_coercive J T hT hPSD hshell lam hlam u hu0 hu x hx
  have hi : (inner ℂ (T x - (lam : ℂ) • x) x).re ≤
      ‖T x - (lam : ℂ) • x‖ * ‖x‖ := by
    simpa only [RCLike.re_eq_complex_re] using
      (re_inner_le_norm (𝕜 := ℂ) (T x - (lam : ℂ) • x) x)
  by_cases hx0 : x = 0
  · subst x
    simp
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hb : (-lam) * ‖x‖ ≤ ‖T x - (lam : ℂ) • x‖ := by
    apply (mul_le_mul_iff_left₀ hnorm).mp
    nlinarith
  apply (le_div_iff₀ (neg_pos.mpr hlam)).mpr
  nlinarith
end Abstract

/-- Actual newborn instantiation, retaining all zero-shift Schur branches
and all vectors in the orthogonal complement of its negative eigenmode. -/
theorem nativeNewborn_negative_eigen_complement_bounds
    (p : ReversalParity) {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness p L K hL) (lam : ℝ) (hlam : lam < 0)
    (u : nativePoleNeutralParitySpace p L K) (hu0 : u ≠ 0)
    (hu : nativePoleNeutralParityCanonical p L K u = (lam : ℂ) • u)
    (x : nativePoleNeutralParitySpace p L K) (hx : inner ℂ u x = 0) :
    0 ≤ (inner ℂ (nativePoleNeutralParityCanonical p L K x) x).re ∧
      (-lam) * ‖x‖ ^ 2 ≤ (inner ℂ
        (nativePoleNeutralParityCanonical p L K x - (lam : ℂ) • x) x).re ∧
      ‖x‖ ≤ ‖nativePoleNeutralParityCanonical p L K x - (lam : ℂ) • x‖ / (-lam) := by
  have hsym : (nativePoleNeutralParityCanonical p L K).IsSymmetric := by
    cases p
    · exact poleNeutralEvenCompressedCanonical_isSymmetric L K
    · exact poleNeutralOddCompressedCanonical_isSymmetric L K
  have hcomp := nativePoleNeutralParity_predecessor_compression_eq p hL
    (show K - 1 ≤ K by omega)
  have hp : ∀ x, 0 ≤ (inner ℂ (predecessorBlock
      (newbornCutoffInclusion p L K) (nativePoleNeutralParityCanonical p L K) x) x).re := by
    intro x
    change predecessorBlock (newbornCutoffInclusion p L K)
      (nativePoleNeutralParityCanonical p L K) =
        nativePoleNeutralParityCanonical p L (K - 1) at hcomp
    rw [hcomp]
    cases p <;> exact s.predecessor_psd x
  exact ⟨oneShell_negative_eigen_complement_nonnegative _ _ hsym hp s.shell_rank lam hlam u hu0 hu x hx,
    oneShell_negative_eigen_shifted_complement_coercive _ _ hsym hp s.shell_rank lam hlam u hu0 hu x hx,
    oneShell_negative_eigen_complement_response_norm _ _ hsym hp s.shell_rank lam hlam u hu0 hu x hx⟩


open CCM
open scoped ComplexConjugate
set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- A source-active actual even eigenmode at or below the actual odd floor
has strictly positive source-moment energy. Equality of the two bottoms is
allowed; the source-silent branch is deliberately not discarded. -/
theorem native_source_active_moment_pos_of_le_odd_bottom
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)
    (hle : lam ≤ poleNeutralOddRayleighBottom L K hL hK)
    (hf : poleNeutralCorrectedCubicSource L K u ≠ 0) :
    0 < (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re := by
  have hpos := poleNeutralOddShifted_isPositive_of_le_bottom hL K hK lam hle
  have he := poleNeutral_source_moment_energy_eq hL K (by omega) lam u hu
  have hn := hpos.2 (poleNeutralIndexLinearMap hL K u)
  change 0 ≤ (inner ℂ
    (poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
      (lam : ℂ) • poleNeutralIndexLinearMap hL K u)
    (poleNeutralIndexLinearMap hL K u)).re at hn
  by_contra hnot
  have hzeroEnergy : (inner ℂ
    (poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
      (lam : ℂ) • poleNeutralIndexLinearMap hL K u)
    (poleNeutralIndexLinearMap hL K u)).re = 0 := by linarith
  have hz := @nativePositive_apply_eq_zero_of_energy_eq_zero
    (poleNeutralOddSubspace L K) inferInstance (poleNeutralOdd_innerProductSpace L K)
    (poleNeutralOddCompressedCanonical L K - (lam : ℂ) • LinearMap.id)
    hpos (poleNeutralIndexLinearMap hL K u) hzeroEnergy
  have hd := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K (by omega) u
  change poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
    poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K u) = _ at hd
  rw [hu, map_smul] at hd
  change poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
    (lam : ℂ) • poleNeutralIndexLinearMap hL K u = 0 at hz
  rw [hz] at hd
  exact (smul_ne_zero hf (poleNeutralCubicCompressionVector_ne_zero hL K hK)) hd.symm

/-- Source normalization at a tied native ground gives a positive real fourth
moment without using a strict parity gap or an inverse at the common eigenvalue. -/
theorem native_source_normalized_tied_ground_moment_pos
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u)
    (htie : poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK)
    (hf : poleNeutralCorrectedCubicSource L K u = 1) :
    0 < (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re := by
  have h := native_source_active_moment_pos_of_le_odd_bottom hL K hK _ u hu htie.le
    (by rw [hf]; exact one_ne_zero)
  simpa only [hf, star_one, one_mul] using h


open CCM
open scoped ComplexConjugate
set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

private theorem actual_odd_projection_zero_pairing_zero (L : ℝ) (K : ℕ) (lam : ℝ)
    (g w : poleNeutralOddSubspace L K)
    (hp : poleNeutralOddShiftedKernelProjection L K lam g = 0)
    (hw : poleNeutralOddShiftedCanonical L K lam w = 0) : inner ℂ g w = 0 := by
  rw [poleNeutralOddShiftedKernelProjection,
    Submodule.orthogonalProjectionOnto_eq_zero_iff] at hp
  exact inner_eq_zero_symm.mp (hp w (LinearMap.mem_ker.mpr hw))

/-- A source-silent simple even tied ground forces visibility of the whole
odd ground kernel. No odd simplicity or choice of an odd eigenvector is used. -/
theorem simple_even_tie_source_silent_odd_kernel_visible
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (htie : poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK)
    (hsimple : Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ)) = 1)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u)
    (hf : poleNeutralCorrectedCubicSource L K u = 0) :
    poleNeutralOddShiftedKernelProjection L K (poleNeutralEvenRayleighBottom L K hL hK)
      (poleNeutralCubicCompressionVector L K) ≠ 0 := by
  intro hp
  have hm := poleNeutral_simpleEven_tie_momentFour_ne_zero hL K hK u hu0 hu htie hsimple
  have hd := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K (by omega) u
  change poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
    poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K u) = _ at hd
  rw [hu, map_smul, hf, zero_smul] at hd
  have hz : inner ℂ (poleNeutralCubicCompressionVector L K)
      (poleNeutralIndexLinearMap hL K u) = 0 :=
    actual_odd_projection_zero_pairing_zero L K _ _ _ hp hd
  rw [poleNeutral_cubic_pairing_eq_momentFour hL K u] at hz
  exact hm hz

/-- Exactly one of the corrected even source and whole odd ground projection
is active at a simple even tie. Every odd-kernel multiplicity is retained. -/
theorem simple_even_tie_whole_kernel_exclusive_visibility
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (htie : poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK)
    (hsimple : Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ)) = 1)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u) :
    (poleNeutralCorrectedCubicSource L K u = 0 ∧
      poleNeutralOddShiftedKernelProjection L K (poleNeutralEvenRayleighBottom L K hL hK)
        (poleNeutralCubicCompressionVector L K) ≠ 0) ∨
    (poleNeutralCorrectedCubicSource L K u ≠ 0 ∧
      poleNeutralOddShiftedKernelProjection L K (poleNeutralEvenRayleighBottom L K hL hK)
        (poleNeutralCubicCompressionVector L K) = 0) := by
  by_cases hf : poleNeutralCorrectedCubicSource L K u = 0
  · exact Or.inl ⟨hf, simple_even_tie_source_silent_odd_kernel_visible hL K hK htie hsimple u hu0 hu hf⟩
  · right
    refine ⟨hf, ?_⟩
    have hp := poleNeutral_even_eigen_shifted_kernel_compatibility hL K hK
      (poleNeutralEvenRayleighBottom L K hL hK) u hu
    exact (smul_eq_zero.mp hp).resolve_left hf


end Zeta23.OPICARound4
