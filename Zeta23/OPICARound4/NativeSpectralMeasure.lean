import Zeta23.OPICARound4.OperatorSignedBound

noncomputable section

namespace Zeta23.OPICARound4
open CCM Filter Topology
open scoped BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- Distinct actual eigenvalues; multiplicity is inside the corresponding eigenspace. -/
abbrev GroupedSpectrum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V) := Module.End.Eigenvalues B

/-- The real value of an actual Hermitian eigenvalue. -/
def groupedEigenvalue {B : F →ₗ[ℂ] F} (_hB : B.IsSymmetric)
    (β : GroupedSpectrum B) : ℝ := (β : ℂ).re

theorem groupedEigenvalue_cast {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric)
    (β : GroupedSpectrum B) : (groupedEigenvalue hB β : ℂ) = β := by
  change ((β.val.re : ℝ) : ℂ) = β.val
  exact Complex.conj_eq_iff_re.mp (hB.conj_eigenvalue_eq_self β.property)

theorem groupedEigenvalue_injective {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric) :
    Function.Injective (groupedEigenvalue hB) := by
  intro β γ h
  exact Subtype.ext (by
    have hh := congrArg Complex.ofReal h
    change β.val = γ.val
    have hb := groupedEigenvalue_cast hB β
    have hc := groupedEigenvalue_cast hB γ
    change (groupedEigenvalue hB β : ℂ) = β.val at hb
    change (groupedEigenvalue hB γ : ℂ) = γ.val at hc
    exact hb.symm.trans (hh.trans hc))

/-- Canonical orthogonal projector onto the whole eigenspace. -/
def groupedSpectralProjector {B : F →ₗ[ℂ] F} (_hB : B.IsSymmetric)
    (β : GroupedSpectrum B) : F →ₗ[ℂ] F :=
  (Module.End.eigenspace B (β : ℂ)).subtype.comp
    (Module.End.eigenspace B (β : ℂ)).orthogonalProjectionOnto.toLinearMap

theorem groupedSpectralProjector_eq_diagonalization {B : F →ₗ[ℂ] F}
    (hB : B.IsSymmetric) (β : GroupedSpectrum B) (v : F) :
    groupedSpectralProjector hB β v = (hB.diagonalization v β : F) := by
  classical
  have hv : ∑ γ, (hB.diagonalization v γ : F) = v := by
    simpa only [hB.diagonalization_symm_apply] using hB.diagonalization.symm_apply_apply v
  change (Module.End.eigenspace B (β : ℂ)).starProjection v = _
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hB.diagonalization v β).property
  intro w hw
  rw [inner_sub_left]
  conv_lhs => lhs; rw [← hv, sum_inner]
  have hs : (∑ γ, inner ℂ (hB.diagonalization v γ : F) w) =
      inner ℂ (hB.diagonalization v β : F) w := by
    apply Finset.sum_eq_single β
    · intro γ _ hγ
      exact hB.orthogonalFamily_eigenspaces' hγ (hB.diagonalization v γ) ⟨w, hw⟩
    · simp
  rw [hs, sub_self]

theorem sum_groupedSpectralProjector {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric) (v : F) :
    ∑ β, groupedSpectralProjector hB β v = v := by
  simpa only [groupedSpectralProjector_eq_diagonalization,
    hB.diagonalization_symm_apply] using hB.diagonalization.symm_apply_apply v

/-- Actual complex coefficient, without discarding its imaginary part. -/
def groupedSpectralCoefficient {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ) (β : GroupedSpectrum B) : ℂ :=
  f (D.symm (groupedSpectralProjector hB β g))

theorem grouped_resolvent_expansion {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ) (z : ℂ)
    (Bi : F ≃ₗ[ℂ] F) (hBi : ∀ v, Bi v = B v - z • v)
    (haway : ∀ β : GroupedSpectrum B, (β : ℂ) - z ≠ 0) :
    f (D.symm (Bi.symm g)) =
      ∑ β, groupedSpectralCoefficient hB D g f β / ((β : ℂ) - z) := by
  have hc (β : GroupedSpectrum B) :
      groupedSpectralProjector hB β (Bi.symm g) =
        (((β : ℂ) - z)⁻¹) • groupedSpectralProjector hB β g := by
    have hh := congrArg (fun v : F => hB.diagonalization v β) (Bi.apply_symm_apply g)
    rw [hBi, map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply,
      hB.diagonalization_apply_self_apply] at hh
    rw [groupedSpectralProjector_eq_diagonalization,
      groupedSpectralProjector_eq_diagonalization]
    have hh' := congrArg (fun x : Module.End.eigenspace B (β : ℂ) => (x : F)) hh
    simp only [Submodule.coe_sub, Submodule.coe_smul] at hh'
    have hd := congrArg (fun x : F => (((β : ℂ) - z)⁻¹) • x) hh'
    simpa only [← sub_smul, smul_smul, inv_mul_cancel₀ (haway β), one_smul] using hd
  rw [← sum_groupedSpectralProjector hB (Bi.symm g), map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [hc, map_smul, map_smul, smul_eq_mul]
  simp only [groupedSpectralCoefficient, div_eq_mul_inv, mul_comm]

theorem grouped_shift_injective {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric)
    (z : ℂ) (haway : ∀ β : GroupedSpectrum B, (β : ℂ) - z ≠ 0) :
    Function.Injective (B - z • (LinearMap.id : F →ₗ[ℂ] F)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  apply hB.diagonalization.injective
  ext β
  have hh := congrArg (fun w : F => hB.diagonalization w β) hv
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, map_zero,
    PiLp.zero_apply, hB.diagonalization_apply_self_apply] at hh
  rw [← sub_smul] at hh
  have hz := (smul_eq_zero.mp hh).resolve_left (haway β)
  simpa using hz

/-- Genuine inverse of the actual shifted operator on its full resolvent set. -/
def groupedShiftedEquiv {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric)
    (z : ℂ) (haway : ∀ β : GroupedSpectrum B, (β : ℂ) - z ≠ 0) : F ≃ₗ[ℂ] F :=
  LinearEquiv.ofInjectiveEndo (B - z • LinearMap.id) (grouped_shift_injective hB z haway)

theorem hermitian_det_star {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) :
    star (LinearMap.det T) = LinearMap.det T := by
  rw [hT.det_eq_prod_eigenvalues rfl]
  simp

/-- The determinant quotient makes the complete grouped response real for
real spectral parameters; no coordinate coefficient is asserted real. -/
theorem grouped_real_response {A : E →ₗ[ℂ] E} {B : F →ₗ[ℂ] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)
    (hrank : RankOneIntertwining A B D g f)
    (t : ℝ) (haway : ∀ β : GroupedSpectrum B, (β : ℂ) - (t : ℂ) ≠ 0) :
    star (∑ β, groupedSpectralCoefficient hB D g f β / ((β : ℂ) - (t : ℂ))) =
      ∑ β, groupedSpectralCoefficient hB D g f β / ((β : ℂ) - (t : ℂ)) := by
  let Bi := groupedShiftedEquiv hB (t : ℂ) haway
  have hs := grouped_resolvent_expansion hB D g f (t : ℂ) Bi (fun _ => rfl) haway
  have hd := det_div_det_eq_one_sub_secularResolventScalar
    (hrank.shift (t : ℂ)) (Bi := Bi) (fun _ => rfl)
  change LinearMap.det (A - (t : ℂ) • LinearMap.id) /
    LinearMap.det (B - (t : ℂ) • LinearMap.id) =
      1 - f (D.symm (Bi.symm g)) at hd
  rw [hs] at hd
  have hAr : (A - (t : ℂ) • LinearMap.id).IsSymmetric :=
    hA.sub (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id)
  have hBr : (B - (t : ℂ) • LinearMap.id).IsSymmetric :=
    hB.sub (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id)
  have hh := congrArg star hd
  rw [star_div₀, hermitian_det_star hAr, hermitian_det_star hBr, hd,
    star_sub, star_one] at hh
  linear_combination hh

/-- Distinct finite poles with a real response have real *grouped* complex
residues. The proof removes one pole and takes a punctured real limit. -/
theorem finite_grouped_residue_star {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eigenvalue : ι → ℝ) (coefficient : ι → ℂ)
    (hinj : Function.Injective eigenvalue)
    (hreal : ∀ t : ℝ, (∀ i, eigenvalue i ≠ t) →
      star (∑ i, coefficient i / ((eigenvalue i : ℂ) - (t : ℂ))) =
        ∑ i, coefficient i / ((eigenvalue i : ℂ) - (t : ℂ)))
    (β : ι) : star (coefficient β) = coefficient β := by
  let regularized : ℝ → ℂ := fun t => ∑ i,
    if i = β then coefficient β else
      ((eigenvalue β : ℂ) - (t : ℂ)) * coefficient i /
        ((eigenvalue i : ℂ) - (t : ℂ))
  have hcont : ContinuousAt regularized (eigenvalue β) := by
    apply tendsto_finsetSum
    intro i _
    by_cases hi : i = β
    · simp only [hi, if_pos, regularized]
      exact continuousAt_const
    · simp only [if_neg hi]
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact sub_ne_zero.mpr (Complex.ofReal_injective.ne (fun he => hi (hinj he)))
  have hvalue : regularized (eigenvalue β) = coefficient β := by
    simp [regularized, Finset.sum_ite_eq']
  have hlim : Tendsto regularized (𝓝[≠] eigenvalue β) (𝓝 (coefficient β)) := by
    rw [← hvalue]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have haw : ∀ᶠ t in 𝓝[≠] eigenvalue β, ∀ i, eigenvalue i ≠ t := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i = β
    · subst i
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff, ne_comm] using ht
    · exact (eventually_ne_nhdsWithin (fun he => hi (hinj he.symm))).mono
        (fun _ ht => ht.symm)
  have hreg : ∀ᶠ t in 𝓝[≠] eigenvalue β, star (regularized t) = regularized t := by
    filter_upwards [haw] with t ht
    have heq : regularized t = ((eigenvalue β : ℂ) - (t : ℂ)) *
        (∑ i, coefficient i / ((eigenvalue i : ℂ) - (t : ℂ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = β
      · subst i
        simp only [if_pos, regularized]
        field_simp [sub_ne_zero.mpr (Complex.ofReal_injective.ne (ht β))]
      · simp only [if_neg hi]
        ring
    rw [heq, star_mul, star_sub, hreal t ht]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  have hs : IsClosed {c : ℂ | star c = c} := isClosed_eq continuous_star continuous_id
  exact hs.mem_of_tendsto hlim hreg

theorem groupedSpectralCoefficient_star {A : E →ₗ[ℂ] E} {B : F →ₗ[ℂ] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)
    (hrank : RankOneIntertwining A B D g f) (β : GroupedSpectrum B) :
    star (groupedSpectralCoefficient hB D g f β) = groupedSpectralCoefficient hB D g f β := by
  classical
  apply finite_grouped_residue_star (groupedEigenvalue hB)
    (groupedSpectralCoefficient hB D g f) (groupedEigenvalue_injective hB)
  intro t ht
  simp only [groupedEigenvalue_cast]
  apply grouped_real_response hA hB D g f hrank t
  intro γ
  rw [← groupedEigenvalue_cast hB γ, ← Complex.ofReal_sub]
  exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ht γ))

/-- Real signed mass, licensed by the preceding reality theorem. -/
def groupedSignedResidue {B : F →ₗ[ℂ] F} (hB : B.IsSymmetric)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ) (β : GroupedSpectrum B) : ℝ :=
  (groupedSpectralCoefficient hB D g f β).re

theorem groupedSignedResidue_cast {A : E →ₗ[ℂ] E} {B : F →ₗ[ℂ] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)
    (hrank : RankOneIntertwining A B D g f) (β : GroupedSpectrum B) :
    (groupedSignedResidue hB D g f β : ℂ) = groupedSpectralCoefficient hB D g f β := by
  exact Complex.conj_eq_iff_re.mp (groupedSpectralCoefficient_star hA hB D g f hrank β)

theorem grouped_shift_away_of_equiv {B : F →ₗ[ℂ] F}
    (z : ℂ) (Bi : F ≃ₗ[ℂ] F) (hBi : ∀ v, Bi v = B v - z • v)
    (β : GroupedSpectrum B) : (β : ℂ) - z ≠ 0 := by
  have hb : Module.End.HasEigenvalue B (β : ℂ) := β.property
  obtain ⟨v, hv, hv0⟩ := hb.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hv
  intro hz
  have hi : Bi v = 0 := by
    rw [hBi, hv, ← sub_smul, hz, zero_smul]
  exact hv0 (Bi.injective (by simpa using hi))

/-- Exact signed real spectral data for the actual complex response. -/
theorem grouped_signed_resolvent_expansion {A : E →ₗ[ℂ] E} {B : F →ₗ[ℂ] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)
    (hrank : RankOneIntertwining A B D g f) (z : ℂ)
    (Bi : F ≃ₗ[ℂ] F) (hBi : ∀ v, Bi v = B v - z • v) :
    f (D.symm (Bi.symm g)) = ∑ β,
      (groupedSignedResidue hB D g f β : ℂ) / ((groupedEigenvalue hB β : ℂ) - z) := by
  simp only [groupedSignedResidue_cast hA hB D g f hrank, groupedEigenvalue_cast]
  exact grouped_resolvent_expansion hB D g f z Bi hBi
    (grouped_shift_away_of_equiv z Bi hBi)

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

set_option backward.isDefEq.respectTransparency false

def nativeOddGroupedProjector (L : ℝ) (K : ℕ)
    (β : GroupedSpectrum (poleNeutralOddCompressedCanonical L K)) :
    poleNeutralOddSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K := by
  letI := poleNeutralOdd_innerProductSpace L K
  simpa only [] using! (groupedSpectralProjector (F := poleNeutralOddSubspace L K)
    (poleNeutralOddCompressedCanonical_isSymmetric L K) β)

def nativeEvenGroupedProjector (L : ℝ) (K : ℕ)
    (β : GroupedSpectrum (poleNeutralEvenCompressedCanonical L K)) :
    poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralEvenSubspace L K := by
  letI := poleNeutralEven_innerProductSpace L K
  simpa only [] using! (groupedSpectralProjector (F := poleNeutralEvenSubspace L K)
    (poleNeutralEvenCompressedCanonical_isSymmetric L K) β)

def nativeOddGroupedEigenvalue (L : ℝ) (K : ℕ)
    (β : GroupedSpectrum (poleNeutralOddCompressedCanonical L K)) : ℝ := (β : ℂ).re

def nativeEvenGroupedEigenvalue (L : ℝ) (K : ℕ)
    (β : GroupedSpectrum (poleNeutralEvenCompressedCanonical L K)) : ℝ := (β : ℂ).re

/-- Native even masses use the odd Hermitian operator and the actual inverse
centered-index map. They are grouped across each whole eigenspace. -/
def nativeEvenGroupedResidue {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (β : GroupedSpectrum (poleNeutralOddCompressedCanonical L K)) : ℝ := by
  letI := poleNeutralEven_innerProductSpace L K
  letI := poleNeutralOdd_innerProductSpace L K
  exact groupedSignedResidue (E := poleNeutralEvenSubspace L K) (F := poleNeutralOddSubspace L K)
    (poleNeutralOddCompressedCanonical_isSymmetric L K)
    (poleNeutralIndexEquiv hL K (by omega)) (poleNeutralCubicCompressionVector L K)
    (poleNeutralCorrectedCubicFunctional L K) β

/-- The odd branch retains the actual adjoint transport and minus source. -/
def nativeOddGroupedResidue {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (β : GroupedSpectrum (poleNeutralEvenCompressedCanonical L K)) : ℝ := by
  letI := poleNeutralEven_innerProductSpace L K
  letI := poleNeutralOdd_innerProductSpace L K
  exact groupedSignedResidue (E := poleNeutralOddSubspace L K) (F := poleNeutralEvenSubspace L K)
    (poleNeutralEvenCompressedCanonical_isSymmetric L K)
    (poleNeutralIndexAdjointEquiv hL K hK) (-poleNeutralCorrectedCubicRieszVector L K)
    (poleNeutralCubicPairingFunctional L K) β

theorem native_odd_rank_one_unshifted {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) :
    RankOneIntertwining (poleNeutralOddCompressedCanonical L K)
      (poleNeutralEvenCompressedCanonical L K) (poleNeutralIndexAdjointEquiv hL K hK)
      (-poleNeutralCorrectedCubicRieszVector L K) (poleNeutralCubicPairingFunctional L K) := by
  letI := poleNeutralEven_innerProductSpace L K
  letI := poleNeutralOdd_innerProductSpace L K
  intro w
  have ha := poleNeutral_adjoint_rankOne_identity hL K hK w
  change poleNeutralEvenCompressedCanonical L K ((poleNeutralIndexLinearMap hL K).adjoint w) -
    (poleNeutralIndexLinearMap hL K).adjoint (poleNeutralOddCompressedCanonical L K w) = _
  rw [smul_neg, ← ha]
  abel

theorem native_even_grouped_residue_cast {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (β : GroupedSpectrum (poleNeutralOddCompressedCanonical L K)) :
    (nativeEvenGroupedResidue hL K hK β : ℂ) =
      poleNeutralCorrectedCubicSource L K ((poleNeutralIndexEquiv hL K (by omega)).symm
        (nativeOddGroupedProjector L K β
          (poleNeutralCubicCompressionVector L K))) := by
  letI := poleNeutralEven_innerProductSpace L K
  letI := poleNeutralOdd_innerProductSpace L K
  simpa only [nativeEvenGroupedResidue, groupedSpectralCoefficient, nativeOddGroupedProjector,
    poleNeutralCorrectedCubicFunctional_apply] using! (groupedSignedResidue_cast
    (E := poleNeutralEvenSubspace L K) (F := poleNeutralOddSubspace L K)
    (poleNeutralEvenCompressedCanonical_isSymmetric L K)
    (poleNeutralOddCompressedCanonical_isSymmetric L K)
    (poleNeutralIndexEquiv hL K (by omega)) (poleNeutralCubicCompressionVector L K)
    (poleNeutralCorrectedCubicFunctional L K)
    (canonicalPoleNeutralRankOneIntertwining hL K (by omega)) β)

theorem native_odd_grouped_residue_cast {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (β : GroupedSpectrum (poleNeutralEvenCompressedCanonical L K)) :
    (nativeOddGroupedResidue hL K hK β : ℂ) =
      poleNeutralCubicPairingFunctional L K ((poleNeutralIndexAdjointEquiv hL K hK).symm
        (nativeEvenGroupedProjector L K β
          (-poleNeutralCorrectedCubicRieszVector L K))) := by
  letI := poleNeutralEven_innerProductSpace L K
  letI := poleNeutralOdd_innerProductSpace L K
  simpa only [nativeOddGroupedResidue, groupedSpectralCoefficient, nativeEvenGroupedProjector] using! (groupedSignedResidue_cast
    (E := poleNeutralOddSubspace L K) (F := poleNeutralEvenSubspace L K)
    (poleNeutralOddCompressedCanonical_isSymmetric L K)
    (poleNeutralEvenCompressedCanonical_isSymmetric L K)
    (poleNeutralIndexAdjointEquiv hL K hK) (-poleNeutralCorrectedCubicRieszVector L K)
    (poleNeutralCubicPairingFunctional L K) (native_odd_rank_one_unshifted hL K hK) β)

theorem native_even_grouped_resolvent_expansion {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    poleNeutralCorrectedCubicSource L K (poleNeutralEvenShiftedRay hL K hK lam hlam) =
      ∑ β, (nativeEvenGroupedResidue hL K hK β : ℂ) /
        ((nativeOddGroupedEigenvalue L K β : ℂ) -
          (lam : ℂ)) := by
  letI := poleNeutralEven_innerProductSpace L K
  letI := poleNeutralOdd_innerProductSpace L K
  simpa only [nativeEvenGroupedResidue, nativeOddGroupedEigenvalue, groupedEigenvalue,
    poleNeutralCorrectedCubicFunctional_apply,
    poleNeutralEvenShiftedRay, secularResolventRay] using! (grouped_signed_resolvent_expansion
    (E := poleNeutralEvenSubspace L K) (F := poleNeutralOddSubspace L K)
    (poleNeutralEvenCompressedCanonical_isSymmetric L K)
    (poleNeutralOddCompressedCanonical_isSymmetric L K)
    (poleNeutralIndexEquiv hL K (by omega)) (poleNeutralCubicCompressionVector L K)
    (poleNeutralCorrectedCubicFunctional L K)
    (canonicalPoleNeutralRankOneIntertwining hL K (by omega)) (lam : ℂ)
    (poleNeutralOddShiftedCanonicalEquiv hL K hK lam hlam) (fun _ => rfl))

theorem native_odd_grouped_resolvent_expansion {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) =
      ∑ β, (nativeOddGroupedResidue hL K hK β : ℂ) /
        ((nativeEvenGroupedEigenvalue L K β : ℂ) -
          (lam : ℂ)) := by
  letI := poleNeutralEven_innerProductSpace L K
  letI := poleNeutralOdd_innerProductSpace L K
  simpa only [nativeOddGroupedResidue, nativeEvenGroupedEigenvalue, groupedEigenvalue,
    poleNeutralOddAdjointShiftedRay,
    secularResolventRay] using! (grouped_signed_resolvent_expansion
    (E := poleNeutralOddSubspace L K) (F := poleNeutralEvenSubspace L K)
    (poleNeutralOddCompressedCanonical_isSymmetric L K)
    (poleNeutralEvenCompressedCanonical_isSymmetric L K)
    (poleNeutralIndexAdjointEquiv hL K hK) (-poleNeutralCorrectedCubicRieszVector L K)
    (poleNeutralCubicPairingFunctional L K) (native_odd_rank_one_unshifted hL K hK) (lam : ℂ)
    (poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam) (fun _ => rfl))

end Zeta23.OPICARound4

#print axioms Zeta23.OPICARound4.groupedSpectralProjector_eq_diagonalization
#print axioms Zeta23.OPICARound4.grouped_resolvent_expansion
#print axioms Zeta23.OPICARound4.groupedSpectralCoefficient_star
#print axioms Zeta23.OPICARound4.native_even_grouped_residue_cast
#print axioms Zeta23.OPICARound4.native_odd_grouped_residue_cast
#print axioms Zeta23.OPICARound4.native_even_grouped_resolvent_expansion
#print axioms Zeta23.OPICARound4.native_odd_grouped_resolvent_expansion

