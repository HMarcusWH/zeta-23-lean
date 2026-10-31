import Zeta23.OPICARound3.UniformNeutralInterval
import Zeta23.OPICARound4.ClosureConsumers

noncomputable section

namespace Zeta23.OPICARound4

open CCM OPICARound3 Set

/-- The joint carrier uses both actual physical exponential pole moments, in
the original ambient coefficient metric. -/
def NativePhysicalNeutralSubspace (L : ℝ) (K : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * K + 1)))) : Prop :=
  ∀ w ∈ S, w ∈ euclideanBoundaryFlatSubspace K ∧
    canonicalPoleExponentialMoment 1 L K ((EuclideanSpace.equiv _ ℂ) w) = 0 ∧
    canonicalPoleExponentialMoment (-1) L K ((EuclideanSpace.equiv _ ℂ) w) = 0

def StrictlyNegativeNativeSubspace (L : ℝ) (K : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * K + 1)))) : Prop :=
  ∀ w ∈ S, w ≠ 0 → fullCanonicalEnergy L K w < 0

/-- The joint index is capped by one only if this independent source-specific
inequality is supplied. It is an OPEN research proposition, not an axiom. -/
def NativeJointNegativeIndexAtMostOne (L : ℝ) (K : ℕ) : Prop :=
  ∀ S : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * K + 1))),
    NativePhysicalNeutralSubspace L K S → StrictlyNegativeNativeSubspace L K S →
      Module.finrank ℂ S ≤ 1

/-- The existing D03 physical two-plane construction, exposed in a native module
to keep production consumers independent of Validation imports. -/
theorem native_frame_negative_physical_plane {a b η : ℝ} {K : ℕ}
    (F : UniformNeutralNegativeFrame a b K η) (L : ℝ) (hL : 0 < L) (hI : L ∈ Icc a b) :
    ∃ S : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * K + 1))),
      Module.finrank ℂ S = 2 ∧
      (∀ w ∈ S, w ∈ euclideanBoundaryFlatSubspace K ∧
        canonicalPoleExponentialMoment 1 L K ((EuclideanSpace.equiv _ ℂ) w) = 0 ∧
        canonicalPoleExponentialMoment (-1) L K ((EuclideanSpace.equiv _ ℂ) w) = 0) ∧
      (∀ w ∈ S, ‖w‖ = 1 →
        (quadraticForm (canonicalSourceMatrix L K) ((EuclideanSpace.equiv _ ℂ) w)).re ≤ -η) := by
  let e := F.even L
  let o := F.odd L
  let f : Fin 2 → EuclideanSpace ℂ (Fin (2 * K + 1)) := ![e, o]
  let S := Submodule.span ℂ (Set.range f)
  have horth : Orthonormal ℂ f := F.orthonormal L hI
  have hdim : Module.finrank ℂ S = 2 := by
    simpa [S] using (finrank_span_eq_card horth.linearIndependent)
  have hrange : Set.range f = ({e, o} : Set (EuclideanSpace ℂ (Fin (2 * K + 1)))) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [f]
    · intro hw
      simp only [mem_insert_iff, mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hcoords : ∀ w ∈ S, ∃ c d : ℂ, c • e + d • o = w := by
    intro w hw
    apply Submodule.mem_span_pair.mp
    simpa [S, hrange] using hw
  have heLegal := F.even_legal L hI
  have hoLegal := F.odd_legal L hI
  have heFull : e ∈ euclideanBoundaryFlatSubspace K :=
    (mem_euclideanBoundaryFlatSubspace_iff K e).mpr
      ((mem_euclideanEvenBoundaryFlatSubspace_iff K e).mp heLegal).1
  have hoFull : o ∈ euclideanBoundaryFlatSubspace K :=
    (mem_euclideanBoundaryFlatSubspace_iff K o).mpr
      ((mem_euclideanOddBoundaryFlatSubspace_iff K o).mp hoLegal).1
  let el : euclideanEvenBoundaryFlatSubspace K := ⟨e, heLegal⟩
  let ol : euclideanOddBoundaryFlatSubspace K := ⟨o, hoLegal⟩
  have hePhys := (poleNeutralEven_iff_exponentialMoments hL K el).mp
    ((mem_poleNeutralEvenSubspace L K el).mpr (F.even_pole L hI))
  have hoPhys := (poleNeutralOdd_iff_exponentialMoments hL K ol).mp
    ((mem_poleNeutralOddSubspace L K ol).mpr (F.odd_pole L hI))
  have hePoles : canonicalPoleEvenFunctional L K e = 0 ∧ canonicalPoleOddFunctional L K e = 0 :=
    (canonicalPoleExponentialMoments_iff_profiles hL K _).mp hePhys
  have hoPoles : canonicalPoleEvenFunctional L K o = 0 ∧ canonicalPoleOddFunctional L K o = 0 :=
    (canonicalPoleExponentialMoments_iff_profiles hL K _).mp hoPhys
  refine ⟨S, hdim, ?_, ?_⟩
  · intro w hw
    obtain ⟨c, d, rfl⟩ := hcoords w hw
    refine ⟨(euclideanBoundaryFlatSubspace K).add_mem
      ((euclideanBoundaryFlatSubspace K).smul_mem c heFull)
      ((euclideanBoundaryFlatSubspace K).smul_mem d hoFull), ?_⟩
    apply (canonicalPoleExponentialMoments_iff_profiles hL K _).mpr
    change canonicalPoleEvenFunctional L K (c • e + d • o) = 0 ∧
      canonicalPoleOddFunctional L K (c • e + d • o) = 0
    simp [map_add, map_smul, hePoles.1, hePoles.2, hoPoles.1, hoPoles.2]
  · intro w hw hnorm
    obtain ⟨c, d, hcd⟩ := hcoords w hw
    have hn := parity_unit_frame_norm_sq K e o heLegal hoLegal
      (F.even_unit L hI) (F.odd_unit L hI) c d
    rw [hcd, hnorm, one_pow] at hn
    have he := F.energy_le L hI c d
    rw [hcd, ← hn, mul_one] at he
    rw [quadraticForm_re_eq_re_inner_apply_self]
    exact he

/-- Reuse D03's independently checked physical two-plane. Homogeneous scaling
extends its whole-unit-sphere bound to every nonzero vector. -/
theorem frame_strictly_negative_native_plane {a b η : ℝ} {K : ℕ}
    (F : UniformNeutralNegativeFrame a b K η) (hη : 0 < η)
    (L : ℝ) (hL : 0 < L) (hI : L ∈ Icc a b) :
    ∃ S : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * K + 1))),
      Module.finrank ℂ S = 2 ∧ NativePhysicalNeutralSubspace L K S ∧
        StrictlyNegativeNativeSubspace L K S := by
  obtain ⟨S, hdim, hphysical, henergy⟩ :=
    native_frame_negative_physical_plane F L hL hI
  refine ⟨S, hdim, hphysical, ?_⟩
  intro w hw hw0
  have hm : unitNormalize w ∈ S := S.smul_mem _ hw
  have hb := henergy (unitNormalize w) hm (norm_unitNormalize hw0)
  rw [quadraticForm_re_eq_re_inner_apply_self] at hb
  have hn : fullCanonicalEnergy L K (unitNormalize w) < 0 := lt_of_le_of_lt hb (by linarith)
  rw [unitNormalize, fullCanonicalEnergy_smul] at hn
  exact neg_of_mul_neg_right hn (sq_nonneg _)

theorem frame_contradicts_native_joint_index {a b η : ℝ} {K : ℕ}
    (F : UniformNeutralNegativeFrame a b K η) (hη : 0 < η)
    (L : ℝ) (hL : 0 < L) (hI : L ∈ Icc a b)
    (hcap : NativeJointNegativeIndexAtMostOne L K) : False := by
  obtain ⟨S, hdim, hphys, hneg⟩ := frame_strictly_negative_native_plane F hη L hL hI
  have hc := hcap S hphys hneg
  omega

/-- Uniform in cutoff, with threshold before the aperture: this cap suffices
conditionally by D03. No individual parity index bound supplies this joint cap. -/
def EventualNativeJointNegativeIndexCap : Prop :=
  ∃ R : ℝ, ∀ L : ℝ, R < L → ∀ K : ℕ, 3 ≤ K →
    NativeJointNegativeIndexAtMostOne L K

theorem no_off_line_zero_of_eventual_native_joint_index
    (h : EventualNativeJointNegativeIndexCap) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 := by
  intro ρ
  by_contra hoff
  obtain ⟨R, hR⟩ := h
  obtain ⟨a, b, K, η, hRa, ha, hab, hK, hη, ⟨F⟩⟩ :=
    cofinally_uniform_neutral_interval_of_off_line_zero ρ hoff R
  exact frame_contradicts_native_joint_index F hη a ha ⟨le_rfl, hab.le⟩ (hR a hRa K hK)

/-- The native odd visible/invisible split uses the genuine adjoint D*. The
invisible branch transports the same eigenvalue into the actual even carrier;
it does not prove a strict gap or eliminate a shared negative ground. -/
theorem native_odd_visible_or_invisible_competitor {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (w : poleNeutralOddSubspace L K)
    (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    poleNeutralCubicPairingFunctional L K w ≠ 0 ∨
      (poleNeutralCubicPairingFunctional L K w = 0 ∧
        ∃ v : poleNeutralEvenSubspace L K, v ≠ 0 ∧
          poleNeutralEvenCompressedCanonical L K v = (lam : ℂ) • v ∧
            v = (poleNeutralIndexLinearMap hL K).adjoint w) := by
  by_cases hp : poleNeutralCubicPairingFunctional L K w = 0
  · right
    refine ⟨hp, ?_⟩
    rcases poleNeutral_odd_eigen_adjoint_competitor_source_dichotomy
      hL K hK lam w hw0 hw with hn | hc
    · exact False.elim (hn hp)
    · exact hc
  · exact Or.inl hp

end Zeta23.OPICARound4
