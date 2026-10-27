import Zeta23.OPICARound3.UniformNeutralInterval
import Zeta23.OPICARound3.Validation.NeutralParityCover

noncomputable section

namespace Zeta23.OPICARound3.Validation

open CCM Matrix Set

theorem cofinally_uniform_neutral_interval_of_off_line_zero_consumer
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) (R : ℝ) :
    ∃ a b : ℝ, ∃ K : ℕ, ∃ η : ℝ, R < a ∧ 0 < a ∧ a < b ∧ 3 ≤ K ∧ 0 < η ∧
      Nonempty (Zeta23.OPICARound3.UniformNeutralNegativeFrame a b K η) := by
  exact Zeta23.OPICARound3.cofinally_uniform_neutral_interval_of_off_line_zero ρ hoff R

/-- The output frame is a genuinely complex two-dimensional physical
neutral subspace, with the advertised bound on its whole unit sphere. -/
theorem frame_negative_physical_plane_consumer {a b η : ℝ} {K : ℕ}
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

end Zeta23.OPICARound3.Validation

#print axioms Zeta23.OPICARound3.Validation.cofinally_uniform_neutral_interval_of_off_line_zero_consumer
#print axioms Zeta23.OPICARound3.Validation.frame_negative_physical_plane_consumer
