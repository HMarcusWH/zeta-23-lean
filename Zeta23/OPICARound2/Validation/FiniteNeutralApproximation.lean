import Zeta23.OPICARound2.FiniteNeutralApproximation

/-! Independently restated legal, physical, fixed-aperture and obstruction
consumers, with exact boundary/normalization controls. No no-exit sign is claimed. -/

noncomputable section

open Complex Matrix

namespace Zeta23.OPICARound2.Validation

theorem neutral_consumer_001 {a : ℝ} (ha : 0 < a) :
    neutralEvenFunctional a 2 CCM.positiveEvenSourceWitness =
      24 / ((a : ℂ) * ((a : ℂ) + 1) * ((a : ℂ) + 4)) :=
  (neutral_even_corrector_pairings ha).1

theorem neutral_consumer_002 {a : ℝ} (ha : 0 < a) :
    neutralOddFunctional a 2 CCM.oddSourceWitnessK2 =
      -12 / (((a : ℂ) + 1) * ((a : ℂ) + 4)) :=
  (neutral_odd_corrector_pairings ha).2

theorem neutral_consumer_003 {a : ℝ} (ha : 0 < a) :
    neutralOddFunctional a 2 CCM.positiveEvenSourceWitness = 0 ∧
      neutralEvenFunctional a 2 CCM.oddSourceWitnessK2 = 0 :=
  ⟨(neutral_even_corrector_pairings ha).2,(neutral_odd_corrector_pairings ha).1⟩

theorem neutral_consumer_004 :
    (fun i : Fin (2 * 2 + 1) => (CCM.centeredIndex 2 i : ℂ) *
      CCM.positiveEvenSourceWitness i) = 2 • CCM.oddSourceWitnessK2 := neutral_native_odd_scaling

theorem neutral_consumer_005 (a : ℝ) {N K : ℕ} (hNK : N ≤ K)
    (u : Fin (2 * N + 1) → ℂ) :
    neutralEvenFunctional a K (CCM.centeredZeroExtend hNK u) = neutralEvenFunctional a N u ∧
      neutralOddFunctional a K (CCM.centeredZeroExtend hNK u) = neutralOddFunctional a N u :=
  ⟨neutralEvenFunctional_centeredZeroExtend a hNK u,neutralOddFunctional_centeredZeroExtend a hNK u⟩

theorem neutral_consumer_006 {a : ℝ} (ha : 0 < a) (K : ℕ) (hK : 2 ≤ K)
    (u : Fin (2 * K + 1) → ℂ) (hu : CCM.BoundaryFlatCoefficients K u) :
    CCM.BoundaryFlatCoefficients K (neutralRepair a K hK u) ∧
      neutralEvenFunctional a K (neutralRepair a K hK u) = 0 ∧
      neutralOddFunctional a K (neutralRepair a K hK u) = 0 :=
  ⟨neutralRepair_legal a K hK u hu,neutralRepair_exact ha K hK u⟩

theorem neutral_consumer_007 (L : ℝ) (K : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    CCM.poleEvenProfile L K ⬝ᵥ u =
      ((L / (16 * Real.pi ^ 2) : ℝ) : ℂ) * neutralEvenFunctional (neutralPoleParameter L) K u ∧
    CCM.poleOddProfile L K ⬝ᵥ u =
      ((1 / (4 * Real.pi) : ℝ) : ℂ) * neutralOddFunctional (neutralPoleParameter L) K u :=
  neutral_native_profile_scaling L K u

theorem neutral_consumer_008 {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (u : Fin (2 * K + 1) → ℂ) :
    CCM.canonicalPoleExponentialMoment 1 L K (neutralRepair (neutralPoleParameter L) K hK u) = 0 ∧
      CCM.canonicalPoleExponentialMoment (-1) L K (neutralRepair (neutralPoleParameter L) K hK u) = 0 :=
  neutralRepair_native_moments hL K hK u

theorem neutral_consumer_009 {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (u : Fin (2 * K + 1) → ℂ) (hu : CCM.BoundaryFlatCoefficients K u) :
    ContDiff ℝ 2 (CCM.localizedFiniteVector L K (neutralRepair (neutralPoleParameter L) K hK u)) :=
  neutralRepair_native_legal_C2 hL K hK u hu

/-- At a degenerate parameter the asserted positive-parameter formula fails;
the denominator hypothesis is load-bearing. -/
theorem neutral_parameter_zero_control :
    neutralEvenFunctional 0 2 CCM.positiveEvenSourceWitness = (-15 / 2 : ℂ) := by
  norm_num [neutralEvenFunctional, CCM.positiveEvenSourceWitness, Fin.sum_univ_succ, CCM.centeredIndex]

/-- A legal corrector is not itself a neutral witness. -/
theorem neutral_corrector_not_neutral_control {L : ℝ} (hL : 0 < L) :
    ¬ (CCM.canonicalPoleExponentialMoment 1 L 2 CCM.positiveEvenSourceWitness = 0 ∧
      CCM.canonicalPoleExponentialMoment (-1) L 2 CCM.positiveEvenSourceWitness = 0) := by
  intro h
  have he := ((CCM.canonicalPoleExponentialMoments_iff_profiles hL 2 _).mp h).1
  have hp := CCM.poleEvenProfile_dot_positiveEvenSourceWitness_re_pos hL
  rw [he, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem neutral_consumer_010 {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Set.Ioo (0 : ℝ) L)
    (hp : Zeta23.paperFT f (Complex.I / 2) = 0)
    (hm : Zeta23.paperFT f (-Complex.I / 2) = 0) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, 3 ≤ K ∧ ∃ u : Fin (2 * K + 1) → ℂ,
      CCM.BoundaryFlatCoefficients K u ∧
      CCM.canonicalPoleExponentialMoment 1 L K u = 0 ∧
      CCM.canonicalPoleExponentialMoment (-1) L K u = 0 ∧
      neutralXSize (CCM.localizedFiniteVector L K u - f) < η :=
  exists_finite_neutral_X_approx hL hf hfc hfs (neutralPhysicalMoments_zero_of_paperFT hp hm) hη

theorem neutral_consumer_011 (hnot : ¬ RiemannHypothesis) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ < L →
      ∃ K : ℕ, 3 ≤ K ∧ ∃ u : Fin (2 * K + 1) → ℂ,
        u ≠ 0 ∧ CCM.BoundaryFlatCoefficients K u ∧
        CCM.canonicalPoleExponentialMoment 1 L K u = 0 ∧
        CCM.canonicalPoleExponentialMoment (-1) L K u = 0 ∧
        (CCM.quadraticForm (CCM.canonicalSourceMatrix L K) u).re < 0 ∧
        ((CCM.quadraticForm (CCM.canonicalSourceMatrix L K) (CCM.evenPart K u)).re < 0 ∨
          (CCM.quadraticForm (CCM.canonicalSourceMatrix L K) (CCM.oddPart K u)).re < 0) :=
  finite_pole_neutral_approximation hnot

/-- Native source-domain instantiation uses the actual compact neutral witness
generated from the supplied actual off-line zero, at a newly selected aperture. -/
theorem neutral_consumer_012 (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∃ K : ℕ, 3 ≤ K ∧ ∃ u : Fin (2 * K + 1) → ℂ,
      u ≠ 0 ∧ CCM.BoundaryFlatCoefficients K u ∧
      CCM.canonicalPoleExponentialMoment 1 L K u = 0 ∧
      CCM.canonicalPoleExponentialMoment (-1) L K u = 0 ∧
      (CCM.quadraticForm (CCM.canonicalSourceMatrix L K) u).re < 0 := by
  obtain ⟨L₀,hL₀,hall⟩ := eventually_finite_neutral_negative_of_off_line_zero ρ hoff
  obtain ⟨K,hK,u,hune,hu,hp,hm,hQ,_hparity⟩ := hall (L₀+1) (by linarith)
  exact ⟨L₀+1,by linarith,K,hK,u,hune,hu,hp,hm,hQ⟩

theorem neutral_consumer_013 {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (u : Fin (2 * K + 1) → ℂ) (hu : CCM.BoundaryFlatCoefficients K u)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfs : Function.support f ⊆ Set.Icc (0 : ℝ) L)
    (hp : Zeta23.paperFT f (Complex.I / 2) = 0)
    (hm : Zeta23.paperFT f (-Complex.I / 2) = 0) :
    0 < neutralRepairXBound L ∧
      neutralXSize (CCM.localizedFiniteVector L K (neutralRepair (neutralPoleParameter L) K hK u) - f) ≤
        neutralRepairXBound L * neutralXSize (CCM.localizedFiniteVector L K u - f) :=
  neutralRepair_X_bound_fixed_aperture hL K hK u hu hf hfc hfs (neutralPhysicalMoments_zero_of_paperFT hp hm)

theorem neutral_consumer_014 {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (hu : CCM.BoundaryFlatCoefficients K u)
    (hp : CCM.canonicalPoleExponentialMoment 1 L K u = 0)
    (hm : CCM.canonicalPoleExponentialMoment (-1) L K u = 0) :
    CCM.BoundaryFlatCoefficients K (CCM.evenPart K u) ∧
    CCM.BoundaryFlatCoefficients K (CCM.oddPart K u) ∧
    (CCM.canonicalPoleExponentialMoment 1 L K (CCM.evenPart K u) = 0 ∧
      CCM.canonicalPoleExponentialMoment (-1) L K (CCM.evenPart K u) = 0) ∧
    (CCM.canonicalPoleExponentialMoment 1 L K (CCM.oddPart K u) = 0 ∧
      CCM.canonicalPoleExponentialMoment (-1) L K (CCM.oddPart K u) = 0) :=
  neutral_parity_components hL K u hu hp hm

theorem neutral_zero_trial_control (a : ℝ) (K : ℕ) (hK : 2 ≤ K) :
    neutralRepair a K hK 0 = 0 := by
  simp [neutralRepair,neutralEvenFunctional,neutralOddFunctional]

theorem neutral_odd_unscaled_control :
    (fun i : Fin (2 * 2 + 1) => (CCM.centeredIndex 2 i : ℂ) * CCM.positiveEvenSourceWitness i) ≠
      CCM.oddSourceWitnessK2 := by
  intro h
  have h0 := congrFun h ⟨0,by decide⟩
  norm_num [CCM.centeredIndex,CCM.positiveEvenSourceWitness,CCM.oddSourceWitnessK2] at h0

#print axioms Zeta23.OPICARound2.neutralRepair_exact
#print axioms Zeta23.OPICARound2.neutralRepair_native_moments
#print axioms Zeta23.OPICARound2.neutralRepair_native_legal_C2
#print axioms Zeta23.OPICARound2.neutralRepair_X_cost
#print axioms Zeta23.OPICARound2.exists_finite_neutral_X_approx
#print axioms Zeta23.OPICARound2.finite_pole_neutral_approximation
#print axioms Zeta23.OPICARound2.neutralRepair_X_bound_fixed_aperture
#print axioms Zeta23.OPICARound2.neutral_parity_components

end Zeta23.OPICARound2.Validation
