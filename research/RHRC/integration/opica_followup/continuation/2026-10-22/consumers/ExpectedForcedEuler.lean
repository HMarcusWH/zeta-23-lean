import Zeta23.OPICAFollowup.ForcedEuler

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.zero_profile_forced_euler`
and `Zeta23.OPICAFollowup.zero_profile_not_homogeneous_operator_vector` (R2-S1b).

Definition audits pin the test class, the distributional Euler image -∫ h (x² φ')' and the
explicit derivative. Both roots are restated in full. Domain consumers check:
- the test class is non-degenerate (an independent smooth bump at 2 belongs to it);
- the atoms are seen by actual tests: on an independent bump at 1 the Euler image of the actual
  zero profile differs from its ordinary part κ ∫ (h - 1) φ by exactly κ ≠ 0;
- the jump clause agrees with the Stage 9 jump -κ/n² and its one-sided derivatives are unique;
- the explicit derivative is the right derivative on (0, ∞) and the a.e. derivative;
- at the non-zero parameter ρ = 3/4 the same forced Euler identity holds and its Euler image is
  not a function, so the construction-level statements are exercised. The zero-dependent roots
  need an actual zero, which Mathlib cannot exhibit. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology ContDiff
open Zeta23.OPICAFollowup
namespace OPICAForcedEulerIndependent

/-! ### Definition audits -/

theorem audit_positiveAxisTest (φ : ℝ → ℂ) :
    PositiveAxisTest φ ↔ ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi 0 := Iff.rfl

theorem audit_eulerImage (ρ : ℂ) (φ : ℝ → ℂ) : eulerImage ρ φ =
    -∫ x in Ioi 0, zeroProfile ρ x * deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv φ y) x := rfl

theorem audit_zeroProfileDeriv (ρ : ℂ) (x : ℝ) :
    zeroProfileDeriv ρ x = -(srhoCellDeriv ρ ⌊x⌋₊ x / normalizationBrho ρ) := rfl

/-! ### Restated roots -/

theorem expected_zero_profile_forced_euler (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = spectralKappa ρ * ((∫ x in Ioi 0, (zeroProfile ρ x - 1) * φ x) +
        ∑' n : ℕ, φ (n + 1))) ∧
    (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * deriv (zeroProfile ρ) x * deriv φ x) = eulerImage ρ φ) ∧
    (∀ x : ℝ, 0 < x → x ∉ Set.range (fun n : ℕ => (n : ℝ)) →
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * deriv (zeroProfile ρ) y)
        (spectralKappa ρ * (1 - zeroProfile ρ x)) x) ∧
    (∀ n : ℕ, 1 ≤ n → ContinuousAt (zeroProfile ρ) n ∧
      ∃ dR dL : ℂ, HasDerivWithinAt (zeroProfile ρ) dR (Ici (n : ℝ)) n ∧
        HasDerivWithinAt (zeroProfile ρ) dL (Iic (n : ℝ)) n ∧
        (n : ℂ) ^ 2 * (dR - dL) = -spectralKappa ρ) :=
  zero_profile_forced_euler ρ hz h0 h1

theorem expected_zero_profile_not_homogeneous_operator_vector (ρ : ℂ) (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    spectralKappa ρ ≠ 0 ∧
    (¬ ∃ g : ℝ → ℂ, LocallyIntegrableOn g (Ioi 0) ∧
      ∀ φ : ℝ → ℂ, PositiveAxisTest φ → eulerImage ρ φ = ∫ x in Ioi 0, g x * φ x) ∧
    (¬ ∃ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioi 0)) ∧
      ∀ φ : ℝ → ℂ, PositiveAxisTest φ → eulerImage ρ φ = ∫ x in Ioi 0, g x * φ x) ∧
    (∀ c : ℂ, ¬ ∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = c * ∫ x in Ioi 0, zeroProfile ρ x * φ x) ∧
    LogFormDomain (zeroProfile ρ) (zeroProfileDeriv ρ) ∧
    logForm (zeroProfileDeriv ρ) =
      (∫ t, ‖logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t‖ ^ 2) +
        1 / 4 * ∫ x in Ioi 0, ‖zeroProfile ρ x‖ ^ 2 :=
  zero_profile_not_homogeneous_operator_vector ρ hz h0 h1

/-! ### Domain consumers -/

/-- An independent bump of radius 1/2 at a point c ≥ 1. -/
def bumpAt (c : ℝ) : ContDiffBump c := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

lemma tsupport_bumpAt (c : ℝ) : tsupport (fun x => ((bumpAt c x : ℝ) : ℂ)) ⊆ Icc (c - 1 / 2) (c + 1 / 2) := by
  refine (tsupport_comp_subset Complex.ofReal_zero (bumpAt c)).trans ?_
  rw [(bumpAt c).tsupport_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  change -(1 / 2 : ℝ) ≤ x - c ∧ x - c ≤ 1 / 2 at hx
  constructor <;> linarith [hx.1, hx.2]

theorem expected_test_bump {c : ℝ} (hc : 1 ≤ c) : PositiveAxisTest (fun x => ((bumpAt c x : ℝ) : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp (bumpAt c).contDiff,
    (bumpAt c).hasCompactSupport.comp_left Complex.ofReal_zero,
    (tsupport_bumpAt c).trans fun x hx => by simp only [mem_Ioi]; linarith [hx.1]⟩

/-- The test class is non-degenerate: the bump at 2 is a test with value 1 at 2. -/
theorem expected_test_class_nondegenerate :
    PositiveAxisTest (fun x => ((bumpAt 2 x : ℝ) : ℂ)) ∧ ((bumpAt 2 2 : ℝ) : ℂ) = 1 := by
  refine ⟨expected_test_bump (by norm_num), ?_⟩
  rw [(bumpAt 2).one_of_mem_closedBall (Metric.mem_closedBall_self (bumpAt _).rIn_pos.le), Complex.ofReal_one]

/-- The atoms are seen by actual tests: on the bump at 1 the Euler image of the actual zero
profile exceeds its ordinary part by exactly κ ≠ 0. -/
theorem expected_atom_detected (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    eulerImage ρ (fun x => ((bumpAt 1 x : ℝ) : ℂ)) -
        spectralKappa ρ * (∫ x in Ioi 0, (zeroProfile ρ x - 1) * ((bumpAt 1 x : ℝ) : ℂ)) =
      spectralKappa ρ ∧ spectralKappa ρ ≠ 0 := by
  have hT := expected_test_bump (le_refl (1 : ℝ))
  have hsum : ∑' n : ℕ, ((bumpAt 1 ((n : ℝ) + 1) : ℝ) : ℂ) = 1 := by
    rw [tsum_eq_single 0 fun n hn => ?_]
    · simp [(bumpAt 1).one_of_mem_closedBall (Metric.mem_closedBall_self (bumpAt _).rIn_pos.le)]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      refine image_eq_zero_of_notMem_tsupport (f := fun x => ((bumpAt 1 x : ℝ) : ℂ)) fun h => ?_
      have := (tsupport_bumpAt 1 h).2
      linarith
  refine ⟨?_, (zero_profile_not_homogeneous_operator_vector ρ hz h0 h1).1⟩
  rw [(zero_profile_forced_euler ρ hz h0 h1).1 _ hT, hsum]; ring

/-- The jump clause agrees with the Stage 9 jump -κ/n², and any one-sided derivatives satisfy
it (they are unique). -/
theorem expected_jump_matches_stage9 (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (n : ℕ) (dR dL : ℂ)
    (hR : HasDerivWithinAt (zeroProfile ρ) dR (Ici ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ))
    (hL : HasDerivWithinAt (zeroProfile ρ) dL (Iic ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ)) :
    ((n + 1 : ℕ) : ℂ) ^ 2 * (dR - dL) = -spectralKappa ρ ∧
      dR - dL = -spectralKappa ρ / ((n + 1 : ℕ) : ℂ) ^ 2 := by
  obtain ⟨-, dR', dL', hR', hL', hj⟩ := (zero_profile_forced_euler ρ hz h0 h1).2.2.2 (n + 1) (by omega)
  have e1 : dR = dR' := (uniqueDiffWithinAt_Ici _).eq_deriv _ hR hR'
  have e2 : dL = dL' := (uniqueDiffWithinAt_Iic _).eq_deriv _ hL hL'
  obtain ⟨dR9, dL9, hR9, hL9, hj9⟩ := (zero_profile_tail_and_jumps ρ hz h0 h1).2.2.2.2.1 n
  have e3 : dR = dR9 := (uniqueDiffWithinAt_Ici _).eq_deriv _ hR hR9
  have e4 : dL = dL9 := (uniqueDiffWithinAt_Iic _).eq_deriv _ hL hL9
  exact ⟨by rw [e1, e2]; exact hj, by rw [e3, e4]; exact hj9⟩

/-- The explicit derivative is the right derivative on (0, ∞) and equals deriv h between
integers. -/
theorem expected_explicit_derivative (ρ : ℂ) :
    (∀ x : ℝ, 0 < x → HasDerivWithinAt (zeroProfile ρ) (zeroProfileDeriv ρ x) (Ioi x) x) ∧
    (∀ x : ℝ, 0 < x → x ∉ Set.range (fun n : ℕ => (n : ℝ)) →
      deriv (zeroProfile ρ) x = zeroProfileDeriv ρ x) :=
  ⟨fun _ hx => hasDerivWithinAt_zeroProfile_Ioi ρ hx, fun _ hx hn => deriv_zeroProfile_eq hx hn⟩

/-- Construction level at the non-zero parameter ρ = 3/4: the forced Euler identity holds and
its Euler image is not given by any function integrable on [1/2, 3/2]. -/
theorem expected_construction_nonvacuous :
    spectralKappa (3 / 4) = 3 / 16 ∧
    (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage (3 / 4) φ = spectralKappa (3 / 4) *
        ((∫ x in Ioi 0, (zeroProfile (3 / 4) x - 1) * φ x) + ∑' n : ℕ, φ (n + 1))) ∧
    (¬ ∃ g : ℝ → ℂ, IntegrableOn g (Icc (1 / 2) (3 / 2)) ∧
      ∀ φ : ℝ → ℂ, PositiveAxisTest φ → eulerImage (3 / 4) φ = ∫ x in Ioi 0, g x * φ x) := by
  have h0 : (0 : ℝ) < (3 / 4 : ℂ).re := by norm_num
  have h1 : (3 / 4 : ℂ).re < 1 := by norm_num
  have hh : (3 / 4 : ℂ) ≠ 1 / 2 := by norm_num
  have hk : spectralKappa (3 / 4) = 3 / 16 := by unfold spectralKappa; norm_num
  refine ⟨hk, fun φ hφ => (forced_euler_identity h0 h1 hh hφ).1, fun ⟨g, hg, hrep⟩ =>
    eulerImage_not_function h0 h1 hh (by rw [hk]; norm_num) hg hrep⟩

end OPICAForcedEulerIndependent
#print axioms Zeta23.OPICAFollowup.zero_profile_forced_euler
#print axioms Zeta23.OPICAFollowup.zero_profile_not_homogeneous_operator_vector
#print axioms OPICAForcedEulerIndependent.audit_eulerImage
#print axioms OPICAForcedEulerIndependent.expected_zero_profile_forced_euler
#print axioms OPICAForcedEulerIndependent.expected_zero_profile_not_homogeneous_operator_vector
#print axioms OPICAForcedEulerIndependent.expected_test_class_nondegenerate
#print axioms OPICAForcedEulerIndependent.expected_atom_detected
#print axioms OPICAForcedEulerIndependent.expected_jump_matches_stage9
#print axioms OPICAForcedEulerIndependent.expected_explicit_derivative
#print axioms OPICAForcedEulerIndependent.expected_construction_nonvacuous
