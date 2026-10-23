import Zeta23.OPICAFollowup.ZeroProfiles

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.zero_profile_regular_selfdual`
and `Zeta23.OPICAFollowup.zero_profile_tail_and_jumps` (R2-S1a).

Definition audits pin κ = ρ(1 - ρ) and h = 1 - S_ρ(|x|)/b_ρ to the actual CP1 finite sums and
normalization. Both roots are restated in full. Domain consumers check:
- h is one minus the actual zero-measure density on the whole line;
- h(0) = ∫ h = 𝓕h(0) = 1 (Fourier inversion at the origin is consistent);
- the one-sided derivatives in the jump clause are unique, so the clause is not vacuous;
- the lattice values h(n) are absolutely summable (paper: absolute convergence of Σ h(n));
- the construction-level clauses (continuity, evenness, h = 1 on [-1, 1], exact cell
  derivatives and the jump formula) hold at the non-zero parameter ρ = 3/4. The zero-dependent
  clauses need an actual zero, which Mathlib cannot exhibit. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap
open Zeta23.OPICAFollowup
namespace OPICAZeroProfilesIndependent

/-! ### Definition audits -/

theorem audit_spectralKappa (ρ : ℂ) : spectralKappa ρ = ρ * (1 - ρ) := rfl

theorem audit_zeroProfile (ρ : ℂ) (x : ℝ) :
    zeroProfile ρ x = 1 - finiteSumSrho ρ |x| / normalizationBrho ρ := rfl

theorem audit_srhoCellDeriv (ρ : ℂ) (n : ℕ) (y : ℝ) : srhoCellDeriv ρ n y =
    -ρ * (y : ℂ) ^ (-ρ - 1) * ∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (ρ - 1) -
      (ρ - 1) * (y : ℂ) ^ (ρ - 1 - 1) * ∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (-ρ) := rfl

/-! ### Restated roots -/

theorem expected_zero_profile_regular_selfdual (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    (∀ x : ℝ, zeroProfile ρ (-x) = zeroProfile ρ x) ∧
    Continuous (zeroProfile ρ) ∧
    Integrable (zeroProfile ρ) ∧ MemLp (zeroProfile ρ) 2 ∧
    (∀ x : ℝ, |x| ≤ 1 → zeroProfile ρ x = 1) ∧
    𝓕 (zeroProfile ρ) = zeroProfile ρ ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∫ x, zeroProfile ρ x * (𝓕 φ : 𝓢(ℝ, ℂ)) x) = ∫ x, zeroProfile ρ x * φ x) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (zeroMeasure ρ).integral φ =
      (∫ x, φ x) + φ 0 - dilatedCombDistribution 0 φ - ∫ x, zeroProfile ρ x * φ x) ∧
    (∫ x, zeroProfile ρ x) = 1 ∧
    (∫ x in Ioi (0 : ℝ), zeroProfile ρ x) = 1 / 2 :=
  zero_profile_regular_selfdual ρ hz h0 h1

theorem expected_zero_profile_tail_and_jumps (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖zeroProfile ρ x - spectralKappa ρ * (bernoulliTwo |x| : ℂ) / (2 * ((|x| : ℝ) : ℂ) ^ 2)‖ ≤
        C * |x| ^ (-3 : ℝ)) ∧
    (∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) →
      HasDerivAt (zeroProfile ρ) (-(srhoCellDeriv ρ n x / normalizationBrho ρ)) x) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) → 1 ≤ x →
      ‖deriv (zeroProfile ρ) x‖ ≤ C * x ^ (-2 : ℝ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) → 1 ≤ x →
      ‖deriv (zeroProfile ρ) x - spectralKappa ρ * (bernoulliOneRight x : ℂ) / (x : ℂ) ^ 2‖ ≤
        C * x ^ (-4 : ℝ)) ∧
    (∀ n : ℕ, ∃ dR dL : ℂ,
      HasDerivWithinAt (zeroProfile ρ) dR (Ici ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) ∧
      HasDerivWithinAt (zeroProfile ρ) dL (Iic ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) ∧
      dR - dL = -spectralKappa ρ / ((n + 1 : ℕ) : ℂ) ^ 2) ∧
    HasDerivWithinAt (zeroProfile ρ) 0 (Iic (1 : ℝ)) 1 ∧
    MemLp (fun x : ℝ => (x : ℂ) * deriv (zeroProfile ρ) x) 2 (volume.restrict (Ioi 0)) :=
  zero_profile_tail_and_jumps ρ hz h0 h1

/-! ### Domain consumers -/

/-- h is one minus the density of the actual normalized zero measure on the whole line. -/
theorem expected_profile_is_one_minus_zero_density {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (x : ℝ) : zeroProfile ρ x = 1 - coPoissonComplexDensity ρ x := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  unfold zeroProfile coPoissonComplexDensity
  rw [coPoissonOriginNormalizer_eq_brho hρ0 hρ1]

/-- h(0) = ∫ h = 𝓕h(0) = 1. -/
theorem expected_origin_value {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    zeroProfile ρ 0 = 1 ∧ 𝓕 (zeroProfile ρ) 0 = 1 ∧ ∫ x, zeroProfile ρ x = 1 := by
  obtain ⟨-, -, -, -, hone, hF, -, -, hint, -⟩ := zero_profile_regular_selfdual ρ hz h0 h1
  have h00 : zeroProfile ρ 0 = 1 := hone 0 (by simp)
  exact ⟨h00, by rw [hF, h00], hint⟩

/-- The one-sided derivatives of the jump clause are unique: any right and left derivatives at
n + 1 satisfy the jump identity. -/
theorem expected_jump_unique {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (n : ℕ) (dR dL : ℂ)
    (hR : HasDerivWithinAt (zeroProfile ρ) dR (Ici ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ))
    (hL : HasDerivWithinAt (zeroProfile ρ) dL (Iic ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ)) :
    dR - dL = -spectralKappa ρ / ((n + 1 : ℕ) : ℂ) ^ 2 := by
  obtain ⟨dR', dL', hR', hL', hj⟩ := (zero_profile_tail_and_jumps ρ hz h0 h1).2.2.2.2.1 n
  have e1 : dR = dR' := (uniqueDiffWithinAt_Ici _).eq_deriv _ hR hR'
  have e2 : dL = dL' := (uniqueDiffWithinAt_Iic _).eq_deriv _ hL hL'
  rw [e1, e2, hj]

/-- The lattice values h(n) are absolutely summable. -/
theorem expected_lattice_values_summable {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : Summable (fun n : ℕ => ‖zeroProfile ρ n‖) := by
  obtain ⟨C, hC0, hC⟩ := (zero_profile_tail_and_jumps ρ hz h0 h1).1
  set M : ℝ := ‖spectralKappa ρ‖ / 2 + C
  have hsum : Summable (fun n : ℕ => M * ((n : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num)).mul_left M
  refine Summable.of_norm_bounded_eventually (g := fun n : ℕ => M * ((n : ℝ) ^ 2)⁻¹) hsum ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have habs : |(n : ℝ)| = n := abs_of_pos hn0
  have ht := hC n (by rw [habs]; exact hn1)
  rw [habs] at ht
  rw [norm_norm]
  have hB : abs (bernoulliTwo n) ≤ 1 := abs_bernoulliTwo_le _
  have hmain : ‖spectralKappa ρ * (bernoulliTwo n : ℂ) / (2 * ((n : ℝ) : ℂ) ^ 2)‖ ≤
      ‖spectralKappa ρ‖ / 2 * ((n : ℝ) ^ 2)⁻¹ := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hn0]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, div_le_iff₀ (by positivity)]
    calc ‖spectralKappa ρ‖ * abs (bernoulliTwo n) ≤ ‖spectralKappa ρ‖ * 1 :=
          mul_le_mul_of_nonneg_left hB (norm_nonneg _)
      _ = ‖spectralKappa ρ‖ / 2 * ((n : ℝ) ^ 2)⁻¹ * (2 * (n : ℝ) ^ 2) := by field_simp
  have h3 : (n : ℝ) ^ (-3 : ℝ) ≤ ((n : ℝ) ^ 2)⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_neg hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  calc ‖zeroProfile ρ n‖ ≤ ‖spectralKappa ρ * (bernoulliTwo n : ℂ) / (2 * ((n : ℝ) : ℂ) ^ 2)‖ +
        ‖zeroProfile ρ n - spectralKappa ρ * (bernoulliTwo n : ℂ) / (2 * ((n : ℝ) : ℂ) ^ 2)‖ :=
        norm_le_insert' _ _
    _ ≤ ‖spectralKappa ρ‖ / 2 * ((n : ℝ) ^ 2)⁻¹ + C * ((n : ℝ) ^ 2)⁻¹ := by
        gcongr; exact ht.trans (mul_le_mul_of_nonneg_left h3 hC0)
    _ = M * ((n : ℝ) ^ 2)⁻¹ := by ring

/-- Construction-level non-vacuity at ρ = 3/4 (ζ(3/4) ≠ 0, so no zero hypothesis is used):
continuity, evenness, h = 1 on [-1, 1], exact cell derivatives and the jump -κ/n². -/
theorem expected_construction_nonvacuous :
    Continuous (zeroProfile (3 / 4)) ∧ (∀ x, zeroProfile (3 / 4) (-x) = zeroProfile (3 / 4) x) ∧
    (∀ x : ℝ, |x| ≤ 1 → zeroProfile (3 / 4) x = 1) ∧
    (∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) →
      HasDerivAt (zeroProfile (3 / 4)) (-(srhoCellDeriv (3 / 4) n x / normalizationBrho (3 / 4))) x) ∧
    (∀ n : ℕ, -(srhoCellDeriv (3 / 4) (n + 1) (n + 1 : ℕ) / normalizationBrho (3 / 4)) -
        -(srhoCellDeriv (3 / 4) n (n + 1 : ℕ) / normalizationBrho (3 / 4)) =
      -spectralKappa (3 / 4) / ((n + 1 : ℕ) : ℂ) ^ 2) :=
  ⟨continuous_zeroProfile _, zeroProfile_neg _, fun x hx => zeroProfile_eq_one _ hx,
    fun n x hx => hasDerivAt_zeroProfile_cell _ hx,
    fun n => zeroProfile_deriv_jump (by norm_num) (by norm_num) (by norm_num) n⟩

end OPICAZeroProfilesIndependent
#print axioms Zeta23.OPICAFollowup.zero_profile_regular_selfdual
#print axioms Zeta23.OPICAFollowup.zero_profile_tail_and_jumps
#print axioms OPICAZeroProfilesIndependent.audit_zeroProfile
#print axioms OPICAZeroProfilesIndependent.audit_srhoCellDeriv
#print axioms OPICAZeroProfilesIndependent.expected_zero_profile_regular_selfdual
#print axioms OPICAZeroProfilesIndependent.expected_zero_profile_tail_and_jumps
#print axioms OPICAZeroProfilesIndependent.expected_profile_is_one_minus_zero_density
#print axioms OPICAZeroProfilesIndependent.expected_origin_value
#print axioms OPICAZeroProfilesIndependent.expected_jump_unique
#print axioms OPICAZeroProfilesIndependent.expected_lattice_values_summable
#print axioms OPICAZeroProfilesIndependent.expected_construction_nonvacuous
