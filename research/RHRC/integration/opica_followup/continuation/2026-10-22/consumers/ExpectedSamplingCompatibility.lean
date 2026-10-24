import Zeta23.OPICAFollowup.SamplingCompatibility

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.native_sampling_gram_identity`
and `Zeta23.OPICAFollowup.native_sampling_form_positive` (R2-S2).

Definition audits pin the linear-first pairings N_ij = ∫_0^∞ h_i conj h_j and
Q_ij = ∫_0^∞ x² h_i' conj h_j' and the sample defect b_i = Σ_{n ≥ 1} h_i(n) - 1/2. Both roots are
restated in full. Domain consumers check:
- the diagonal: N_ii > 0 is real, Q_ii - N_ii/4 is real and nonnegative;
- at a zero on the critical line (κ real) the self-pairing forces b real;
- conjugate coincidence: for an actual zero ρ, conj ρ is an actual zero with κ(conj ρ) = conj κ(ρ),
  the divided identity is unavailable, and the retained undivided identity gives
  b_ρ = conj b_(conj ρ);
- the finite-cell pairing and the generic Gram positivity are construction-level: they hold at
  the non-zero parameters ρ = 3/4, σ = 2/3. The zero-dependent roots need an actual zero, which
  Mathlib cannot exhibit;
- the finite countercontrol is non-vacuous: with A = 1, g = 1 and the nonreal parameter κ = i,
  N_00 = 1/2 > 0 and the identities (S2.1) hold. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology ComplexConjugate ComplexOrder
open Zeta23.OPICAFollowup
namespace OPICASamplingCompatibilityIndependent

/-! ### Definition audits -/

theorem audit_profileGram (ρ σ : ℂ) :
    profileGram ρ σ = ∫ x in Ioi (0 : ℝ), zeroProfile ρ x * conj (zeroProfile σ x) := rfl

theorem audit_profileFormGram (ρ σ : ℂ) : profileFormGram ρ σ =
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * deriv (zeroProfile ρ) x * conj (deriv (zeroProfile σ) x) := rfl

theorem audit_profileSampleDefect (ρ : ℂ) :
    profileSampleDefect ρ = (∑' n : ℕ, zeroProfile ρ (n + 1)) - 1 / 2 := rfl

/-! ### Restated roots -/

theorem expected_native_sampling_gram_identity {ι : Type*} (ρ : ι → ℂ)
    (hz : ∀ i, riemannZeta (ρ i) = 0) (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) :
    (∀ i, Summable (fun n : ℕ => zeroProfile (ρ i) (n + 1))) ∧
    (∀ i j, IntegrableOn (fun x => zeroProfile (ρ i) x * conj (zeroProfile (ρ j) x)) (Ioi 0)) ∧
    (∀ i j, IntegrableOn (fun x : ℝ => (x : ℂ) ^ 2 * deriv (zeroProfile (ρ i)) x *
      conj (deriv (zeroProfile (ρ j)) x)) (Ioi 0)) ∧
    (∀ i, ∫ x in Ioi (0 : ℝ), zeroProfile (ρ i) x = 1 / 2) ∧
    (∀ i j (N : ℕ), ∫ x in (0 : ℝ)..((N : ℝ) + 1),
      (x : ℂ) ^ 2 * zeroProfileDeriv (ρ i) x * conj (zeroProfileDeriv (ρ j) x) =
        spectralKappa (ρ i) * ((∫ x in (0 : ℝ)..((N : ℝ) + 1),
          (zeroProfile (ρ i) x - 1) * conj (zeroProfile (ρ j) x)) +
            ∑ m ∈ Finset.range N, conj (zeroProfile (ρ j) (m + 1))) +
        (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv (ρ i) N ((N : ℝ) + 1) / normalizationBrho (ρ i)) *
          conj (zeroProfile (ρ j) ((N : ℝ) + 1))) ∧
    (∀ i j, Tendsto (fun N : ℕ => (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 *
      -(srhoCellDeriv (ρ i) N ((N : ℝ) + 1) / normalizationBrho (ρ i)) *
        conj (zeroProfile (ρ j) ((N : ℝ) + 1))) atTop (𝓝 0)) ∧
    (∀ i j, profileFormGram (ρ i) (ρ j) =
      spectralKappa (ρ i) * (profileGram (ρ i) (ρ j) + conj (profileSampleDefect (ρ j)))) ∧
    (∀ i j, profileFormGram (ρ i) (ρ j) =
      conj (spectralKappa (ρ j)) * (profileGram (ρ i) (ρ j) + profileSampleDefect (ρ i))) :=
  native_sampling_gram_identity ρ hz h0 h1

theorem expected_native_sampling_form_positive {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (hz : ∀ i, riemannZeta (ρ i) = 0) (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) :
    (Matrix.of fun i j => profileGram (ρ i) (ρ j)).PosSemidef ∧
    (Matrix.of fun i j => profileFormGram (ρ i) (ρ j)).PosSemidef ∧
    (Matrix.of fun i j => profileFormGram (ρ i) (ρ j) - profileGram (ρ i) (ρ j) / 4).PosSemidef ∧
    (∀ i j, (spectralKappa (ρ i) - conj (spectralKappa (ρ j))) * profileGram (ρ i) (ρ j) =
      conj (spectralKappa (ρ j)) * profileSampleDefect (ρ i) -
        spectralKappa (ρ i) * conj (profileSampleDefect (ρ j))) ∧
    (∀ i j, spectralKappa (ρ i) - conj (spectralKappa (ρ j)) ≠ 0 →
      profileGram (ρ i) (ρ j) / (spectralKappa (ρ i) * conj (spectralKappa (ρ j))) =
        (profileSampleDefect (ρ i) / spectralKappa (ρ i) -
          conj (profileSampleDefect (ρ j) / spectralKappa (ρ j))) /
            (spectralKappa (ρ i) - conj (spectralKappa (ρ j)))) ∧
    (∀ i, (spectralKappa (ρ i)).im ≠ 0 →
      (profileSampleDefect (ρ i) / spectralKappa (ρ i)).im / (spectralKappa (ρ i)).im =
        (∫ x in Ioi (0 : ℝ), ‖zeroProfile (ρ i) x‖ ^ 2) / ‖spectralKappa (ρ i)‖ ^ 2 ∧
      0 < ∫ x in Ioi (0 : ℝ), ‖zeroProfile (ρ i) x‖ ^ 2) :=
  native_sampling_form_positive ρ hz h0 h1

/-! ### Domain consumers -/

/-- The diagonal of the actual Gram data: N_ii > 0 is real and Q_ii - N_ii/4 ≥ 0. -/
theorem expected_diagonal (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    0 < (profileGram ρ ρ).re ∧ (profileGram ρ ρ).im = 0 ∧
      0 ≤ profileFormGram ρ ρ - profileGram ρ ρ / 4 := by
  obtain ⟨-, -, hPSD, -⟩ := native_sampling_form_positive (fun _ : Unit => ρ) (fun _ => hz)
    (fun _ => h0) (fun _ => h1)
  have hN : profileGram ρ ρ = ((∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [profileGram, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      simp only; push_cast; rw [Complex.mul_conj'])
  have hpos := (native_sampling_form_positive (fun _ : Unit => ρ) (fun _ => hz) (fun _ => h0)
    (fun _ => h1)).2.2.2.2.2
  refine ⟨?_, by rw [hN]; simp, ?_⟩
  · have hint : 0 < ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 := by
      by_cases hk : (spectralKappa ρ).im = 0
      · -- independent of the imaginary part: h = 1 on (0, 1]
        have hI : IntegrableOn (fun x => ‖zeroProfile ρ x‖ ^ 2) (Ioi 0) :=
          ((memLp_two_zeroProfile hz h0 h1).restrict (Ioi 0)).integrable_norm_pow (p := 2) two_ne_zero
        have h1' : (∫ x in Ioc (0 : ℝ) 1, ‖zeroProfile ρ x‖ ^ 2) = 1 := by
          rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (1 : ℝ)) fun x hx => by
            simp only [zeroProfile_eq_one ρ (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩), norm_one, one_pow]]
          simp
        have hle := setIntegral_mono_set hI (Eventually.of_forall fun x => sq_nonneg ‖zeroProfile ρ x‖)
          (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0).eventuallyLE
        linarith
      · exact (hpos () hk).2
    rw [hN]; simpa using hint
  · have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hPSD).2 (fun _ => 1)
    simpa [dotProduct, Matrix.mulVec] using this

/-- On the critical line κ is real and the self-pairing forces the sample defect to be real. -/
theorem expected_online_sample_real (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hk : (spectralKappa ρ).im = 0) : (profileSampleDefect ρ).im = 0 := by
  obtain ⟨-, -, -, hU, -⟩ := native_sampling_form_positive (fun _ : Unit => ρ) (fun _ => hz)
    (fun _ => h0) (fun _ => h1)
  have h := congrArg Complex.im (hU () ())
  have hκ : spectralKappa ρ ≠ 0 := by
    obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
    exact mul_ne_zero hρ0 (sub_ne_zero.mpr (Ne.symm hρ1))
  have hre : (spectralKappa ρ).re ≠ 0 := fun hr => hκ (Complex.ext hr hk)
  simp only [Complex.mul_im, Complex.sub_im, Complex.sub_re, Complex.conj_re, Complex.conj_im, hk,
    neg_zero, sub_self, zero_mul, add_zero] at h
  have : 2 * (spectralKappa ρ).re * (profileSampleDefect ρ).im = 0 := by linarith
  rcases mul_eq_zero.mp this with h2 | h2
  · exact absurd (by linarith : (spectralKappa ρ).re = 0) hre
  · exact h2

/-- Conjugate coincidence: conj ρ is an actual zero, κ(conj ρ) = conj κ(ρ), the divided identity
does not apply, and the retained undivided identity gives b_ρ = conj b_(conj ρ). -/
theorem expected_conjugate_coincidence (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    riemannZeta (conj ρ) = 0 ∧ spectralKappa (conj ρ) = conj (spectralKappa ρ) ∧
      spectralKappa ρ - conj (spectralKappa (conj ρ)) = 0 ∧
      profileSampleDefect ρ = conj (profileSampleDefect (conj ρ)) := by
  have hz' : riemannZeta (conj ρ) = 0 := by rw [riemannZeta_conj, hz, map_zero]
  have hκ : spectralKappa (conj ρ) = conj (spectralKappa ρ) := by
    simp [spectralKappa, map_mul, map_sub, map_one]
  let r : Bool → ℂ := fun b => if b then ρ else conj ρ
  obtain ⟨-, -, -, hU, -⟩ := native_sampling_form_positive r (fun b => by cases b <;> simp [r, hz, hz'])
    (fun b => by cases b <;> simp [r, h0]) (fun b => by cases b <;> simp [r, h1])
  have h := hU true false
  simp only [r, if_true, Bool.false_eq_true, if_false, hκ, Complex.conj_conj, sub_self, zero_mul] at h
  have hk0 : spectralKappa ρ ≠ 0 := by
    obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
    exact mul_ne_zero hρ0 (sub_ne_zero.mpr (Ne.symm hρ1))
  refine ⟨hz', hκ, by rw [hκ, Complex.conj_conj, sub_self], ?_⟩
  have : spectralKappa ρ * (profileSampleDefect ρ - conj (profileSampleDefect (conj ρ))) = 0 := by
    linear_combination -h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hk0)

/-- Construction level at the non-zero parameters ρ = 3/4, σ = 2/3: the finite-cell pairing with
its boundary term holds. -/
theorem expected_construction_nonvacuous (N : ℕ) :
    ∫ x in (0 : ℝ)..((N : ℝ) + 1),
      (x : ℂ) ^ 2 * zeroProfileDeriv (3 / 4) x * conj (zeroProfileDeriv (2 / 3) x) =
        spectralKappa (3 / 4) * ((∫ x in (0 : ℝ)..((N : ℝ) + 1),
          (zeroProfile (3 / 4) x - 1) * conj (zeroProfile (2 / 3) x)) +
            ∑ m ∈ Finset.range N, conj (zeroProfile (2 / 3) (m + 1))) +
        (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv (3 / 4) N ((N : ℝ) + 1) / normalizationBrho (3 / 4)) *
          conj (zeroProfile (2 / 3) ((N : ℝ) + 1)) :=
  gram_finite (by norm_num) (by norm_num) (by norm_num) N

/-- The paper's falsification control with a nonreal parameter: A = 1, g = 1, κ = i. -/
theorem expected_countercontrol_nonreal :
    (I : ℂ).im ≠ 0 ∧
    (∑ k : Fin 1, controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k *
      conj (controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k)) = 1 / 2 ∧
    (∑ k : Fin 1, ((1 : ℝ) : ℂ) * controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k *
      conj (controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k)) =
      I * ((∑ k : Fin 1, controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k *
        conj (controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k)) +
        conj (∑ k : Fin 1, ((1 : ℝ) : ℂ) * controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k)) := by
  have hI : (I : ℂ).im ≠ 0 := by simp
  obtain ⟨-, -, h1, -⟩ := finite_countercontrol (ι := Fin 1) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1)
    (fun _ => one_pos) (fun _ => I) (fun _ => hI)
  refine ⟨hI, ?_, h1 0 0⟩
  have hd : ((1 : ℝ) : ℂ) - I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have hd' : (1 : ℂ) + I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have hd'' : (1 : ℂ) - I ≠ 0 := by simpa using hd
  have key : (1 - I) * (1 + I) = (2 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  simp only [controlVector, Fin.sum_univ_one, map_div₀, map_mul, map_sub, Complex.conj_I, map_one,
    Complex.ofReal_one]
  rw [div_mul_div_comm, sub_neg_eq_add, key]
  ring_nf
  rw [Complex.I_sq]
  ring

end OPICASamplingCompatibilityIndependent
#print axioms Zeta23.OPICAFollowup.native_sampling_gram_identity
#print axioms Zeta23.OPICAFollowup.native_sampling_form_positive
#print axioms OPICASamplingCompatibilityIndependent.audit_profileFormGram
#print axioms OPICASamplingCompatibilityIndependent.expected_native_sampling_gram_identity
#print axioms OPICASamplingCompatibilityIndependent.expected_native_sampling_form_positive
#print axioms OPICASamplingCompatibilityIndependent.expected_diagonal
#print axioms OPICASamplingCompatibilityIndependent.expected_online_sample_real
#print axioms OPICASamplingCompatibilityIndependent.expected_conjugate_coincidence
#print axioms OPICASamplingCompatibilityIndependent.expected_construction_nonvacuous
#print axioms Zeta23.OPICAFollowup.finite_countercontrol
#print axioms OPICASamplingCompatibilityIndependent.expected_countercontrol_nonreal
