import Zeta23.OPICAFollowup.NativeResolvent
import Zeta23.OPICAFollowup.ProfileEulerMaclaurin

/-!
The generic forced resolvent and its exact boundary amplitude (F3). Take an arbitrary parameter
1/2 < Re ρ < 1 with Im ρ ≠ 0, not necessarily a zero of ζ, and put κ = ρ(1 - ρ),
b_ρ = (1 - 2ρ)/κ. The generic forced profile is

  h̃_ρ(x) = 1 - S_ρ(x)/b_ρ - (ζ(ρ)/b_ρ) x^(ρ-1),   x > 0,

with S_ρ the exact finite-sum function of CP1. The boundary amplitude ζ(ρ)/b_ρ is the coefficient of
the homogeneous power.

- **Ends.** On (0, 1), S_ρ = 0, so h̃ = 1 - (ζ(ρ)/b_ρ) x^(ρ-1). It lies in the log form domain near 0
  because Re ρ > 1/2. At infinity the finite-sum Euler-Maclaurin expansion of ZeroProfiles is
  S_ρ = ζ(1-ρ) x^(-ρ) - ζ(ρ) x^(ρ-1) + b_ρ + O(x⁻²). The growing homogeneous term cancels against the
  boundary term exactly, leaving h̃ = -(ζ(1-ρ)/b_ρ) x^(-ρ) + κ B₂({x})/(2x²) + O(x⁻³). The derivative
  satisfies the matching bounds.
- **Force equation.** The power x^(ρ-1) solves the homogeneous cell equation (x² u')' = -κ u and is
  smooth on (0, ∞). Adding it to the Stage 11 Euler identity (valid for every strip parameter
  ≠ 1/2) changes no atom: ∫ x² h̃' φ' = κ (∫ (h̃ - 1) φ + Σ_{n ≥ 1} φ(n)) on positive-axis tests.
- **Resolvent.** The Stage 15 transfer, generalized here to any log-form-domain profile with this
  Euler identity, gives the weak equation (-D² + 1/4 - κ) ψ = κ 𝔤 on Schwartz tests for
  ψ = e^(t/2) h̃(e^t). Since κ is off the cut, ψ is the unique H¹ weak solution, and h̃ is the unique
  log-form-domain solution of the physical equation. ψ has the arithmetic quotient
  κ ζ(1/2 + iξ)/(a - κ) and equals `nativeLogResolvent` κ.
- **Plateau (F3.2).** h̃ ≡ 1 on (0, 1) exactly when ζ(ρ) = 0, and then h̃ is the zero profile.

This is a diagnostic identity, not a zero-exclusion theorem. Nothing here asserts that ζ(ρ) ≠ 0 or
= 0 for any ρ, and no integrability of h̃ is asserted for generic ρ.
-/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff

namespace Zeta23.OPICAFollowup

section Definitions

/-- The boundary amplitude ζ(ρ)/b_ρ: the coefficient of the homogeneous power x^(ρ-1). -/
def boundaryAmplitude (ρ : ℂ) : ℂ := riemannZeta ρ / normalizationBrho ρ

/-- The generic forced profile h̃_ρ(x) = 1 - S_ρ(|x|)/b_ρ - ζ(ρ) |x|^(ρ-1)/b_ρ, built from the
actual finite sums S_ρ (not a continued Dirichlet series). -/
def genericForcedProfile (ρ : ℂ) (x : ℝ) : ℂ :=
  zeroProfile ρ x - boundaryAmplitude ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1)

/-- Its derivative on (0, ∞): h' - (ζ(ρ)/b_ρ)(ρ - 1) x^(ρ-2). -/
def genericForcedProfileDeriv (ρ : ℂ) (x : ℝ) : ℂ :=
  zeroProfileDeriv ρ x - boundaryAmplitude ρ * ((ρ - 1) * (x : ℂ) ^ (ρ - 2))

end Definitions

section Ends

variable {ρ : ℂ}

lemma genericForcedProfile_of_pos (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    genericForcedProfile ρ x = zeroProfile ρ x - boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1) := by
  rw [genericForcedProfile, abs_of_pos hx]

/-- Near zero: h̃(x) = 1 - (ζ(ρ)/b_ρ) x^(ρ-1) on (0, 1]. -/
lemma genericForcedProfile_near_zero (ρ : ℂ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    genericForcedProfile ρ x = 1 - boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1) := by
  rw [genericForcedProfile_of_pos ρ hx, zeroProfile_eq_one ρ (by rw [abs_of_pos hx]; exact hx1)]

lemma genericForcedProfileDeriv_near_zero (ρ : ℂ) {x : ℝ} (hx1 : x < 1) :
    genericForcedProfileDeriv ρ x = -(boundaryAmplitude ρ * ((ρ - 1) * (x : ℂ) ^ (ρ - 2))) := by
  rw [genericForcedProfileDeriv, zeroProfileDeriv]
  rcases lt_or_ge x 0 with h | h
  · rw [Nat.floor_of_nonpos h.le, srhoCellDeriv_zero, zero_div, neg_zero, zero_sub]
  · rw [Nat.floor_eq_zero.mpr hx1, srhoCellDeriv_zero, zero_div, neg_zero, zero_sub]

lemma kappa_eq_brho (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    spectralKappa ρ = -((2 * ρ - 1) / normalizationBrho ρ) := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have h1' : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have h2 : (1 : ℂ) - 2 * ρ ≠ 0 := fun h => hh (by linear_combination -h / 2)
  have h2' : (1 : ℂ) - ρ * 2 ≠ 0 := fun h => h2 (by linear_combination h)
  rw [normalizationBrho, spectralKappa]
  field_simp
  ring

/-- At infinity: h̃(x) = -(ζ(1-ρ)/b_ρ) x^(-ρ) + κ B₂({x})/(2x²) - R_ρ(x)/b_ρ for x ≥ 1, where the
growing homogeneous terms cancel exactly. -/
theorem genericForcedProfile_tail (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) {x : ℝ}
    (hx : 1 ≤ x) :
    genericForcedProfile ρ x = -(riemannZeta (1 - ρ) / normalizationBrho ρ) * (x : ℂ) ^ (-ρ) +
      spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2) -
        srhoRemainder ρ x / normalizationBrho ρ := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
  have hx0 : 0 < x := by linarith
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  rw [genericForcedProfile_of_pos ρ hx0, zeroProfile, abs_of_pos hx0, finiteSumSrho_expansion h0 h1 hx,
    boundaryAmplitude, kappa_eq_brho h0 h1 hh, ← brho_eq h0 h1]
  field_simp
  ring

/-- The derivative at infinity: h̃'(x) = ρ (ζ(1-ρ)/b_ρ) x^(-ρ-1) - (2ρ - 1) B₁({x})/(b_ρ x²) - R'_ρ(x)/b_ρ. -/
theorem genericForcedProfileDeriv_tail (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) {x : ℝ}
    (hx : 1 ≤ x) :
    genericForcedProfileDeriv ρ x = ρ * (riemannZeta (1 - ρ) / normalizationBrho ρ) * (x : ℂ) ^ (-ρ - 1) -
      (2 * ρ - 1) * (bernoulliOneRight x : ℂ) / (normalizationBrho ρ * (x : ℂ) ^ 2) -
        srhoDerivRemainder ρ x / normalizationBrho ρ := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
  have hx0 : 0 < x := by linarith
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hcell : x ∈ Ico (⌊x⌋₊ : ℝ) (⌊x⌋₊ + 1) := ⟨Nat.floor_le hx0.le, Nat.lt_floor_add_one x⟩
  rw [genericForcedProfileDeriv, zeroProfileDeriv, srhoCellDeriv_expansion h0 h1 hcell hx,
    boundaryAmplitude, show ρ - 1 - 1 = ρ - 2 by ring]
  field_simp
  ring

/-- The generic profile is bounded near zero by (1 + |A|) x^(Re ρ - 1). -/
lemma norm_genericForcedProfile_le_near_zero (ρ : ℂ) (h1 : ρ.re < 1) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖genericForcedProfile ρ x‖ ≤ (1 + ‖boundaryAmplitude ρ‖) * x ^ (ρ.re - 1) := by
  rw [genericForcedProfile_near_zero ρ hx hx1]
  have hp : ‖(x : ℂ) ^ (ρ - 1)‖ = x ^ (ρ.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  have hge : 1 ≤ x ^ (ρ.re - 1) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hx1 (by linarith)
  calc ‖1 - boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1)‖ ≤ 1 + ‖boundaryAmplitude ρ‖ * x ^ (ρ.re - 1) := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_one, norm_mul, hp]
    _ ≤ (1 + ‖boundaryAmplitude ρ‖) * x ^ (ρ.re - 1) := by nlinarith [norm_nonneg (boundaryAmplitude ρ)]

/-- The generic profile decays like x^(-Re ρ) at infinity. -/
lemma norm_genericForcedProfile_le_tail (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖genericForcedProfile ρ x‖ ≤ C * x ^ (-ρ.re) := by
  refine ⟨‖riemannZeta (1 - ρ) / normalizationBrho ρ‖ + ‖spectralKappa ρ‖ / 2 +
    srhoRemainderConst ρ / ‖normalizationBrho ρ‖,
    add_nonneg (add_nonneg (norm_nonneg _) (by positivity))
      (div_nonneg (srhoRemainderConst_nonneg ρ) (norm_nonneg _)), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  rw [genericForcedProfile_tail h0 h1 hh hx]
  have hp : ‖(x : ℂ) ^ (-ρ)‖ = x ^ (-ρ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp
  have hx2 : ‖(x : ℂ) ^ 2‖ = x ^ (2 : ℝ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, Real.rpow_two]
  have hB : ‖(bernoulliTwo x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_bernoulliTwo_le x
  have hR := srhoRemainder_norm_le h0 h1 hx0
  have e2 : x ^ (-(2 : ℝ)) ≤ x ^ (-ρ.re) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have e3 : x ^ (-(3 : ℝ)) ≤ x ^ (-ρ.re) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hinv : (x ^ (2 : ℝ))⁻¹ = x ^ (-(2 : ℝ)) := (Real.rpow_neg hx0.le _).symm
  have t1 : ‖-(riemannZeta (1 - ρ) / normalizationBrho ρ) * (x : ℂ) ^ (-ρ)‖ =
      ‖riemannZeta (1 - ρ) / normalizationBrho ρ‖ * x ^ (-ρ.re) := by rw [norm_mul, norm_neg, hp]
  have t2 : ‖spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2)‖ ≤
      ‖spectralKappa ρ‖ / 2 * x ^ (-ρ.re) := by
    rw [norm_div, norm_mul, norm_mul, hx2, Complex.norm_ofNat]
    calc ‖spectralKappa ρ‖ * ‖(bernoulliTwo x : ℂ)‖ / (2 * x ^ (2 : ℝ))
        ≤ ‖spectralKappa ρ‖ * 1 / (2 * x ^ (2 : ℝ)) := by gcongr
      _ = ‖spectralKappa ρ‖ / 2 * (x ^ (2 : ℝ))⁻¹ := by ring
      _ ≤ ‖spectralKappa ρ‖ / 2 * x ^ (-ρ.re) := by rw [hinv]; gcongr
  have t3 : ‖srhoRemainder ρ x / normalizationBrho ρ‖ ≤
      srhoRemainderConst ρ / ‖normalizationBrho ρ‖ * x ^ (-ρ.re) := by
    rw [norm_div, div_mul_eq_mul_div]
    gcongr
    exact hR.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast e3) (srhoRemainderConst_nonneg ρ))
  calc _ ≤ ‖-(riemannZeta (1 - ρ) / normalizationBrho ρ) * (x : ℂ) ^ (-ρ)‖ +
        ‖spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2)‖ +
          ‖srhoRemainder ρ x / normalizationBrho ρ‖ := by
        refine (norm_sub_le _ _).trans ?_; gcongr; exact norm_add_le _ _
    _ ≤ _ := by rw [t1]; linarith

end Ends

section Domain

variable {ρ : ℂ}

lemma hasDerivAt_abs_cpow (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ((|y| : ℝ) : ℂ) ^ (ρ - 1)) ((ρ - 1) * (x : ℂ) ^ (ρ - 2)) x := by
  have h := hasDerivAt_cpow_neg (1 - ρ) hx
  have e1 : -(1 - ρ) = ρ - 1 := by ring
  simp only [e1] at h
  rw [show ρ - 1 - 1 = ρ - 2 by ring] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [abs_of_pos hy]

/-- The derivative decays like x^(-Re ρ - 1) at infinity. -/
lemma norm_genericForcedProfileDeriv_le_tail (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖genericForcedProfileDeriv ρ x‖ ≤ C * x ^ (-ρ.re - 1) := by
  have hDn : 0 ≤ srhoDerivRemainderConst ρ := by unfold srhoDerivRemainderConst; positivity
  refine ⟨‖ρ * (riemannZeta (1 - ρ) / normalizationBrho ρ)‖ + ‖2 * ρ - 1‖ / ‖normalizationBrho ρ‖ +
    srhoDerivRemainderConst ρ / ‖normalizationBrho ρ‖, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  rw [genericForcedProfileDeriv_tail h0 h1 hh hx]
  have hp : ‖(x : ℂ) ^ (-ρ - 1)‖ = x ^ (-ρ.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp
  have hx2 : ‖(x : ℂ) ^ 2‖ = x ^ (2 : ℝ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, Real.rpow_two]
  have hB : ‖(bernoulliOneRight x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_bernoulliOneRight_le x
  have hR := srhoDerivRemainder_norm_le h0 h1 hx0
  have e2 : x ^ (-(2 : ℝ)) ≤ x ^ (-ρ.re - 1) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have e4 : x ^ (-(4 : ℝ)) ≤ x ^ (-ρ.re - 1) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hinv : (x ^ (2 : ℝ))⁻¹ = x ^ (-(2 : ℝ)) := (Real.rpow_neg hx0.le _).symm
  have hbpos : 0 < ‖normalizationBrho ρ‖ := by
    obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
    exact norm_pos_iff.mpr (normalizationBrho_ne_zero hρ0 hρ1 hh)
  have t1 : ‖ρ * (riemannZeta (1 - ρ) / normalizationBrho ρ) * (x : ℂ) ^ (-ρ - 1)‖ =
      ‖ρ * (riemannZeta (1 - ρ) / normalizationBrho ρ)‖ * x ^ (-ρ.re - 1) := by rw [norm_mul, hp]
  have t2 : ‖(2 * ρ - 1) * (bernoulliOneRight x : ℂ) / (normalizationBrho ρ * (x : ℂ) ^ 2)‖ ≤
      ‖2 * ρ - 1‖ / ‖normalizationBrho ρ‖ * x ^ (-ρ.re - 1) := by
    rw [norm_div, norm_mul, norm_mul, hx2]
    calc ‖2 * ρ - 1‖ * ‖(bernoulliOneRight x : ℂ)‖ / (‖normalizationBrho ρ‖ * x ^ (2 : ℝ))
        ≤ ‖2 * ρ - 1‖ * 1 / (‖normalizationBrho ρ‖ * x ^ (2 : ℝ)) := by gcongr
      _ = ‖2 * ρ - 1‖ / ‖normalizationBrho ρ‖ * (x ^ (2 : ℝ))⁻¹ := by field_simp
      _ ≤ ‖2 * ρ - 1‖ / ‖normalizationBrho ρ‖ * x ^ (-ρ.re - 1) := by rw [hinv]; gcongr
  have t3 : ‖srhoDerivRemainder ρ x / normalizationBrho ρ‖ ≤
      srhoDerivRemainderConst ρ / ‖normalizationBrho ρ‖ * x ^ (-ρ.re - 1) := by
    rw [norm_div, div_mul_eq_mul_div]
    gcongr
    exact hR.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast e4) hDn)
  calc _ ≤ ‖ρ * (riemannZeta (1 - ρ) / normalizationBrho ρ) * (x : ℂ) ^ (-ρ - 1)‖ +
        ‖(2 * ρ - 1) * (bernoulliOneRight x : ℂ) / (normalizationBrho ρ * (x : ℂ) ^ 2)‖ +
          ‖srhoDerivRemainder ρ x / normalizationBrho ρ‖ := by
        refine (norm_sub_le _ _).trans ?_; gcongr; exact norm_sub_le _ _
    _ ≤ _ := by rw [t1]; linarith

/-- Near zero the derivative is the homogeneous power: ‖h̃'(x)‖ = ‖A (ρ - 1)‖ x^(Re ρ - 2). -/
lemma norm_genericForcedProfileDeriv_near_zero (ρ : ℂ) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ‖genericForcedProfileDeriv ρ x‖ = ‖boundaryAmplitude ρ * (ρ - 1)‖ * x ^ (ρ.re - 2) := by
  rw [genericForcedProfileDeriv_near_zero ρ hx1, norm_neg, ← mul_assoc, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- A generic zero-profile derivative bound: ‖h'(x)‖ ≤ C for x > 0 (no zero hypothesis). -/
lemma norm_zeroProfileDeriv_le_generic (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖zeroProfileDeriv ρ x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := norm_genericForcedProfileDeriv_le_tail h0 h1 hh
  refine ⟨C + ‖boundaryAmplitude ρ * (ρ - 1)‖, by positivity, fun x => ?_⟩
  rcases lt_or_ge x 1 with hx1 | hx1
  · rw [zeroProfileDeriv]
    rcases lt_or_ge x 0 with h | h
    · rw [Nat.floor_of_nonpos h.le, srhoCellDeriv_zero, zero_div, neg_zero, norm_zero]; positivity
    · rw [Nat.floor_eq_zero.mpr hx1, srhoCellDeriv_zero, zero_div, neg_zero, norm_zero]; positivity
  · have hx0 : 0 < x := by linarith
    have he : zeroProfileDeriv ρ x = genericForcedProfileDeriv ρ x +
        boundaryAmplitude ρ * ((ρ - 1) * (x : ℂ) ^ (ρ - 2)) := by
      rw [genericForcedProfileDeriv]; ring
    have hp : ‖(x : ℂ) ^ (ρ - 2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by simp; linarith)
    have hq : x ^ (-ρ.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [← mul_assoc, norm_mul]
    have := hC x hx1
    gcongr
    · exact this.trans (mul_le_of_le_one_right hC0 hq)
    · exact mul_le_of_le_one_right (norm_nonneg _) hp

/-- An L² test on (0, ∞) by a two-ended power majorant. -/
lemma memLp_two_of_power_bound {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    {C r0 r1 : ℝ} (hr0 : -1 < 2 * r0) (hr1 : 2 * r1 < -1)
    (hb : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ C * (if x < 1 then x ^ r0 else x ^ r1)) :
    MemLp f 2 (volume.restrict (Ioi 0)) := by
  refine (memLp_two_iff_integrable_sq_norm hf).mpr ?_
  have hI0 : IntegrableOn (fun x : ℝ => x ^ (2 * r0)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' hr0)
  have hI1 : IntegrableOn (fun x : ℝ => x ^ (2 * r1)) (Ioi 1) := integrableOn_Ioi_rpow_of_lt hr1 one_pos
  have hdom : Integrable (fun x : ℝ => C ^ 2 * (Ioc 0 1).indicator (fun x => x ^ (2 * r0)) x +
      C ^ 2 * (Ioi 1).indicator (fun x => x ^ (2 * r1)) x) (volume.restrict (Ioi 0)) :=
    (((integrable_indicator_iff measurableSet_Ioc).mpr hI0).mono_measure Measure.restrict_le_self
      |>.const_mul _).add
    (((integrable_indicator_iff measurableSet_Ioi).mpr hI1).mono_measure Measure.restrict_le_self
      |>.const_mul _)
  refine hdom.mono' (hf.norm.pow 2) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsq : ∀ r : ℝ, (x ^ r) ^ 2 = x ^ (2 * r) := fun r => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; ring_nf
  have hbx := hb x hx0
  have hn := norm_nonneg (f x)
  split_ifs at hbx with hx1
  · rw [indicator_of_mem (show x ∈ Ioc 0 1 from ⟨hx0, hx1.le⟩),
      indicator_of_notMem (show x ∉ Ioi 1 from not_lt.mpr hx1.le), mul_zero, add_zero, ← hsq, ← mul_pow]
    exact pow_le_pow_left₀ hn hbx 2
  · rcases eq_or_lt_of_le (not_lt.mp hx1) with h | h
    · subst h
      rw [indicator_of_mem (show (1 : ℝ) ∈ Ioc 0 1 from ⟨one_pos, le_rfl⟩),
        indicator_of_notMem (show (1 : ℝ) ∉ Ioi 1 from fun h => lt_irrefl (1 : ℝ) h), mul_zero, add_zero]
      simp only [Real.one_rpow, mul_one] at hbx ⊢
      exact pow_le_pow_left₀ hn hbx 2
    · rw [indicator_of_notMem (show x ∉ Ioc 0 1 from fun h' => absurd h'.2 (not_le.mpr h)),
        indicator_of_mem (show x ∈ Ioi 1 from h), mul_zero, zero_add, ← hsq, ← mul_pow]
      exact pow_le_pow_left₀ hn hbx 2

lemma continuousOn_genericForcedProfile (ρ : ℂ) : ContinuousOn (genericForcedProfile ρ) (Ioi 0) :=
  fun _ hx => ((continuous_zeroProfile ρ).continuousAt.sub
    (continuousAt_const.mul (hasDerivAt_abs_cpow ρ hx).continuousAt)).continuousWithinAt

lemma measurable_genericForcedProfileDeriv (ρ : ℂ) : Measurable (genericForcedProfileDeriv ρ) :=
  (measurable_zeroProfileDeriv ρ).sub (measurable_const.mul (measurable_const.mul
    (Complex.measurable_ofReal.pow_const _)))

/-- F3: for 1/2 < Re ρ < 1 the generic forced profile lies in the actual log form domain. -/
theorem genericForcedProfile_mem_logFormDomain (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    LogFormDomain (genericForcedProfile ρ) (genericForcedProfileDeriv ρ) := by
  have h0 : 0 < ρ.re := by linarith
  have hh : ρ ≠ 1 / 2 := fun h => by rw [h] at h12; norm_num at h12
  obtain ⟨Cz, hCz0, hCz⟩ := norm_zeroProfileDeriv_le_generic h0 h1 hh
  have hm := measurable_genericForcedProfileDeriv ρ
  have hII : ∀ a b : ℝ, 0 < a → 0 < b →
      IntervalIntegrable (genericForcedProfileDeriv ρ) volume a b := by
    intro a b ha hb
    have hz : IntervalIntegrable (zeroProfileDeriv ρ) volume a b :=
      (intervalIntegrable_const (c := Cz)).mono_fun (measurable_zeroProfileDeriv ρ).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg hCz0]; exact hCz x)
    have hpow : ContinuousOn (fun x : ℝ => boundaryAmplitude ρ * ((ρ - 1) * (x : ℂ) ^ (ρ - 2)))
        (uIcc a b) := by
      intro x hx
      have hx0 : 0 < x := by
        rcases le_total a b with hab | hab
        · rw [uIcc_of_le hab] at hx; linarith [hx.1]
        · rw [uIcc_of_ge hab] at hx; linarith [hx.1]
      have hc : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (ρ - 2)) x :=
        (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne'))
      exact (continuousAt_const.mul (continuousAt_const.mul hc)).continuousWithinAt
    exact hz.sub hpow.intervalIntegrable
  have hder : ∀ x : ℝ, 0 < x →
      HasDerivWithinAt (genericForcedProfile ρ) (genericForcedProfileDeriv ρ x) (Ioi x) x := by
    intro x hx
    exact (hasDerivWithinAt_zeroProfile_Ioi ρ hx).sub
      ((hasDerivAt_abs_cpow ρ hx).const_mul (boundaryAmplitude ρ)).hasDerivWithinAt
  have hFTC : ∀ a b : ℝ, 0 < a → a ≤ b →
      genericForcedProfile ρ b - genericForcedProfile ρ a = ∫ x in a..b, genericForcedProfileDeriv ρ x := by
    intro a b ha hab
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
      ((continuousOn_genericForcedProfile ρ).mono fun x hx => lt_of_lt_of_le ha hx.1)
      (fun x hx => hder x (lt_trans ha hx.1)) (hII a b ha (lt_of_lt_of_le ha hab))]
  obtain ⟨C1, hC10, hC1⟩ := norm_genericForcedProfile_le_tail h0 h1 hh
  obtain ⟨C2, hC20, hC2⟩ := norm_genericForcedProfileDeriv_le_tail h0 h1 hh
  refine ⟨fun a b ha hb => ?_, hII, hm, ?_, ?_⟩
  · rcases le_total a b with hab | hab
    · exact hFTC a b ha hab
    · rw [intervalIntegral.integral_symm, ← hFTC b a hb hab]; ring
  · refine memLp_two_of_power_bound (C := 1 + ‖boundaryAmplitude ρ‖ + C1) (r0 := ρ.re - 1) (r1 := -ρ.re)
      ((continuousOn_genericForcedProfile ρ).aestronglyMeasurable measurableSet_Ioi)
      (by linarith) (by linarith) fun x hx => ?_
    split_ifs with hx1
    · exact (norm_genericForcedProfile_le_near_zero ρ h1 hx hx1.le).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx.le _))
    · exact (hC1 x (not_lt.mp hx1)).trans
        (mul_le_mul_of_nonneg_right (by linarith [norm_nonneg (boundaryAmplitude ρ)])
          (Real.rpow_nonneg hx.le _))
  · refine memLp_two_of_power_bound (C := ‖boundaryAmplitude ρ * (ρ - 1)‖ + C2) (r0 := ρ.re - 1)
      (r1 := -ρ.re) ((Complex.measurable_ofReal.mul hm).aestronglyMeasurable)
      (by linarith) (by linarith) fun x hx => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    split_ifs with hx1
    · rw [norm_genericForcedProfileDeriv_near_zero ρ hx hx1]
      have e : x * (‖boundaryAmplitude ρ * (ρ - 1)‖ * x ^ (ρ.re - 2)) =
          ‖boundaryAmplitude ρ * (ρ - 1)‖ * x ^ (ρ.re - 1) := by
        rw [mul_left_comm, ← Real.rpow_one_add' hx.le (by linarith)]; ring_nf
      rw [e]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx.le _)
    · have hx1' : 1 ≤ x := not_lt.mp hx1
      calc x * ‖genericForcedProfileDeriv ρ x‖ ≤ x * (C2 * x ^ (-ρ.re - 1)) :=
            mul_le_mul_of_nonneg_left (hC2 x hx1') hx.le
        _ = C2 * x ^ (-ρ.re) := by
            rw [mul_left_comm, ← Real.rpow_one_add' hx.le (by linarith)]; ring_nf
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [norm_nonneg (boundaryAmplitude ρ * (ρ - 1))])
            (Real.rpow_nonneg hx.le _)

end Domain

section Euler

variable {ρ : ℂ}

/-- A positive-axis test vanishes near every point outside some (a, M) with 0 < a < M. -/
lemma PositiveAxisTest.exists_Ioo {φ : ℝ → ℂ} (hφ : PositiveAxisTest φ) :
    ∃ a M : ℝ, 0 < a ∧ a < M ∧ ∀ x, x ∉ Ioo a M → φ =ᶠ[𝓝 x] 0 := by
  obtain ⟨-, hc, hsub⟩ := hφ
  rcases (tsupport φ).eq_empty_or_nonempty with he | hne
  · exact ⟨1, 2, one_pos, one_lt_two, fun x _ =>
      notMem_tsupport_iff_eventuallyEq.mp (by rw [he]; exact notMem_empty x)⟩
  · obtain ⟨m, hmK, hmin⟩ := hc.isCompact.exists_isMinOn hne continuousOn_id
    obtain ⟨M0, hM0⟩ := hc.isCompact.bddAbove
    have hm0 : 0 < m := hsub hmK
    have hmM : m ≤ M0 := hM0 hmK
    refine ⟨m / 2, max M0 0 + 1, by positivity, by linarith [le_max_left M0 0], fun x hx => ?_⟩
    refine notMem_tsupport_iff_eventuallyEq.mp fun hxK => hx ⟨?_, ?_⟩
    · have h' : m ≤ x := hmin hxK
      linarith
    · have := hM0 hxK; linarith [le_max_left M0 0]

lemma integral_Ioi_eq_interval {f : ℝ → ℂ} {a M : ℝ} (ha : 0 < a) (haM : a ≤ M)
    (hf : ∀ x, x ∉ Ioo a M → f x = 0) : ∫ x in Ioi (0 : ℝ), f x = ∫ x in a..M, f x := by
  rw [intervalIntegral.integral_of_le haM]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun x hx => lt_trans ha hx.1) fun x hx => hf x fun h => hx.2 ⟨h.1, h.2.le⟩

lemma cpow_two_mul (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ 2 * ((ρ - 1) * (x : ℂ) ^ (ρ - 2)) = (ρ - 1) * (x : ℂ) ^ ρ := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have : (x : ℂ) ^ ρ = (x : ℂ) ^ (ρ - 2) * (x : ℂ) ^ 2 := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hxc]; push_cast; ring_nf
  rw [this]; ring

/-- The homogeneous power solves the cell equation: ∫ x² (x^(ρ-1))' φ' = κ ∫ x^(ρ-1) φ. -/
lemma power_euler (ρ : ℂ) {φ : ℝ → ℂ} (hφ : PositiveAxisTest φ) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * ((ρ - 1) * (x : ℂ) ^ (ρ - 2)) * deriv φ x =
      spectralKappa ρ * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (ρ - 1) * φ x := by
  obtain ⟨a, M, ha, haM, hz⟩ := hφ.exists_Ioo
  have hφ0 : ∀ x, x ∉ Ioo a M → φ x = 0 := fun x hx => (hz x hx).self_of_nhds
  have hdφ0 : ∀ x, x ∉ Ioo a M → deriv φ x = 0 := fun x hx => by rw [(hz x hx).deriv_eq]; simp
  have hpos : ∀ x ∈ uIcc a M, 0 < x := fun x hx => by
    rw [uIcc_of_le haM.le] at hx; linarith [hx.1]
  rw [integral_Ioi_eq_interval ha haM.le (fun x hx => by rw [hdφ0 x hx, mul_zero]),
    integral_Ioi_eq_interval ha haM.le (fun x hx => by rw [hφ0 x hx, mul_zero])]
  have hd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
    ((hφ.1.differentiable (by simp)).differentiableAt).hasDerivAt
  have hU : ∀ x ∈ uIcc a M, HasDerivAt (fun y : ℝ => (ρ - 1) * (y : ℂ) ^ ρ)
      ((ρ - 1) * (ρ * (x : ℂ) ^ (ρ - 1))) x := by
    intro x hx
    have h := hasDerivAt_cpow_neg (-ρ) (hpos x hx)
    simp only [neg_neg] at h
    exact h.const_mul (ρ - 1)
  have hUc : ContinuousOn (fun x : ℝ => (ρ - 1) * (ρ * (x : ℂ) ^ (ρ - 1))) (uIcc a M) := fun x hx =>
    (continuousAt_const.mul (continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hpos x hx).ne')))).continuousWithinAt
  have hφc : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU (fun x _ => hd x)
    hUc.intervalIntegrable (hφc.intervalIntegrable _ _)
  rw [hφ0 a (fun h => lt_irrefl a h.1), hφ0 M (fun h => lt_irrefl M h.2), mul_zero, mul_zero,
    sub_zero, zero_sub] at hIBP
  have e1 : ∫ x in a..M, (x : ℂ) ^ 2 * ((ρ - 1) * (x : ℂ) ^ (ρ - 2)) * deriv φ x =
      ∫ x in a..M, (ρ - 1) * (x : ℂ) ^ ρ * deriv φ x :=
    intervalIntegral.integral_congr fun x hx => by
      rw [cpow_two_mul ρ (hpos x hx)]
  have e2 : ∫ x in a..M, (ρ - 1) * (ρ * (x : ℂ) ^ (ρ - 1)) * φ x =
      -spectralKappa ρ * ∫ x in a..M, (x : ℂ) ^ (ρ - 1) * φ x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by simp only [spectralKappa]; ring
  rw [e1, hIBP, e2]; ring

/-- The forced Euler identity for the generic profile on positive-axis tests:
∫ x² h̃' φ' = κ (∫ (h̃ - 1) φ + Σ_{n ≥ 1} φ(n)) (no zero hypothesis). -/
theorem generic_forced_euler (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) {φ : ℝ → ℂ}
    (hφ : PositiveAxisTest φ) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * genericForcedProfileDeriv ρ x * deriv φ x) =
      spectralKappa ρ * ((∫ x in Ioi (0 : ℝ), (genericForcedProfile ρ x - 1) * φ x) +
        ∑' n : ℕ, φ (n + 1)) := by
  obtain ⟨E1, E2⟩ := forced_euler_identity h0 h1 hh hφ
  obtain ⟨a, M, ha, haM, hz⟩ := hφ.exists_Ioo
  have hφ0 : ∀ x, x ∉ Ioo a M → φ x = 0 := fun x hx => (hz x hx).self_of_nhds
  have hdφ0 : ∀ x, x ∉ Ioo a M → deriv φ x = 0 := fun x hx => by rw [(hz x hx).deriv_eq]; simp
  have hpos : ∀ x ∈ uIcc a M, 0 < x := fun x hx => by
    rw [uIcc_of_le haM.le] at hx; linarith [hx.1]
  have hφc : Continuous φ := hφ.1.continuous
  have hdφc : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
  -- the zero-profile part, with the a.e. derivative replaced by the explicit one
  have hZ : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * deriv φ x) =
      spectralKappa ρ * ((∫ x in Ioi (0 : ℝ), (zeroProfile ρ x - 1) * φ x) + ∑' n : ℕ, φ (n + 1)) := by
    rw [← E1, ← E2]
    refine integral_congr_ae ?_
    filter_upwards [deriv_zeroProfile_ae ρ] with x hx
    rw [hx]
  have hP := power_euler ρ hφ
  -- interval integrability on [a, M]
  obtain ⟨Cz, hCz0, hCz⟩ := norm_zeroProfileDeriv_le_generic h0 h1 hh
  have iZ : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * deriv φ x) volume a M := by
    have hb : IntervalIntegrable (zeroProfileDeriv ρ) volume a M :=
      (intervalIntegrable_const (c := Cz)).mono_fun (measurable_zeroProfileDeriv ρ).aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg hCz0]; exact hCz x)
    have h1' := hb.continuousOn_mul (g := fun x : ℝ => (x : ℂ) ^ 2) (by fun_prop)
    exact h1'.mul_continuousOn hdφc.continuousOn
  have hpc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (ρ - 1)) (uIcc a M) := fun x hx =>
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hpos x hx).ne')).continuousWithinAt
  have hpc2 : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (ρ - 2)) (uIcc a M) := fun x hx =>
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hpos x hx).ne')).continuousWithinAt
  have iP : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ 2 * ((ρ - 1) * (x : ℂ) ^ (ρ - 2)) * deriv φ x)
      volume a M :=
    ((((by fun_prop : Continuous fun x : ℝ => (x : ℂ) ^ 2).continuousOn.mul
      (continuousOn_const.mul hpc2)).mul hdφc.continuousOn)).intervalIntegrable
  have iH : IntervalIntegrable (fun x : ℝ => (zeroProfile ρ x - 1) * φ x) volume a M :=
    (((continuous_zeroProfile ρ).sub continuous_const).mul hφc).intervalIntegrable _ _
  have iQ : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (ρ - 1) * φ x) volume a M :=
    (hpc.mul hφc.continuousOn).intervalIntegrable
  have vZ : ∀ x, x ∉ Ioo a M → (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * deriv φ x = 0 := fun x hx => by
    rw [hdφ0 x hx, mul_zero]
  have vP : ∀ x, x ∉ Ioo a M → (x : ℂ) ^ 2 * ((ρ - 1) * (x : ℂ) ^ (ρ - 2)) * deriv φ x = 0 :=
    fun x hx => by rw [hdφ0 x hx, mul_zero]
  have vH : ∀ x, x ∉ Ioo a M → (zeroProfile ρ x - 1) * φ x = 0 := fun x hx => by rw [hφ0 x hx, mul_zero]
  have vQ : ∀ x, x ∉ Ioo a M → (x : ℂ) ^ (ρ - 1) * φ x = 0 := fun x hx => by rw [hφ0 x hx, mul_zero]
  rw [integral_Ioi_eq_interval ha haM.le vZ, integral_Ioi_eq_interval ha haM.le vH] at hZ
  rw [integral_Ioi_eq_interval ha haM.le vP, integral_Ioi_eq_interval ha haM.le vQ] at hP
  have lhs : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * genericForcedProfileDeriv ρ x * deriv φ x) =
      (∫ x in a..M, (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * deriv φ x) -
        boundaryAmplitude ρ * ∫ x in a..M, (x : ℂ) ^ 2 * ((ρ - 1) * (x : ℂ) ^ (ρ - 2)) * deriv φ x := by
    rw [integral_Ioi_eq_interval ha haM.le (fun x hx => by rw [hdφ0 x hx, mul_zero]),
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub iZ (iP.const_mul _)]
    exact intervalIntegral.integral_congr fun x _ => by simp only [genericForcedProfileDeriv]; ring
  have rhs : (∫ x in Ioi (0 : ℝ), (genericForcedProfile ρ x - 1) * φ x) =
      (∫ x in a..M, (zeroProfile ρ x - 1) * φ x) -
        boundaryAmplitude ρ * ∫ x in a..M, (x : ℂ) ^ (ρ - 1) * φ x := by
    rw [integral_Ioi_eq_interval ha haM.le (fun x hx => by rw [hφ0 x hx, mul_zero]),
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub iH (iQ.const_mul _)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    simp only [genericForcedProfile_of_pos ρ (hpos x hx)]; ring
  rw [lhs, rhs, hZ, hP]; ring

end Euler

section Weak

/-- The compact log-variable weak equation for any log-form-domain profile (h, h') whose Euler
identity on positive-axis tests is ∫ x² h' φ' = κ (∫ (h - 1) φ + Σ_{n ≥ 1} φ(n)). -/
theorem log_weak_compact_of {h hd : ℝ → ℂ} {κ : ℂ} (hD : LogFormDomain h hd)
    (hE : ∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * hd x * deriv φ x) =
        κ * ((∫ x in Ioi (0 : ℝ), (h x - 1) * φ x) + ∑' n : ℕ, φ (n + 1)))
    {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    (∫ t, logUnitaryDeriv h hd t * deriv χ t) + (1 / 4 - κ) * ∫ t, logUnitary h t * χ t =
      κ * ∫ t, sawtoothWeight t * (deriv χ t - χ t / 2) := by
  set ψ := logUnitary h
  set ψ' := logUnitaryDeriv h hd
  obtain ⟨R0, hR0, hR⟩ := exists_support_bound hc
  set R := R0 + 1
  have hRpos : 0 ≤ R := by linarith
  have hvan : ∀ t ∉ Ioc (-R) R, χ t = 0 := fun t ht => hR t (by
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht
    rcases ht with ht | ht
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith)
  have hd' : ∀ x, HasDerivAt χ (deriv χ x) x := fun x =>
    ((hχ.differentiable (by simp)).differentiableAt).hasDerivAt
  have hχ'c : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  have hvan' : ∀ t ∉ Ioc (-R) R, deriv χ t = 0 := fun t ht => by
    have hloc : χ =ᶠ[𝓝 t] fun _ => 0 := by
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with ht | ht
      · filter_upwards [Iio_mem_nhds (by linarith : t < -R0)] with y (hy : y < -R0)
        exact hR y (by rw [abs_of_neg (by linarith)]; linarith)
      · filter_upwards [Ioi_mem_nhds (by linarith : R0 < t)] with y (hy : R0 < y)
        exact hR y (by rw [abs_of_pos (by linarith)]; exact hy)
    rw [hloc.deriv_eq, deriv_const]
  have hψrep := fun a b => (hD.logUnitary_integral_eq a b).2
  have hψint := fun a b => (hD.logUnitary_integral_eq a b).1
  have hψc : Continuous ψ := hD.continuous_logUnitary
  -- the forced Euler identity on the attached x-test
  have hv := positiveAxisTest_logTest hχ hc
  have F := hE _ hv
  -- (a) the form side
  set G : ℝ → ℂ := fun x => (x : ℂ) ^ 2 * hd x *
    (((x ^ (-(3 / 2) : ℝ) : ℝ) : ℂ) * (deriv χ (Real.log x) - χ (Real.log x) / 2))
  have hFa : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * hd x * deriv (logTest χ) x) =
      ∫ x in Ioi (0 : ℝ), G x := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx0
    simp only [G, (hasDerivAt_logTest hχ hx0).deriv]
  have hexp : ∀ t : ℝ, (Real.exp t : ℂ) * (Real.exp t : ℂ) ^ 2 * (Real.exp (t * -(3 / 2)) : ℂ) =
      (Real.exp (t / 2) : ℂ) * (Real.exp t : ℂ) := by
    intro t
    have : Real.exp t * Real.exp t ^ 2 * Real.exp (t * -(3 / 2)) = Real.exp (t / 2) * Real.exp t := by
      rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    exact_mod_cast this
  have hGt : ∀ t, Real.exp t • G (Real.exp t) = (ψ' t - ψ t / 2) * (deriv χ t - χ t / 2) := by
    intro t
    simp only [G, ψ, ψ', logUnitary, logUnitaryDeriv, Real.log_exp, Complex.real_smul, exp_rpow]
    linear_combination (hd (Real.exp t) * (deriv χ t - χ t / 2)) * hexp t
  have hA : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * hd x * deriv (logTest χ) x) =
      ∫ t, (ψ' t - ψ t / 2) * (deriv χ t - χ t / 2) := by
    rw [hFa, ← integral_exp_smul_comp G]
    exact integral_congr_ae (Eventually.of_forall hGt)
  -- (b) the continuum side
  have hB : (∫ x in Ioi (0 : ℝ), (h x - 1) * logTest χ x) = ∫ t, (ψ t - (Real.exp (t / 2) : ℂ)) * χ t := by
    rw [← integral_exp_smul_comp (fun x => (h x - 1) * logTest χ x)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [logTest_exp, Complex.real_smul, ψ, logUnitary]
    have : (Real.exp t : ℂ) * (Real.exp (-t / 2) : ℂ) = (Real.exp (t / 2) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; ring_nf
    linear_combination ((h (Real.exp t) - 1) * χ t) * this
  -- (c) the atoms
  have hC : (∑' n : ℕ, logTest χ (n + 1)) =
      ∑' n : ℕ, ((((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * χ (Real.log (n + 1)) :=
    tsum_congr fun n => logTest_of_pos χ (by positivity)
  -- (d) the sawtooth identity
  have hS := sawtooth_compact_identity hχ hc
  -- integrability
  have hχc := hχ.continuous
  have i1 : Integrable (fun t => ψ' t * deriv χ t) := integrable_of_vanish hRpos
    ((hψint (-R) R).mul_continuousOn hχ'c.continuousOn) fun t ht => by rw [hvan' t ht, mul_zero]
  have i3 : Integrable (fun t => ψ' t * χ t) := integrable_of_vanish hRpos
    ((hψint (-R) R).mul_continuousOn hχc.continuousOn) fun t ht => by rw [hvan t ht, mul_zero]
  have i2 : Integrable (fun t => ψ t * χ t) := (hψc.mul hχc).integrable_of_hasCompactSupport hc.mul_left
  have i4 : Integrable (fun t => ψ t * deriv χ t) :=
    (hψc.mul hχ'c).integrable_of_hasCompactSupport hc.deriv.mul_left
  have i5 : Integrable (fun t => (Real.exp (t / 2) : ℂ) * χ t) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2))).mul
      hχc).integrable_of_hasCompactSupport hc.mul_left
  -- integration by parts: ∫ ψ' χ + ∫ ψ χ' = 0
  have hIBP : (∫ t, ψ' t * χ t) + ∫ t, ψ t * deriv χ t = 0 := by
    have hchiR : χ R = 0 := hR R (by rw [abs_of_pos (by linarith)]; linarith)
    have hchiR' : χ (-R) = 0 := hR (-R) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    rw [integral_eq_interval_of_vanish hRpos (fun t ht => by rw [hvan t ht, mul_zero]),
      integral_eq_interval_of_vanish hRpos (fun t ht => by rw [hvan' t ht, mul_zero]),
      integral_primitive_mul_deriv hψrep hψint hd' hχ'c (-R) R, hchiR, hchiR']
    ring
  -- assemble
  have hL : (∫ t, (ψ' t - ψ t / 2) * (deriv χ t - χ t / 2)) =
      (∫ t, ψ' t * deriv χ t) - (1 / 2) * ((∫ t, ψ' t * χ t) + ∫ t, ψ t * deriv χ t) +
        (1 / 4) * ∫ t, ψ t * χ t := by
    have i34 : Integrable (fun t => (1 / 2 : ℂ) * (ψ' t * χ t + ψ t * deriv χ t)) := (i3.add i4).const_mul _
    have i22 : Integrable (fun t => (1 / 4 : ℂ) * (ψ t * χ t)) := i2.const_mul _
    calc (∫ t, (ψ' t - ψ t / 2) * (deriv χ t - χ t / 2))
        = ∫ t, (ψ' t * deriv χ t - (1 / 2 : ℂ) * (ψ' t * χ t + ψ t * deriv χ t) +
            (1 / 4 : ℂ) * (ψ t * χ t)) :=
          integral_congr_ae (Eventually.of_forall fun t => by ring)
      _ = (∫ t, ψ' t * deriv χ t) - (∫ t, (1 / 2 : ℂ) * (ψ' t * χ t + ψ t * deriv χ t)) +
            ∫ t, (1 / 4 : ℂ) * (ψ t * χ t) := by
          rw [integral_add (f := fun t => ψ' t * deriv χ t - (1 / 2 : ℂ) * (ψ' t * χ t + ψ t * deriv χ t))
            (g := fun t => (1 / 4 : ℂ) * (ψ t * χ t)) (i1.sub i34) i22,
            integral_sub (f := fun t => ψ' t * deriv χ t)
            (g := fun t => (1 / 2 : ℂ) * (ψ' t * χ t + ψ t * deriv χ t)) i1 i34]
      _ = _ := by rw [integral_const_mul, integral_const_mul, integral_add i3 i4]
  have hR' : (∫ t, (ψ t - (Real.exp (t / 2) : ℂ)) * χ t) =
      (∫ t, ψ t * χ t) - ∫ t, (Real.exp (t / 2) : ℂ) * χ t := by
    rw [← integral_sub i2 i5]
    exact integral_congr_ae (Eventually.of_forall fun t => by ring)
  rw [hA, hB, hC, hL, hIBP, hR'] at F
  rw [hS]
  linear_combination F


variable {ρ : ℂ}

lemma logH1_genericForcedProfile (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    LogH1 (logUnitary (genericForcedProfile ρ))
      (logUnitaryDeriv (genericForcedProfile ρ) (genericForcedProfileDeriv ρ)) :=
  (log_unitary_form_identity _ _ (genericForcedProfile_mem_logFormDomain h12 h1)).2.2.2.2.2

/-- The weak forced equation of the generic log profile on Schwartz tests. -/
theorem genericForcedProfile_weak_equation (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) (φ : 𝓢(ℝ, ℂ)) :
    (∫ t, logUnitaryDeriv (genericForcedProfile ρ) (genericForcedProfileDeriv ρ) t * deriv φ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (genericForcedProfile ρ) t * φ t =
      spectralKappa ρ * nativeLogForce φ := by
  have h0 : 0 < ρ.re := by linarith
  have hh : ρ ≠ 1 / 2 := fun h => by rw [h] at h12; norm_num at h12
  have hD := logH1_genericForcedProfile h12 h1
  rw [nativeLogForce_apply]
  exact weak_extend hD.memLp hD.memLp_deriv (fun χ hχ hc =>
    log_weak_compact_of (genericForcedProfile_mem_logFormDomain h12 h1)
      (fun φ hφ => generic_forced_euler h0 h1 hh hφ) hχ hc) φ

end Weak

section LogDecay

variable {ρ : ℂ}

lemma exp_neg_mul_abs_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Real.exp (-(δ * |t|)) ≤ (min 1 (δ ^ 2 / 2))⁻¹ * (1 + t ^ 2)⁻¹ := by
  set c := min 1 (δ ^ 2 / 2)
  have hc : 0 < c := lt_min one_pos (by positivity)
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ δ * |t|)
  have hpos : 0 < Real.exp (δ * |t|) := Real.exp_pos _
  have hlow : c * (1 + t ^ 2) ≤ Real.exp (δ * |t|) := by
    have h1 : c ≤ 1 := min_le_left _ _
    have h2 : c ≤ δ ^ 2 / 2 := min_le_right _ _
    have ht : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    have : c * (1 + t ^ 2) ≤ 1 + (δ * |t|) ^ 2 / 2 := by
      rw [ht, mul_pow]; nlinarith [sq_nonneg |t|, abs_nonneg t]
    nlinarith [abs_nonneg t, hδ.le, mul_nonneg hδ.le (abs_nonneg t)]
  rw [Real.exp_neg, ← mul_inv]
  exact inv_anti₀ (by positivity) hlow

lemma integrable_exp_neg_mul_abs {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => Real.exp (-(δ * |t|))) :=
  (integrable_inv_one_add_sq.const_mul _).mono' (by fun_prop) (Eventually.of_forall fun t => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact exp_neg_mul_abs_le hδ t)

/-- In log variables the generic profile decays like e^(-(Re ρ - 1/2)|t|) at both ends. -/
lemma norm_logUnitary_generic_le (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, ‖logUnitary (genericForcedProfile ρ) t‖ ≤ K * Real.exp (-((ρ.re - 1 / 2) * |t|)) := by
  have h0 : 0 < ρ.re := by linarith
  have hh : ρ ≠ 1 / 2 := fun h => by rw [h] at h12; norm_num at h12
  obtain ⟨C1, hC10, hC1⟩ := norm_genericForcedProfile_le_tail h0 h1 hh
  refine ⟨1 + ‖boundaryAmplitude ρ‖ + C1, by positivity, fun t => ?_⟩
  rw [logUnitary, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases lt_or_ge t 0 with ht | ht
  · have hb := norm_genericForcedProfile_le_near_zero ρ h1 (Real.exp_pos t)
      (Real.exp_le_one_iff.mpr ht.le)
    rw [exp_rpow] at hb
    calc Real.exp (t / 2) * ‖genericForcedProfile ρ (Real.exp t)‖
        ≤ Real.exp (t / 2) * ((1 + ‖boundaryAmplitude ρ‖) * Real.exp (t * (ρ.re - 1))) := by gcongr
      _ = (1 + ‖boundaryAmplitude ρ‖) * Real.exp (-((ρ.re - 1 / 2) * |t|)) := by
          rw [abs_of_neg ht, mul_left_comm, ← Real.exp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · have hb := hC1 (Real.exp t) (Real.one_le_exp_iff.mpr ht)
    rw [exp_rpow] at hb
    calc Real.exp (t / 2) * ‖genericForcedProfile ρ (Real.exp t)‖
        ≤ Real.exp (t / 2) * (C1 * Real.exp (t * -ρ.re)) := by gcongr
      _ = C1 * Real.exp (-((ρ.re - 1 / 2) * |t|)) := by
          rw [abs_of_nonneg ht, mul_left_comm, ← Real.exp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [norm_nonneg (boundaryAmplitude ρ)])
          (Real.exp_pos _).le

lemma norm_logUnitaryDeriv_generic_le (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, ‖logUnitaryDeriv (genericForcedProfile ρ) (genericForcedProfileDeriv ρ) t‖ ≤
      K * Real.exp (-((ρ.re - 1 / 2) * |t|)) := by
  have h0 : 0 < ρ.re := by linarith
  have hh : ρ ≠ 1 / 2 := fun h => by rw [h] at h12; norm_num at h12
  obtain ⟨C1, hC10, hC1⟩ := norm_genericForcedProfile_le_tail h0 h1 hh
  obtain ⟨C2, hC20, hC2⟩ := norm_genericForcedProfileDeriv_le_tail h0 h1 hh
  set A := ‖boundaryAmplitude ρ‖
  set B := ‖boundaryAmplitude ρ * (ρ - 1)‖
  refine ⟨(1 + A) / 2 + B + C1 / 2 + C2, by positivity, fun t => ?_⟩
  rw [logUnitaryDeriv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hsplit : ‖genericForcedProfile ρ (Real.exp t) / 2 + (Real.exp t : ℂ) * genericForcedProfileDeriv ρ (Real.exp t)‖ ≤
      ‖genericForcedProfile ρ (Real.exp t)‖ / 2 + Real.exp t * ‖genericForcedProfileDeriv ρ (Real.exp t)‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_div, Complex.norm_ofNat, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases lt_or_ge t 0 with ht | ht
  · have hx1 : Real.exp t < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr ht
    have hb := norm_genericForcedProfile_le_near_zero ρ h1 (Real.exp_pos t) hx1.le
    have hd := norm_genericForcedProfileDeriv_near_zero ρ (Real.exp_pos t) hx1
    rw [exp_rpow] at hb hd
    have hE : Real.exp t * Real.exp (t * (ρ.re - 2)) = Real.exp (t * (ρ.re - 1)) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (t / 2) * ‖genericForcedProfile ρ (Real.exp t) / 2 + (Real.exp t : ℂ) * genericForcedProfileDeriv ρ (Real.exp t)‖
        ≤ Real.exp (t / 2) * ((1 + A) * Real.exp (t * (ρ.re - 1)) / 2 +
            Real.exp t * (B * Real.exp (t * (ρ.re - 2)))) := by
          gcongr
          refine hsplit.trans ?_
          gcongr
          exact hd.le
      _ = ((1 + A) / 2 + B) * Real.exp (-((ρ.re - 1 / 2) * |t|)) := by
          rw [mul_left_comm (Real.exp t), hE, abs_of_neg ht]
          rw [show (1 + A) * Real.exp (t * (ρ.re - 1)) / 2 + B * Real.exp (t * (ρ.re - 1)) =
            ((1 + A) / 2 + B) * Real.exp (t * (ρ.re - 1)) by ring, mul_left_comm, ← Real.exp_add]
          ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · have hx1 : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
    have hb := hC1 (Real.exp t) hx1
    have hd := hC2 (Real.exp t) hx1
    rw [exp_rpow] at hb hd
    have hE : Real.exp t * Real.exp (t * (-ρ.re - 1)) = Real.exp (t * -ρ.re) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (t / 2) * ‖genericForcedProfile ρ (Real.exp t) / 2 + (Real.exp t : ℂ) * genericForcedProfileDeriv ρ (Real.exp t)‖
        ≤ Real.exp (t / 2) * (C1 * Real.exp (t * -ρ.re) / 2 +
            Real.exp t * (C2 * Real.exp (t * (-ρ.re - 1)))) := by
          gcongr
          refine hsplit.trans ?_
          gcongr
      _ = (C1 / 2 + C2) * Real.exp (-((ρ.re - 1 / 2) * |t|)) := by
          rw [mul_left_comm (Real.exp t), hE, abs_of_nonneg ht]
          rw [show C1 * Real.exp (t * -ρ.re) / 2 + C2 * Real.exp (t * -ρ.re) =
            (C1 / 2 + C2) * Real.exp (t * -ρ.re) by ring, mul_left_comm, ← Real.exp_add]
          ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (by linarith [norm_nonneg (boundaryAmplitude ρ), norm_nonneg (boundaryAmplitude ρ * (ρ - 1))])
          (Real.exp_pos _).le

lemma integrable_logUnitary_generic (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    Integrable (logUnitary (genericForcedProfile ρ)) := by
  obtain ⟨K, -, hK⟩ := norm_logUnitary_generic_le h12 h1
  exact ((integrable_exp_neg_mul_abs (by linarith : 0 < ρ.re - 1 / 2)).const_mul K).mono'
    (logH1_genericForcedProfile h12 h1).continuous.aestronglyMeasurable (Eventually.of_forall hK)

lemma integrable_logUnitaryDeriv_generic (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    Integrable (logUnitaryDeriv (genericForcedProfile ρ) (genericForcedProfileDeriv ρ)) := by
  obtain ⟨K, -, hK⟩ := norm_logUnitaryDeriv_generic_le h12 h1
  exact ((integrable_exp_neg_mul_abs (by linarith : 0 < ρ.re - 1 / 2)).const_mul K).mono'
    (logH1_genericForcedProfile h12 h1).measurable_deriv.aestronglyMeasurable (Eventually.of_forall hK)

end LogDecay

section Resolvent

variable {ρ : ℂ}

lemma generic_kappa_im (h12 : 1 / 2 < ρ.re) (him : ρ.im ≠ 0) : (spectralKappa ρ).im ≠ 0 := by
  have hk : (spectralKappa ρ).im = (1 - 2 * ρ.re) * ρ.im := by
    simp only [spectralKappa, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    ring
  rw [hk]
  exact mul_ne_zero (by linarith) him

/-- The undivided Fourier identity for the generic log profile. -/
theorem logFourier_generic_undivided (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) (ξ : ℝ) :
    ((spectralEnergy ξ : ℂ) - spectralKappa ρ) * logFourier (logUnitary (genericForcedProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) := by
  have hD := logH1_genericForcedProfile h12 h1
  have hq := fourier_quotient_of_weak hD.integral_eq hD.intervalIntegrable
    (integrable_logUnitary_generic h12 h1) (integrable_logUnitaryDeriv_generic h12 h1)
    (genericForcedProfile_weak_equation h12 h1) (ξ / (2 * π))
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have e1 : (2 * π * (ξ / (2 * π)) : ℝ) = ξ := by field_simp
  have e2 : (4 * (π : ℂ) ^ 2 * ((ξ / (2 * π) : ℝ) : ℂ) ^ 2 + (1 / 4 - spectralKappa ρ)) =
      (spectralEnergy ξ : ℂ) - spectralKappa ρ := by
    have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast hπ
    rw [spectralEnergy]; push_cast; field_simp; ring
  rw [e1, e2] at hq
  rw [logFourier_eq_fourier]
  exact hq

/-- Uniqueness of H¹ weak solutions of the forced equation off the cut, for any reference solution. -/
theorem weak_solution_unique {ψ ψ' : ℝ → ℂ} {κ : ℂ} (hκ : κ ∈ spectralResolventSet)
    (hψ : LogH1 ψ ψ')
    (hWψ : ∀ φ : 𝓢(ℝ, ℂ), (∫ t, ψ' t * deriv φ t) + (1 / 4 - κ) * ∫ t, ψ t * φ t = κ * nativeLogForce φ)
    {D D' : ℝ → ℂ} (hDD : LogH1 D D')
    (hW : ∀ φ : 𝓢(ℝ, ℂ), (∫ t, D' t * deriv φ t) + (1 / 4 - κ) * ∫ t, D t * φ t = κ * nativeLogForce φ) :
    D = ψ := by
  have hE := hDD.sub hψ
  have hc : ∀ η : ℝ, ((4 * π ^ 2 * η ^ 2 : ℝ) : ℂ) + (1 / 4 - κ) ≠ 0 := by
    intro η
    have h := spectralEnergy_sub_ne hκ (2 * π * η)
    rw [spectralEnergy] at h
    convert h using 1
    push_cast; ring
  have hW0 : ∀ φ : 𝓢(ℝ, ℂ), (∫ t, (D' t - ψ' t) * deriv φ t) + (1 / 4 - κ) * ∫ t, (D t - ψ t) * φ t = 0 := by
    intro φ
    have e1 : (∫ t, (D' t - ψ' t) * deriv φ t) = (∫ t, D' t * deriv φ t) - ∫ t, ψ' t * deriv φ t := by
      rw [← integral_sub (integrable_mul_deriv_schwartz hDD.memLp_deriv φ)
        (integrable_mul_deriv_schwartz hψ.memLp_deriv φ)]
      exact integral_congr_ae (Eventually.of_forall fun t => by ring)
    have e2 : (∫ t, (D t - ψ t) * φ t) = (∫ t, D t * φ t) - ∫ t, ψ t * φ t := by
      rw [← integral_sub (integrable_mul_schwartz hDD.memLp φ) (integrable_mul_schwartz hψ.memLp φ)]
      exact integral_congr_ae (Eventually.of_forall fun t => by ring)
    rw [e1, e2]
    linear_combination hW φ - hWψ φ
  have h0' := weak_unique hE hc hW0
  funext t
  exact sub_eq_zero.mp (congrFun h0' t)

/-- Fourier inversion: a continuous integrable log profile with the arithmetic quotient as its
log-Fourier transform is the forced log-resolvent. -/
theorem eq_nativeLogResolvent_of_logFourier {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψ1 : Integrable ψ)
    {κ : ℂ} (hκ : κ ∈ spectralResolventSet)
    (hq : ∀ ξ : ℝ, logFourier ψ ξ = κ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - κ)) :
    ψ = nativeLogResolvent κ := by
  set q : ℝ → ℂ := fun ξ => κ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - κ) with hqdef
  have h2π : (2 * π : ℝ) ≠ 0 := Real.two_pi_pos.ne'
  have hF : 𝓕 ψ = fun η => q (2 * π * η) := by
    funext η
    have h := hq (2 * π * η)
    rw [logFourier_eq_fourier, show 2 * π * η / (2 * π) = η by field_simp] at h
    exact h
  have hFi : Integrable (𝓕 ψ) := by
    rw [hF]; exact (integrable_resolvent_quotient hκ).comp_mul_left' h2π
  have hinv := Continuous.fourierInv_fourier_eq hψc hψ1 hFi
  funext t
  conv_lhs => rw [← hinv]
  rw [Real.fourierInv_eq', hF, nativeLogResolvent]
  have hs := Measure.integral_comp_mul_left (fun ξ : ℝ => cexp (((ξ * t : ℝ) : ℂ) * I) * q ξ) (2 * π)
  have hpt : ∀ v : ℝ, cexp (((2 * π * inner ℝ v t : ℝ) : ℂ) * I) • q (2 * π * v) =
      cexp ((((2 * π * v) * t : ℝ) : ℂ) * I) * q (2 * π * v) := by
    intro v
    rw [smul_eq_mul, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
    congr 3
    simp only [RCLike.re_to_real]; ring_nf
  simp_rw [hpt]
  rw [hs, abs_of_pos (inv_pos.mpr Real.two_pi_pos), Complex.real_smul]
  push_cast
  ring

end Resolvent

section Roots

variable {ρ : ℂ}

/-- F3: for an arbitrary parameter 1/2 < Re ρ < 1, Im ρ ≠ 0 (not necessarily a zero), the generic
forced profile h̃ = 1 - S_ρ/b_ρ - ζ(ρ) x^(ρ-1)/b_ρ lies in the log form domain, solves the actual
force equation (the physical Euler identity on positive-axis tests, and in log variables the weak
equation (-D² + 1/4 - κ) ψ = κ 𝔤 on Schwartz tests), is its unique solution in the log form domain
and in H¹, has the arithmetic Fourier quotient and equals the forced log-resolvent. Both ends are
controlled: h̃ = O(x^(Re ρ - 1)) and h̃' = O(x^(Re ρ - 2)) near 0, h̃ = O(x^(-Re ρ)) and
h̃' = O(x^(-Re ρ - 1)) at infinity. -/
theorem generic_forced_profile_unique (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0) :
    LogFormDomain (genericForcedProfile ρ) (genericForcedProfileDeriv ρ) ∧
    (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * genericForcedProfileDeriv ρ x * deriv φ x) =
        spectralKappa ρ * ((∫ x in Ioi (0 : ℝ), (genericForcedProfile ρ x - 1) * φ x) +
          ∑' n : ℕ, φ (n + 1))) ∧
    (∀ g g' : ℝ → ℂ, LogFormDomain g g' →
      (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
        (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * g' x * deriv φ x) =
          spectralKappa ρ * ((∫ x in Ioi (0 : ℝ), (g x - 1) * φ x) + ∑' n : ℕ, φ (n + 1))) →
      ∀ x : ℝ, 0 < x → g x = genericForcedProfile ρ x) ∧
    LogH1 (logUnitary (genericForcedProfile ρ))
      (logUnitaryDeriv (genericForcedProfile ρ) (genericForcedProfileDeriv ρ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ),
      (∫ t, logUnitaryDeriv (genericForcedProfile ρ) (genericForcedProfileDeriv ρ) t * deriv φ t) +
        (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (genericForcedProfile ρ) t * φ t =
          spectralKappa ρ * nativeLogForce φ) ∧
    (∀ D D' : ℝ → ℂ, LogH1 D D' →
      (∀ φ : 𝓢(ℝ, ℂ), (∫ t, D' t * deriv φ t) + (1 / 4 - spectralKappa ρ) * ∫ t, D t * φ t =
        spectralKappa ρ * nativeLogForce φ) → D = logUnitary (genericForcedProfile ρ)) ∧
    (∀ ξ : ℝ, logFourier (logUnitary (genericForcedProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ)) ∧
    logUnitary (genericForcedProfile ρ) = nativeLogResolvent (spectralKappa ρ) ∧
    (∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖genericForcedProfile ρ x‖ ≤ (1 + ‖boundaryAmplitude ρ‖) * x ^ (ρ.re - 1)) ∧
    (∀ x : ℝ, 0 < x → x < 1 →
      ‖genericForcedProfileDeriv ρ x‖ = ‖boundaryAmplitude ρ * (ρ - 1)‖ * x ^ (ρ.re - 2)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖genericForcedProfile ρ x‖ ≤ C * x ^ (-ρ.re)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖genericForcedProfileDeriv ρ x‖ ≤ C * x ^ (-ρ.re - 1)) := by
  have h0 : 0 < ρ.re := by linarith
  have hh : ρ ≠ 1 / 2 := fun h => by rw [h] at h12; norm_num at h12
  have hR : spectralKappa ρ ∈ spectralResolventSet := Or.inl (generic_kappa_im h12 him)
  have hDom := genericForcedProfile_mem_logFormDomain h12 h1
  have hD := logH1_genericForcedProfile h12 h1
  have hW := genericForcedProfile_weak_equation h12 h1
  have hq : ∀ ξ : ℝ, logFourier (logUnitary (genericForcedProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ) := fun ξ => by
    rw [eq_div_iff (spectralEnergy_sub_ne hR ξ), mul_comm]
    exact logFourier_generic_undivided h12 h1 ξ
  refine ⟨hDom, fun φ hφ => generic_forced_euler h0 h1 hh hφ, ?_, hD, hW,
    fun D D' hDD hWD => weak_solution_unique hR hD hW hDD hWD, hq,
    eq_nativeLogResolvent_of_logFourier hD.continuous (integrable_logUnitary_generic h12 h1) hR hq,
    fun x hx hx1 => norm_genericForcedProfile_le_near_zero ρ h1 hx hx1,
    fun x hx hx1 => norm_genericForcedProfileDeriv_near_zero ρ hx hx1,
    norm_genericForcedProfile_le_tail h0 h1 hh, norm_genericForcedProfileDeriv_le_tail h0 h1 hh⟩
  intro g g' hg hgE x hx
  have hgH := (log_unitary_form_identity _ _ hg).2.2.2.2.2
  have hgW : ∀ φ : 𝓢(ℝ, ℂ), (∫ t, logUnitaryDeriv g g' t * deriv φ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary g t * φ t = spectralKappa ρ * nativeLogForce φ := by
    intro φ
    rw [nativeLogForce_apply]
    exact weak_extend hgH.memLp hgH.memLp_deriv (fun χ hχ hc => log_weak_compact_of hg hgE hχ hc) φ
  have hEq := weak_solution_unique hR hD hW hgH hgW
  have ht := congrFun hEq (Real.log x)
  simp only [logUnitary, Real.exp_log hx] at ht
  have hne : (Real.exp (Real.log x / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  exact mul_left_cancel₀ hne ht

/-- F3 (F3.2): on (0, 1) the generic profile is 1 - (ζ(ρ)/b_ρ) x^(ρ-1), so it has the plateau
h̃ ≡ 1 there exactly when ζ(ρ) = 0, in which case it is the zero profile. At infinity the retained
homogeneous term is -(ζ(1-ρ)/b_ρ) x^(-ρ), plus the Bernoulli tail κ B₂({x})/(2x²) and an O(x⁻³)
remainder. No integrability of h̃ is asserted for generic ρ. -/
theorem generic_boundary_amplitude (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    boundaryAmplitude ρ = riemannZeta ρ / normalizationBrho ρ ∧
    normalizationBrho ρ = (1 - 2 * ρ) / spectralKappa ρ ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, genericForcedProfile ρ x = 1 - boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1)) ∧
    ((∀ x ∈ Ioo (0 : ℝ) 1, genericForcedProfile ρ x = 1) ↔ riemannZeta ρ = 0) ∧
    (riemannZeta ρ = 0 → genericForcedProfile ρ = zeroProfile ρ) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖genericForcedProfile ρ x - (-(riemannZeta (1 - ρ) / normalizationBrho ρ) * (x : ℂ) ^ (-ρ) +
        spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2))‖ ≤ C * x ^ (-3 : ℝ)) := by
  have h0 : 0 < ρ.re := by linarith
  have hh : ρ ≠ 1 / 2 := fun h => by rw [h] at h12; norm_num at h12
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
  have hBA : ∀ x ∈ Ioo (0 : ℝ) 1, genericForcedProfile ρ x = 1 - boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1) :=
    fun x hx => genericForcedProfile_near_zero ρ hx.1 hx.2.le
  refine ⟨rfl, ?_, hBA, ⟨fun hpl => ?_, fun hz x hx => ?_⟩, fun hz => ?_, ?_⟩
  · rw [normalizationBrho, spectralKappa]
  · have h2 := hpl (1 / 2) ⟨by norm_num, by norm_num⟩
    rw [hBA (1 / 2) ⟨by norm_num, by norm_num⟩] at h2
    have hp : ((1 / 2 : ℝ) : ℂ) ^ (ρ - 1) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; left; norm_num
    have hA : boundaryAmplitude ρ = 0 := by
      have : boundaryAmplitude ρ * ((1 / 2 : ℝ) : ℂ) ^ (ρ - 1) = 0 := by linear_combination -h2
      exact (mul_eq_zero.mp this).resolve_right hp
    rw [boundaryAmplitude, div_eq_zero_iff] at hA
    exact hA.resolve_right hb
  · rw [hBA x hx, boundaryAmplitude, hz, zero_div, zero_mul, sub_zero]
  · funext x; rw [genericForcedProfile, boundaryAmplitude, hz, zero_div, zero_mul, sub_zero]
  · refine ⟨srhoRemainderConst ρ / ‖normalizationBrho ρ‖,
      div_nonneg (srhoRemainderConst_nonneg ρ) (norm_nonneg _), fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith
    rw [genericForcedProfile_tail h0 h1 hh hx,
      show ∀ a b c : ℂ, a + b - c - (a + b) = -c from fun a b c => by ring, norm_neg, norm_div,
      div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (srhoRemainder_norm_le h0 h1 hx0) (norm_nonneg _)

end Roots

end Zeta23.OPICAFollowup
