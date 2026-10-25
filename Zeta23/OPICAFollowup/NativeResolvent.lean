import Zeta23.OPICAFollowup.WeightedSpectralMeasure
import Zeta23.OPICAFollowup.SamplingCompatibility

/-!
The native forced log-resolvent and the sampling Stieltjes identity (F2). For an actual zero ρ of ζ
in the strip, with κ = ρ(1 - ρ) off the cut [1/4, ∞) (every nonreal κ, i.e. every off-line zero),
the zero profile h of `ZeroProfiles` is identified with an explicit resolvent.

- **Weak equation.** The log profile ψ(t) = e^(t/2) h(e^t) and ψ' (the log-unitary derivative) form
  an H¹ pair. Against compact tests χ, the forced Euler equation of `ForcedEuler`, transferred
  through x^(-1/2) χ(log x), gives ∫ ψ' χ' + (1/4 - κ) ∫ ψ χ = κ ∫ w (χ' - χ/2). A cutoff argument
  extends this to every Schwartz test, where the right side is κ 𝔤(φ) for the actual force
  𝔤 = -(D + 1/2) w of F1.
- **Quotient, uniqueness, inversion.** Fourier transforming the weak equation gives
  (ξ² + 1/4 - κ) 𝓕_log ψ(ξ) = κ ζ(1/2 + iξ). The multiplier never vanishes off the cut, so an H¹
  weak solution is unique (the difference has zero L² Fourier transform). The quotient is
  integrable, and Fourier inversion identifies ψ with the forced log-resolvent
  `nativeLogResolvent` κ, (1/2π) ∫ e^(iξt) κ ζ(1/2 + iξ)/(a(ξ) - κ) dξ.
- **Sample.** Summation by parts on each integer cell, with its endpoint terms, gives
  b = Σ_{n ≥ 1} h(n) - 1/2 = ∫_0^∞ {x} h'(x) dx. In log variables this is the H⁻¹-H¹ pairing
  ∫ w (ψ' - ψ/2) of 𝔤 with ψ. Polarized Plancherel with the real weight w, 𝓕_log w = -ζ(s)/s and
  𝓕_log(ψ' - ψ/2) = -conj(s) 𝓕_log ψ (s = 1/2 + iξ) gives b = κ ∫ dω/(a - κ) = κ M(κ).
- **Norms.** The same Plancherel identities give ‖h‖² = |κ|² ∫ dω/|a - κ|², the Euler form
  ∫ x²|h'|² = |κ|² ∫ a dω/|a - κ|², and the mixed pairings
  N(ρ, σ) = κ_ρ conj κ_σ ∫ dω/((a - κ_ρ)(a - conj κ_σ)) and
  Q(ρ, σ) = κ_ρ conj κ_σ ∫ a dω/((a - κ_ρ)(a - conj κ_σ)). The resolvent identity under ω recovers
  the undivided S2 identity (κ_ρ - conj κ_σ) N = conj κ_σ b_ρ - κ_ρ conj b_σ. With the budget of
  `WeightedSpectralMeasure`, |b| ≤ |κ| (1 + |κ|/|Im κ|)(log(2π) - γ) for nonreal κ.

Nothing here asserts that any zero is off the line, that any sample is real, or that the
hypotheses are satisfiable: the theorems are conditional on an actual zero with the stated κ.
-/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff

namespace Zeta23.OPICAFollowup

section LogTests
/-- The test x^(-1/2) χ(log x) on (0, ∞) attached to a log-line test χ (zero for x ≤ 0). -/
def logTest (χ : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * χ (Real.log x) else 0

lemma logTest_of_pos (χ : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    logTest χ x = ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * χ (Real.log x) := if_pos hx

lemma exp_rpow (t r : ℝ) : Real.exp t ^ r = Real.exp (t * r) := by
  rw [← Real.exp_log (Real.rpow_pos_of_pos (Real.exp_pos t) r), Real.log_rpow (Real.exp_pos t),
    Real.log_exp, mul_comm]

lemma logTest_exp (χ : ℝ → ℂ) (t : ℝ) :
    logTest χ (Real.exp t) = (Real.exp (-t / 2) : ℂ) * χ t := by
  rw [logTest_of_pos χ (Real.exp_pos t), Real.log_exp, exp_rpow]
  congr 3; ring

lemma exists_support_bound {χ : ℝ → ℂ} (hc : HasCompactSupport χ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t, R < |t| → χ t = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun t ht => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := hR h
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_max_left R 1]

lemma logTest_eq_zero_of_not_mem {χ : ℝ → ℂ} {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ t, R < |t| → χ t = 0)
    {x : ℝ} (hx : x ∉ Icc (Real.exp (-R)) (Real.exp R)) : logTest χ x = 0 := by
  rcases le_or_gt x 0 with h | h
  · rw [logTest, if_neg (not_lt.mpr h)]
  · rw [logTest_of_pos χ h, hR, mul_zero]
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have hl : Real.log x < -R := (Real.log_lt_iff_lt_exp h).mpr hx
      rw [abs_of_neg (by linarith)]; linarith
    · have hl : R < Real.log x := (Real.lt_log_iff_exp_lt h).mpr hx
      rw [abs_of_pos (by linarith)]; exact hl

lemma contDiffOn_logTest {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiffOn ℝ ∞ (fun x : ℝ => ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * χ (Real.log x)) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ∞ (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) x :=
    Real.contDiffAt_rpow_const_of_ne hx0.ne'
  have h2 : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hx0.ne'
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x h1).mul (hχ.contDiffAt.comp x h2)

theorem positiveAxisTest_logTest {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    PositiveAxisTest (logTest χ) := by
  obtain ⟨R, hR0, hR⟩ := exists_support_bound hc
  have hsupp : Function.support (logTest χ) ⊆ Icc (Real.exp (-R)) (Real.exp R) := fun x hx => by
    by_contra h; exact hx (logTest_eq_zero_of_not_mem hR0.le hR h)
  have htsupp : tsupport (logTest χ) ⊆ Icc (Real.exp (-R)) (Real.exp R) :=
    closure_minimal hsupp isClosed_Icc
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp |>.mono le_rfl, ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun x => ?_
    rcases lt_or_ge 0 x with hx | hx
    · have := (contDiffOn_logTest hχ).contDiffAt (Ioi_mem_nhds hx)
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with y hy using logTest_of_pos χ hy
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos (-R)))] with y hy
      exact logTest_eq_zero_of_not_mem hR0.le hR (fun h => absurd h.1 (not_le.mpr hy))
  · exact htsupp.trans fun x hx => lt_of_lt_of_le (Real.exp_pos _) hx.1

/-- The derivative of the log test at x > 0: x^(-3/2) (χ'(log x) - χ(log x)/2). -/
theorem hasDerivAt_logTest {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logTest χ)
      (((x ^ (-(3 / 2) : ℝ) : ℝ) : ℂ) * (deriv χ (Real.log x) - χ (Real.log x) / 2)) x := by
  have hd1 : HasDerivAt (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) ((-(1 / 2)) * x ^ (-(1 / 2) - 1 : ℝ)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hd2 : HasDerivAt (fun x => χ (Real.log x)) (deriv χ (Real.log x) * x⁻¹) x := by
    have := ((hχ.differentiable (by simp)).differentiableAt (x := Real.log x)).hasDerivAt.scomp x
      (Real.hasDerivAt_log hx.ne')
    simpa [Function.comp_def, Complex.real_smul, mul_comm] using this
  have hd := (hd1.ofReal_comp).mul hd2
  have hev : (fun y => ((y ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * χ (Real.log y)) =ᶠ[𝓝 x] logTest χ := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using (logTest_of_pos χ hy).symm
  refine (hd.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  have e1 : x ^ (-(1 / 2) - 1 : ℝ) = x ^ (-(3 / 2) : ℝ) := by norm_num
  have e2 : x ^ (-(1 / 2) : ℝ) * x⁻¹ = x ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx]; norm_num
  rw [e1]
  have e2' : ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * (x : ℂ)⁻¹ = ((x ^ (-(3 / 2) : ℝ) : ℝ) : ℂ) := by
    rw [← e2]; push_cast; ring
  push_cast
  linear_combination (deriv χ (Real.log x)) * e2'

/-- Real product rule for a C¹ factor P and a primitive U of U', in the form P'U + PU'. -/
lemma integral_deriv_mul_primitive' {P U U' : ℝ → ℝ} (hP : ContDiff ℝ 1 P) {a b : ℝ} (hab : a ≤ b)
    (hU' : IntervalIntegrable U' volume a b) (hrep : ∀ x, U x = U a + ∫ t in a..x, U' t) :
    ∫ x in a..b, (deriv P x * U x + P x * U' x) = P b * U b - P a * U a := by
  have h := integral_deriv_mul_primitive hP (c := U a) hab hU'
  rw [← hrep b] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [← hrep x]

lemma continuous_of_primitive {φ φ' : ℝ → ℂ} (hrep : ∀ a b : ℝ, φ b - φ a = ∫ t in a..b, φ' t)
    (hint : ∀ a b : ℝ, IntervalIntegrable φ' volume a b) : Continuous φ := by
  have hc := (intervalIntegral.continuous_primitive hint 0).const_add (φ 0)
  refine hc.congr fun y => ?_
  have := hrep 0 y; linear_combination -this

/-- Complex integration by parts for a primitive φ (φ(b) - φ(a) = ∫_a^b φ') against a C¹ factor g. -/
theorem integral_primitive_mul_deriv {φ φ' g g' : ℝ → ℂ}
    (hrep : ∀ a b : ℝ, φ b - φ a = ∫ t in a..b, φ' t)
    (hint : ∀ a b : ℝ, IntervalIntegrable φ' volume a b)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') (a b : ℝ) :
    ∫ x in a..b, φ' x * g x = φ b * g b - φ a * g a - ∫ x in a..b, φ x * g' x := by
  wlog hab : a ≤ b generalizing a b
  · have := this b a (le_of_not_ge hab)
    rw [intervalIntegral.integral_symm (f := fun x => φ' x * g x) b a,
      intervalIntegral.integral_symm (f := fun x => φ x * g' x) b a, this]
    ring
  have hgC : ContDiff ℝ 1 g := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (hg x).differentiableAt, ?_⟩
    rw [show deriv g = g' from funext fun x => (hg x).deriv]; exact hg'
  have hgc : Continuous g := hgC.continuous
  have hφc : Continuous φ := continuous_of_primitive hrep hint
  have hp : ContDiff ℝ 1 (fun x => (g x).re) := Complex.reCLM.contDiff.comp hgC
  have hq : ContDiff ℝ 1 (fun x => (g x).im) := Complex.imCLM.contDiff.comp hgC
  have hdp : ∀ x, deriv (fun x => (g x).re) x = (g' x).re := fun x =>
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hg x)).deriv
  have hdq : ∀ x, deriv (fun x => (g x).im) x = (g' x).im := fun x =>
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hg x)).deriv
  have hre : ∀ x, (φ x).re = (φ a).re + ∫ t in a..x, (φ' t).re := fun x => by
    have h1 := congrArg Complex.re (hrep a x)
    have h2 : (∫ t in a..x, φ' t).re = ∫ t in a..x, (φ' t).re :=
      (Complex.reCLM.intervalIntegral_comp_comm (hint a x)).symm
    rw [Complex.sub_re, h2] at h1
    linarith
  have him : ∀ x, (φ x).im = (φ a).im + ∫ t in a..x, (φ' t).im := fun x => by
    have h1 := congrArg Complex.im (hrep a x)
    have h2 : (∫ t in a..x, φ' t).im = ∫ t in a..x, (φ' t).im :=
      (Complex.imCLM.intervalIntegral_comp_comm (hint a x)).symm
    rw [Complex.sub_im, h2] at h1
    linarith
  have hIre : IntervalIntegrable (fun t => (φ' t).re) volume a b := ⟨(hint a b).1.re, (hint a b).2.re⟩
  have hIim : IntervalIntegrable (fun t => (φ' t).im) volume a b := ⟨(hint a b).1.im, (hint a b).2.im⟩
  have e1 := integral_deriv_mul_primitive' hp hab hIre hre
  have e2 := integral_deriv_mul_primitive' hq hab hIim him
  have e3 := integral_deriv_mul_primitive' hp hab hIim him
  have e4 := integral_deriv_mul_primitive' hq hab hIre hre
  simp only [hdp, hdq] at e1 e2 e3 e4
  -- integrability of the real pieces
  have pc : ∀ {A : ℝ → ℝ} {B : ℝ → ℝ} {C : ℝ → ℝ} {D : ℝ → ℝ}, Continuous A → Continuous B →
      Continuous C → IntervalIntegrable D volume a b →
      IntervalIntegrable (fun x => A x * B x + C x * D x) volume a b := fun hA hB hC hD =>
    ((hA.mul hB).intervalIntegrable a b).add (hD.continuousOn_mul hC.continuousOn)
  have cre := Complex.continuous_re
  have cim := Complex.continuous_im
  have j1 := pc (A := fun x => (g' x).re) (B := fun x => (φ x).re) (C := fun x => (g x).re)
    (cre.comp hg') (cre.comp hφc) (cre.comp hgc) hIre
  have j2 := pc (A := fun x => (g' x).im) (B := fun x => (φ x).im) (C := fun x => (g x).im)
    (cim.comp hg') (cim.comp hφc) (cim.comp hgc) hIim
  have j3 := pc (A := fun x => (g' x).re) (B := fun x => (φ x).im) (C := fun x => (g x).re)
    (cre.comp hg') (cim.comp hφc) (cre.comp hgc) hIim
  have j4 := pc (A := fun x => (g' x).im) (B := fun x => (φ x).re) (C := fun x => (g x).im)
    (cim.comp hg') (cre.comp hφc) (cim.comp hgc) hIre
  have i1 : IntervalIntegrable (fun x => φ x * g' x) volume a b :=
    (hφc.mul hg').intervalIntegrable a b
  have i2 : IntervalIntegrable (fun x => φ' x * g x) volume a b :=
    (hint a b).mul_continuousOn hgc.continuousOn
  rw [eq_sub_iff_add_eq, ← intervalIntegral.integral_add i2 i1]
  apply Complex.ext
  · have h := (Complex.reCLM.intervalIntegral_comp_comm (i2.add i1)).symm
    simp only [Complex.reCLM_apply] at h
    rw [h]
    have hfun : (fun x => (φ' x * g x + φ x * g' x).re) = fun x =>
        ((g' x).re * (φ x).re + (g x).re * (φ' x).re) - ((g' x).im * (φ x).im + (g x).im * (φ' x).im) := by
      funext x; simp only [Complex.add_re, Complex.mul_re]; ring
    rw [hfun, intervalIntegral.integral_sub j1 j2, e1, e2]
    simp only [Complex.sub_re, Complex.mul_re]; ring
  · have h := (Complex.imCLM.intervalIntegral_comp_comm (i2.add i1)).symm
    simp only [Complex.imCLM_apply] at h
    rw [h]
    have hfun : (fun x => (φ' x * g x + φ x * g' x).im) = fun x =>
        ((g' x).re * (φ x).im + (g x).re * (φ' x).im) + ((g' x).im * (φ x).re + (g x).im * (φ' x).re) := by
      funext x; simp only [Complex.add_im, Complex.mul_im]; ring
    rw [hfun, intervalIntegral.integral_add j3 j4, e3, e4]
    simp only [Complex.sub_im, Complex.mul_im]; ring

/-- A primitive of an integrable derivative that is itself integrable tends to 0 at +∞. -/
lemma tendsto_atTop_of_primitive {φ φ' : ℝ → ℂ} (hrep : ∀ a b : ℝ, φ b - φ a = ∫ t in a..b, φ' t)
    (hf : Integrable φ) (hf' : Integrable φ') : Tendsto φ atTop (𝓝 0) := by
  have hlim : Tendsto φ atTop (𝓝 (φ 0 + ∫ t in Ioi (0 : ℝ), φ' t)) := by
    have := (intervalIntegral_tendsto_integral_Ioi 0 hf'.integrableOn tendsto_id).const_add (φ 0)
    refine this.congr fun R => ?_
    have := hrep 0 R; simp only [id]; linear_combination -this
  have h0 := (hf.integrableAtFilter atTop).eq_zero_of_tendsto (fun s hs => by
    rcases mem_atTop_sets.1 hs with ⟨b, hb⟩
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb) hlim
  rwa [h0] at hlim

/-- A primitive of an integrable derivative that is itself integrable tends to 0 at -∞. -/
lemma tendsto_atBot_of_primitive {φ φ' : ℝ → ℂ} (hrep : ∀ a b : ℝ, φ b - φ a = ∫ t in a..b, φ' t)
    (hf : Integrable φ) (hf' : Integrable φ') : Tendsto φ atBot (𝓝 0) := by
  have hlim : Tendsto φ atBot (𝓝 (φ 0 - ∫ t in Iic (0 : ℝ), φ' t)) := by
    have := (intervalIntegral_tendsto_integral_Iic 0 hf'.integrableOn tendsto_id).const_sub (φ 0)
    refine this.congr fun R => ?_
    have := hrep R 0; simp only [id]; linear_combination this
  have h0 := (hf.integrableAtFilter atBot).eq_zero_of_tendsto (fun s hs => by
    rcases mem_atBot_sets.1 hs with ⟨b, hb⟩
    rw [← top_le_iff, ← Real.volume_Iic (a := b)]
    exact measure_mono hb) hlim
  rwa [h0] at hlim

/-- Fourier transform of the derivative of an integrable primitive: 𝓕 φ' = 2πiη 𝓕 φ. -/
theorem fourier_deriv_of_primitive {φ φ' : ℝ → ℂ} (hrep : ∀ a b : ℝ, φ b - φ a = ∫ t in a..b, φ' t)
    (hint : ∀ a b : ℝ, IntervalIntegrable φ' volume a b) (hf : Integrable φ) (hf' : Integrable φ')
    (η : ℝ) : 𝓕 φ' η = (2 * π * I * η) * 𝓕 φ η := by
  set e : ℝ → ℂ := fun t => cexp (↑(-2 * π * t * η) * I) with he_def
  set e' : ℝ → ℂ := fun t => (-(2 * π * η) * I) * e t
  have he : ∀ t, HasDerivAt e (e' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (↑(-2 * π * t * η) * I : ℂ)) (↑(-2 * π * η) * I) t := by
      have h2 := ((hasDerivAt_id t).const_mul (-2 * π * η)).ofReal_comp.mul_const I
      have hfun : (fun y : ℝ => (((-2 * π * η * id y : ℝ) : ℂ) * I)) =
          fun t : ℝ => (↑(-2 * π * t * η) * I : ℂ) := by
        funext y; simp only [id]; ring_nf
      rw [hfun, mul_one] at h2
      exact h2
    have := h1.cexp
    convert this using 1
    simp only [e', e]; push_cast; ring
  have hec : Continuous e' := by simp only [e', e]; fun_prop
  have hnorm : ∀ t, ‖e t‖ = 1 := fun t => by
    simp only [e]; rw [Complex.norm_exp_ofReal_mul_I]
  have hF : ∀ g : ℝ → ℂ, 𝓕 g η = ∫ t, e t * g t := fun g => by
    rw [Real.fourier_real_eq_integral_exp_smul]; simp only [smul_eq_mul, e]
  have hec0 : Continuous e := by simp only [e]; fun_prop
  have hI1 : Integrable (fun t => φ' t * e t) :=
    hf'.mul_bdd hec0.aestronglyMeasurable (Eventually.of_forall fun t => (hnorm t).le)
  have hI2 : Integrable (fun t => φ t * e' t) := by
    refine (hf.mul_bdd (c := ‖-(2 * π * η) * I‖) hec.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_))
    simp only [e', norm_mul, hnorm, mul_one, le_refl]
  have hibp : ∀ R : ℝ, ∫ x in (-R)..R, φ' x * e x =
      φ R * e R - φ (-R) * e (-R) - ∫ x in (-R)..R, φ x * e' x :=
    fun R => integral_primitive_mul_deriv hrep hint he hec (-R) R
  have hL : Tendsto (fun R : ℝ => ∫ x in (-R)..R, φ' x * e x) atTop (𝓝 (∫ x, φ' x * e x)) :=
    intervalIntegral_tendsto_integral hI1 tendsto_neg_atTop_atBot tendsto_id
  have hR : Tendsto (fun R : ℝ => φ R * e R - φ (-R) * e (-R) - ∫ x in (-R)..R, φ x * e' x) atTop
      (𝓝 (0 - 0 - ∫ x, φ x * e' x)) := by
    have hb : ∀ {u : ℝ → ℝ}, Tendsto (fun R => φ (u R)) atTop (𝓝 0) →
        Tendsto (fun R => φ (u R) * e (u R)) atTop (𝓝 0) := fun hu => by
      refine squeeze_zero_norm (fun R => ?_) (tendsto_norm_zero.comp hu)
      rw [norm_mul, hnorm, mul_one]; rfl
    refine ((hb (u := id) (tendsto_atTop_of_primitive hrep hf hf')).sub
      (hb (u := fun R => -R) ((tendsto_atBot_of_primitive hrep hf hf').comp tendsto_neg_atTop_atBot))).sub
      (intervalIntegral_tendsto_integral hI2 tendsto_neg_atTop_atBot tendsto_id)
  have heq := tendsto_nhds_unique hL (hR.congr fun R => (hibp R).symm)
  rw [hF, hF]
  calc (∫ x, e x * φ' x) = ∫ x, φ' x * e x := integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    _ = ∫ x, -(φ x * e' x) := by rw [heq, integral_neg]; ring
    _ = ∫ x, (2 * π * I * η) * (e x * φ x) := integral_congr_ae (Eventually.of_forall fun x => by
        simp only [e']; ring)
    _ = (2 * π * I * η) * ∫ x, e x * φ x := integral_const_mul _ _

end LogTests

section Transfer

lemma integral_eq_interval_of_vanish {f : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ t ∉ Ioc (-R) R, f t = 0) : ∫ t, f t = ∫ t in (-R)..R, f t := by
  rw [intervalIntegral.integral_of_le (by linarith), setIntegral_eq_integral_of_forall_compl_eq_zero h]

lemma integrable_of_vanish {f : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R) (hf : IntervalIntegrable f volume (-R) R)
    (h : ∀ t ∉ Ioc (-R) R, f t = 0) : Integrable f :=
  ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hf).integrable_of_forall_notMem_eq_zero h

variable {ρ : ℂ}

/-- The log-line weak form of the forced Euler equation on compactly supported smooth tests:
∫ ψ' χ' + (1/4 - κ) ∫ ψ χ = κ ∫ w (χ' - χ/2) for ψ = U h, the log unitary of the zero profile. -/
theorem log_weak_compact (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {χ : ℝ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    (∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv χ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (zeroProfile ρ) t * χ t =
      spectralKappa ρ * ∫ t, sawtoothWeight t * (deriv χ t - χ t / 2) := by
  set h := zeroProfile ρ
  set hd := zeroProfileDeriv ρ
  set ψ := logUnitary h
  set ψ' := logUnitaryDeriv h hd
  set κ := spectralKappa ρ
  have hD := zeroProfile_mem_logFormDomain hz h0 h1
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
  obtain ⟨E1, E2, -⟩ := zero_profile_forced_euler ρ hz h0 h1
  have hv := positiveAxisTest_logTest hχ hc
  have F := (E2 _ hv).trans (E1 _ hv)
  -- (a) the form side
  set G : ℝ → ℂ := fun x => (x : ℂ) ^ 2 * hd x *
    (((x ^ (-(3 / 2) : ℝ) : ℝ) : ℂ) * (deriv χ (Real.log x) - χ (Real.log x) / 2))
  have hFa : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * deriv h x * deriv (logTest χ) x) =
      ∫ x in Ioi (0 : ℝ), G x := by
    refine integral_congr_ae ?_
    filter_upwards [deriv_zeroProfile_ae ρ, ae_restrict_mem measurableSet_Ioi] with x hx hx0
    have hx' : deriv h x = hd x := hx
    simp only [G, hx', (hasDerivAt_logTest hχ hx0).deriv]
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
  have hA : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * deriv h x * deriv (logTest χ) x) =
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

end Transfer

section Decay

lemma sq_tendsto_of_primitive_real {u u' : ℝ → ℝ} (hrep : ∀ a b, u b - u a = ∫ x in a..b, u' x)
    (hint : ∀ a b, IntervalIntegrable u' volume a b) (hcross : Integrable (fun x => u x * u' x))
    (hu2 : Integrable (fun x => u x ^ 2)) :
    Tendsto (fun x => u x ^ 2) atTop (𝓝 0) ∧ Tendsto (fun x => u x ^ 2) atBot (𝓝 0) := by
  have hloc : ∀ a b, a ≤ b → ∫ x in a..b, 2 * (u x * u' x) = u b ^ 2 - u a ^ 2 := by
    intro a b hab
    have hU : ∀ y, u y = u a + ∫ t in a..y, u' t := fun y => by linarith [hrep a y]
    have h := local_energy_line_primitive (c := u a) hab (hint a b)
    rw [intervalIntegral.integral_same, add_zero, ← hU b] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [← hU x]
  have hf : Integrable (fun x => 2 * (u x * u' x)) := hcross.const_mul 2
  constructor
  · have hlim := intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id
    have hlim2 : Tendsto (fun b => u b ^ 2) atTop (𝓝 ((∫ x in Ioi 0, 2 * (u x * u' x)) + u 0 ^ 2)) := by
      refine (hlim.add_const (u 0 ^ 2)).congr' ?_
      filter_upwards [eventually_ge_atTop 0] with b hb
      simp only [id]; rw [hloc 0 b hb]; ring
    have h0 := (hu2.integrableAtFilter atTop).eq_zero_of_tendsto (fun s hs => by
      rcases mem_atTop_sets.1 hs with ⟨b, hb⟩
      rw [← top_le_iff, ← Real.volume_Ici (a := b)]
      exact measure_mono hb) hlim2
    rwa [h0] at hlim2
  · have hlim := intervalIntegral_tendsto_integral_Iic 0 hf.integrableOn tendsto_id
    have hlim2 : Tendsto (fun a => u a ^ 2) atBot (𝓝 (u 0 ^ 2 - ∫ x in Iic 0, 2 * (u x * u' x))) := by
      refine (hlim.const_sub (u 0 ^ 2)).congr' ?_
      filter_upwards [eventually_le_atBot 0] with a ha
      simp only [id]; rw [hloc a 0 ha]; ring
    have h0 := (hu2.integrableAtFilter atBot).eq_zero_of_tendsto (fun s hs => by
      rcases mem_atBot_sets.1 hs with ⟨b, hb⟩
      rw [← top_le_iff, ← Real.volume_Iic (a := b)]
      exact measure_mono hb) hlim2
    rwa [h0] at hlim2

lemma integrable_mul_of_sq {u u' : ℝ → ℝ} (hmu : AEStronglyMeasurable u volume)
    (hmu' : AEStronglyMeasurable u' volume) (hu2 : Integrable (fun x => u x ^ 2))
    (hu2' : Integrable (fun x => u' x ^ 2)) : Integrable (fun x => u x * u' x) :=
  ((hu2.add hu2').div_const 2).mono' (hmu.mul hmu') (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_mul, Pi.add_apply]
    nlinarith [sq_nonneg (|u x| - |u' x|), sq_abs (u x), sq_abs (u' x)])

lemma tendsto_zero_of_sq {φ : ℝ → ℂ} {l : Filter ℝ} (h1 : Tendsto (fun x => (φ x).re ^ 2) l (𝓝 0))
    (h2 : Tendsto (fun x => (φ x).im ^ 2) l (𝓝 0)) : Tendsto φ l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun x => ‖φ x‖ ^ 2) l (𝓝 0) := by
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr fun x => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Real.sqrt_zero, Function.comp_def] at this
  refine this.congr fun x => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

end Decay

namespace LogH1

variable {φ φ' : ℝ → ℂ}

/-- An H¹(ℝ) function vanishes at ±∞. -/
theorem tendsto_zero (hφ : LogH1 φ φ') :
    Tendsto φ atTop (𝓝 0) ∧ Tendsto φ atBot (𝓝 0) := by
  have hm : AEStronglyMeasurable φ volume := hφ.continuous.aestronglyMeasurable
  have hm' : AEStronglyMeasurable φ' volume := hφ.measurable_deriv.aestronglyMeasurable
  have hn := (memLp_two_iff_integrable_sq_norm hm).mp hφ.memLp
  have hn' := (memLp_two_iff_integrable_sq_norm hm').mp hφ.memLp_deriv
  have bre : ∀ z : ℂ, z.re ^ 2 ≤ ‖z‖ ^ 2 := fun z =>
    sq_le_sq' (neg_abs_le _ |>.trans' (neg_le_neg (Complex.abs_re_le_norm _)))
      ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have bim : ∀ z : ℂ, z.im ^ 2 ≤ ‖z‖ ^ 2 := fun z =>
    sq_le_sq' (neg_abs_le _ |>.trans' (neg_le_neg (Complex.abs_im_le_norm _)))
      ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  have sqI : ∀ {f : ℝ → ℂ} (g : ℂ → ℝ), Continuous g → (∀ z, g z ^ 2 ≤ ‖z‖ ^ 2) →
      AEStronglyMeasurable f volume → Integrable (fun x => ‖f x‖ ^ 2) →
      Integrable (fun x => g (f x) ^ 2) := fun g hg hb hf hfi =>
    hfi.mono' ((hg.comp_aestronglyMeasurable hf).pow 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb _)
  have i1 := sqI _ Complex.continuous_re bre hm hn
  have i2 := sqI _ Complex.continuous_im bim hm hn
  have i3 := sqI _ Complex.continuous_re bre hm' hn'
  have i4 := sqI _ Complex.continuous_im bim hm' hn'
  have hre : ∀ a b, (φ b).re - (φ a).re = ∫ t in a..b, (φ' t).re := fun a b => by
    rw [← Complex.sub_re, hφ.integral_eq a b]
    exact (Complex.reCLM.intervalIntegral_comp_comm (hφ.intervalIntegrable a b)).symm
  have him : ∀ a b, (φ b).im - (φ a).im = ∫ t in a..b, (φ' t).im := fun a b => by
    rw [← Complex.sub_im, hφ.integral_eq a b]
    exact (Complex.imCLM.intervalIntegral_comp_comm (hφ.intervalIntegrable a b)).symm
  have mre := Complex.continuous_re.comp_aestronglyMeasurable hm
  have mim := Complex.continuous_im.comp_aestronglyMeasurable hm
  have mre' := Complex.continuous_re.comp_aestronglyMeasurable hm'
  have mim' := Complex.continuous_im.comp_aestronglyMeasurable hm'
  obtain ⟨r1, r2⟩ := sq_tendsto_of_primitive_real hre (fun a b => ⟨(hφ.intervalIntegrable a b).1.re,
    (hφ.intervalIntegrable a b).2.re⟩) (integrable_mul_of_sq mre mre' i1 i3) i1
  obtain ⟨s1, s2⟩ := sq_tendsto_of_primitive_real him (fun a b => ⟨(hφ.intervalIntegrable a b).1.im,
    (hφ.intervalIntegrable a b).2.im⟩) (integrable_mul_of_sq mim mim' i2 i4) i2
  exact ⟨tendsto_zero_of_sq r1 s1, tendsto_zero_of_sq r2 s2⟩

end LogH1

section WeakExtension

lemma integrable_mul_of_memLp_two {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    Integrable (fun x => f x * g x) := by
  have : ENNReal.HolderTriple 2 2 1 := ⟨by norm_num [ENNReal.inv_two_add_inv_two]⟩
  exact hf.integrable_mul hg

/-- The fixed cutoff: a smooth bump equal to 1 on [-1, 1] and supported in (-2, 2). -/
def cutoffBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The truncated test χ_n = β(t/(n+1)) φ(t). -/
def truncTest (φ : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ := ((cutoffBump (t / ((n : ℝ) + 1)) : ℝ) : ℂ) * φ t

lemma contDiff_cutoff : ContDiff ℝ ∞ (fun s : ℝ => cutoffBump s) := cutoffBump.contDiff

lemma truncTest_contDiff {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) : ContDiff ℝ ∞ (truncTest φ n) := by
  unfold truncTest
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_cutoff.comp (contDiff_id.div_const _))).mul hφ

lemma truncTest_hasCompactSupport (φ : ℝ → ℂ) (n : ℕ) : HasCompactSupport (truncTest φ n) := by
  have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * ((n : ℝ) + 1))) fun t ht => ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
  have : t / ((n : ℝ) + 1) ∉ Function.support (fun s : ℝ => cutoffBump s) := by
    rw [cutoffBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, abs_div, abs_of_pos hR, not_lt,
      le_div_iff₀ hR]
    change 2 * ((n : ℝ) + 1) ≤ |t|; linarith
  simp only [Function.mem_support, not_not] at this
  simp [truncTest, this]

lemma hasDerivAt_truncTest {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (t : ℝ) :
    HasDerivAt (truncTest φ n) ((((deriv (fun s : ℝ => cutoffBump s) (t / ((n : ℝ) + 1))) /
      ((n : ℝ) + 1) : ℝ) : ℂ) * φ t + ((cutoffBump (t / ((n : ℝ) + 1)) : ℝ) : ℂ) * deriv φ t) t := by
  have hb : HasDerivAt (fun s : ℝ => cutoffBump s) (deriv (fun s : ℝ => cutoffBump s) (t / ((n : ℝ) + 1)))
      (t / ((n : ℝ) + 1)) := ((contDiff_cutoff.differentiable (by simp)) _).hasDerivAt
  have hs : HasDerivAt (fun t : ℝ => t / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) t :=
    (hasDerivAt_id t).div_const _
  have hcomp := (hb.comp t hs).ofReal_comp
  have hφd : HasDerivAt φ (deriv φ t) t := ((hφ.differentiable (by simp)) t).hasDerivAt
  have := hcomp.mul hφd
  have hfun : (fun y => ((((fun s : ℝ => cutoffBump s) ∘ fun t => t / ((n : ℝ) + 1)) y : ℝ) : ℂ)) * φ =
      truncTest φ n := by funext y; rfl
  rw [hfun] at this
  refine this.congr_deriv ?_
  simp only [Function.comp_def, mul_one_div]

/-- Extension of a weak identity from compactly supported smooth tests to Schwartz tests, for
ψ, ψ' ∈ L²: truncate φ by β(t/(n+1)) and pass to the limit by dominated convergence. -/
theorem weak_extend {ψ ψ' : ℝ → ℂ} (hψ : MemLp ψ 2) (hψ' : MemLp ψ' 2) {c κ : ℂ}
    (hc : ∀ χ : ℝ → ℂ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∫ t, ψ' t * deriv χ t) + c * ∫ t, ψ t * χ t =
        κ * ∫ t, sawtoothWeight t * (deriv χ t - χ t / 2))
    (φ : 𝓢(ℝ, ℂ)) :
    (∫ t, ψ' t * deriv φ t) + c * ∫ t, ψ t * φ t =
      κ * ∫ t, sawtoothWeight t * (deriv φ t - φ t / 2) := by
  set b : ℝ → ℝ := fun s => cutoffBump s with hb_def
  set b' : ℝ → ℝ := deriv b
  have hbc : Continuous b' := contDiff_cutoff.continuous_deriv (by simp)
  obtain ⟨Cb, hCb⟩ : ∃ C, ∀ s, ‖b' s‖ ≤ C :=
    hbc.bounded_above_of_compact_support cutoffBump.hasCompactSupport.deriv
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 0)
  have hb1 : ∀ s, ‖b s‖ ≤ 1 := fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg cutoffBump.nonneg]; exact cutoffBump.le_one
  have hφs : ContDiff ℝ ∞ (φ : ℝ → ℂ) := φ.smooth ⊤
  have hφ2 : MemLp (φ : ℝ → ℂ) 2 := φ.memLp 2
  have hdφ : ⇑(SchwartzMap.derivCLM ℂ ℂ φ) = deriv φ := funext fun x => SchwartzMap.derivCLM_apply ℂ φ x
  have hφ'2 : MemLp (deriv (φ : ℝ → ℂ)) 2 := hdφ ▸ (SchwartzMap.derivCLM ℂ ℂ φ).memLp 2
  have hφc : Continuous (φ : ℝ → ℂ) := φ.continuous
  have hφ'c : Continuous (deriv (φ : ℝ → ℂ)) := hdφ ▸ (SchwartzMap.derivCLM ℂ ℂ φ).continuous
  have hw := memLp_two_sawtoothWeight
  set R : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hR1 : ∀ n, 1 ≤ R n := fun n => by simp only [R]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hRpos : ∀ n, 0 < R n := fun n => lt_of_lt_of_le one_pos (hR1 n)
  have hD : ∀ n t, deriv (truncTest φ n) t = ((b' (t / R n) / R n : ℝ) : ℂ) * φ t +
      ((b (t / R n) : ℝ) : ℂ) * deriv φ t := fun n t => (hasDerivAt_truncTest hφs n t).deriv
  have hlim0 : ∀ t : ℝ, Tendsto (fun n : ℕ => t / R n) atTop (𝓝 0) := fun t =>
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hb0 : b 0 = 1 := cutoffBump.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
  have hblim : ∀ t, Tendsto (fun n : ℕ => ((b (t / R n) : ℝ) : ℂ)) atTop (𝓝 1) := fun t => by
    have := (Complex.continuous_ofReal.comp contDiff_cutoff.continuous).tendsto 0 |>.comp (hlim0 t)
    simpa [Function.comp_def, ← hb_def, hb0] using this
  have hb'lim : ∀ t, Tendsto (fun n : ℕ => ((b' (t / R n) / R n : ℝ) : ℂ)) atTop (𝓝 0) := fun t => by
    rw [← Complex.ofReal_zero]
    refine Complex.continuous_ofReal.continuousAt.tendsto.comp ?_
    refine squeeze_zero_norm (a := fun n => Cb / R n) (fun n => ?_) ?_
    · rw [norm_div, Real.norm_of_nonneg (hRpos n).le]
      exact div_le_div_of_nonneg_right (hCb _) (hRpos n).le
    · exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hbnd' : ∀ n t, ‖((b' (t / R n) / R n : ℝ) : ℂ)‖ ≤ Cb := fun n t => by
    rw [Complex.norm_real, norm_div, Real.norm_of_nonneg (hRpos n).le]
    exact (div_le_self (norm_nonneg _) (hR1 n)).trans (hCb _)
  have hbnd : ∀ n t, ‖((b (t / R n) : ℝ) : ℂ)‖ ≤ 1 := fun n t => by rw [Complex.norm_real]; exact hb1 _
  have hcA : ∀ n, Continuous fun t => ((b' (t / R n) / R n : ℝ) : ℂ) := fun n =>
    Complex.continuous_ofReal.comp ((hbc.comp (continuous_id.div_const _)).div_const _)
  have hcB : ∀ n, Continuous fun t => ((b (t / R n) : ℝ) : ℂ) := fun n =>
    Complex.continuous_ofReal.comp (contDiff_cutoff.continuous.comp (continuous_id.div_const _))
  have hcD : ∀ n, Continuous fun t => ((b' (t / R n) / R n : ℝ) : ℂ) * φ t +
      ((b (t / R n) : ℝ) : ℂ) * deriv φ t := fun n => ((hcA n).mul hφc).add ((hcB n).mul hφ'c)
  have iA := integrable_mul_of_memLp_two hψ' hφ2
  have iB := integrable_mul_of_memLp_two hψ' hφ'2
  have iC := integrable_mul_of_memLp_two hψ hφ2
  have iD := integrable_mul_of_memLp_two hw hφ2
  have iE := integrable_mul_of_memLp_two hw hφ'2
  have key : ∀ (f : ℝ → ℂ) (n : ℕ) (t : ℝ), ‖f t * (((b' (t / R n) / R n : ℝ) : ℂ) * φ t +
      ((b (t / R n) : ℝ) : ℂ) * deriv φ t)‖ ≤ Cb * ‖f t * φ t‖ + ‖f t * deriv φ t‖ := by
    intro f n t
    rw [mul_add, ← mul_assoc, ← mul_assoc, mul_comm (f t) _, mul_comm (f t) _, mul_assoc, mul_assoc]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hbnd' n t) (norm_nonneg _)
    · rw [norm_mul]; exact (mul_le_mul_of_nonneg_right (hbnd n t) (norm_nonneg _)).trans (by rw [one_mul])
  have hpt : ∀ (f : ℝ → ℂ) (t : ℝ), Tendsto (fun n : ℕ => f t * (((b' (t / R n) / R n : ℝ) : ℂ) * φ t +
      ((b (t / R n) : ℝ) : ℂ) * deriv φ t)) atTop (𝓝 (f t * deriv φ t)) := fun f t => by
    have := ((hb'lim t).mul_const (φ t)).add ((hblim t).mul_const (deriv φ t))
    rw [zero_mul, zero_add, one_mul] at this
    exact this.const_mul (f t)
  have L1 : Tendsto (fun n => ∫ t, ψ' t * deriv (truncTest φ n) t) atTop (𝓝 (∫ t, ψ' t * deriv φ t)) := by
    simp_rw [hD]
    exact tendsto_integral_of_dominated_convergence _ (fun n => hψ'.aestronglyMeasurable.mul
      (hcD n).aestronglyMeasurable) ((iA.norm.const_mul Cb).add iB.norm)
      (fun n => Eventually.of_forall (key ψ' n)) (Eventually.of_forall (hpt ψ'))
  have L2 : Tendsto (fun n => ∫ t, ψ t * truncTest φ n t) atTop (𝓝 (∫ t, ψ t * φ t)) := by
    refine tendsto_integral_of_dominated_convergence (fun t => ‖ψ t * φ t‖) (fun n =>
      hψ.aestronglyMeasurable.mul ((hcB n).mul hφc).aestronglyMeasurable) iC.norm
      (fun n => Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
    · simp only [truncTest]
      rw [mul_left_comm, norm_mul _ (ψ t * φ t)]
      exact (mul_le_mul_of_nonneg_right (hbnd n t) (norm_nonneg _)).trans (by rw [one_mul])
    · simp only [truncTest]
      have := ((hblim t).mul_const (ψ t * φ t))
      rw [one_mul] at this
      exact this.congr fun n => by ring
  have L3 : Tendsto (fun n => ∫ t, sawtoothWeight t * (deriv (truncTest φ n) t - truncTest φ n t / 2))
      atTop (𝓝 (∫ t, sawtoothWeight t * (deriv φ t - φ t / 2))) := by
    simp_rw [hD]
    refine tendsto_integral_of_dominated_convergence
      (fun t => Cb * ‖sawtoothWeight t * φ t‖ + ‖sawtoothWeight t * deriv φ t‖ +
        ‖sawtoothWeight t * φ t‖ / 2) (fun n => hw.aestronglyMeasurable.mul
      ((hcD n).sub (((hcB n).mul hφc).div_const 2)).aestronglyMeasurable)
      (((iD.norm.const_mul Cb).add iE.norm).add (iD.norm.div_const 2))
      (fun n => Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
    · simp only [truncTest]
      rw [mul_sub]
      refine (norm_sub_le _ _).trans (add_le_add (key sawtoothWeight n t) ?_)
      rw [show sawtoothWeight t * (((b (t / R n) : ℝ) : ℂ) * φ t / 2) =
          ((b (t / R n) : ℝ) : ℂ) * (sawtoothWeight t * φ t) / 2 by ring, norm_div, norm_mul,
        Complex.norm_ofNat]
      exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_right (hbnd n t) (norm_nonneg _)).trans
        (by rw [one_mul])) (by norm_num)
    · simp only [truncTest]
      have h1 := hpt sawtoothWeight t
      have h2 := ((hblim t).mul_const (sawtoothWeight t * φ t / 2))
      rw [one_mul] at h2
      have := h1.sub h2
      rw [show sawtoothWeight t * (deriv φ t - φ t / 2) =
        sawtoothWeight t * deriv φ t - sawtoothWeight t * φ t / 2 by ring]
      exact this.congr fun n => by ring
  have E : ∀ n : ℕ, (∫ t, ψ' t * deriv (truncTest φ n) t) + c * ∫ t, ψ t * truncTest φ n t =
      κ * ∫ t, sawtoothWeight t * (deriv (truncTest φ n) t - truncTest φ n t / 2) := fun n =>
    hc _ (truncTest_contDiff hφs n) (truncTest_hasCompactSupport φ n)
  exact tendsto_nhds_unique ((L1.add (L2.const_mul c)).congr E) (L3.const_mul κ)

end WeakExtension

section ProfileDecay

lemma exp_neg_abs_half_le (t : ℝ) : Real.exp (-|t| / 2) ≤ 8 / (1 + t ^ 2) := by
  have h := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ |t| / 2)
  have hpos : 0 < Real.exp (|t| / 2) := Real.exp_pos _
  rw [show -|t| / 2 = -(|t| / 2) by ring, Real.exp_neg, inv_le_comm₀ hpos (by positivity), inv_div]
  have : (1 + t ^ 2) / 8 ≤ 1 + |t| / 2 + (|t| / 2) ^ 2 / 2 := by
    have := sq_abs t; nlinarith [abs_nonneg t]
  linarith

lemma integrable_exp_neg_abs_half : Integrable (fun t : ℝ => Real.exp (-|t| / 2)) := by
  refine (integrable_inv_one_add_sq.const_mul 8).mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← div_eq_mul_inv]
  exact exp_neg_abs_half_le t

lemma exp_half_div_le (t : ℝ) : Real.exp (t / 2) * (1 + Real.exp t ^ 2)⁻¹ ≤ Real.exp (-|t| / 2) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have h1 : Real.exp t ^ 2 = Real.exp (2 * t) := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    calc Real.exp (t / 2) ≤ Real.exp (-t / 2) * Real.exp (2 * t) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-t / 2) * (1 + Real.exp (2 * t)) := by gcongr; linarith
  · rw [abs_of_neg ht, neg_neg]
    calc Real.exp (t / 2) * (1 + Real.exp t ^ 2)⁻¹ ≤ Real.exp (t / 2) * 1 := by
          gcongr; exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (Real.exp t)])
      _ = Real.exp (t / 2) := mul_one _

theorem norm_logUnitary_zeroProfile_le {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, ‖logUnitary (zeroProfile ρ) t‖ ≤ K * Real.exp (-|t| / 2) := by
  obtain ⟨K, hK0, hK⟩ := zeroProfile_norm_le hz h0 h1
  refine ⟨K, hK0, fun t => ?_⟩
  rw [logUnitary, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (t / 2) * ‖zeroProfile ρ (Real.exp t)‖ ≤ Real.exp (t / 2) * (K * (1 + Real.exp t ^ 2)⁻¹) :=
        by gcongr; exact hK _
    _ = K * (Real.exp (t / 2) * (1 + Real.exp t ^ 2)⁻¹) := by ring
    _ ≤ K * Real.exp (-|t| / 2) := by gcongr; exact exp_half_div_le t

theorem norm_logUnitaryDeriv_zeroProfile_le {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, ‖logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t‖ ≤
      K * Real.exp (-|t| / 2) := by
  obtain ⟨K, hK0, hK⟩ := zeroProfile_norm_le hz h0 h1
  obtain ⟨C, hC0, hC⟩ := zeroProfileDeriv_bound hz h0 h1
  refine ⟨K / 2 + C, by positivity, fun t => ?_⟩
  rw [logUnitaryDeriv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have e1 : ‖zeroProfile ρ (Real.exp t) / 2‖ ≤ K / 2 * (1 + Real.exp t ^ 2)⁻¹ := by
    rw [norm_div, Complex.norm_ofNat]
    have := hK (Real.exp t); rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]; linarith
  have e2 : Real.exp (t / 2) * ‖(Real.exp t : ℂ) * zeroProfileDeriv ρ (Real.exp t)‖ ≤
      C * Real.exp (-|t| / 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hb := hC (Real.exp t) (Real.exp_pos t)
    rcases le_or_gt 0 t with ht | ht
    · have hm : min 1 (Real.exp t ^ (-2 : ℝ)) ≤ Real.exp (-(2 * t)) := by
        refine (min_le_right _ _).trans (le_of_eq ?_)
        rw [← Real.exp_log (Real.rpow_pos_of_pos (Real.exp_pos t) _), Real.log_rpow (Real.exp_pos t),
          Real.log_exp]; ring_nf
      calc Real.exp (t / 2) * (Real.exp t * ‖zeroProfileDeriv ρ (Real.exp t)‖)
          ≤ Real.exp (t / 2) * (Real.exp t * (C * Real.exp (-(2 * t)))) := by
            gcongr; exact hb.trans (by gcongr)
        _ = C * (Real.exp (t / 2) * Real.exp t * Real.exp (-(2 * t))) := by ring
        _ = C * Real.exp (-|t| / 2) := by
            rw [← Real.exp_add, ← Real.exp_add, abs_of_nonneg ht]; ring_nf
    · have hm : min 1 (Real.exp t ^ (-2 : ℝ)) ≤ 1 := min_le_left _ _
      calc Real.exp (t / 2) * (Real.exp t * ‖zeroProfileDeriv ρ (Real.exp t)‖)
          ≤ Real.exp (t / 2) * (Real.exp t * (C * 1)) := by gcongr; exact hb.trans (by gcongr)
        _ = C * (Real.exp (t / 2) * Real.exp t) := by ring
        _ ≤ C * Real.exp (-|t| / 2) := by
            gcongr
            rw [← Real.exp_add, abs_of_neg ht]
            exact Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (t / 2) * ‖zeroProfile ρ (Real.exp t) / 2 + (Real.exp t : ℂ) * zeroProfileDeriv ρ (Real.exp t)‖
      ≤ Real.exp (t / 2) * ‖zeroProfile ρ (Real.exp t) / 2‖ +
          Real.exp (t / 2) * ‖(Real.exp t : ℂ) * zeroProfileDeriv ρ (Real.exp t)‖ := by
        rw [← mul_add]; gcongr; exact norm_add_le _ _
    _ ≤ Real.exp (t / 2) * (K / 2 * (1 + Real.exp t ^ 2)⁻¹) + C * Real.exp (-|t| / 2) := by
        gcongr
    _ = K / 2 * (Real.exp (t / 2) * (1 + Real.exp t ^ 2)⁻¹) + C * Real.exp (-|t| / 2) := by ring
    _ ≤ K / 2 * Real.exp (-|t| / 2) + C * Real.exp (-|t| / 2) := by
        gcongr; exact exp_half_div_le t
    _ = (K / 2 + C) * Real.exp (-|t| / 2) := by ring

end ProfileDecay

section FourierQuotient

/-- The Fourier quotient of a weak solution: if ψ, ψ' ∈ L¹ (ψ a primitive of ψ') satisfy
∫ ψ' φ' + c ∫ ψ φ = κ 𝔤(φ) for every Schwartz φ, then (4π²η² + c) 𝓕ψ(η) = κ ζ(1/2 + 2πiη). -/
theorem fourier_quotient_of_weak {ψ ψ' : ℝ → ℂ} (hrep : ∀ a b : ℝ, ψ b - ψ a = ∫ t in a..b, ψ' t)
    (hint : ∀ a b : ℝ, IntervalIntegrable ψ' volume a b) (hψ1 : Integrable ψ) (hψ'1 : Integrable ψ')
    {c κ : ℂ} (hW : ∀ φ : 𝓢(ℝ, ℂ), (∫ t, ψ' t * deriv φ t) + c * ∫ t, ψ t * φ t = κ * nativeLogForce φ)
    (η : ℝ) : (4 * π ^ 2 * η ^ 2 + c) * 𝓕 ψ η = κ * riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) := by
  set B : ℝ → ℂ := fun η => (4 * π ^ 2 * η ^ 2 + c) * 𝓕 ψ η - κ * riemannZeta (1 / 2 + (2 * π * η : ℝ) * I)
  have hBc : Continuous B := by
    have hz : Continuous fun η : ℝ => riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) :=
      continuous_zeta_critical_line.comp (continuous_const.mul continuous_id)
    exact ((by fun_prop : Continuous fun η : ℝ => (4 * π ^ 2 * η ^ 2 + c : ℂ)).mul
      (continuous_fourier_of_integrable hψ1)).sub (continuous_const.mul hz)
  have hBint : ∀ g : 𝓢(ℝ, ℂ), ∫ η, B η * g η = 0 := by
    intro g
    have hgI : Integrable (g : ℝ → ℂ) := g.integrable
    have hxg : Integrable (fun x : ℝ => x • g x) := by
      refine (g.integrable_pow_mul volume 1).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
      rw [norm_smul, pow_one]
    have hG : Integrable (fun x : ℝ => (-2 * π * I * x) • g x) := by
      have := hxg.const_mul (-2 * π * I)
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Complex.real_smul, smul_eq_mul]; ring
    have hx2g : Integrable (fun x : ℝ => ((4 * π ^ 2 * x ^ 2 : ℝ) : ℂ) * g x) := by
      have := (g.integrable_pow_mul volume 2).const_mul (4 * π ^ 2)
      refine this.mono' (by fun_prop) (Eventually.of_forall fun x => le_of_eq ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, sq_abs]
      ring
    have hW' := hW (𝓕 g)
    have hcoe : ((𝓕 g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 (g : ℝ → ℂ) := SchwartzMap.fourier_coe g
    have hd : deriv ((𝓕 g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 (fun x : ℝ => (-2 * π * I * x) • g x) := by
      rw [hcoe]; exact Real.deriv_fourier hgI hxg
    rw [hd, hcoe] at hW'
    have e1 : (∫ t, ψ' t * 𝓕 (fun x : ℝ => (-2 * π * I * x) • g x) t) =
        ∫ η : ℝ, ((4 * π ^ 2 * η ^ 2 : ℝ) : ℂ) * 𝓕 ψ η * g η := by
      rw [← integral_fourier_mul_eq_of_integrable' hψ'1 hG]
      refine integral_congr_ae (Eventually.of_forall fun η => ?_)
      beta_reduce
      rw [fourier_deriv_of_primitive hrep hint hψ1 hψ'1 η]
      simp only [smul_eq_mul]
      push_cast
      ring_nf
      rw [Complex.I_sq]; ring
    have e2 : (∫ t, ψ t * 𝓕 (g : ℝ → ℂ) t) = ∫ η, 𝓕 ψ η * g η :=
      (integral_fourier_mul_eq_of_integrable' hψ1 hgI).symm
    have e3 : nativeLogForce (𝓕 g) = ∫ η, riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) * g η := by
      rw [← fourier_nativeLogForce g]; rfl
    rw [e1, e2, e3] at hW'
    have hF1 : Integrable (fun η : ℝ => ((4 * π ^ 2 * η ^ 2 : ℝ) : ℂ) * 𝓕 ψ η * g η) := by
      obtain ⟨C, hC⟩ : ∃ C, ∀ η, ‖𝓕 ψ η‖ ≤ C :=
        ⟨_, fun η => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ η⟩
      refine (hx2g.bdd_mul (c := C) (continuous_fourier_of_integrable hψ1).aestronglyMeasurable
        (Eventually.of_forall hC)).congr (Eventually.of_forall fun η => ?_)
      ring
    have hF2 : Integrable (fun η => 𝓕 ψ η * g η) := by
      obtain ⟨C, hC⟩ : ∃ C, ∀ η, ‖𝓕 ψ η‖ ≤ C :=
        ⟨_, fun η => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ η⟩
      exact hgI.bdd_mul (continuous_fourier_of_integrable hψ1).aestronglyMeasurable (Eventually.of_forall hC)
    have hF3 : Integrable (fun η : ℝ => riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) * g η) := by
      obtain ⟨C, hC⟩ : ∃ C, ∀ η, ‖𝓕 sawtoothWeight η‖ ≤ C :=
        ⟨_, fun η => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ η⟩
      have hlin : Integrable (fun η : ℝ => (1 / 2 + (2 * π * η : ℝ) * I) * g η) := by
        have h1 := hgI.const_mul (1 / 2 : ℂ)
        have h2 := hxg.const_mul (2 * π * I)
        refine (h1.add h2).congr (Eventually.of_forall fun η => ?_)
        simp only [Complex.real_smul, Pi.add_apply]; push_cast; ring
      refine ((hlin.bdd_mul (c := C) (continuous_fourier_of_integrable integrable_sawtoothWeight).aestronglyMeasurable
        (Eventually.of_forall hC)).neg).congr (Eventually.of_forall fun η => ?_)
      have hne : (1 / 2 + (2 * π * η : ℝ) * I : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this
      simp only [Pi.neg_apply]
      set s : ℂ := 1 / 2 + (2 * π * η : ℝ) * I
      rw [fourier_sawtoothWeight, show -(-riemannZeta s / s * (s * g η)) = riemannZeta s * g η * (s / s) by ring,
        div_self hne, mul_one]
    have hsplit : (∫ η, B η * g η) = (∫ η : ℝ, ((4 * π ^ 2 * η ^ 2 : ℝ) : ℂ) * 𝓕 ψ η * g η) +
        c * (∫ η, 𝓕 ψ η * g η) - κ * ∫ η : ℝ, riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) * g η := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (f := fun η : ℝ => ((4 * π ^ 2 * η ^ 2 : ℝ) : ℂ) * 𝓕 ψ η * g η)
          (g := fun η => c * (𝓕 ψ η * g η)) hF1 (hF2.const_mul c),
        ← integral_sub (f := fun η : ℝ => ((4 * π ^ 2 * η ^ 2 : ℝ) : ℂ) * 𝓕 ψ η * g η + c * (𝓕 ψ η * g η))
          (g := fun η : ℝ => κ * (riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) * g η))
          (hF1.add (hF2.const_mul c)) (hF3.const_mul κ)]
      refine integral_congr_ae (Eventually.of_forall fun η => ?_)
      simp only [B]; push_cast; ring
    rw [hsplit, hW']; ring
  have hae : ∀ᵐ x ∂volume, B x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hBc.locallyIntegrable fun g hg hgc => ?_
    have hgC : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hgcC : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) := hgc.comp_left Complex.ofReal_zero
    have := hBint (hgcC.toSchwartzMap hgC)
    have hev : ∀ x, (hgcC.toSchwartzMap hgC) x = ((g x : ℝ) : ℂ) := fun x => rfl
    simp only [hev] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Complex.real_smul]; ring
  have hB0 : B = 0 := (Continuous.ae_eq_iff_eq volume hBc continuous_const).mp hae
  have := congrFun hB0 η
  simp only [B, Pi.zero_apply] at this
  linear_combination this

lemma tendsto_mul_bdd_zero {f g : ℝ → ℂ} {l : Filter ℝ} (hf : Tendsto f l (𝓝 0)) {C : ℝ}
    (hg : ∀ x, ‖g x‖ ≤ C) : Tendsto (fun x => f x * g x) l (𝓝 0) := by
  have h2 : Tendsto (fun x => ‖f x‖ * C) l (𝓝 0) := by
    simpa using (tendsto_norm_zero.comp hf).mul_const C
  exact squeeze_zero_norm (fun x => (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (hg x) (norm_nonneg _))) h2

/-- Integration by parts of an H¹(ℝ) function against a Schwartz test: ∫ D' φ = -∫ D φ'. -/
theorem LogH1.integral_deriv_mul_schwartz {D D' : ℝ → ℂ} (hD : LogH1 D D') (φ : 𝓢(ℝ, ℂ)) :
    ∫ t, D' t * φ t = -∫ t, D t * deriv φ t := by
  have hdφ : ⇑(SchwartzMap.derivCLM ℂ ℂ φ) = deriv φ := funext fun x => SchwartzMap.derivCLM_apply ℂ φ x
  have hφd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x => (φ.differentiableAt).hasDerivAt
  have hφ'c : Continuous (deriv (φ : ℝ → ℂ)) := hdφ ▸ (SchwartzMap.derivCLM ℂ ℂ φ).continuous
  have i1 : Integrable (fun t => D' t * φ t) := integrable_mul_of_memLp_two hD.memLp_deriv (φ.memLp 2)
  have i2 : Integrable (fun t => D t * deriv φ t) :=
    integrable_mul_of_memLp_two hD.memLp (hdφ ▸ (SchwartzMap.derivCLM ℂ ℂ φ).memLp 2)
  have hibp : ∀ R : ℝ, ∫ t in (-R)..R, D' t * φ t = D R * φ R - D (-R) * φ (-R) - ∫ t in (-R)..R, D t * deriv φ t :=
    fun R => integral_primitive_mul_deriv hD.integral_eq hD.intervalIntegrable hφd hφ'c (-R) R
  have hL := intervalIntegral_tendsto_integral i1 tendsto_neg_atTop_atBot tendsto_id
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖φ x‖ ≤ C := ⟨_, fun x => by simpa using φ.le_seminorm ℂ 0 0 x⟩
  obtain ⟨hT, hB⟩ := hD.tendsto_zero
  have hb : ∀ u : ℝ → ℝ, Tendsto (fun R => D (u R)) atTop (𝓝 0) →
      Tendsto (fun R => D (u R) * φ (u R)) atTop (𝓝 0) := fun u hu =>
    tendsto_mul_bdd_zero hu (fun R => hC (u R))
  have hR := ((hb id hT).sub (hb (fun R => -R) (hB.comp tendsto_neg_atTop_atBot))).sub
    (intervalIntegral_tendsto_integral i2 tendsto_neg_atTop_atBot tendsto_id)
  have := tendsto_nhds_unique hL (hR.congr fun R => (hibp R).symm)
  rw [this]; ring

/-- The L² Fourier transform paired with a Schwartz test: ∫ φ · 𝓕D = ∫ D · 𝓕φ for D ∈ L². -/
lemma integral_smul_fourier_toLp {D : ℝ → ℂ} (hD : MemLp D 2) (φ : 𝓢(ℝ, ℂ)) :
    ∫ x, φ x • (𝓕 (hD.toLp D) : Lp ℂ 2 (volume : Measure ℝ)) x = ∫ x, D x * 𝓕 (φ : ℝ → ℂ) x := by
  have h1 : ∫ x, φ x • (𝓕 (hD.toLp D) : Lp ℂ 2 (volume : Measure ℝ)) x =
      ((𝓕 (hD.toLp D) : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ)) φ :=
    (Lp.toTemperedDistribution_apply _ φ).symm
  rw [h1, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
    Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [hD.coeFn_toLp] with x hx
  rw [hx, smul_eq_mul, mul_comm, SchwartzMap.fourier_coe]

/-- Uniqueness of H¹ weak solutions of (-∂² + c) D = 0 when 4π²η² + c never vanishes. -/
theorem weak_unique {D D' : ℝ → ℂ} (hD : LogH1 D D') {c : ℂ}
    (hc : ∀ η : ℝ, ((4 * π ^ 2 * η ^ 2 : ℝ) : ℂ) + c ≠ 0)
    (hW : ∀ φ : 𝓢(ℝ, ℂ), (∫ t, D' t * deriv φ t) + c * ∫ t, D t * φ t = 0) : D = 0 := by
  set F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hD.memLp.toLp D) with hF
  set m : ℝ → ℂ := fun x => ((4 * π ^ 2 * x ^ 2 : ℝ) : ℂ) + c
  have hmc : Continuous m := by simp only [m]; fun_prop
  have hFli : LocallyIntegrable (fun x => m x * F x) := by
    have h := ((Lp.memLp F).locallyIntegrable (by norm_num)).locallyIntegrableOn univ
    exact locallyIntegrableOn_univ.mp (h.continuousOn_mul hmc.continuousOn isClosed_univ.isLocallyClosed)
  have hzero : ∀ᵐ x ∂volume, m x * F x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hFli fun g hg hgc => ?_
    have hgC : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hgcC : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) := hgc.comp_left Complex.ofReal_zero
    set G : 𝓢(ℝ, ℂ) := hgcC.toSchwartzMap hgC
    have hGv : ∀ x, G x = ((g x : ℝ) : ℂ) := fun x => rfl
    have h2C : ContDiff ℝ ∞ (fun x : ℝ => ((-(4 * π ^ 2 * x ^ 2) : ℝ) : ℂ) * G x) := by
      exact (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_id.pow 2)).neg).mul G.smooth'
    have h2c : HasCompactSupport (fun x : ℝ => ((-(4 * π ^ 2 * x ^ 2) : ℝ) : ℂ) * G x) := hgcC.mul_left
    set G2 : 𝓢(ℝ, ℂ) := h2c.toSchwartzMap h2C
    have hG2v : ∀ x, G2 x = ((-(4 * π ^ 2 * x ^ 2) : ℝ) : ℂ) * G x := fun x => rfl
    -- the test φ = 𝓕 G and its second derivative 𝓕 G2
    have hGI : Integrable (G : ℝ → ℂ) := G.integrable
    have hxG : Integrable (fun x : ℝ => x • G x) := by
      refine (G.integrable_pow_mul volume 1).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
      rw [norm_smul, pow_one]
    have hG1 : Integrable (fun x : ℝ => (-2 * π * I * x) • G x) := by
      have := hxG.const_mul (-2 * π * I)
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Complex.real_smul, smul_eq_mul]; ring
    have hx2 : Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * G x) := by
      refine (G.integrable_pow_mul volume 2).mono' (by fun_prop) (Eventually.of_forall fun x => le_of_eq ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x),
        sq_abs]
    have hxG1 : Integrable (fun x : ℝ => x • ((-2 * π * I * x) • G x)) := by
      refine (hx2.const_mul (-2 * π * I)).congr (Eventually.of_forall fun x => ?_)
      simp only [Complex.real_smul, smul_eq_mul]; push_cast; ring
    have hd1 : deriv (𝓕 (G : ℝ → ℂ)) = 𝓕 (fun x : ℝ => (-2 * π * I * x) • G x) := Real.deriv_fourier hGI hxG
    have hd2 : deriv (deriv (𝓕 (G : ℝ → ℂ))) = 𝓕 (G2 : ℝ → ℂ) := by
      rw [hd1, Real.deriv_fourier hG1 hxG1]
      congr 1; funext x
      simp only [hG2v, smul_eq_mul]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    set φ : 𝓢(ℝ, ℂ) := 𝓕 G
    have hφv : (φ : ℝ → ℂ) = 𝓕 (G : ℝ → ℂ) := SchwartzMap.fourier_coe G
    have hW' := hW φ
    -- integrate by parts against φ' (a Schwartz function)
    have hdφ : ⇑(SchwartzMap.derivCLM ℂ ℂ φ) = deriv φ := funext fun x => SchwartzMap.derivCLM_apply ℂ φ x
    have hibp := hD.integral_deriv_mul_schwartz (SchwartzMap.derivCLM ℂ ℂ φ)
    rw [hdφ, hφv, hd2] at hibp
    rw [hφv] at hW'
    rw [hibp, ← integral_smul_fourier_toLp hD.memLp G2, ← integral_smul_fourier_toLp hD.memLp G] at hW'
    -- assemble ∫ g • (m F) = 0
    have i1 : Integrable (fun x => G2 x • F x) :=
      (integrable_mul_of_memLp_two (G2.memLp 2) (Lp.memLp F)).congr (Eventually.of_forall fun x => rfl)
    have i2 : Integrable (fun x => G x • F x) :=
      (integrable_mul_of_memLp_two (G.memLp 2) (Lp.memLp F)).congr (Eventually.of_forall fun x => rfl)
    calc ∫ x, g x • (m x * F x) = -(∫ x, G2 x • F x) + c * ∫ x, G x • F x := by
          rw [← integral_neg, ← integral_const_mul, ← integral_add (f := fun x => -(G2 x • F x))
            (g := fun x => c * (G x • F x)) i1.neg (i2.const_mul c)]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [m, hG2v, hGv, Complex.real_smul, smul_eq_mul]; push_cast; ring
      _ = 0 := by linear_combination hW'
  have hF0 : (F : ℝ → ℂ) =ᵐ[volume] 0 := by
    filter_upwards [hzero] with x hx
    exact (mul_eq_zero.mp hx).resolve_left (hc x)
  have hFz : F = 0 := (Lp.eq_zero_iff_ae_eq_zero).mpr hF0
  have hD0 : hD.memLp.toLp D = 0 := by
    have h := congrArg (fun f : Lp ℂ 2 (volume : Measure ℝ) => 𝓕⁻ f) hFz
    simpa [hF] using h
  have hae : D =ᵐ[volume] 0 := by
    have := hD.memLp.coeFn_toLp
    rw [hD0] at this
    filter_upwards [this, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x h1 h2
    rw [← h1, h2]
  exact (Continuous.ae_eq_iff_eq volume hD.continuous continuous_const).mp hae

end FourierQuotient

section Polarization

lemma fourier_add_mul {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (a : ℂ) (η : ℝ) :
    𝓕 (fun x => f x + a * g x) η = 𝓕 f η + a * 𝓕 g η := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  have h1 : Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * η) * I) * f v) :=
    hf.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun v => by
      rw [Complex.norm_exp_ofReal_mul_I])
  have h2 : Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * η) * I) * g v) :=
    hg.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun v => by
      rw [Complex.norm_exp_ofReal_mul_I])
  rw [← integral_const_mul, ← integral_add h1 (h2.const_mul a)]
  exact integral_congr_ae (Eventually.of_forall fun v => by ring)

lemma conj_mul_polarization (a b : ℂ) : starRingEnd ℂ a * b =
    (((‖a + b‖ ^ 2 - ‖a - b‖ ^ 2) / 4 : ℝ) : ℂ) +
      (((‖a - I * b‖ ^ 2 - ‖a + I * b‖ ^ 2) / 4 : ℝ) : ℂ) * I := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Polarized Plancherel on L¹ ∩ L²: ∫ conj f g = ∫ conj (𝓕 f) 𝓕 g. -/
theorem integral_conj_mul_fourier {f g : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2)
    (hg1 : Integrable g) (hg2 : MemLp g 2) :
    ∫ x, starRingEnd ℂ (f x) * g x = ∫ η, starRingEnd ℂ (𝓕 f η) * 𝓕 g η := by
  have key : ∀ a : ℂ, (∫ x, ‖f x + a * g x‖ ^ 2) = ∫ η, ‖𝓕 f η + a * 𝓕 g η‖ ^ 2 := by
    intro a
    have h := integral_norm_sq_fourier_of_mem (f := fun x => f x + a * g x) (hf1.add (hg1.const_mul a))
      (hf2.add (hg2.const_mul a))
    rw [← h.2]
    exact integral_congr_ae (Eventually.of_forall fun η => by
      simp only; rw [fourier_add_mul hf1 hg1 a η])
  have hI : ∀ (u v : ℝ → ℂ), MemLp u 2 → MemLp v 2 → ∀ a : ℂ,
      Integrable (fun x => ‖u x + a * v x‖ ^ 2) := fun u v hu hv a =>
    (memLp_two_iff_integrable_sq_norm (hu.add (hv.const_mul a)).1).mp (hu.add (hv.const_mul a))
  -- the Fourier transforms are in L²
  have hFf : MemLp (𝓕 f) 2 := (memLp_two_iff_integrable_sq_norm
    (continuous_fourier_of_integrable hf1).aestronglyMeasurable).mpr (integral_norm_sq_fourier_of_mem hf1 hf2).1
  have hFg : MemLp (𝓕 g) 2 := (memLp_two_iff_integrable_sq_norm
    (continuous_fourier_of_integrable hg1).aestronglyMeasurable).mpr (integral_norm_sq_fourier_of_mem hg1 hg2).1
  have expand : ∀ (u v : ℝ → ℂ), MemLp u 2 → MemLp v 2 → ∫ x, starRingEnd ℂ (u x) * v x =
      (((((∫ x, ‖u x + 1 * v x‖ ^ 2) - ∫ x, ‖u x + (-1) * v x‖ ^ 2) / 4 : ℝ)) : ℂ) +
        (((((∫ x, ‖u x + (-I) * v x‖ ^ 2) - ∫ x, ‖u x + I * v x‖ ^ 2) / 4 : ℝ)) : ℂ) * I := by
    intro u v hu hv
    have hp : ∀ x, starRingEnd ℂ (u x) * v x =
        ((((‖u x + 1 * v x‖ ^ 2 - ‖u x + (-1) * v x‖ ^ 2) / 4 : ℝ)) : ℂ) +
          ((((‖u x + (-I) * v x‖ ^ 2 - ‖u x + I * v x‖ ^ 2) / 4 : ℝ)) : ℂ) * I := fun x => by
      rw [conj_mul_polarization]; simp only [one_mul, neg_mul, ← sub_eq_add_neg]
    simp_rw [hp]
    rw [integral_add, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      integral_div, integral_div, integral_sub (hI u v hu hv 1) (hI u v hu hv (-1)),
      integral_sub (hI u v hu hv (-I)) (hI u v hu hv I)]
    · exact (((hI u v hu hv 1).sub (hI u v hu hv (-1))).div_const 4).ofReal
    · exact ((((hI u v hu hv (-I)).sub (hI u v hu hv I)).div_const 4).ofReal).mul_const I
  rw [expand f g hf2 hg2, expand (𝓕 f) (𝓕 g) hFf hFg, key 1, key (-1), key (-I), key I]

end Polarization

section Sample

lemma continuousOn_srhoCellDeriv_Icc (ρ : ℂ) (n : ℕ) :
    ContinuousOn (srhoCellDeriv ρ n) (Icc (n : ℝ) (n + 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : srhoCellDeriv ρ 0 = fun _ => 0 := funext (srhoCellDeriv_zero ρ)
    rw [this]; exact continuousOn_const
  · exact (continuousOn_srhoCellDeriv ρ n).mono fun x hx =>
      lt_of_lt_of_le (by exact_mod_cast hn) hx.1

/-- One cell of the summation by parts: ∫_n^(n+1) {x} h'(x) dx = h(n+1) - ∫_n^(n+1) h. -/
lemma integral_fract_mul_deriv_cell (ρ : ℂ) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1), ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x =
      zeroProfile ρ ((n : ℝ) + 1) - ∫ x in (n : ℝ)..(n + 1), zeroProfile ρ x := by
  set b := normalizationBrho ρ
  set G : ℝ → ℂ := fun x => ((x - n : ℝ) : ℂ) * -(srhoCellDeriv ρ n x / b)
  have hle : (n : ℝ) ≤ n + 1 := by linarith
  have hGc : ContinuousOn G (Icc (n : ℝ) (n + 1)) :=
    ((Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).continuousOn).mul
      ((continuousOn_srhoCellDeriv_Icc ρ n).div_const b).neg
  have hhc := continuous_zeroProfile ρ
  have hF : ∀ x ∈ Ioo (n : ℝ) (n + 1), HasDerivAt (fun y => ((y - n : ℝ) : ℂ) * zeroProfile ρ y)
      (zeroProfile ρ x + G x) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => ((y - n : ℝ) : ℂ)) 1 x := by
      have := ((hasDerivAt_id x).sub_const (n : ℝ)).ofReal_comp
      simpa using this
    have := h1.mul (hasDerivAt_zeroProfile_cell ρ hx)
    exact this.congr_deriv (by simp only [G, b]; ring)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun y => ((y - n : ℝ) : ℂ) * zeroProfile ρ y) hle
    (((Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).mul hhc).continuousOn) hF
    ((hhc.continuousOn.add hGc).intervalIntegrable_of_Icc hle)
  rw [intervalIntegral.integral_add (hhc.intervalIntegrable _ _) (hGc.intervalIntegrable_of_Icc hle)] at hFTC
  have hcongr : ∫ x in (n : ℝ)..(n + 1), ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x =
      ∫ x in (n : ℝ)..(n + 1), G x := by
    have hnull : (volume : Measure ℝ) {((n : ℝ) + 1)} = 0 := measure_singleton _
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxI
    rw [uIoc_of_le hle] at hxI
    have hx2 : x < (n : ℝ) + 1 := lt_of_le_of_ne hxI.2 (fun h => hx (by simp [h]))
    have hfl : ⌊x⌋ = (n : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; exact ⟨hxI.1.le, hx2⟩
    simp only [G, Int.fract, hfl, Int.cast_natCast]
    rw [zeroProfileDeriv_eq_cell ρ ⟨hxI.1.le, hx2⟩]
  rw [hcongr]
  have e1 : ((((n : ℝ) + 1 - n : ℝ)) : ℂ) = 1 := by push_cast; ring
  have e0 : (((n : ℝ) - n : ℝ) : ℂ) = 0 := by simp
  simp only [e1, e0, one_mul, zero_mul, sub_zero] at hFTC
  linear_combination hFTC

lemma integrableOn_fract_mul_zeroProfileDeriv {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := zeroProfileDeriv_bound hz h0 h1
  have hm : AEStronglyMeasurable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x) volume :=
    ((Complex.measurable_ofReal.comp measurable_fract).mul
      (measurable_zeroProfileDeriv ρ)).aestronglyMeasurable
  have hb : ∀ x : ℝ, 0 < x →
      ‖((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x‖ ≤ C * min 1 (x ^ (-2 : ℝ)) := by
    intro x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one x).le).trans (hC x hx)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' ((continuous_const (y := C)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      hm.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx => ?_)
    exact (hb x hx.1).trans (mul_le_of_le_one_right hC0 (min_le_left _ _))
  · refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      zero_lt_one).const_mul C) hm.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    exact (hb x (lt_trans zero_lt_one hx)).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC0)

/-- Summation by parts with every endpoint term: the sample defect S_ρ - 1/2 is ∫_0^∞ {x} h'(x) dx. -/
theorem profileSampleDefect_eq_integral {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    profileSampleDefect ρ = ∫ x in Ioi (0 : ℝ), ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x := by
  have hI := integrableOn_fract_mul_zeroProfileDeriv hz h0 h1
  have hT1 := intervalIntegral_tendsto_integral_Ioi 0 hI tendsto_natCast_atTop_atTop
  have hT2 := intervalIntegral_tendsto_integral_Ioi 0 (integrable_zeroProfile hz h0 h1).integrableOn
    tendsto_natCast_atTop_atTop
  have hT3 := (summable_zeroProfile_nat hz h0 h1).hasSum.tendsto_sum_nat
  have heq : ∀ N : ℕ, ∫ x in (0 : ℝ)..N, ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x =
      (∑ n ∈ Finset.range N, zeroProfile ρ (n + 1)) - ∫ x in (0 : ℝ)..N, zeroProfile ρ x := by
    intro N
    have hii : ∀ k < N, IntervalIntegrable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x)
        volume ((fun k : ℕ => (k : ℝ)) k) ((fun k : ℕ => (k : ℝ)) (k + 1)) := by
      intro k _
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)).mpr
        (hI.mono_set fun x hx => lt_of_le_of_lt (Nat.cast_nonneg k) hx.1)
    have hii2 : ∀ k < N, IntervalIntegrable (zeroProfile ρ) volume ((fun k : ℕ => (k : ℝ)) k)
        ((fun k : ℕ => (k : ℝ)) (k + 1)) :=
      fun k _ => (continuous_zeroProfile ρ).intervalIntegrable _ _
    have hs1 := intervalIntegral.sum_integral_adjacent_intervals hii
    have hs2 := intervalIntegral.sum_integral_adjacent_intervals hii2
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hs1 hs2
    rw [← hs1, ← hs2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => integral_fract_mul_deriv_cell ρ k
  have hT : Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..N, ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x)
      atTop (𝓝 (profileSampleDefect ρ)) := by
    have := hT3.sub hT2
    rw [integral_Ioi_zeroProfile hz h0 h1] at this
    exact this.congr fun N => (heq N).symm
  exact tendsto_nhds_unique hT hT1

lemma logUnitaryDeriv_sub_half (h h' : ℝ → ℂ) (t : ℝ) :
    logUnitaryDeriv h h' t - logUnitary h t / 2 =
      (Real.exp (t / 2) : ℂ) * ((Real.exp t : ℂ) * h' (Real.exp t)) := by
  simp only [logUnitaryDeriv, logUnitary]; ring

lemma sawtooth_mul_shift (h h' : ℝ → ℂ) (t : ℝ) :
    sawtoothWeight t * (logUnitaryDeriv h h' t - logUnitary h t / 2) =
      Real.exp t • (((Int.fract (Real.exp t) : ℝ) : ℂ) * h' (Real.exp t)) := by
  rw [logUnitaryDeriv_sub_half, sawtoothWeight, Complex.real_smul, Complex.ofReal_mul]
  have e : (Real.exp (-t / 2) : ℂ) * (Real.exp (t / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show -t / 2 + t / 2 = 0 by ring, Real.exp_zero,
      Complex.ofReal_one]
  linear_combination (((Int.fract (Real.exp t) : ℝ) : ℂ) * (Real.exp t : ℂ) * h' (Real.exp t)) * e

/-- The sample defect as the H⁻¹-H¹ pairing ⟨𝔤, ψ⟩ = ∫ w (ψ' - ψ/2) of the actual force with the
log-unitary profile. -/
theorem profileSampleDefect_eq_pairing {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    profileSampleDefect ρ = ∫ t, sawtoothWeight t *
      (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t - logUnitary (zeroProfile ρ) t / 2) := by
  rw [profileSampleDefect_eq_integral hz h0 h1, ← integral_exp_smul_comp]
  exact integral_congr_ae (Eventually.of_forall fun t => (sawtooth_mul_shift _ _ t).symm)

/-- Polarized Plancherel in the log convention: ∫ conj f g = (1/2π) ∫ conj (𝓕_log f) 𝓕_log g. -/
theorem integral_conj_mul_logFourier {f g : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2)
    (hg1 : Integrable g) (hg2 : MemLp g 2) :
    ∫ t, starRingEnd ℂ (f t) * g t =
      1 / (2 * π) * ∫ ξ, starRingEnd ℂ (logFourier f ξ) * logFourier g ξ := by
  rw [integral_conj_mul_fourier hf1 hf2 hg1 hg2]
  simp_rw [logFourier_eq_fourier]
  have := Measure.integral_comp_div (fun η => starRingEnd ℂ (𝓕 f η) * 𝓕 g η) (2 * π)
  rw [this, abs_of_pos Real.two_pi_pos, Complex.real_smul]
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  push_cast
  field_simp

end Sample

section Resolvent

lemma logH1_zeroProfile {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    LogH1 (logUnitary (zeroProfile ρ)) (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ)) :=
  (log_unitary_form_identity _ _ (zeroProfile_mem_logFormDomain hz h0 h1)).2.2.2.2.2

lemma integrable_logUnitary_zeroProfile {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : Integrable (logUnitary (zeroProfile ρ)) := by
  obtain ⟨K, -, hK⟩ := norm_logUnitary_zeroProfile_le hz h0 h1
  exact (integrable_exp_neg_abs_half.const_mul K).mono'
    (logH1_zeroProfile hz h0 h1).continuous.aestronglyMeasurable (Eventually.of_forall hK)

lemma integrable_logUnitaryDeriv_zeroProfile {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : Integrable (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ)) := by
  obtain ⟨K, -, hK⟩ := norm_logUnitaryDeriv_zeroProfile_le hz h0 h1
  exact (integrable_exp_neg_abs_half.const_mul K).mono'
    (logH1_zeroProfile hz h0 h1).measurable_deriv.aestronglyMeasurable (Eventually.of_forall hK)

/-- The weak forced equation of the actual log profile on Schwartz tests:
∫ ψ' φ' + (1/4 - κ) ∫ ψ φ = κ ⟨𝔤, φ⟩. -/
theorem zeroProfile_weak_equation {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : 𝓢(ℝ, ℂ)) :
    (∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv φ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (zeroProfile ρ) t * φ t =
      spectralKappa ρ * nativeLogForce φ := by
  have hD := logH1_zeroProfile hz h0 h1
  rw [nativeLogForce_apply]
  exact weak_extend hD.memLp hD.memLp_deriv (fun χ hχ hc => log_weak_compact hz h0 h1 hχ hc) φ

lemma spectralEnergy_sub_ne {κ : ℂ} (hκ : κ ∈ spectralResolventSet) (ξ : ℝ) :
    (spectralEnergy ξ : ℂ) - κ ≠ 0 := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap hκ
  intro h
  have := hgap _ (quarter_le_spectralEnergy ξ)
  rw [h, norm_zero] at this
  linarith

/-- The undivided Fourier identity (a(ξ) - κ) 𝓕_log ψ(ξ) = κ ζ(1/2 + iξ) for every actual zero in the
strip, with no hypothesis on κ (critical-line zeros included). It is a supporting result: the
removable quotient remark for critical-line zeros is not promoted to a root. -/
theorem logFourier_zeroProfile_undivided {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (ξ : ℝ) :
    ((spectralEnergy ξ : ℂ) - spectralKappa ρ) * logFourier (logUnitary (zeroProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) := by
  have hD := logH1_zeroProfile hz h0 h1
  have hq := fourier_quotient_of_weak hD.integral_eq hD.intervalIntegrable
    (integrable_logUnitary_zeroProfile hz h0 h1) (integrable_logUnitaryDeriv_zeroProfile hz h0 h1)
    (zeroProfile_weak_equation hz h0 h1) (ξ / (2 * π))
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have e1 : (2 * π * (ξ / (2 * π)) : ℝ) = ξ := by field_simp
  have e2 : (4 * (π : ℂ) ^ 2 * ((ξ / (2 * π) : ℝ) : ℂ) ^ 2 + (1 / 4 - spectralKappa ρ)) =
      (spectralEnergy ξ : ℂ) - spectralKappa ρ := by
    have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast hπ
    rw [spectralEnergy]; push_cast; field_simp; ring
  rw [e1, e2] at hq
  rw [logFourier_eq_fourier]
  exact hq

/-- The actual log-Fourier quotient 𝓕_log ψ(ξ) = κ ζ(1/2 + iξ)/(a(ξ) - κ) off the cut. -/
theorem logFourier_zeroProfile_quotient {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : spectralKappa ρ ∈ spectralResolventSet) (ξ : ℝ) :
    logFourier (logUnitary (zeroProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ) := by
  rw [eq_div_iff (spectralEnergy_sub_ne hκ ξ), mul_comm]
  exact logFourier_zeroProfile_undivided hz h0 h1 ξ

/-- 𝓕_log ψ' = iξ 𝓕_log ψ for the actual log profile. -/
theorem logFourier_zeroProfile_deriv {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (ξ : ℝ) :
    logFourier (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ)) ξ =
      (ξ : ℂ) * I * logFourier (logUnitary (zeroProfile ρ)) ξ := by
  have hD := logH1_zeroProfile hz h0 h1
  have h := fourier_deriv_of_primitive hD.integral_eq hD.intervalIntegrable
    (integrable_logUnitary_zeroProfile hz h0 h1) (integrable_logUnitaryDeriv_zeroProfile hz h0 h1)
    (ξ / (2 * π))
  rw [logFourier_eq_fourier, logFourier_eq_fourier, h]
  have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  congr 1
  push_cast; field_simp

lemma conj_shift_algebra (Z κ : ℂ) (ξ : ℝ) (a : ℂ) :
    starRingEnd ℂ (-Z / (1 / 2 + ξ * I)) *
      ((ξ : ℂ) * I * (κ * Z / (a - κ)) + (-1 / 2 : ℂ) * (κ * Z / (a - κ))) =
      κ * (starRingEnd ℂ Z * Z) * (a - κ)⁻¹ := by
  have hs : starRingEnd ℂ (1 / 2 + ξ * I) = 1 / 2 - ξ * I := by
    apply Complex.ext <;> simp
  have hs0 : (1 / 2 - (ξ : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  set q := κ * Z / (a - κ)
  have e : (ξ : ℂ) * I * q + (-1 / 2 : ℂ) * q = -(1 / 2 - ξ * I) * q := by ring
  rw [map_div₀, map_neg, hs, e]
  generalize (1 / 2 - (ξ : ℂ) * I) = u at hs0 ⊢
  have : -starRingEnd ℂ Z / u * (-u * q) = starRingEnd ℂ Z * q := by field_simp
  rw [this]
  simp only [q]
  ring

/-- b = κ M(κ): the sample defect is κ times the arithmetic Stieltjes function. -/
theorem profileSampleDefect_eq_kappa_stieltjes {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    profileSampleDefect ρ = spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ) := by
  set ψ := logUnitary (zeroProfile ρ) with hψdef
  set ψ' := logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) with hψ'def
  have hD : LogH1 ψ ψ' := logH1_zeroProfile hz h0 h1
  have hψ1 : Integrable ψ := integrable_logUnitary_zeroProfile hz h0 h1
  have hψ'1 : Integrable ψ' := integrable_logUnitaryDeriv_zeroProfile hz h0 h1
  set g : ℝ → ℂ := fun t => ψ' t + (-1 / 2 : ℂ) * ψ t with hg
  have hg1 : Integrable g := hψ'1.add (hψ1.const_mul _)
  have hg2 : MemLp g 2 := hD.memLp_deriv.add (hD.memLp.const_mul _)
  have hLg : ∀ ξ, logFourier g ξ = logFourier ψ' ξ + (-1 / 2 : ℂ) * logFourier ψ ξ := by
    intro ξ; simp only [logFourier_eq_fourier]; exact fourier_add_mul hψ'1 hψ1 _ _
  have hb : profileSampleDefect ρ = ∫ t, starRingEnd ℂ (sawtoothWeight t) * g t := by
    rw [profileSampleDefect_eq_pairing hz h0 h1]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [g, sawtoothWeight, Complex.conj_ofReal]; ring
  rw [hb, integral_conj_mul_logFourier integrable_sawtoothWeight memLp_two_sawtoothWeight hg1 hg2]
  have hpt : ∀ ξ : ℝ, starRingEnd ℂ (logFourier sawtoothWeight ξ) * logFourier g ξ =
      spectralKappa ρ * ((‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 : ℝ) : ℂ) *
        ((spectralEnergy ξ : ℂ) - spectralKappa ρ)⁻¹ := by
    intro ξ
    rw [hLg, logFourier_zeroProfile_deriv hz h0 h1, logFourier_zeroProfile_quotient hz h0 h1 hκ,
      logFourier_sawtoothWeight]
    have hZ : starRingEnd ℂ (riemannZeta (1 / 2 + ξ * I)) * riemannZeta (1 / 2 + ξ * I) =
        ((‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; ring
    rw [conj_shift_algebra, hZ]
  simp_rw [hpt]
  rw [arithmeticStieltjes, integral_arithmeticSpectralMeasure, ← integral_const_mul,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [arithmeticDensity, Complex.real_smul]
  push_cast
  ring

end Resolvent

section Inversion

/-- The forced log-resolvent at κ: the inverse log-Fourier transform
t ↦ (1/2π) ∫ e^(iξt) κ ζ(1/2 + iξ)/(a(ξ) - κ) dξ of the actual arithmetic quotient. -/
def nativeLogResolvent (κ : ℂ) (t : ℝ) : ℂ :=
  1 / (2 * π) * ∫ ξ : ℝ, cexp (((ξ * t : ℝ) : ℂ) * I) *
    (κ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - κ))

lemma integrable_inv_spectralEnergy : Integrable (fun ξ : ℝ => (spectralEnergy ξ)⁻¹) := by
  refine (integrable_inv_one_add_sq.const_mul 4).mono'
    (continuous_spectralEnergy.inv₀ fun ξ => (spectralEnergy_pos ξ).ne').aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (inv_pos.mpr (spectralEnergy_pos ξ)).le, spectralEnergy]
  have h2 : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
  calc (ξ ^ 2 + 1 / 4)⁻¹ = 4 * (4 * ξ ^ 2 + 1)⁻¹ := by field_simp
    _ ≤ 4 * (1 + ξ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ h2 (by nlinarith [sq_nonneg ξ])) (by norm_num)

/-- The arithmetic quotient κ ζ(1/2 + iξ)/(a(ξ) - κ) is integrable off the cut. -/
lemma integrable_resolvent_quotient {κ : ℂ} (hκ : κ ∈ spectralResolventSet) :
    Integrable (fun ξ : ℝ => κ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - κ)) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap hκ
  set C := ‖κ‖ * (1 + ‖κ‖ / δ)
  have hC : 0 ≤ C := by positivity
  have hm : Continuous (fun ξ : ℝ => κ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - κ)) :=
    (continuous_const.mul continuous_zeta_critical_line).div
      ((Complex.continuous_ofReal.comp continuous_spectralEnergy).sub continuous_const)
      (spectralEnergy_sub_ne hκ)
  refine (((sawtooth_weighted_zeta_moment.1.add integrable_inv_spectralEnergy).const_mul C)).mono'
    hm.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  have ha := spectralEnergy_pos ξ
  have hb := norm_inv_sub_le hδ hgap ξ
  set Z := ‖riemannZeta (1 / 2 + ξ * I)‖
  have hZ : Z ≤ Z ^ 2 + 1 := by nlinarith [sq_nonneg (Z - 1)]
  rw [div_eq_mul_inv, norm_mul, norm_mul]
  calc ‖κ‖ * Z * ‖((spectralEnergy ξ : ℂ) - κ)⁻¹‖
      ≤ ‖κ‖ * Z * ((1 + ‖κ‖ / δ) * (spectralEnergy ξ)⁻¹) := by gcongr
    _ = C * (Z * (spectralEnergy ξ)⁻¹) := by ring
    _ ≤ C * ((Z ^ 2 + 1) * (spectralEnergy ξ)⁻¹) := by gcongr
    _ = C * (Z ^ 2 / (ξ ^ 2 + 1 / 4) + (spectralEnergy ξ)⁻¹) := by
        rw [spectralEnergy]; ring

/-- Fourier inversion: the actual log profile is the forced log-resolvent. -/
theorem logUnitary_zeroProfile_eq_nativeLogResolvent {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    logUnitary (zeroProfile ρ) = nativeLogResolvent (spectralKappa ρ) := by
  set q : ℝ → ℂ := fun ξ =>
    spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ) with hq
  have hD := logH1_zeroProfile hz h0 h1
  have hψ1 := integrable_logUnitary_zeroProfile hz h0 h1
  have h2π : (2 * π : ℝ) ≠ 0 := Real.two_pi_pos.ne'
  have hF : 𝓕 (logUnitary (zeroProfile ρ)) = fun η => q (2 * π * η) := by
    funext η
    have h := logFourier_zeroProfile_quotient hz h0 h1 hκ (2 * π * η)
    rw [logFourier_eq_fourier, show 2 * π * η / (2 * π) = η by field_simp] at h
    exact h
  have hFi : Integrable (𝓕 (logUnitary (zeroProfile ρ))) := by
    rw [hF]; exact (integrable_resolvent_quotient hκ).comp_mul_left' h2π
  have hinv := Continuous.fourierInv_fourier_eq hD.continuous hψ1 hFi
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

end Inversion

section Uniqueness

lemma LogH1.sub {A A' B B' : ℝ → ℂ} (hA : LogH1 A A') (hB : LogH1 B B') :
    LogH1 (fun t => A t - B t) (fun t => A' t - B' t) where
  integral_eq a b := by
    rw [intervalIntegral.integral_sub (hA.intervalIntegrable a b) (hB.intervalIntegrable a b),
      ← hA.integral_eq, ← hB.integral_eq]
    ring
  intervalIntegrable a b := (hA.intervalIntegrable a b).sub (hB.intervalIntegrable a b)
  measurable_deriv := hA.measurable_deriv.sub hB.measurable_deriv
  memLp := hA.memLp.sub hB.memLp
  memLp_deriv := hA.memLp_deriv.sub hB.memLp_deriv

lemma integrable_mul_schwartz {u : ℝ → ℂ} (hu : MemLp u 2) (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun t => u t * φ t) :=
  integrable_mul_of_memLp_two hu (φ.memLp 2)

lemma integrable_mul_deriv_schwartz {u : ℝ → ℂ} (hu : MemLp u 2) (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun t => u t * deriv φ t) := by
  have := integrable_mul_of_memLp_two hu ((SchwartzMap.derivCLM ℂ ℂ φ).memLp 2)
  simpa only [SchwartzMap.derivCLM_apply] using this

/-- Uniqueness among H¹ weak solutions of (-D² + 1/4 - κ) ψ = κ 𝔤 off the cut. -/
theorem zeroProfile_weak_unique {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : spectralKappa ρ ∈ spectralResolventSet) {D D' : ℝ → ℂ} (hDD : LogH1 D D')
    (hW : ∀ φ : 𝓢(ℝ, ℂ), (∫ t, D' t * deriv φ t) + (1 / 4 - spectralKappa ρ) * ∫ t, D t * φ t =
      spectralKappa ρ * nativeLogForce φ) :
    D = logUnitary (zeroProfile ρ) := by
  have hD := logH1_zeroProfile hz h0 h1
  have hE := hDD.sub hD
  have hc : ∀ η : ℝ, ((4 * π ^ 2 * η ^ 2 : ℝ) : ℂ) + (1 / 4 - spectralKappa ρ) ≠ 0 := by
    intro η
    have h := spectralEnergy_sub_ne hκ (2 * π * η)
    rw [spectralEnergy] at h
    convert h using 1
    push_cast; ring
  have hW0 : ∀ φ : 𝓢(ℝ, ℂ), (∫ t, (D' t - logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t) *
      deriv φ t) + (1 / 4 - spectralKappa ρ) * ∫ t, (D t - logUnitary (zeroProfile ρ) t) * φ t = 0 := by
    intro φ
    have e1 : (∫ t, (D' t - logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t) * deriv φ t) =
        (∫ t, D' t * deriv φ t) -
          ∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv φ t := by
      rw [← integral_sub (integrable_mul_deriv_schwartz hDD.memLp_deriv φ)
        (integrable_mul_deriv_schwartz hD.memLp_deriv φ)]
      exact integral_congr_ae (Eventually.of_forall fun t => by ring)
    have e2 : (∫ t, (D t - logUnitary (zeroProfile ρ) t) * φ t) =
        (∫ t, D t * φ t) - ∫ t, logUnitary (zeroProfile ρ) t * φ t := by
      rw [← integral_sub (integrable_mul_schwartz hDD.memLp φ) (integrable_mul_schwartz hD.memLp φ)]
      exact integral_congr_ae (Eventually.of_forall fun t => by ring)
    rw [e1, e2]
    linear_combination hW φ - zeroProfile_weak_equation hz h0 h1 φ
  have h0' := weak_unique hE hc hW0
  funext t
  exact sub_eq_zero.mp (congrFun h0' t)

end Uniqueness

section Norms

/-- The shifted log profile g = ψ' - ψ/2 (written ψ' + (-1/2) ψ). -/
def logShift (ρ : ℂ) (t : ℝ) : ℂ :=
  logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t + (-1 / 2 : ℂ) * logUnitary (zeroProfile ρ) t

lemma logShift_eq (ρ : ℂ) (t : ℝ) :
    logShift ρ t = (Real.exp (t / 2) : ℂ) * ((Real.exp t : ℂ) * zeroProfileDeriv ρ (Real.exp t)) := by
  rw [← logUnitaryDeriv_sub_half, logShift]; ring

lemma integrable_logShift {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    Integrable (logShift ρ) :=
  (integrable_logUnitaryDeriv_zeroProfile hz h0 h1).add
    ((integrable_logUnitary_zeroProfile hz h0 h1).const_mul _)

lemma memLp_logShift {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    MemLp (logShift ρ) 2 :=
  (logH1_zeroProfile hz h0 h1).memLp_deriv.add ((logH1_zeroProfile hz h0 h1).memLp.const_mul _)

lemma logFourier_logShift {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ξ : ℝ) :
    logFourier (logShift ρ) ξ = ((ξ : ℂ) * I - 1 / 2) * logFourier (logUnitary (zeroProfile ρ)) ξ := by
  have h := fourier_add_mul (integrable_logUnitaryDeriv_zeroProfile hz h0 h1)
    (integrable_logUnitary_zeroProfile hz h0 h1) (-1 / 2 : ℂ) (ξ / (2 * π))
  rw [← logFourier_eq_fourier, ← logFourier_eq_fourier, ← logFourier_eq_fourier,
    logFourier_zeroProfile_deriv hz h0 h1] at h
  rw [show logShift ρ = fun t => logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t +
    (-1 / 2 : ℂ) * logUnitary (zeroProfile ρ) t from rfl, h]
  ring

/-- The unitary change of variables for the mixed Gram pairing N(ρ, σ). -/
lemma profileGram_eq_log (ρ σ : ℂ) :
    profileGram ρ σ = ∫ t, starRingEnd ℂ (logUnitary (zeroProfile σ) t) * logUnitary (zeroProfile ρ) t := by
  rw [profileGram, ← integral_exp_smul_comp]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [logUnitary, map_mul, Complex.conj_ofReal, Complex.real_smul]
  rw [← exp_half_sq t, Complex.ofReal_pow]
  ring

/-- The unitary change of variables for the mixed form pairing Q(ρ, σ). -/
lemma profileFormGram_eq_log (ρ σ : ℂ) :
    profileFormGram ρ σ = ∫ t, starRingEnd ℂ (logShift σ t) * logShift ρ t := by
  have hae : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      (x : ℂ) ^ 2 * deriv (zeroProfile ρ) x * starRingEnd ℂ (deriv (zeroProfile σ) x) =
        (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * starRingEnd ℂ (zeroProfileDeriv σ x) := by
    filter_upwards [deriv_zeroProfile_ae ρ, deriv_zeroProfile_ae σ] with x h1 h2
    rw [h1, h2]
  rw [profileFormGram, integral_congr_ae hae, ← integral_exp_smul_comp]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [logShift_eq, map_mul, Complex.conj_ofReal, Complex.real_smul]
  rw [← exp_half_sq t, Complex.ofReal_pow]
  ring

lemma spectral_integral_eq (F : ℝ → ℂ) (c : ℂ) :
    1 / (2 * π) * ∫ ξ : ℝ, c * ((‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 : ℝ) : ℂ) * F ξ =
      c * ∫ ξ, F ξ ∂arithmeticSpectralMeasure := by
  rw [integral_arithmeticSpectralMeasure, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [arithmeticDensity, Complex.real_smul]
  push_cast
  ring

lemma spectral_integral_eq_real (F : ℝ → ℝ) (c : ℝ) :
    1 / (2 * π) * ∫ ξ : ℝ, c * ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 * F ξ =
      c * ∫ ξ, F ξ ∂arithmeticSpectralMeasure := by
  rw [integral_arithmeticSpectralMeasure, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [arithmeticDensity, smul_eq_mul]
  ring

lemma norm_sq_quotient (κ : ℂ) (ξ : ℝ) :
    ‖κ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - κ)‖ ^ 2 =
      ‖κ‖ ^ 2 * ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 * (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ := by
  rw [norm_div, norm_mul, div_pow, mul_pow, div_eq_mul_inv]

/-- ‖h‖² = |κ|² ∫ dω/|a - κ|². -/
theorem zeroProfile_norm_spectral {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 =
      ‖spectralKappa ρ‖ ^ 2 *
        ∫ ξ, (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure := by
  have hU := log_unitary_form_identity _ _ (zeroProfile_mem_logFormDomain hz h0 h1)
  rw [← hU.2.1, (logFourier_plancherel (integrable_logUnitary_zeroProfile hz h0 h1) hU.1).2,
    ← spectral_integral_eq_real]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [logFourier_zeroProfile_quotient hz h0 h1 hκ, norm_sq_quotient]

/-- The Euler form ∫ x² |h'|² = |κ|² ∫ a dω/|a - κ|². -/
theorem zeroProfile_form_spectral {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    logForm (zeroProfileDeriv ρ) =
      ‖spectralKappa ρ‖ ^ 2 * ∫ ξ, spectralEnergy ξ *
        (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure := by
  have hU := log_unitary_form_identity _ _ (zeroProfile_mem_logFormDomain hz h0 h1)
  obtain ⟨hI0, hE0⟩ := logFourier_plancherel (integrable_logUnitary_zeroProfile hz h0 h1) hU.1
  obtain ⟨hI1, hE1⟩ := logFourier_plancherel (integrable_logUnitaryDeriv_zeroProfile hz h0 h1) hU.2.2.2.1
  rw [hU.2.2.2.2.1, ← hU.2.1, hE0, hE1, ← spectral_integral_eq_real]
  rw [show ∀ A B : ℝ, 1 / (2 * π) * A + 1 / 4 * (1 / (2 * π) * B) = 1 / (2 * π) * (A + 1 / 4 * B)
    from fun A B => by ring, ← integral_const_mul, ← integral_add hI1 (hI0.const_mul _)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [logFourier_zeroProfile_deriv hz h0 h1, norm_mul, mul_pow, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, logFourier_zeroProfile_quotient hz h0 h1 hκ,
    norm_sq_quotient, spectralEnergy]
  ring

lemma conj_quotient (κ Z : ℂ) (ξ : ℝ) :
    starRingEnd ℂ (κ * Z / ((spectralEnergy ξ : ℂ) - κ)) =
      starRingEnd ℂ κ * starRingEnd ℂ Z / ((spectralEnergy ξ : ℂ) - starRingEnd ℂ κ) := by
  rw [map_div₀, map_mul, map_sub, Complex.conj_ofReal]

/-- The mixed Gram pairing N(ρ, σ) = κ_ρ conj κ_σ ∫ dω/((a - κ_ρ)(a - conj κ_σ)). -/
theorem profileGram_spectral {ρ σ : ℂ} (hzρ : riemannZeta ρ = 0) (h0ρ : 0 < ρ.re) (h1ρ : ρ.re < 1)
    (hκρ : spectralKappa ρ ∈ spectralResolventSet) (hzσ : riemannZeta σ = 0) (h0σ : 0 < σ.re)
    (h1σ : σ.re < 1) (hκσ : spectralKappa σ ∈ spectralResolventSet) :
    profileGram ρ σ = spectralKappa ρ * starRingEnd ℂ (spectralKappa σ) *
      ∫ ξ, (((spectralEnergy ξ : ℂ) - spectralKappa ρ) *
        ((spectralEnergy ξ : ℂ) - starRingEnd ℂ (spectralKappa σ)))⁻¹ ∂arithmeticSpectralMeasure := by
  rw [profileGram_eq_log, integral_conj_mul_logFourier (integrable_logUnitary_zeroProfile hzσ h0σ h1σ)
    (logH1_zeroProfile hzσ h0σ h1σ).memLp (integrable_logUnitary_zeroProfile hzρ h0ρ h1ρ)
    (logH1_zeroProfile hzρ h0ρ h1ρ).memLp, ← spectral_integral_eq]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [logFourier_zeroProfile_quotient hzσ h0σ h1σ hκσ, logFourier_zeroProfile_quotient hzρ h0ρ h1ρ hκρ,
    conj_quotient]
  have hZ : starRingEnd ℂ (riemannZeta (1 / 2 + ξ * I)) * riemannZeta (1 / 2 + ξ * I) =
      ((‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; ring
  rw [← hZ, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-- The mixed form pairing Q(ρ, σ) = κ_ρ conj κ_σ ∫ a dω/((a - κ_ρ)(a - conj κ_σ)). -/
theorem profileFormGram_spectral {ρ σ : ℂ} (hzρ : riemannZeta ρ = 0) (h0ρ : 0 < ρ.re)
    (h1ρ : ρ.re < 1) (hκρ : spectralKappa ρ ∈ spectralResolventSet) (hzσ : riemannZeta σ = 0)
    (h0σ : 0 < σ.re) (h1σ : σ.re < 1) (hκσ : spectralKappa σ ∈ spectralResolventSet) :
    profileFormGram ρ σ = spectralKappa ρ * starRingEnd ℂ (spectralKappa σ) *
      ∫ ξ, (spectralEnergy ξ : ℂ) * (((spectralEnergy ξ : ℂ) - spectralKappa ρ) *
        ((spectralEnergy ξ : ℂ) - starRingEnd ℂ (spectralKappa σ)))⁻¹ ∂arithmeticSpectralMeasure := by
  rw [profileFormGram_eq_log, integral_conj_mul_logFourier (integrable_logShift hzσ h0σ h1σ)
    (memLp_logShift hzσ h0σ h1σ) (integrable_logShift hzρ h0ρ h1ρ) (memLp_logShift hzρ h0ρ h1ρ),
    ← spectral_integral_eq]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [logFourier_logShift hzσ h0σ h1σ, logFourier_logShift hzρ h0ρ h1ρ,
    logFourier_zeroProfile_quotient hzσ h0σ h1σ hκσ, logFourier_zeroProfile_quotient hzρ h0ρ h1ρ hκρ,
    map_mul, conj_quotient]
  have hZ : starRingEnd ℂ (riemannZeta (1 / 2 + ξ * I)) * riemannZeta (1 / 2 + ξ * I) =
      ((‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; ring
  have hs : starRingEnd ℂ ((ξ : ℂ) * I - 1 / 2) * ((ξ : ℂ) * I - 1 / 2) = (spectralEnergy ξ : ℂ) := by
    rw [spectralEnergy]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, sq] <;> ring
  rw [← hZ, mul_inv]
  linear_combination (starRingEnd ℂ (spectralKappa σ) * starRingEnd ℂ (riemannZeta (1 / 2 + ξ * I)) /
    ((spectralEnergy ξ : ℂ) - starRingEnd ℂ (spectralKappa σ)) *
    (spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ))) * hs

end Norms

section Compatibility

lemma conj_mem_spectralResolventSet {κ : ℂ} (hκ : κ ∈ spectralResolventSet) :
    starRingEnd ℂ κ ∈ spectralResolventSet := by
  rcases hκ with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

lemma arithmeticStieltjes_conj (κ : ℂ) :
    arithmeticStieltjes (starRingEnd ℂ κ) = starRingEnd ℂ (arithmeticStieltjes κ) := by
  rw [arithmeticStieltjes, arithmeticStieltjes, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [map_inv₀, map_sub, Complex.conj_ofReal]

/-- The resolvent identity under ω: (κ - μ) ∫ dω/((a - κ)(a - μ)) = M(κ) - M(μ). -/
lemma resolvent_difference {κ μ : ℂ} (hκ : κ ∈ spectralResolventSet) (hμ : μ ∈ spectralResolventSet) :
    (κ - μ) * ∫ ξ, (((spectralEnergy ξ : ℂ) - κ) * ((spectralEnergy ξ : ℂ) - μ))⁻¹
      ∂arithmeticSpectralMeasure = arithmeticStieltjes κ - arithmeticStieltjes μ := by
  rw [← integral_const_mul, arithmeticStieltjes, arithmeticStieltjes,
    ← integral_sub (integrable_resolvent_kernel hκ) (integrable_resolvent_kernel hμ)]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  have h1 := spectralEnergy_sub_ne hκ ξ
  have h2 := spectralEnergy_sub_ne hμ ξ
  simp only
  field_simp
  ring

/-- The pairing form of the sample in Fourier variables, with its conjugation and normalization. -/
lemma profileSampleDefect_eq_fourier_pairing {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    profileSampleDefect ρ = 1 / (2 * π) * ∫ ξ : ℝ, starRingEnd ℂ (logFourier sawtoothWeight ξ) *
      (((ξ : ℂ) * I - 1 / 2) * logFourier (logUnitary (zeroProfile ρ)) ξ) := by
  have hb : profileSampleDefect ρ = ∫ t, starRingEnd ℂ (sawtoothWeight t) * logShift ρ t := by
    rw [profileSampleDefect_eq_pairing hz h0 h1]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [logShift, sawtoothWeight, Complex.conj_ofReal]; ring
  rw [hb, integral_conj_mul_logFourier integrable_sawtoothWeight memLp_two_sawtoothWeight
    (integrable_logShift hz h0 h1) (memLp_logShift hz h0 h1)]
  simp_rw [logFourier_logShift hz h0 h1]

end Compatibility

section Roots

/-- F2: for an actual zero ρ of ζ in the strip whose parameter κ = ρ(1 - ρ) lies off the cut
[1/4, ∞) (this contains every nonreal κ, i.e. every off-line zero), the log profile
ψ(t) = e^(t/2) h(e^t) lies in H¹ with derivative ψ', solves the weak forced equation
(-D² + 1/4 - κ) ψ = κ 𝔤 against every Schwartz test, is the unique H¹ weak solution, has the actual
log-Fourier quotient κ ζ(1/2 + iξ)/(a(ξ) - κ), and is the forced log-resolvent. -/
theorem native_forced_resolvent_unique {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    LogH1 (logUnitary (zeroProfile ρ)) (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv φ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (zeroProfile ρ) t * φ t =
        spectralKappa ρ * nativeLogForce φ) ∧
    (∀ D D' : ℝ → ℂ, LogH1 D D' →
      (∀ φ : 𝓢(ℝ, ℂ), (∫ t, D' t * deriv φ t) + (1 / 4 - spectralKappa ρ) * ∫ t, D t * φ t =
        spectralKappa ρ * nativeLogForce φ) → D = logUnitary (zeroProfile ρ)) ∧
    (∀ ξ : ℝ, logFourier (logUnitary (zeroProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ)) ∧
    logUnitary (zeroProfile ρ) = nativeLogResolvent (spectralKappa ρ) :=
  ⟨logH1_zeroProfile hz h0 h1, zeroProfile_weak_equation hz h0 h1,
    fun _ _ hDD hW => zeroProfile_weak_unique hz h0 h1 hκ hDD hW,
    logFourier_zeroProfile_quotient hz h0 h1 hκ,
    logUnitary_zeroProfile_eq_nativeLogResolvent hz h0 h1 hκ⟩

/-- F2: the sample b = Σ_{n ≥ 1} h(n) - 1/2 is, by summation by parts with every cell endpoint
term, ∫_0^∞ {x} h'(x) dx; in log variables it is the H⁻¹-H¹ pairing ∫ w (ψ' - ψ/2) of the actual
force 𝔤 = -(D + 1/2) w with ψ, bounded by ‖w‖₂ times the H¹ form; with the real weight's
conjugation and the 1/(2π) Plancherel normalization it equals κ M(κ). -/
theorem native_sample_stieltjes_identity {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    profileSampleDefect ρ = (∑' n : ℕ, zeroProfile ρ (n + 1)) - 1 / 2 ∧
    (∀ n : ℕ, ∫ x in (n : ℝ)..(n + 1), ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x =
      zeroProfile ρ ((n : ℝ) + 1) - ∫ x in (n : ℝ)..(n + 1), zeroProfile ρ x) ∧
    IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x) (Ioi 0) ∧
    profileSampleDefect ρ = ∫ x in Ioi (0 : ℝ), ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x ∧
    profileSampleDefect ρ = ∫ t, sawtoothWeight t *
      (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t - logUnitary (zeroProfile ρ) t / 2) ∧
    ‖profileSampleDefect ρ‖ ≤ (∫ t, ‖sawtoothWeight t‖ ^ 2) ^ (1 / 2 : ℝ) *
      ((∫ t, ‖logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t‖ ^ 2) +
        1 / 4 * ∫ t, ‖logUnitary (zeroProfile ρ) t‖ ^ 2) ^ (1 / 2 : ℝ) ∧
    (∀ t, starRingEnd ℂ (sawtoothWeight t) = sawtoothWeight t) ∧
    profileSampleDefect ρ = 1 / (2 * π) * ∫ ξ : ℝ, starRingEnd ℂ (logFourier sawtoothWeight ξ) *
      (((ξ : ℂ) * I - 1 / 2) * logFourier (logUnitary (zeroProfile ρ)) ξ) ∧
    profileSampleDefect ρ = spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ) := by
  have hpair := profileSampleDefect_eq_pairing hz h0 h1
  refine ⟨rfl, integral_fract_mul_deriv_cell ρ, integrableOn_fract_mul_zeroProfileDeriv hz h0 h1,
    profileSampleDefect_eq_integral hz h0 h1, hpair, ?_, fun t => by rw [sawtoothWeight, Complex.conj_ofReal],
    profileSampleDefect_eq_fourier_pairing hz h0 h1,
    profileSampleDefect_eq_kappa_stieltjes hz h0 h1 hκ⟩
  rw [hpair]
  exact log_fourier_plancherel.2.2.2.2.2.2 _ _ _ memLp_two_sawtoothWeight (logH1_zeroProfile hz h0 h1)

/-- F2 (F2.4)-(F2.5): for an actual zero with nonreal κ, the norm and the Euler form of h are
|κ|² ∫ dω/|a - κ|² and |κ|² ∫ a dω/|a - κ|², and ‖h‖² = |κ|² Im M(κ)/Im κ. For every second actual
zero σ off the cut, the mixed pairings are N(ρ, σ) = κ_ρ conj κ_σ ∫ dω/((a - κ_ρ)(a - conj κ_σ)) and
Q(ρ, σ) = κ_ρ conj κ_σ ∫ a dω/((a - κ_ρ)(a - conj κ_σ)), compatible with the undivided S2 identity
(κ_ρ - conj κ_σ) N = conj κ_σ b_ρ - κ_ρ conj b_σ. Finally |b| ≤ |κ|(1 + |κ|/|Im κ|)(log 2π - γ). -/
theorem native_profile_spectral_norms {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : (spectralKappa ρ).im ≠ 0) :
    ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 =
      ‖spectralKappa ρ‖ ^ 2 *
        ∫ ξ, (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    logForm (zeroProfileDeriv ρ) =
      ‖spectralKappa ρ‖ ^ 2 * ∫ ξ, spectralEnergy ξ *
        (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 =
      ‖spectralKappa ρ‖ ^ 2 * ((arithmeticStieltjes (spectralKappa ρ)).im / (spectralKappa ρ).im) ∧
    (∀ σ : ℂ, riemannZeta σ = 0 → 0 < σ.re → σ.re < 1 → spectralKappa σ ∈ spectralResolventSet →
      profileGram ρ σ = spectralKappa ρ * starRingEnd ℂ (spectralKappa σ) *
        ∫ ξ, (((spectralEnergy ξ : ℂ) - spectralKappa ρ) *
          ((spectralEnergy ξ : ℂ) - starRingEnd ℂ (spectralKappa σ)))⁻¹ ∂arithmeticSpectralMeasure ∧
      profileFormGram ρ σ = spectralKappa ρ * starRingEnd ℂ (spectralKappa σ) *
        ∫ ξ, (spectralEnergy ξ : ℂ) * (((spectralEnergy ξ : ℂ) - spectralKappa ρ) *
          ((spectralEnergy ξ : ℂ) - starRingEnd ℂ (spectralKappa σ)))⁻¹ ∂arithmeticSpectralMeasure ∧
      (spectralKappa ρ - starRingEnd ℂ (spectralKappa σ)) * profileGram ρ σ =
        starRingEnd ℂ (spectralKappa σ) * profileSampleDefect ρ -
          spectralKappa ρ * starRingEnd ℂ (profileSampleDefect σ)) ∧
    ‖profileSampleDefect ρ‖ ≤ ‖spectralKappa ρ‖ * (1 + ‖spectralKappa ρ‖ / |(spectralKappa ρ).im|) *
      (Real.log (2 * π) - Real.eulerMascheroniConstant) := by
  have hR : spectralKappa ρ ∈ spectralResolventSet := Or.inl hκ
  obtain ⟨-, hIm, -, hM, -⟩ := arithmetic_stieltjes_sign_budget hκ
  have hN := zeroProfile_norm_spectral hz h0 h1 hR
  refine ⟨hN, zeroProfile_form_spectral hz h0 h1 hR, by rw [hN, hIm], fun σ hzσ h0σ h1σ hκσ => ?_, ?_⟩
  · have hG := profileGram_spectral hz h0 h1 hR hzσ h0σ h1σ hκσ
    refine ⟨hG, profileFormGram_spectral hz h0 h1 hR hzσ h0σ h1σ hκσ, ?_⟩
    have hD := resolvent_difference hR (conj_mem_spectralResolventSet hκσ)
    rw [arithmeticStieltjes_conj] at hD
    rw [hG, profileSampleDefect_eq_kappa_stieltjes hz h0 h1 hR,
      profileSampleDefect_eq_kappa_stieltjes hzσ h0σ h1σ hκσ, map_mul]
    linear_combination (spectralKappa ρ * starRingEnd ℂ (spectralKappa σ)) * hD
  · rw [profileSampleDefect_eq_kappa_stieltjes hz h0 h1 hR, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hM (norm_nonneg _)

end Roots

end Zeta23.OPICAFollowup
