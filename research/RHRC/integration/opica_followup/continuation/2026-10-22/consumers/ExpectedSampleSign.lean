import Zeta23.OPICAFollowup.Consumers

/- Supporting physical consumer for the raw-sample sign already stated after (F2.5)
   in the frozen paper. This is not an additional primary root or a new originality
   claim. The arithmetic sample defect differs from normalizationBrho. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology
open Zeta23.OPICAFollowup
namespace OPICASampleSign

theorem form_self (ρ : ℂ) :
    profileFormGram ρ ρ = ((logForm (zeroProfileDeriv ρ) : ℝ) : ℂ) := by
  rw [profileFormGram, logForm, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [deriv_zeroProfile_ae ρ] with x hx
  rw [hx]
  calc
    (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * starRingEnd ℂ (zeroProfileDeriv ρ x) =
        (x : ℂ) ^ 2 * (zeroProfileDeriv ρ x * starRingEnd ℂ (zeroProfileDeriv ρ x)) := by ring
    _ = _ := by rw [Complex.mul_conj']; push_cast; rfl

/-- A genuine necessary restriction on the sample at every hypothetical nonreal-κ zero.
It does not assert an independent reality/sign restriction on that arithmetic sample. -/
theorem sample_im_ratio {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hκ : (spectralKappa ρ).im ≠ 0) :
    (profileSampleDefect ρ).im / (spectralKappa ρ).im =
      logForm (zeroProfileDeriv ρ) / ‖spectralKappa ρ‖ ^ 2 ∧
    0 < (profileSampleDefect ρ).im / (spectralKappa ρ).im ∧
    (profileSampleDefect ρ).im ≠ 0 := by
  let κ := spectralKappa ρ
  let b := profileSampleDefect ρ
  let N := ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2
  let Q := logForm (zeroProfileDeriv ρ)
  have hG : (Q : ℂ) = κ * ((N : ℂ) + starRingEnd ℂ b) := by
    simpa only [κ, b, N, Q, form_self, profileGram_self] using
      (gram_identity hz h0 h1 hz h0 h1)
  have hre := congrArg Complex.re hG
  have him := congrArg Complex.im hG
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_add] at hre him
  have hn : ‖κ‖ ^ 2 = κ.re ^ 2 + κ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have he : ‖κ‖ ^ 2 * b.im = Q * κ.im := by
    rw [hn]
    linear_combination κ.re * him - κ.im * hre
  have hk0 : κ ≠ 0 := by
    intro he
    apply hκ
    change κ.im = 0
    rw [he, Complex.zero_im]
  have hnorm : 0 < ‖κ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hk0)
  have hN : 0 < N := integral_norm_sq_pos hz h0 h1
  have hQ : 0 < Q := by
    have heq := (zeroProfile_mem_logFormDomain hz h0 h1).logForm_eq.2
    have hi : 0 ≤ ∫ t, ‖logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t‖ ^ 2 :=
      integral_nonneg fun t => sq_nonneg _
    dsimp only [Q]
    rw [heq]
    dsimp only [N] at hN
    linarith
  have hratio : b.im / κ.im = Q / ‖κ‖ ^ 2 := by
    apply (div_eq_div_iff hκ (ne_of_gt hnorm)).mpr
    nlinarith [he]
  have hpos : 0 < b.im / κ.im := by rw [hratio]; exact div_pos hQ hnorm
  refine ⟨hratio, hpos, ?_⟩
  intro hb0
  rw [hb0, zero_div] at hpos
  exact (lt_irrefl 0) hpos

/-- An independently established real sample would exclude an off-line zero.
The reality hypothesis is explicit and is not established here. -/
theorem real_sample_implies_on_line {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0)
    (hb : (profileSampleDefect ρ).im = 0) : ρ.re = 1 / 2 := by
  by_contra hre
  have hk : (spectralKappa ρ).im ≠ 0 := by
    have he : (spectralKappa ρ).im = (1 - 2 * ρ.re) * ρ.im := by
      simp only [spectralKappa, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [he]
    exact mul_ne_zero (by intro he; apply hre; linarith) him
  exact (sample_im_ratio hz h0 h1 hk).2.2 hb

end OPICASampleSign
#print axioms OPICASampleSign.form_self
#print axioms OPICASampleSign.sample_im_ratio
#print axioms OPICASampleSign.real_sample_implies_on_line
