import Zeta23.ExceptionalZero.PositiveLaplaceTilt
import Zeta23.ExceptionalZero.PositiveMGFContinuation
import Mathlib.Tactic.Linarith

/-!
# A positive Laplace transform cannot continue through its finite abscissa

The abscissa is the infimum of the actual real Laplace-integrability
domain. Positivity makes that domain upward closed. A hypothetical
continuation disk at the abscissa can be recentered at an interior point;
the actual tilted MGF and its positive Taylor coefficients then force
Laplace integrability below the infimum, a contradiction.

No boundary singularity, moment-series summability, or fact about an
actual zeta tail is a premise. Applying this general result to a zeta
tail still requires constructing its positive density and proving the
actual domain and continuation identities internally.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Zeta23.ExceptionalZero

/-- The genuine real integrability domain of the literal Laplace weights. -/
def positiveLaplaceDomain (u : ℝ → ℝ) : Set ℝ :=
  {p | Integrable (positiveLaplaceWeight u p) positiveLaplaceHalfLine}

/-- Its real abscissa. The results using it explicitly require a nonempty
domain bounded below; no convention for the other cases is used. -/
def positiveLaplaceAbscissa (u : ℝ → ℝ) : ℝ := sInf (positiveLaplaceDomain u)

/-- Positivity on the half-line makes the actual integrability domain
upward closed. -/
theorem integrable_positiveLaplaceWeight_mono {u : ℝ → ℝ} {p q : ℝ}
    (hu : Measurable u) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (hLaplace : Integrable (positiveLaplaceWeight u p) positiveLaplaceHalfLine)
    (hpq : p ≤ q) :
    Integrable (positiveLaplaceWeight u q) positiveLaplaceHalfLine := by
  have hmeas : AEStronglyMeasurable (positiveLaplaceWeight u q) positiveLaplaceHalfLine :=
    (hu.mul ((measurable_const.mul measurable_id).exp)).aestronglyMeasurable
  refine hLaplace.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  have hut : 0 ≤ u t := hnonneg t ht
  unfold positiveLaplaceWeight
  rw [Real.norm_of_nonneg (mul_nonneg hut (Real.exp_pos _).le)]
  change u t * Real.exp (-q * t) ≤ u t * Real.exp (-p * t)
  apply mul_le_mul_of_nonneg_left _ hut
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Every genuinely integrable parameter lies above the actual abscissa. -/
theorem positiveLaplaceAbscissa_le_of_integrable {u : ℝ → ℝ} {p : ℝ}
    (hbelow : BddBelow (positiveLaplaceDomain u))
    (hp : Integrable (positiveLaplaceWeight u p) positiveLaplaceHalfLine) :
    positiveLaplaceAbscissa u ≤ p := csInf_le hbelow hp

/-- All real parameters strictly above the finite abscissa belong to
the genuine domain; this is obtained from positivity and the infimum. -/
theorem integrable_positiveLaplaceWeight_of_abscissa_lt {u : ℝ → ℝ} {p : ℝ}
    (hu : Measurable u) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (hne : (positiveLaplaceDomain u).Nonempty)
    (hp : positiveLaplaceAbscissa u < p) :
    Integrable (positiveLaplaceWeight u p) positiveLaplaceHalfLine := by
  obtain ⟨q, hq, hqp⟩ := exists_lt_of_csInf_lt hne hp
  exact integrable_positiveLaplaceWeight_mono hu hnonneg hq hqp.le

/-- A continuation agreeing with the actual Laplace integral on the right
part of a disk cannot be differentiable throughout that disk at the
actual finite abscissa. -/
theorem not_differentiable_positiveLaplace_continuation_at_abscissa
    {u : ℝ → ℝ} {H : ℂ → ℂ} {r : ℝ}
    (hu : Measurable u) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (hne : (positiveLaplaceDomain u).Nonempty)
    (hbelow : BddBelow (positiveLaplaceDomain u)) (hr : 0 < r)
    (hagree : ∀ z ∈ Metric.ball (positiveLaplaceAbscissa u : ℂ) r,
      positiveLaplaceAbscissa u < z.re → H z = positiveLaplaceTransform u z) :
    ¬ DifferentiableOn ℂ H (Metric.ball (positiveLaplaceAbscissa u : ℂ) r) := by
  intro hH
  let σ : ℝ := positiveLaplaceAbscissa u
  let p0 : ℝ := σ + r / 4
  let R : ℝ := 3 * r / 4
  let K : ℂ → ℂ := fun z => H ((p0 : ℂ) - z)
  have hp0 : σ < p0 := by dsimp [p0]; linarith
  have hbase : ‖(p0 : ℂ) - (σ : ℂ)‖ = r / 4 := by
    rw [← Complex.ofReal_sub, Complex.norm_real]
    have hsub : p0 - σ = r / 4 := by dsimp [p0]; ring
    rw [hsub, Real.norm_of_nonneg (by linarith : 0 ≤ r / 4)]
  have hmap : MapsTo (fun z : ℂ => (p0 : ℂ) - z)
      (Metric.ball 0 R) (Metric.ball (σ : ℂ) r) := by
    intro z hz
    have hzNorm : ‖z‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : ((p0 : ℂ) - z) - (σ : ℂ) = ((p0 : ℂ) - (σ : ℂ)) - z := by ring
    rw [hsub]
    calc
      ‖((p0 : ℂ) - (σ : ℂ)) - z‖ ≤ ‖(p0 : ℂ) - (σ : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ < r := by rw [hbase]; dsimp [R] at hzNorm; linarith
  have hK : DifferentiableOn ℂ K (Metric.ball 0 R) :=
    hH.comp (differentiable_const.sub differentiable_id).differentiableOn hmap
  have hLaplaceNhd : ∀ᶠ p in 𝓝 p0,
      Integrable (positiveLaplaceWeight u p) positiveLaplaceHalfLine := by
    filter_upwards [isOpen_Ioi.eventually_mem hp0] with p hp
    exact integrable_positiveLaplaceWeight_of_abscissa_lt hu hnonneg hne hp
  have h0 : 0 ∈ interior (integrableExpSet id (positiveLaplaceTilt u p0)) :=
    zero_mem_interior_integrableExpSet_positiveLaplaceTilt hu hnonneg hLaplaceNhd
  have hKagree : K =ᶠ[𝓝 (0 : ℂ)] complexMGF id (positiveLaplaceTilt u p0) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by linarith : 0 < r / 8)] with z hz
    have hzNorm : ‖z‖ < r / 8 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hzR : z ∈ Metric.ball (0 : ℂ) R := by
      apply Metric.mem_ball.mpr
      rw [dist_zero_right]
      dsimp [R]
      linarith
    have hright : σ < ((p0 : ℂ) - z).re := by
      rw [Complex.sub_re, Complex.ofReal_re]
      have hre := Complex.re_le_norm z
      dsimp [p0]
      linarith
    change H ((p0 : ℂ) - z) = complexMGF id (positiveLaplaceTilt u p0) z
    rw [complexMGF_positiveLaplaceTilt hu hnonneg p0 z]
    exact hagree _ (hmap hzR) hright
  have hexp : Integrable (fun t : ℝ => Real.exp ((r / 2) * t)) (positiveLaplaceTilt u p0) :=
    integrable_exp_mul_of_complexMGF_continuation (X := id)
      (positiveLaplaceTilt_ae_nonneg u p0) h0 hK hKagree
      (by linarith) (by dsimp [R]; linarith)
  have hnew : Integrable (positiveLaplaceWeight u (p0 - r / 2)) positiveLaplaceHalfLine :=
    (integrable_exp_positiveLaplaceTilt_iff hu hnonneg p0 (r / 2)).mp hexp
  have hle : σ ≤ p0 - r / 2 := positiveLaplaceAbscissa_le_of_integrable hbelow hnew
  have hlt : p0 - r / 2 < σ := by dsimp [p0]; linarith
  exact (not_lt_of_ge hle) hlt

/-- No analytic continuation agreeing with the actual right-hand Laplace
integral in a neighborhood can be analytic at its finite abscissa. -/
theorem not_analyticAt_positiveLaplace_continuation_at_abscissa
    {u : ℝ → ℝ} {H : ℂ → ℂ}
    (hu : Measurable u) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (hne : (positiveLaplaceDomain u).Nonempty)
    (hbelow : BddBelow (positiveLaplaceDomain u))
    (hagree : ∀ᶠ z in 𝓝 (positiveLaplaceAbscissa u : ℂ),
      positiveLaplaceAbscissa u < z.re → H z = positiveLaplaceTransform u z) :
    ¬ AnalyticAt ℂ H (positiveLaplaceAbscissa u : ℂ) := by
  intro hH
  obtain ⟨r, hr, hball⟩ := hH.exists_ball_analyticOnNhd
  obtain ⟨δ, hδ, hagreeBall⟩ := Metric.mem_nhds_iff.mp hagree
  have hpositive : 0 < min r δ := lt_min hr hδ
  apply not_differentiable_positiveLaplace_continuation_at_abscissa
    (H := H) (r := min r δ) hu hnonneg hne hbelow hpositive
  · intro z hz hright
    exact hagreeBall ((Metric.ball_subset_ball (min_le_right r δ)) hz) hright
  · exact hball.differentiableOn.mono (Metric.ball_subset_ball (min_le_left r δ))

/-- The actual total Laplace-transform function itself is singular at
the finite abscissa of its genuine integrability domain. -/
theorem positiveLaplaceTransform_not_analyticAt_abscissa {u : ℝ → ℝ}
    (hu : Measurable u) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (hne : (positiveLaplaceDomain u).Nonempty)
    (hbelow : BddBelow (positiveLaplaceDomain u)) :
    ¬ AnalyticAt ℂ (positiveLaplaceTransform u) (positiveLaplaceAbscissa u : ℂ) :=
  not_analyticAt_positiveLaplace_continuation_at_abscissa hu hnonneg hne hbelow
    (Eventually.of_forall fun _ _ => rfl)

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.integrable_positiveLaplaceWeight_mono
#print axioms Zeta23.ExceptionalZero.positiveLaplaceAbscissa_le_of_integrable
#print axioms Zeta23.ExceptionalZero.integrable_positiveLaplaceWeight_of_abscissa_lt
#print axioms Zeta23.ExceptionalZero.not_differentiable_positiveLaplace_continuation_at_abscissa
#print axioms Zeta23.ExceptionalZero.not_analyticAt_positiveLaplace_continuation_at_abscissa
#print axioms Zeta23.ExceptionalZero.positiveLaplaceTransform_not_analyticAt_abscissa
