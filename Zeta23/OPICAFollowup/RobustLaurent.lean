import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.Basic
import Zeta23.OPICA.ResidueLimits

/-! Actual local Laurent observations on a common disk. Coefficients are defined
from a holomorphic pole clearing and proved equal to normalized contour integrals;
the circle budget is never supplied as a coefficient estimate premise. -/

noncomputable section
namespace Zeta23.OPICAFollowup
open Filter Topology Metric Set Complex
open scoped Real

private def poleClearingOrder {f : ℂ → ℂ} {c : ℂ} (hf : MeromorphicAt f c) : ℕ :=
  Classical.choose hf + 1

private def poleCleared {f : ℂ → ℂ} {c : ℂ} (hf : MeromorphicAt f c) (z : ℂ) : ℂ :=
  (z-c) ^ poleClearingOrder hf * f z

private lemma poleCleared_analyticAt {f : ℂ → ℂ} {c : ℂ} (hf : MeromorphicAt f c) :
    AnalyticAt ℂ (poleCleared hf) c := by
  have ha : AnalyticAt ℂ (fun z => (z-c) ^ Classical.choose hf * f z) c := by
    simpa only [smul_eq_mul] using Classical.choose_spec hf
  have hp : AnalyticAt ℂ (fun z : ℂ => z-c) c := analyticAt_id.sub analyticAt_const
  have heq : poleCleared hf = fun z => (z-c)*((z-c) ^ Classical.choose hf * f z) := by
    funext z
    simp only [poleCleared, poleClearingOrder, pow_succ]
    ring
  rw [heq]
  exact hp.mul ha

private lemma poleCleared_differentiableOn {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : MeromorphicAt f c) (hd : AnalyticOnNhd ℂ f (closedBall c r \ {c})) :
    DifferentiableOn ℂ (poleCleared hf) (closedBall c r) := by
  intro z hz
  by_cases hzc : z = c
  · subst z
    exact (poleCleared_analyticAt hf).differentiableAt.differentiableWithinAt
  · exact ((((analyticAt_id.sub analyticAt_const).pow (poleClearingOrder hf)).mul
      (hd z ⟨hz, hzc⟩)).differentiableAt).differentiableWithinAt

/-- True Laurent coefficient: a normalized Taylor coefficient after clearing the
actual finite central pole. Orders below the clearing range have coefficient zero. -/
def meromorphicLaurentCoefficient (f : ℂ → ℂ) (c : ℂ) (hf : MeromorphicAt f c)
    (j : ℤ) : ℂ :=
  if 0 ≤ j + (poleClearingOrder hf : ℤ) then
    iteratedDeriv (j + (poleClearingOrder hf : ℤ)).toNat (poleCleared hf) c /
      ((j + (poleClearingOrder hf : ℤ)).toNat.factorial : ℂ)
  else 0

/-- Canonical observed coefficient: the actual Laurent coefficient obtained from
the meromorphic germ, independently identified with every admissible circle. -/
abbrev laurentObservedCoefficient (f : ℂ → ℂ) (c : ℂ) (hf : MeromorphicAt f c)
    (j : ℤ) : ℂ := meromorphicLaurentCoefficient f c hf j

/-- Actual uniform error on the common circle. A small budget is a separate
analytic obligation and is not supplied by compact-time convergence. -/
def ContourErrorBudget (f g : ℂ → ℂ) (c : ℂ) (r E : ℝ) : Prop :=
  ∀ z ∈ sphere c r, ‖g z-f z‖ ≤ E

/-- Successive actual errors pay the sum of their circle budgets. -/
lemma ContourErrorBudget.trans {f g h : ℂ → ℂ} {c : ℂ} {r E F : ℝ}
    (hfg : ContourErrorBudget f g c r E) (hgh : ContourErrorBudget g h c r F) :
    ContourErrorBudget f h c r (E+F) := by
  intro z hz
  calc
    ‖h z-f z‖ = ‖(h z-g z)+(g z-f z)‖ := by congr 1; ring
    _ ≤ ‖h z-g z‖+‖g z-f z‖ := norm_add_le _ _
    _ ≤ F+E := add_le_add (hgh z hz) (hfg z hz)
    _ = E+F := add_comm _ _

/-- Correcting both expressions pays the actual correction error as well. -/
lemma ContourErrorBudget.sub {f g C D : ℂ → ℂ} {c : ℂ} {r E F : ℝ}
    (hfg : ContourErrorBudget f g c r E) (hCD : ContourErrorBudget C D c r F) :
    ContourErrorBudget (fun z => f z-C z) (fun z => g z-D z) c r (E+F) := by
  intro z hz
  calc
    ‖(g z-D z)-(f z-C z)‖ = ‖(g z-f z)-(D z-C z)‖ := by congr 1; ring
    _ ≤ ‖g z-f z‖+‖D z-C z‖ := norm_sub_le _ _
    _ ≤ E+F := add_le_add (hfg z hz) (hCD z hz)

/-- The normalized contour observation, separately identified with the true coefficient. -/
def contourLaurentCoefficient (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (j : ℤ) : ℂ :=
  (2*Real.pi*Complex.I : ℂ)⁻¹ *
    ∮ z in C(c,r), (z-c) ^ (-(j+1)) * f z

private lemma sphere_sub_ne_zero {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ∈ sphere c r) : z-c ≠ 0 := by
  have hn := mem_sphere_iff_norm.mp hz
  intro heq
  rw [heq, norm_zero] at hn
  linarith

private lemma weighted_circleIntegrable {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (sphere c r)) (j : ℤ) :
    CircleIntegrable (fun z => (z-c)^(-(j+1))*f z) c r := by
  apply ContinuousOn.circleIntegrable hr.le
  exact ((continuousOn_id.sub continuousOn_const).zpow₀ _
    (fun z hz => Or.inl (sphere_sub_ne_zero hr hz))).mul hf

lemma contourLaurentCoefficient_sub {f g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (sphere c r))
    (hg : ContinuousOn g (sphere c r)) (j : ℤ) :
    contourLaurentCoefficient (fun z => g z-f z) c r j =
      contourLaurentCoefficient g c r j-contourLaurentCoefficient f c r j := by
  unfold contourLaurentCoefficient
  rw [← mul_sub, ← circleIntegral.integral_sub
    (weighted_circleIntegrable hr hg j) (weighted_circleIntegrable hr hf j)]
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  ring

lemma contourLaurentCoefficient_norm_le {f : ℂ → ℂ} {c : ℂ} {r E : ℝ}
    (hr : 0 < r) (hE : ∀ z ∈ sphere c r, ‖f z‖ ≤ E) (j : ℤ) :
    ‖contourLaurentCoefficient f c r j‖ ≤ r^(-j)*E := by
  have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z => (z-c)^(-(j+1))*f z) hr.le (C := r^(-(j+1))*E) (fun z hz => by
      rw [norm_mul, norm_zpow, mem_sphere_iff_norm.mp hz]
      exact mul_le_mul_of_nonneg_left (hE z hz) (zpow_nonneg hr.le _))
  have hp : r*r^(-(j+1)) = r^(-j) := by
    calc
      _ = r^(1:ℤ)*r^(-(j+1)) := by rw [zpow_one]
      _ = r^(-j) := by rw [← zpow_add₀ hr.ne']; congr 1; ring
  simpa only [smul_eq_mul, contourLaurentCoefficient, ← mul_assoc, hp] using hb

lemma contourLaurentCoefficient_eq_normalized_deriv {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedBall c r)) (n : ℕ) :
    contourLaurentCoefficient f c r n = iteratedDeriv n f c / (n.factorial : ℂ) := by
  have hc := hf.circleIntegral_one_div_sub_center_pow_smul hr n
  have hint : (∮ z in C(c,r), (z-c)^(-((n:ℤ)+1))*f z) =
      (2*Real.pi*Complex.I/(n.factorial : ℂ))*iteratedDeriv n f c := by
    simpa only [smul_eq_mul, one_div, zpow_neg, ← Int.natCast_succ, zpow_natCast]
      using hc
  unfold contourLaurentCoefficient
  rw [hint]
  have hpi : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  field_simp

lemma meromorphicLaurentCoefficient_eq_contour {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : MeromorphicAt f c)
    (hd : AnalyticOnNhd ℂ f (closedBall c r \ {c})) {j : ℤ} (hj : -1 ≤ j) :
    meromorphicLaurentCoefficient f c hf j = contourLaurentCoefficient f c r j := by
  have hk : 1 ≤ poleClearingOrder hf := by simp [poleClearingOrder]
  have hdegree : 0 ≤ j+(poleClearingOrder hf : ℤ) := by omega
  let n := (j+(poleClearingOrder hf : ℤ)).toNat
  have hn : (n : ℤ) = j+(poleClearingOrder hf : ℤ) := Int.toNat_of_nonneg hdegree
  have hc := contourLaurentCoefficient_eq_normalized_deriv hr
    (poleCleared_differentiableOn hf hd) n
  rw [meromorphicLaurentCoefficient, if_pos hdegree]
  change _ = contourLaurentCoefficient f c r j
  rw [← hc]
  unfold contourLaurentCoefficient
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  have hzc := sphere_sub_ne_zero hr hz
  simp only [poleCleared]
  rw [← zpow_natCast, ← mul_assoc, ← zpow_add₀ hzc, hn]
  congr 2
  ring

/-- The common meromorphic disk identifies both coefficients with actual contour
integrals before applying the circle error budget. Central pole orders are arbitrary. -/
theorem laurent_coefficient_error_bound {f g : ℂ → ℂ} {c : ℂ} {r E : ℝ}
    (hr : 0 < r) (hf : MeromorphicAt f c) (hg : MeromorphicAt g c)
    (hfd : AnalyticOnNhd ℂ f (closedBall c r \ {c}))
    (hgd : AnalyticOnNhd ℂ g (closedBall c r \ {c}))
    (hE : ContourErrorBudget f g c r E) {j : ℤ} (hj : -1 ≤ j) :
    ‖laurentObservedCoefficient g c hg j-laurentObservedCoefficient f c hf j‖ ≤
      r^(-j)*E := by
  change ‖meromorphicLaurentCoefficient g c hg j-meromorphicLaurentCoefficient f c hf j‖ ≤ _
  have hs : sphere c r ⊆ closedBall c r \ {c} := by
    intro z hz
    exact ⟨sphere_subset_closedBall hz, sub_ne_zero.mp (sphere_sub_ne_zero hr hz)⟩
  rw [meromorphicLaurentCoefficient_eq_contour hr hg hgd hj,
    meromorphicLaurentCoefficient_eq_contour hr hf hfd hj,
    ← contourLaurentCoefficient_sub hr (hfd.continuousOn.mono hs) (hgd.continuousOn.mono hs)]
  exact contourLaurentCoefficient_norm_le hr hE j

theorem laurent_observation_survives {f g : ℂ → ℂ} {c : ℂ} {r E : ℝ}
    (hr : 0 < r) (hf : MeromorphicAt f c) (hg : MeromorphicAt g c)
    (hfd : AnalyticOnNhd ℂ f (closedBall c r \ {c}))
    (hgd : AnalyticOnNhd ℂ g (closedBall c r \ {c}))
    (hE : ContourErrorBudget f g c r E) {j : ℤ} (hj : -1 ≤ j)
    (hstrict : E < ‖laurentObservedCoefficient f c hf j‖*r^j) :
    laurentObservedCoefficient g c hg j ≠ 0 := by
  have hb := laurent_coefficient_error_bound hr hf hg hfd hgd hE hj
  intro hzero
  rw [hzero, zero_sub, norm_neg] at hb
  have hp := zpow_pos hr j
  have hc := (mul_le_mul_of_nonneg_right hb hp.le)
  have hcancel : (r^(-j)*E)*r^j = E := by
    rw [mul_right_comm, ← zpow_add₀ hr.ne', neg_add_cancel, zpow_zero, one_mul]
  rw [hcancel] at hc
  exact (not_lt_of_ge hc) hstrict

lemma meromorphicLaurentCoefficient_eq_normalized_deriv {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : MeromorphicAt f c)
    (ha : AnalyticOnNhd ℂ f (closedBall c r)) (n : ℕ) :
    meromorphicLaurentCoefficient f c hf n = iteratedDeriv n f c/(n.factorial : ℂ) := by
  rw [meromorphicLaurentCoefficient_eq_contour hr hf (ha.mono sdiff_subset) (by omega)]
  exact contourLaurentCoefficient_eq_normalized_deriv hr ha.differentiableOn n

lemma contourLaurentCoefficient_radius_eq {f : ℂ → ℂ} {c : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hf : MeromorphicAt f c)
    (hfr : AnalyticOnNhd ℂ f (closedBall c r \ {c}))
    (hfs : AnalyticOnNhd ℂ f (closedBall c s \ {c})) {j : ℤ} (hj : -1 ≤ j) :
    contourLaurentCoefficient f c r j = contourLaurentCoefficient f c s j := by
  rw [← meromorphicLaurentCoefficient_eq_contour hr hf hfr hj,
    ← meromorphicLaurentCoefficient_eq_contour hs hf hfs hj]

/-- A genuine factorization on the actual circle identifies the leading Laurent
coefficient with the analytic factor value, including the residue degree -1. -/
lemma meromorphicLaurentCoefficient_of_factorization {f U : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : MeromorphicAt f c)
    (hfd : AnalyticOnNhd ℂ f (closedBall c r \ {c}))
    (hU : AnalyticOnNhd ℂ U (closedBall c r)) {j : ℤ} (hj : -1 ≤ j)
    (hfactor : ∀ z ∈ sphere c r, f z = (z-c)^j*U z) :
    meromorphicLaurentCoefficient f c hf j = U c := by
  rw [meromorphicLaurentCoefficient_eq_contour hr hf hfd hj]
  have heq : contourLaurentCoefficient f c r j = contourLaurentCoefficient U c r 0 := by
    unfold contourLaurentCoefficient
    congr 1
    apply circleIntegral.integral_congr hr.le
    intro z hz
    change (z-c)^(-(j+1))*f z = (z-c)^(-(0+1:ℤ))*U z
    rw [hfactor z hz, ← mul_assoc, ← zpow_add₀ (sphere_sub_ne_zero hr hz)]
    congr 2
    ring
  rw [heq]
  simpa using contourLaurentCoefficient_eq_normalized_deriv hr hU.differentiableOn 0

/-- A genuine local factorization identifies the germ-defined coefficient. The
common analytic circle is obtained by shrinking neighborhoods, not assumed as
a coefficient identity. -/
lemma meromorphicLaurentCoefficient_of_germ_factorization {f U : ℂ → ℂ} {c : ℂ}
    (hf : MeromorphicAt f c) (hU : AnalyticAt ℂ U c) {j : ℤ} (hj : -1 ≤ j)
    (hfactor : f =ᶠ[𝓝[≠] c] fun z => (z-c)^j*U z) :
    meromorphicLaurentCoefficient f c hf j = U c := by
  have hfa : ∀ᶠ z in 𝓝 c, z ≠ c → AnalyticAt ℂ f z := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff]
      using hf.eventually_analyticAt
  have hfe : ∀ᶠ z in 𝓝 c, z ≠ c → f z = (z-c)^j*U z := by
    simpa only [Filter.EventuallyEq, eventually_nhdsWithin_iff, mem_compl_iff,
      mem_singleton_iff] using hfactor
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.mp
    (hU.eventually_analyticAt.and (hfa.and hfe))
  have hr : 0 < ε/2 := half_pos hε
  have hnear {z : ℂ} (hz : z ∈ closedBall c (ε/2)) : dist z c < ε :=
    lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith)
  apply meromorphicLaurentCoefficient_of_factorization hr hf
    (fun z hz => (hall (hnear hz.1)).2.1 hz.2)
    (fun z hz => (hall (hnear hz)).1) hj
  intro z hz
  exact (hall (hnear (sphere_subset_closedBall hz))).2.2
    (sub_ne_zero.mp (sphere_sub_ne_zero hr hz))

/-- For holomorphic observations the unnormalized derivative costs an actual factorial. -/
lemma laurent_derivative_error_bound {f g : ℂ → ℂ} {c : ℂ} {r E : ℝ}
    (hr : 0 < r) (hf : MeromorphicAt f c) (hg : MeromorphicAt g c)
    (hfa : AnalyticOnNhd ℂ f (closedBall c r))
    (hga : AnalyticOnNhd ℂ g (closedBall c r))
    (hE : ∀ z ∈ sphere c r, ‖g z-f z‖ ≤ E) (n : ℕ) :
    ‖iteratedDeriv n g c-iteratedDeriv n f c‖ ≤
      (n.factorial : ℝ)*(r^(-(n:ℤ))*E) := by
  have hb := laurent_coefficient_error_bound hr hf hg
    (hfa.mono sdiff_subset) (hga.mono sdiff_subset) hE (j := n) (by omega)
  have heq : iteratedDeriv n g c-iteratedDeriv n f c =
      (n.factorial : ℂ)*(meromorphicLaurentCoefficient g c hg n-
        meromorphicLaurentCoefficient f c hf n) := by
    rw [meromorphicLaurentCoefficient_eq_normalized_deriv hr hg hga,
      meromorphicLaurentCoefficient_eq_normalized_deriv hr hf hfa]
    have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp [hfac]
  rw [heq, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)

def laurentMonomial (a c : ℂ) (j : ℤ) (z : ℂ) : ℂ := a*(z-c)^j

lemma laurentMonomial_meromorphicAt (a c : ℂ) (j : ℤ) :
    MeromorphicAt (laurentMonomial a c j) c := by
  have hp : MeromorphicAt (fun z : ℂ => z-c) c :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  exact (MeromorphicAt.const a c).mul (hp.zpow j)

lemma laurentMonomial_analyticOnNhd (a c : ℂ) (j : ℤ) (s : Set ℂ) :
    AnalyticOnNhd ℂ (laurentMonomial a c j) (s \ {c}) := by
  intro z hz
  exact analyticAt_const.mul
    ((analyticAt_id.sub analyticAt_const).zpow (sub_ne_zero.mpr hz.2))

lemma contourLaurentCoefficient_monomial (a c : ℂ) (j : ℤ) {r : ℝ} (hr : 0 < r) :
    contourLaurentCoefficient (laurentMonomial a c j) c r j = a := by
  have hint : (∮ z in C(c,r), (z-c)^(-(j+1))*laurentMonomial a c j z) =
      ∮ z in C(c,r), a*(z-c)⁻¹ := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hzc := sphere_sub_ne_zero hr hz
    calc
      _ = a*((z-c)^(-(j+1))*(z-c)^j) := by dsimp [laurentMonomial]; ring
      _ = a*(z-c)^(-1:ℤ) := by rw [← zpow_add₀ hzc]; congr 2; ring
      _ = a*(z-c)⁻¹ := by rw [zpow_neg_one]
  unfold contourLaurentCoefficient
  rw [hint, circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv c hr.ne']
  have hpi : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  field_simp

lemma meromorphicLaurentCoefficient_monomial (a c : ℂ) {j : ℤ} (hj : -1 ≤ j)
    {r : ℝ} (hr : 0 < r) :
    meromorphicLaurentCoefficient (laurentMonomial a c j) c
      (laurentMonomial_meromorphicAt a c j) j = a := by
  rw [meromorphicLaurentCoefficient_eq_contour hr _
    (laurentMonomial_analyticOnNhd a c j _) hj]
  exact contourLaurentCoefficient_monomial a c j hr

lemma laurentMonomial_circle_norm (a c : ℂ) (j : ℤ) {r : ℝ}
    {z : ℂ} (hz : z ∈ sphere c r) : ‖laurentMonomial a c j z‖ = ‖a‖*r^j := by
  rw [laurentMonomial, norm_mul, norm_zpow, mem_sphere_iff_norm.mp hz]

/-- At equality in the circle budget an actual meromorphic monomial perturbation
cancels the true coefficient. No positive-degree or non-pole subcase is substituted. -/
lemma laurent_equality_sharp_cancellation {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : MeromorphicAt f c)
    (hfd : AnalyticOnNhd ℂ f (closedBall c r \ {c})) {j : ℤ} (hj : -1 ≤ j) :
    let a := meromorphicLaurentCoefficient f c hf j
    let g := fun z => f z-laurentMonomial a c j z
    ∃ hg : MeromorphicAt g c,
      meromorphicLaurentCoefficient g c hg j = 0 ∧
      ∀ z ∈ sphere c r, ‖g z-f z‖ = ‖a‖*r^j := by
  dsimp only
  let a := meromorphicLaurentCoefficient f c hf j
  let g := fun z => f z-laurentMonomial a c j z
  have hm := laurentMonomial_meromorphicAt a c j
  have hg : MeromorphicAt g c := hf.sub hm
  have hga : AnalyticOnNhd ℂ g (closedBall c r \ {c}) :=
    hfd.sub (laurentMonomial_analyticOnNhd a c j _)
  refine ⟨hg, ?_, ?_⟩
  · have hs : sphere c r ⊆ closedBall c r \ {c} := by
      intro z hz
      exact ⟨sphere_subset_closedBall hz, sub_ne_zero.mp (sphere_sub_ne_zero hr hz)⟩
    rw [meromorphicLaurentCoefficient_eq_contour hr hg hga hj,
      contourLaurentCoefficient_sub hr
        ((laurentMonomial_analyticOnNhd a c j _).continuousOn.mono hs)
        (hfd.continuousOn.mono hs), contourLaurentCoefficient_monomial a c j hr,
      ← meromorphicLaurentCoefficient_eq_contour hr hf hfd hj]
    exact sub_self a
  · intro z hz
    have herr : g z-f z = -laurentMonomial a c j z := by dsimp [g]; ring
    rw [herr, norm_neg]
    exact laurentMonomial_circle_norm a c j hz

end Zeta23.OPICAFollowup
