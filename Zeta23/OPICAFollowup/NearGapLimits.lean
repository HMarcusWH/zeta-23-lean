import Zeta23.OPICAFollowup.DilatedComb
import Zeta23.OPICA.SignedHeatSeparator

/-! Actual near-gap Jordan-measure budget. The controlled weak-limit theorem,
explicit nonzero dilation family and normalized nonmeasure limit remain OPEN. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup
open Zeta23.OPICA

def hasNearGap (nu : LocallyFiniteSignedMeasure) (a : ℝ) : Prop :=
  nu.positive (Ioo (-a) a)=0 ∧ nu.negative (Ioo (-a) a)=0

/-- The actual canonical Jordan carrier for the CT1 auxiliary dilation defect.
It represents D_L + D_(-L) - 2 cosh(L/2) D_0.  Canonicalization is
necessary: scaled lattice supports can meet the integer lattice, so the
uncancelled positive/negative measures need not be mutually singular.
The nonzero, gap, self-duality and normalized-limit roots are still OPEN. -/
def nearGapCombFamily (L : ℝ) : LocallyFiniteSignedMeasure :=
  localJordanAdd
    (localJordanAdd (dilatedCombJordan L) (dilatedCombJordan (-L)))
    (localJordanScale (-(2 * Real.cosh (L / 2))) (dilatedCombJordan 0))

/-- Exact cancellation of the origin coefficient in the CT1 signed dilation
comb.  This is the coefficient identity; its realization as an atom of the
canonical Jordan carrier is a separate physical measure obligation. -/
theorem nearGapComb_origin_coefficient_zero (L : ℝ) :
    Real.exp (L / 2) + Real.exp (-L / 2) -
      2 * Real.cosh (L / 2) = 0 := by
  rw [Real.cosh_eq]
  ring

/-- The original CT1 parameter range places the actual punctured gap
strictly between the half-unit and the unit gap. -/
theorem nearGapComb_radius_bounds {L : ℝ} (hL : 0 < L)
    (hupper : L < Real.log 2) :
    (1 / 2 : ℝ) < Real.exp (-L) ∧ Real.exp (-L) < 1 := by
  constructor
  · have h : Real.exp (-Real.log (2 : ℝ)) < Real.exp (-L) :=
      Real.exp_lt_exp.mpr (by linarith)
    have heq : Real.exp (-Real.log (2 : ℝ)) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rwa [heq] at h
  · have h : Real.exp (-L) < Real.exp (0 : ℝ) :=
      Real.exp_lt_exp.mpr (by linarith)
    simpa only [Real.exp_zero] using h

lemma nearGap_origin_zero (mu : Measure ℝ) {a : ℝ} (ha : 0<a)
    (hgap : mu (Ioo (-a) a)=0) : mu {0}=0 := by
  apply measure_mono_null _ hgap
  intro x hx
  simp only [mem_singleton_iff] at hx
  subst x
  exact ⟨by linarith, ha⟩

lemma nearGap_triangle_bound (mu : Measure ℝ) [IsLocallyFiniteMeasure mu]
    {a : ℝ} (ha : a≤1) (hgap : mu (Ioo (-a) a)=0) :
    (∫ x, unitTriangle x ∂mu)≤(1-a)*mu.real (Icc (-1) 1) := by
  let g : ℝ→ℝ := (Icc (-1) 1).indicator (fun _ => 1-a)
  have hg : Integrable g mu :=
    (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  have hae : ∀ᵐ x ∂mu, x∉Ioo (-a) a := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hgap
  have hle : ∀ᵐ x ∂mu, unitTriangle x≤g x := by
    filter_upwards [hae] with x hx
    have habs : a≤|x| := by
      by_contra h
      exact hx (abs_lt.mp (lt_of_not_ge h))
    by_cases hbox : x∈Icc (-1) 1
    · dsimp only [g]
      rw [indicator_of_mem hbox]
      exact max_le (by linarith) (by linarith)
    · dsimp only [g]
      rw [indicator_of_notMem hbox]
      have hxabs : 1≤|x| := by
        by_contra h
        have hh := abs_lt.mp (lt_of_not_ge h)
        exact hbox ⟨hh.1.le,hh.2.le⟩
      rw [unitTriangle_eq_zero_of_one_le_abs hxabs]
  have ht : Integrable unitTriangle mu := hg.mono'
    unitTriangle_continuous.aestronglyMeasurable (hle.mono fun x hx => by
      rwa [Real.norm_of_nonneg (unitTriangle_nonneg x)])
  calc
    _ ≤ ∫ x, g x ∂mu := integral_mono_ae ht hg hle
    _ = _ := by
      rw [integral_indicator measurableSet_Icc,setIntegral_const]
      simp [smul_eq_mul,mul_comm]

lemma nearGap_sinc_negative_zero (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) {a : ℝ} (ha : 0<a)
    (hgap : hasNearGap nu a) (hoff : nu.OffLatticeNonnegative) :
    (∫ x, sincSquared x ∂nu.negative)=0 := by
  rw [←sincSquared_integral_compl_lattice nu.negative (nu.negative_hasLinearGrowth hnu)
    (nearGap_origin_zero nu.negative ha hgap.2)]
  rw [show nu.negative.restrict integerLatticeᶜ=0 from Measure.restrict_eq_zero.mpr hoff]
  simp

/-- Exact HT2 measure budget, with actual Jordan parts and literal variation.
The proof does not require evenness, so in particular covers the paper's even measures. -/
theorem near_gap_mass_bound (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    {a R d : ℝ} (ha : 0<a) (ha1 : a≤1) (hgap : hasNearGap nu a)
    (hoff : nu.OffLatticeNonnegative) (hR : 1≤R) (hd : 0<d) (_hdhalf : d≤1/2) :
    nu.negative (signedBudgetRegion R d)=0 ∧
    nu.positive.real (signedBudgetRegion R d)≤
      (Real.pi^2*R^2/(4*d^2))*(1-a)*nu.totalVariation.real (Icc (-1) 1) := by
  have hE : signedBudgetRegion R d⊆integerLatticeᶜ := by
    intro x hx hn
    obtain ⟨n,hn⟩ := hn
    have hh := signedBudgetRegion_integer_distance hx n
    change (n:ℝ)=x at hn
    rw [←hn,sub_self,abs_zero] at hh
    linarith
  refine ⟨measure_mono_null hE hoff,?_⟩
  have hpair := signed_sinc_triangle_pairing nu hnu hself
  change (∫ x, sincSquared x ∂nu.positive)-(∫ x, sincSquared x ∂nu.negative)=
    (∫ x, unitTriangle x ∂nu.positive)-(∫ x, unitTriangle x ∂nu.negative) at hpair
  rw [nearGap_sinc_negative_zero nu hnu ha hgap hoff,sub_zero] at hpair
  have htriangle := nearGap_triangle_bound nu.positive ha1 hgap.1
  have htri_nonneg : 0≤∫ x, unitTriangle x ∂nu.negative :=
    integral_nonneg unitTriangle_nonneg
  have htv : nu.positive.real (Icc (-1) 1)≤nu.totalVariation.real (Icc (-1) 1) := by
    apply ENNReal.toReal_mono isCompact_Icc.measure_lt_top.ne
    change nu.positive _≤(nu.positive+nu.negative) _
    rw [Measure.add_apply]
    exact le_add_of_nonneg_right (by positivity)
  have hupper : (∫ x, sincSquared x ∂nu.positive)≤
      (1-a)*nu.totalVariation.real (Icc (-1) 1) := by
    rw [hpair]
    exact (sub_le_self _ htri_nonneg).trans (htriangle.trans
      (mul_le_mul_of_nonneg_left htv (by linarith)))
  have hi := sincSquared_integrable_of_linear_growth nu.positive (nu.positive_hasLinearGrowth hnu)
  have hlower : (4*d^2/(Real.pi^2*R^2))*nu.positive.real (signedBudgetRegion R d)≤
      ∫ x, sincSquared x ∂nu.positive := by
    calc
      _ = ∫ _x in signedBudgetRegion R d, (4*d^2/(Real.pi^2*R^2)) ∂nu.positive := by
        rw [setIntegral_const,smul_eq_mul,mul_comm]
      _ ≤ ∫ x in signedBudgetRegion R d, sincSquared x ∂nu.positive := by
        apply setIntegral_mono_on
        · exact integrableOn_const (signedBudgetRegion_finite nu.positive R d).ne
        · exact hi.integrableOn
        · exact signedBudgetRegion_measurable R d
        · intro x hx
          exact sincSquared_lower_on_signedBudgetRegion hR hd hx
      _ ≤ _ := setIntegral_le_integral hi (Eventually.of_forall sincSquared_nonneg)
  have hc : 0<4*d^2/(Real.pi^2*R^2) := by positivity
  have hh : nu.positive.real (signedBudgetRegion R d)≤
      ((1-a)*nu.totalVariation.real (Icc (-1) 1))/(4*d^2/(Real.pi^2*R^2)) :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlower.trans hupper)
  convert hh using 1
  field_simp [hd.ne', (show R≠0 by linarith)]

#print axioms Zeta23.OPICAFollowup.near_gap_mass_bound
end Zeta23.OPICAFollowup
