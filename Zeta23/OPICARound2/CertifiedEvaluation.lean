import Zeta23.OPICARound2.ProbeGram
import Zeta23.OPICARound2.TruncationControls
import Zeta23.CCM.UniversalSincSourceTail
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Zeta23.OPICARound2.FixedFilter
import Zeta23.CCM.UniversalSincSourceDensityIdentification
import Zeta23.CCM.OriginalSincNativeConvolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Zeta23.CCM.UniversalSincDetectorInverse
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Zeta23.OPICARound2.CausalProbe
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Absolute finite certificates for the actual probe. All coefficient norms
below are Euclidean norms; the default norm on a finite function space is not
used as a substitute for the spectral norm of a matrix. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Matrix WithLp
open scoped Topology BigOperators ComplexConjugate

namespace Zeta23.OPICARound2

abbrev ProbeCoefficientSpace (N : ℕ) := EuclideanSpace ℂ (Fin N)

def probeCoefficientVector {N : ℕ} (x : Fin N → ℂ) : ProbeCoefficientSpace N := toLp 2 x

def probeCertificateMatrix {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    ProbeCoefficientSpace N →L[ℂ] ProbeCoefficientSpace N :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

theorem probeCertificateMatrix_apply {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    probeCertificateMatrix A (probeCoefficientVector x)=probeCoefficientVector (A*ᵥx) := rfl

def probeNominalEnergy {N : ℕ} (q : ℝ) (b : Fin N → ℂ)
    (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) : ℝ :=
  q-2*(inner ℂ (probeCoefficientVector b) (probeCoefficientVector x)).re+
    (inner ℂ (probeCoefficientVector x) (probeCertificateMatrix A (probeCoefficientVector x))).re

theorem probeCertificate_target_inner {N : ℕ} (x : Fin N → ℂ) :
    inner ℂ probeTarget (probeFiniteOutput x)=
      inner ℂ (probeCoefficientVector (probeTargetColumn N)) (probeCoefficientVector x) := by
  rw [probeTarget_inner_output]
  change (star (probeTargetColumn N)) ⬝ᵥ x=x ⬝ᵥ star (probeTargetColumn N)
  exact dotProduct_comm _ _

theorem probeCertificate_output_inner {N : ℕ} (x y : Fin N → ℂ) :
    inner ℂ (probeFiniteOutput x) (probeFiniteOutput y)=
      inner ℂ (probeCoefficientVector x) (probeCertificateMatrix (probeGram N) (probeCoefficientVector y)) := by
  rw [probeCertificateMatrix_apply]
  change inner ℂ (∑ i : Fin N,x i • probeColumn (i.val+1)) (probeFiniteOutput y)=_
  rw [sum_inner]
  simp_rw [inner_smul_left (𝕜:=ℂ) (E:=CausalProbeL2),probeColumn_inner_output]
  simp only [probeCoefficientVector,EuclideanSpace.inner_toLp_toLp,dotProduct,Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  change star (x i)*(probeGram N*ᵥy) i=(probeGram N*ᵥy) i*star (x i)
  ring

theorem probeCertificate_output_norm_sq {N : ℕ} (x : Fin N → ℂ) :
    ‖probeFiniteOutput x‖^2=
      (inner ℂ (probeCoefficientVector x) (probeCertificateMatrix (probeGram N) (probeCoefficientVector x))).re := by
  have h := congrArg Complex.re (probeCertificate_output_inner x x)
  simpa only [inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow,Complex.ofReal_re] using h

theorem probeCertificate_energy_identity {N : ℕ} (x : Fin N → ℂ) :
    ‖probeResidual x‖^2=probeNominalEnergy probeQ0 (probeTargetColumn N) (probeGram N) x := by
  have h := @norm_sub_sq ℂ CausalProbeL2 _ _ _ probeTarget (probeFiniteOutput x)
  rw [probeCertificate_target_inner,probeCertificate_output_norm_sq] at h
  exact h

theorem probeCertificate_inner_perturbation {N : ℕ} (b bhat x : ProbeCoefficientSpace N) :
    |(inner ℂ b x).re-(inner ℂ bhat x).re|≤‖b-bhat‖*‖x‖ := by
  have h := norm_inner_le_norm (𝕜:=ℂ) (b-bhat) x
  have hr := Complex.abs_re_le_norm (inner ℂ (b-bhat) x)
  rw [inner_sub_left] at hr h
  simpa only [Complex.sub_re] using hr.trans h

theorem probeCertificate_quadratic_perturbation {N : ℕ}
    (A B : ProbeCoefficientSpace N →L[ℂ] ProbeCoefficientSpace N) (x : ProbeCoefficientSpace N) :
    |(inner ℂ x (A x)).re-(inner ℂ x (B x)).re|≤‖A-B‖*‖x‖^2 := by
  have h := norm_inner_le_norm (𝕜:=ℂ) x ((A-B) x)
  have hr := Complex.abs_re_le_norm (inner ℂ x ((A-B) x))
  have hb := (A-B).le_opNorm x
  have hc := mul_le_mul_of_nonneg_left hb (norm_nonneg x)
  rw [ContinuousLinearMap.sub_apply,inner_sub_right] at hr h
  have hd := hr.trans (h.trans hc)
  simpa only [Complex.sub_re] using hd.trans_eq (by ring)

theorem probeCertificate_primal_upper {N : ℕ} (x : Fin N → ℂ)
    (qhat : ℝ) (bhat : Fin N → ℂ) (Ghat : Matrix (Fin N) (Fin N) ℂ)
    (epsilonQ epsilonB epsilonG : ℝ)
    (hQ : |probeQ0-qhat|≤epsilonQ)
    (hB : ‖probeCoefficientVector (probeTargetColumn N)-probeCoefficientVector bhat‖≤epsilonB)
    (hG : ‖probeCertificateMatrix (probeGram N)-probeCertificateMatrix Ghat‖≤epsilonG) :
    ‖probeResidual x‖^2≤probeNominalEnergy qhat bhat Ghat x+epsilonQ+
      2*epsilonB*‖probeCoefficientVector x‖+epsilonG*‖probeCoefficientVector x‖^2 := by
  have hb := probeCertificate_inner_perturbation
    (probeCoefficientVector (probeTargetColumn N)) (probeCoefficientVector bhat) (probeCoefficientVector x)
  have hg := probeCertificate_quadratic_perturbation
    (probeCertificateMatrix (probeGram N)) (probeCertificateMatrix Ghat) (probeCoefficientVector x)
  have hb' := mul_le_mul_of_nonneg_right hB (norm_nonneg (probeCoefficientVector x))
  have hg' := mul_le_mul_of_nonneg_right hG (sq_nonneg ‖probeCoefficientVector x‖)
  have hq := (abs_le.mp hQ).2
  have hbl := (abs_le.mp (hb.trans hb')).1
  have hgu := (abs_le.mp (hg.trans hg')).2
  rw [probeCertificate_energy_identity]
  unfold probeNominalEnergy
  linarith

def probeCertificateGradient {N : ℕ} (x : Fin N → ℂ) : ProbeCoefficientSpace N :=
  probeCoefficientVector (probeTargetColumn N-probeGram N*ᵥx)

def ProbeCertifiedGramLower (N : ℕ) (ell : ℝ) : Prop :=
  ∀ y : Fin N → ℂ, ell*‖probeCoefficientVector y‖^2≤
    (inner ℂ (probeCoefficientVector y) (probeCertificateMatrix (probeGram N) (probeCoefficientVector y))).re

theorem probeCertificate_gradient_component {N : ℕ} (x : Fin N → ℂ) (i : Fin N) :
    probeCertificateGradient x i=inner ℂ (probeColumn (i.val+1)) (probeResidual x) := by
  change (probeTargetColumn N) i-(probeGram N*ᵥx) i=_
  rw [probeResidual,inner_sub_right,probeColumn_inner_output]
  rfl

theorem probeCertificate_gradient_inner {N : ℕ} (h x : Fin N → ℂ) :
    inner ℂ (probeCoefficientVector h) (probeCertificateGradient x)=
      inner ℂ (probeFiniteOutput h) (probeResidual x) := by
  change (probeTargetColumn N-probeGram N*ᵥx) ⬝ᵥ star h=_
  change _=inner ℂ (∑ i : Fin N,h i • probeColumn (i.val+1)) (probeResidual x)
  rw [sum_inner]
  simp_rw [inner_smul_left (𝕜:=ℂ) (E:=CausalProbeL2)]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  have hi := probeCertificate_gradient_component x i
  change (probeTargetColumn N i-(probeGram N*ᵥx) i)=_ at hi
  rw [Pi.sub_apply,Pi.star_apply,hi]
  change inner ℂ (probeColumn (i.val+1)) (probeResidual x)*star (h i)=
    star (h i)*inner ℂ (probeColumn (i.val+1)) (probeResidual x)
  ring

theorem nonnegative_gram_gap_bound (ell a b z : ℝ) (hell : 0<ell)
    (ha : 0≤a) (hb : 0≤b) (hz : 0≤z)
    (hcoercive : ell*a^2≤z) (hdual : z≤a*b) : z≤b^2/ell := by
  by_cases hzero : z=0
  · rw [hzero]
    positivity
  have hpos : 0<z := lt_of_le_of_ne hz (Ne.symm hzero)
  have hsq : z^2≤a^2*b^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ hz (mul_nonneg ha hb)).mpr hdual
  have hsq' := mul_le_mul_of_nonneg_left hsq hell.le
  have hcoercive' := mul_le_mul_of_nonneg_right hcoercive (sq_nonneg b)
  have hprod : z*(ell*z)≤z*b^2 := by nlinarith
  have hle : ell*z≤b^2 := le_of_mul_le_mul_left hprod hpos
  apply (le_div_iff₀ hell).mpr
  nlinarith

theorem probeCertificate_displacement_bound {N : ℕ} (x : Fin N → ℂ)
    (ell : ℝ) (hell : 0<ell) (hG : ProbeCertifiedGramLower N ell) :
    ‖probeBestOutput N-probeFiniteOutput x‖^2≤‖probeCertificateGradient x‖^2/ell := by
  let h : Fin N → ℂ := probeProjectionCoefficients N probeTarget-x
  have hsyn : probeFiniteOutput h=probeBestOutput N-probeFiniteOutput x := by
    rw [probeBestOutput_eq_coefficients]
    change probeSynthesis N (probeProjectionCoefficients N probeTarget-x)=
      probeSynthesis N (probeProjectionCoefficients N probeTarget)-probeSynthesis N x
    exact (probeSynthesis N).map_sub _ _
  have hmem : probeFiniteOutput h∈probeFiniteSpace N := ⟨h,rfl⟩
  have hort : inner ℂ (probeFiniteOutput h) (probeTarget-probeBestOutput N)=0 :=
    inner_eq_zero_symm.mpr (probeBestResidual_inner_space N hmem)
  have hres : probeResidual x=(probeTarget-probeBestOutput N)+probeFiniteOutput h := by
    rw [hsyn]
    unfold probeResidual
    abel
  have hinner : inner ℂ (probeCoefficientVector h) (probeCertificateGradient x)=
      ((‖probeFiniteOutput h‖^2:ℝ):ℂ) := by
    rw [probeCertificate_gradient_inner,hres,inner_add_right,hort,zero_add,
      inner_self_eq_norm_sq_to_K]
    simp only [Complex.ofReal_pow,RCLike.ofReal_eq_complex_ofReal]
  have hdual := norm_inner_le_norm (𝕜:=ℂ) (probeCoefficientVector h) (probeCertificateGradient x)
  rw [hinner,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)] at hdual
  have hcoercive := hG h
  rw [← probeCertificate_output_norm_sq] at hcoercive
  have hb := nonnegative_gram_gap_bound ell ‖probeCoefficientVector h‖ ‖probeCertificateGradient x‖
    (‖probeFiniteOutput h‖^2) hell (norm_nonneg _) (norm_nonneg _) (sq_nonneg _) hcoercive hdual
  rwa [hsyn] at hb

theorem probeCertificate_two_sided {N : ℕ} (x : Fin N → ℂ)
    (ell : ℝ) (hell : 0<ell) (hG : ProbeCertifiedGramLower N ell) :
    ‖probeResidual x‖^2-‖probeCertificateGradient x‖^2/ell≤probeError N^2 ∧
      probeError N^2≤‖probeResidual x‖^2 := by
  have hp := probe_residual_pythagoras x
  have hb := probeCertificate_displacement_bound x ell hell hG
  constructor
  · linarith
  · nlinarith [sq_nonneg ‖probeBestOutput N-probeFiniteOutput x‖]

theorem probeCertificate_budget_nonnegative {N : ℕ} (qhat : ℝ) (bhat : Fin N → ℂ)
    (Ghat : Matrix (Fin N) (Fin N) ℂ) (epsilonQ epsilonB epsilonG : ℝ)
    (hQ : |probeQ0-qhat|≤epsilonQ)
    (hB : ‖probeCoefficientVector (probeTargetColumn N)-probeCoefficientVector bhat‖≤epsilonB)
    (hG : ‖probeCertificateMatrix (probeGram N)-probeCertificateMatrix Ghat‖≤epsilonG) :
    0≤epsilonQ ∧ 0≤epsilonB ∧ 0≤epsilonG :=
  ⟨(abs_nonneg _).trans hQ,(norm_nonneg _).trans hB,(norm_nonneg _).trans hG⟩

theorem probeCertificate_estimated_gram_lower {N : ℕ}
    (Ghat : Matrix (Fin N) (Fin N) ℂ) (ell epsilonG : ℝ)
    (hG : ‖probeCertificateMatrix (probeGram N)-probeCertificateMatrix Ghat‖≤epsilonG)
    (hhat : ∀ y : Fin N → ℂ, ell*‖probeCoefficientVector y‖^2≤
      (inner ℂ (probeCoefficientVector y) (probeCertificateMatrix Ghat (probeCoefficientVector y))).re) :
    ProbeCertifiedGramLower N (ell-epsilonG) := by
  intro y
  have hb := probeCertificate_quadratic_perturbation
    (probeCertificateMatrix (probeGram N)) (probeCertificateMatrix Ghat) (probeCoefficientVector y)
  have he := mul_le_mul_of_nonneg_right hG (sq_nonneg ‖probeCoefficientVector y‖)
  have hl := (abs_le.mp (hb.trans he)).1
  have hy := hhat y
  nlinarith

/-- Finite primal upper and conditioned two-sided bounds. Every matrix and
target error is measured against the actual native Gram data. -/
theorem finite_residual_certificate {N : ℕ} (x : Fin N → ℂ)
    (qhat : ℝ) (bhat : Fin N → ℂ) (Ghat : Matrix (Fin N) (Fin N) ℂ)
    (epsilonQ epsilonB epsilonG : ℝ)
    (hQ : |probeQ0-qhat|≤epsilonQ)
    (hB : ‖probeCoefficientVector (probeTargetColumn N)-probeCoefficientVector bhat‖≤epsilonB)
    (hG : ‖probeCertificateMatrix (probeGram N)-probeCertificateMatrix Ghat‖≤epsilonG) :
    (0≤epsilonQ ∧ 0≤epsilonB ∧ 0≤epsilonG) ∧
    ‖probeResidual x‖^2≤probeNominalEnergy qhat bhat Ghat x+epsilonQ+
      2*epsilonB*‖probeCoefficientVector x‖+epsilonG*‖probeCoefficientVector x‖^2 ∧
    (∀ ell : ℝ, 0<ell → ProbeCertifiedGramLower N ell →
      ‖probeResidual x‖^2-‖probeCertificateGradient x‖^2/ell≤probeError N^2 ∧
        probeError N^2≤‖probeResidual x‖^2) :=
  ⟨probeCertificate_budget_nonnegative qhat bhat Ghat epsilonQ epsilonB epsilonG hQ hB hG,
    probeCertificate_primal_upper x qhat bhat Ghat epsilonQ epsilonB epsilonG hQ hB hG,
    fun ell hell hGram => probeCertificate_two_sided x ell hell hGram⟩

end Zeta23.OPICARound2

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Filter Set MeasureTheory ProbabilityTheory Complex
open scoped Topology BigOperators FourierTransform
open Zeta23.CCM.UniversalSinc

namespace Zeta23.OPICARound2

def sourcePrefixBlockLaw (M : ℕ) : Measure ℝ :=
  sourceCoordinateLaw.map (sourceSampleTailPartial probeSigma 2 (M-2))

instance sourcePrefixBlockLaw_probability (M : ℕ) : IsProbabilityMeasure (sourcePrefixBlockLaw M) :=
  Measure.isProbabilityMeasure_map (measurable_sourceSampleTailPartial _ _ _).aemeasurable

/-- The literal first two boxes, averaged against a genuine probability law.
The finite prefix below instantiates that law with the unchanged coordinates
numbered 2 through M-1. -/
def probeBoxSmoothedDensity (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ,originalBoxPairDensity probeSigma (x-y) ∂μ

def probePrefixDensity (M : ℕ) : ℝ → ℝ := probeBoxSmoothedDensity (sourcePrefixBlockLaw M)

theorem probeBoxPair_height (x : ℝ) :
    ‖originalBoxPairDensity probeSigma x‖≤1/(2*width probeSigma 0) := by
  have ha := width_pos probeSigma_pos 0
  have hb := width_pos probeSigma_pos 1
  rw [Real.norm_eq_abs,abs_of_nonneg (originalBoxPairDensity_nonneg probeSigma_pos x)]
  unfold originalBoxPairDensity uniformBoxPairDensity
  apply (div_le_iff₀ (by positivity : 0<4*width probeSigma 0*width probeSigma 1)).mpr
  have hgap : min (width probeSigma 0) (x+width probeSigma 1)-
      max (-width probeSigma 0) (x-width probeSigma 1)≤2*width probeSigma 1 := by
    linarith [min_le_right (width probeSigma 0) (x+width probeSigma 1),
      le_max_right (-width probeSigma 0) (x-width probeSigma 1)]
  calc
    max 0 (min (width probeSigma 0) (x+width probeSigma 1)-
      max (-width probeSigma 0) (x-width probeSigma 1))≤2*width probeSigma 1 :=
      max_le (by positivity) hgap
    _=(1/(2*width probeSigma 0))*(4*width probeSigma 0*width probeSigma 1) := by
      field_simp
      <;> ring

theorem probeBoxSmoothedDensity_nonneg (μ : Measure ℝ) (x : ℝ) :
    0≤probeBoxSmoothedDensity μ x :=
  integral_nonneg (fun y => originalBoxPairDensity_nonneg probeSigma_pos (x-y))

theorem probeBoxSmoothedDensity_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Continuous (probeBoxSmoothedDensity μ) := by
  apply continuous_of_dominated (bound:=fun _ : ℝ => 1/(2*width probeSigma 0))
  · intro x
    exact ((continuous_originalBoxPairDensity probeSigma).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · intro x
    exact ae_of_all _ (fun y => probeBoxPair_height (x-y))
  · exact integrable_const _
  · exact ae_of_all _ (fun y => (continuous_originalBoxPairDensity probeSigma).comp
      (continuous_id.sub continuous_const))

theorem probeBoxSmoothedDensity_joint_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable (fun p : ℝ×ℝ => originalBoxPairDensity probeSigma (p.2-p.1)) (μ.prod volume) := by
  have hprefix : Integrable (originalBoxPairDensity probeSigma) :=
    integrable_uniformBoxPairDensity (width_pos probeSigma_pos 0) (width_pos probeSigma_pos 1)
  have hm : Continuous (fun p : ℝ×ℝ => originalBoxPairDensity probeSigma (p.2-p.1)) :=
    (continuous_originalBoxPairDensity probeSigma).comp (continuous_snd.sub continuous_fst)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun y => hprefix.comp_sub_right y)
  · have heq : (fun y : ℝ => ∫ x : ℝ,‖originalBoxPairDensity probeSigma (x-y)‖)=fun _ => (1:ℝ) := by
      funext y
      simp_rw [Real.norm_eq_abs,abs_of_nonneg (originalBoxPairDensity_nonneg probeSigma_pos _)]
      rw [integral_sub_right_eq_self]
      exact integral_uniformBoxPairDensity (width_pos probeSigma_pos 0) (width_pos probeSigma_pos 1)
    rw [heq]
    exact integrable_const 1

theorem probeBoxSmoothedDensity_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable (probeBoxSmoothedDensity μ) :=
  (probeBoxSmoothedDensity_joint_integrable μ).integral_prod_right

theorem probeBoxSmoothedDensity_mass (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ x : ℝ,probeBoxSmoothedDensity μ x)=1 := by
  unfold probeBoxSmoothedDensity
  rw [← integral_integral_swap (probeBoxSmoothedDensity_joint_integrable μ)]
  have hinner (y : ℝ) : (∫ x : ℝ,originalBoxPairDensity probeSigma (x-y))=1 := by
    rw [integral_sub_right_eq_self]
    exact integral_uniformBoxPairDensity (width_pos probeSigma_pos 0) (width_pos probeSigma_pos 1)
  simp_rw [hinner]
  simp

theorem probeBoxPair_zero_outside {x : ℝ}
    (hx : width probeSigma 0+width probeSigma 1< |x|) : originalBoxPairDensity probeSigma x=0 := by
  have hgap : min (width probeSigma 0) (x+width probeSigma 1)-
      max (-width probeSigma 0) (x-width probeSigma 1)≤0 := by
    by_cases h : 0≤x
    · rw [abs_of_nonneg h] at hx
      linarith [min_le_left (width probeSigma 0) (x+width probeSigma 1),
        le_max_right (-width probeSigma 0) (x-width probeSigma 1)]
    · rw [abs_of_neg (lt_of_not_ge h)] at hx
      linarith [min_le_right (width probeSigma 0) (x+width probeSigma 1),
        le_max_left (-width probeSigma 0) (x-width probeSigma 1)]
  rw [originalBoxPairDensity,uniformBoxPairDensity,max_eq_left hgap,zero_div]

theorem sourcePrefixBlock_abs_le (M : ℕ) (omega : ℕ→ℝ) :
    |sourceSampleTailPartial probeSigma 2 (M-2) omega|≤probeSigma/3 := by
  have hnorm := norm_sum_le (Finset.range (M-2))
    (fun n : ℕ => width probeSigma (n+2)*unitClamp (omega (n+2)))
  have hterm := Finset.sum_le_sum (fun n (_ : n∈Finset.range (M-2)) =>
    sourceSampleAtom_norm_le_width probeSigma_pos.le omega (n+2))
  have htail := (hasSum_tail_width probeSigma_pos.le 2).summable.sum_le_tsum
    (Finset.range (M-2)) (fun n _ => width_nonneg probeSigma_pos.le (n+2))
  rw [(hasSum_tail_width probeSigma_pos.le 2).tsum_eq] at htail
  simpa only [sourceSampleTailPartial,Real.norm_eq_abs,Nat.cast_ofNat,
    show (2:ℝ)+1=3 by norm_num] using hnorm.trans (hterm.trans htail)

theorem sourcePrefixBlockLaw_ae_support (M : ℕ) :
    ∀ᵐ y ∂sourcePrefixBlockLaw M, |y|≤probeSigma/3 := by
  unfold sourcePrefixBlockLaw
  apply (ae_map_iff (measurable_sourceSampleTailPartial _ _ _).aemeasurable
    (measurableSet_le continuous_abs.measurable measurable_const)).mpr
  exact ae_of_all _ (sourcePrefixBlock_abs_le M)

theorem probePrefixDensity_zero_outside (M : ℕ) {x : ℝ} (hx : probeSigma< |x|) :
    probePrefixDensity M x=0 := by
  unfold probePrefixDensity probeBoxSmoothedDensity
  apply integral_eq_zero_of_ae
  filter_upwards [sourcePrefixBlockLaw_ae_support M] with y hy
  have htri : |x|≤|x-y|+|y| := by simpa only [sub_add_cancel] using abs_add_le (x-y) y
  apply probeBoxPair_zero_outside
  have hw : width probeSigma 0+width probeSigma 1=2*probeSigma/3 := by norm_num [width]; ring
  rw [hw]
  linarith

theorem probePrefixDensity_support (M : ℕ) :
    tsupport (probePrefixDensity M)⊆Icc (-probeSigma) probeSigma := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  exact hx (probePrefixDensity_zero_outside M (lt_of_not_ge (fun h => hnot (abs_le.mp h))))

theorem probeBoxSmoothedDensity_joint_character_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ) :
    Integrable (fun p : ℝ×ℝ => (originalBoxPairDensity probeSigma (p.2-p.1):ℂ)*
      Complex.exp (I*(r:ℂ)*(p.2:ℂ))) (μ.prod volume) := by
  apply (probeBoxSmoothedDensity_joint_integrable μ).mono'
  · exact ((Complex.continuous_ofReal.comp ((continuous_originalBoxPairDensity probeSigma).comp
      (continuous_snd.sub continuous_fst))).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with p
    rw [Complex.norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have he : ‖Complex.exp (I*(r:ℂ)*(p.2:ℂ))‖=1 := by
      rw [show I*(r:ℂ)*(p.2:ℂ)=I*((r*p.2:ℝ):ℂ) by push_cast; ring,
        Complex.norm_exp_I_mul_ofReal]
    rw [he,mul_one,abs_of_nonneg (originalBoxPairDensity_nonneg probeSigma_pos _)]

theorem probeBoxPair_shift_transform (r y : ℝ) :
    (∫ x : ℝ,(originalBoxPairDensity probeSigma (x-y):ℂ)*Complex.exp (I*(r:ℂ)*(x:ℂ)))=
      Zeta23.paperFT (fun x : ℝ => (originalBoxPairDensity probeSigma x:ℂ)) (r:ℂ)*
        Complex.exp (I*(r:ℂ)*(y:ℂ)) := by
  have hfun : (fun x : ℝ => (originalBoxPairDensity probeSigma (x-y):ℂ)*
      Complex.exp (I*(r:ℂ)*(x:ℂ)))=fun x : ℝ =>
      (originalBoxPairDensity probeSigma (x-y):ℂ)*Complex.exp (I*(r:ℂ)*(((x-y)+y:ℝ):ℂ)) := by
    funext x
    rw [sub_add_cancel]
  rw [hfun,integral_sub_right_eq_self
    (fun x : ℝ => (originalBoxPairDensity probeSigma x:ℂ)*Complex.exp (I*(r:ℂ)*((x+y:ℝ):ℂ))) y]
  have hs : (fun x : ℝ => (originalBoxPairDensity probeSigma x:ℂ)*Complex.exp (I*(r:ℂ)*((x+y:ℝ):ℂ)))=
      fun x : ℝ => ((originalBoxPairDensity probeSigma x:ℂ)*Complex.exp (I*(r:ℂ)*(x:ℂ)))*
        Complex.exp (I*(r:ℂ)*(y:ℂ)) := by
    funext x
    rw [Complex.ofReal_add,mul_add,Complex.exp_add]
    ring
  rw [hs,integral_mul_const]
  rfl

theorem probeBoxSmoothedDensity_paperFT (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ) :
    Zeta23.paperFT (fun x : ℝ => (probeBoxSmoothedDensity μ x:ℂ)) (r:ℂ)=
      partialProduct probeSigma r 2*charFun μ r := by
  rw [Zeta23.paperFT_def]
  have hinner (x : ℝ) : (probeBoxSmoothedDensity μ x:ℂ)*Complex.exp (I*(r:ℂ)*(x:ℂ))=
      ∫ y : ℝ,(originalBoxPairDensity probeSigma (x-y):ℂ)*Complex.exp (I*(r:ℂ)*(x:ℂ)) ∂μ := by
    unfold probeBoxSmoothedDensity
    rw [← integral_complex_ofReal,integral_mul_const]
  simp_rw [hinner]
  rw [← integral_integral_swap (probeBoxSmoothedDensity_joint_character_integrable μ r)]
  simp_rw [probeBoxPair_shift_transform]
  rw [integral_const_mul]
  have hphase : (∫ y : ℝ,Complex.exp (I*(r:ℂ)*(y:ℂ)) ∂μ)=charFun μ r := by
    rw [charFun_apply_real]
    apply integral_congr_ae
    filter_upwards with y
    congr 1
    ring
  rw [hphase,paperFT_originalBoxPairDensity_ofReal probeSigma_pos]

theorem probePrefixDensity_paperFT (M : ℕ) (hM : 2≤M) (r : ℝ) :
    Zeta23.paperFT (fun x : ℝ => (probePrefixDensity M x:ℂ)) (r:ℂ)=
      partialProduct probeSigma r M := by
  rw [probePrefixDensity,probeBoxSmoothedDensity_paperFT,sourcePrefixBlockLaw,
    charFun_sourceSampleTailPartial]
  have hs : M=2+(M-2) := by omega
  conv_rhs => rw [hs]
  unfold partialProduct
  rw [Finset.prod_range_add]
  simp only [Nat.add_comm]

def probePrefixDensityMeasure (M : ℕ) : Measure ℝ :=
  volume.withDensity (fun x : ℝ => ENNReal.ofReal (probePrefixDensity M x))

instance probePrefixDensityMeasure_probability (M : ℕ) :
    IsProbabilityMeasure (probePrefixDensityMeasure M) := by
  constructor
  unfold probePrefixDensityMeasure probePrefixDensity
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (probeBoxSmoothedDensity_integrable (sourcePrefixBlockLaw M))
      (ae_of_all _ (probeBoxSmoothedDensity_nonneg (sourcePrefixBlockLaw M))),
    probeBoxSmoothedDensity_mass]
  norm_num

theorem probePrefixDensityMeasure_charFun (M : ℕ) (hM : 2≤M) (r : ℝ) :
    charFun (probePrefixDensityMeasure M) r=partialProduct probeSigma r M := by
  rw [charFun_apply_real]
  unfold probePrefixDensityMeasure probePrefixDensity
  rw [integral_withDensity_eq_integral_toReal_smul
    (probeBoxSmoothedDensity_continuous (sourcePrefixBlockLaw M)).measurable.ennreal_ofReal
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (probeBoxSmoothedDensity_nonneg (sourcePrefixBlockLaw M) _),
    RCLike.real_smul_eq_coe_mul]
  have hFT := probePrefixDensity_paperFT M hM r
  rw [Zeta23.paperFT_def] at hFT
  apply Eq.trans _ hFT
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  congr 1
  ring

theorem probePrefixDensity_actual_law (M : ℕ) (hM : 2≤M) :
    sourceCoordinateLaw.map (sourceSamplePartialSum probeSigma M)=probePrefixDensityMeasure M := by
  letI : IsProbabilityMeasure (sourceCoordinateLaw.map (sourceSamplePartialSum probeSigma M)) :=
    Measure.isProbabilityMeasure_map (measurable_sourceSamplePartialSum _ _).aemeasurable
  apply Measure.ext_of_charFun
  funext r
  rw [charFun_sourceSamplePartialSum,probePrefixDensityMeasure_charFun M hM]

theorem probePrefixDensity_actual_tail_split (M : ℕ) (hM : 2≤M) :
    originalSourceLaw probeSigma=probePrefixDensityMeasure M∗originalSourceTailLaw probeSigma M := by
  rw [originalSourceLaw_eq_prefix_conv_tail probeSigma_pos.le M,probePrefixDensity_actual_law M hM]

#print axioms Zeta23.OPICARound2.probeBoxSmoothedDensity_mass
#print axioms Zeta23.OPICARound2.probePrefixDensity_support
#print axioms Zeta23.OPICARound2.probePrefixDensity_actual_law
#print axioms Zeta23.OPICARound2.probePrefixDensity_actual_tail_split

end Zeta23.OPICARound2

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Filter Set MeasureTheory
open scoped Topology BigOperators FourierTransform
open Zeta23.CCM.UniversalSinc

namespace Zeta23.OPICARound2

theorem probePrefixProduct_continuous (M : ℕ) :
    Continuous (fun x : ℝ => partialProduct probeSigma x M) := by
  unfold partialProduct
  apply continuous_finset_prod
  intro n _
  exact continuous_sinc.comp (continuous_const.mul Complex.continuous_ofReal)

theorem probePrefixProduct_power_bound (N : ℕ) (x : ℝ) (hx : x≠0) :
    ‖partialProduct probeSigma x N‖*|x|^N≤∏ n∈Finset.range N,(width probeSigma n)⁻¹ := by
  induction N with
  | zero => simp [partialProduct]
  | succ N ih =>
    have hxpos : 0< |x| := abs_pos.mpr hx
    have ha := width_pos probeSigma_pos N
    have hfactor : ‖sinc ((width probeSigma N:ℂ)*(x:ℂ))‖*|x|≤(width probeSigma N)⁻¹ := by
      apply (le_div_iff₀ hxpos).mp
      have h := sinc_norm_ofReal_le_inv_abs (mul_ne_zero ha.ne' hx)
      rw [Complex.ofReal_mul,abs_mul,abs_of_pos ha] at h
      simpa only [div_eq_mul_inv,_root_.mul_inv_rev,mul_comm,one_mul] using h
    calc
      _=(‖partialProduct probeSigma x N‖*|x|^N)*
          (‖sinc ((width probeSigma N:ℂ)*(x:ℂ))‖*|x|) := by
        rw [partialProduct,Finset.prod_range_succ,Complex.norm_mul,pow_succ]
        unfold partialProduct
        ring
      _≤(∏ n∈Finset.range N,(width probeSigma n)⁻¹)*(width probeSigma N)⁻¹ :=
        mul_le_mul ih hfactor (mul_nonneg (norm_nonneg _) (abs_nonneg _))
          (Finset.prod_nonneg (fun n _ => inv_nonneg.mpr (width_nonneg probeSigma_pos.le n)))
      _=∏ n∈Finset.range (N+1),(width probeSigma n)⁻¹ := (Finset.prod_range_succ _ _).symm

def probePrefixMomentConstant : ℝ := max 1 (∏ n∈Finset.range 10,(width probeSigma n)⁻¹)

theorem probePrefixMomentConstant_pos : 0<probePrefixMomentConstant :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem probePrefixProduct_moment_bound (M k : ℕ) (hM : 12≤M) (hk : k≤8) (x : ℝ) :
    |x|^k*‖partialProduct probeSigma x M‖≤
      (2*probePrefixMomentConstant)*(1+x^2)⁻¹ := by
  let f : ℝ := |x|^k*‖partialProduct probeSigma x M‖
  have hf : 0≤f := mul_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _)
  have hC : 1≤probePrefixMomentConstant := le_max_left _ _
  have hC' : (∏ n∈Finset.range 10,(width probeSigma n)⁻¹)≤probePrefixMomentConstant := le_max_right _ _
  have hb : f*(1+x^2)≤2*probePrefixMomentConstant := by
    by_cases hx : 1≤|x|
    · have hx0 : x≠0 := abs_pos.mp (zero_lt_one.trans_le hx)
      have hp := probePrefixProduct_power_bound 10 x hx0
      have hm := partialProduct_norm_antitone probeSigma x (by omega : 10≤M)
      have hp' := mul_le_mul_of_nonneg_right hm (pow_nonneg (abs_nonneg x) 10)
      have hexp : |x|^(k+2)≤|x|^10 := pow_le_pow_right₀ hx (by omega)
      have hsmall := mul_le_mul_of_nonneg_left hexp (norm_nonneg (partialProduct probeSigma x M))
      have hpower : f*|x|^2≤probePrefixMomentConstant := by
        dsimp [f]
        rw [pow_add] at hsmall
        nlinarith [hp'.trans hp]
      have hs : 1≤|x|^2 := by nlinarith
      have hfx : f≤f*|x|^2 := by nlinarith
      nlinarith [sq_abs x]
    · have hx' : |x|≤1 := le_of_lt (lt_of_not_ge hx)
      have hpow : |x|^k≤1 := pow_le_one₀ (abs_nonneg x) hx'
      have hnorm := partialProduct_norm_le_one probeSigma x M
      have hfx : f≤1 := by
        dsimp [f]
        nlinarith [pow_nonneg (abs_nonneg x) k,norm_nonneg (partialProduct probeSigma x M)]
      have hs : x^2≤1 := by nlinarith [sq_abs x,abs_nonneg x]
      nlinarith [sq_nonneg x]
  change f≤_
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0<1+x^2)).mpr hb

theorem probePrefixProduct_moment_integrable (M k : ℕ) (hM : 12≤M) (hk : k≤8) :
    Integrable (fun x : ℝ => |x|^k*‖partialProduct probeSigma x M‖) := by
  apply (integrable_inv_one_add_sq.const_mul (2*probePrefixMomentConstant)).mono'
  · exact ((continuous_id.abs.pow k).mul (probePrefixProduct_continuous M).norm).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg x) k) (norm_nonneg _))]
    exact probePrefixProduct_moment_bound M k hM hk x

theorem probePrefixProduct_integrable (M : ℕ) (hM : 12≤M) :
    Integrable (fun x : ℝ => partialProduct probeSigma x M) := by
  have hn : Integrable (fun x : ℝ => ‖partialProduct probeSigma x M‖) := by
    simpa only [pow_zero,one_mul] using probePrefixProduct_moment_integrable M 0 hM (by omega)
  exact (integrable_norm_iff (probePrefixProduct_continuous M).aestronglyMeasurable).mp hn

def probePrefixInverse (M : ℕ) (x : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(𝓕 (fun xi : ℝ => partialProduct probeSigma xi M)) (x/(2*Real.pi))

theorem probePrefixInverse_contDiff (M : ℕ) (hM : 12≤M) : ContDiff ℝ 8 (probePrefixInverse M) := by
  have hF : ContDiff ℝ 8 (𝓕 (fun xi : ℝ => partialProduct probeSigma xi M)) := by
    apply Real.contDiff_fourier
    intro n hn
    simpa only [Real.norm_eq_abs] using probePrefixProduct_moment_integrable M n hM (by exact_mod_cast hn)
  exact contDiff_const.mul (hF.comp (contDiff_id.div_const (2*Real.pi)))

#print axioms Zeta23.OPICARound2.probePrefixProduct_moment_integrable
#print axioms Zeta23.OPICARound2.probePrefixInverse_contDiff

end Zeta23.OPICARound2
namespace Zeta23.OPICARound2

def probePrefixDensityComplex (M : ℕ) (x : ℝ) : ℂ := (probePrefixDensity M x:ℂ)

theorem probePrefixDensityComplex_continuous (M : ℕ) : Continuous (probePrefixDensityComplex M) :=
  Complex.continuous_ofReal.comp (probeBoxSmoothedDensity_continuous (sourcePrefixBlockLaw M))

theorem probePrefixDensityComplex_integrable (M : ℕ) : Integrable (probePrefixDensityComplex M) :=
  (probeBoxSmoothedDensity_integrable (sourcePrefixBlockLaw M)).ofReal

theorem probePrefixDensityComplex_fourier (M : ℕ) (hM : 2≤M) :
    𝓕 (probePrefixDensityComplex M)=fun w : ℝ => partialProduct probeSigma (-(2*Real.pi)*w) M := by
  funext w
  calc
    _=Zeta23.paperFT (probePrefixDensityComplex M) (-(2*Real.pi*w)) := Zeta23.fourier_eq_paperFT _ w
    _=Zeta23.paperFT (probePrefixDensityComplex M) ((-(2*Real.pi)*w:ℝ):ℂ) := by
      congr 1
      push_cast
      ring
    _=_ := probePrefixDensity_paperFT M hM _

theorem probePrefixDensityComplex_fourier_integrable (M : ℕ) (hM : 12≤M) :
    Integrable (𝓕 (probePrefixDensityComplex M)) := by
  rw [probePrefixDensityComplex_fourier M (by omega)]
  exact (probePrefixProduct_integrable M hM).comp_mul_left'
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero))

theorem probePrefixInverse_physical_identity (M : ℕ) (hM : 12≤M) :
    probePrefixInverse M=probePrefixDensityComplex M := by
  funext x
  have hinv : (𝓕⁻ (𝓕 (probePrefixDensityComplex M))) x=probePrefixInverse M x := by
    let g : ℝ→ℂ := fun xi => partialProduct probeSigma xi M*Complex.exp (I*((-x:ℝ):ℂ)*(xi:ℂ))
    calc
      _=∫ w : ℝ,g (-(2*Real.pi)*w) := by
        rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,
          probePrefixDensityComplex_fourier M (by omega)]
        apply integral_congr_ae
        filter_upwards with w
        simp only [smul_eq_mul,g]
        rw [mul_comm]
        congr 1
        congr 1
        push_cast
        ring
      _=|(-(2*Real.pi):ℝ)⁻¹| • ∫ xi : ℝ,g xi :=
        Measure.integral_comp_mul_left g (-(2*Real.pi))
      _=((1/(2*Real.pi):ℝ):ℂ)*Zeta23.paperFT
          (fun xi : ℝ => partialProduct probeSigma xi M) ((-x:ℝ):ℂ) := by
        have hn : |(-(2*Real.pi):ℝ)⁻¹|=1/(2*Real.pi) := by
          rw [inv_neg,abs_neg,abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
          simp only [one_div]
        rw [hn,RCLike.real_smul_eq_coe_mul]
        rfl
      _=probePrefixInverse M x := by
        rw [Zeta23.paperFT_ofReal_eq_fourier]
        simp only [neg_neg,probePrefixInverse]
  calc
    _=(𝓕⁻ (𝓕 (probePrefixDensityComplex M))) x := hinv.symm
    _=_ := (probePrefixDensityComplex_integrable M).fourierInv_fourier_eq
      (probePrefixDensityComplex_fourier_integrable M hM)
        (probePrefixDensityComplex_continuous M).continuousAt

theorem probePrefixDensityComplex_contDiff (M : ℕ) (hM : 12≤M) :
    ContDiff ℝ 8 (probePrefixDensityComplex M) := by
  rw [← probePrefixInverse_physical_identity M hM]
  exact probePrefixInverse_contDiff M hM

theorem probePrefixDensity_contDiff (M : ℕ) (hM : 12≤M) : ContDiff ℝ 8 (probePrefixDensity M) := by
  have hr := Complex.reCLM.contDiff.comp (probePrefixDensityComplex_contDiff M hM)
  simpa only [probePrefixDensityComplex,Function.comp_def,Complex.reCLM_apply,Complex.ofReal_re] using hr

theorem probePrefixDensity_hasCompactSupport (M : ℕ) : HasCompactSupport (probePrefixDensity M) := by
  apply HasCompactSupport.intro (K:=Icc (-probeSigma) probeSigma) isCompact_Icc
  intro x hx
  exact probePrefixDensity_zero_outside M (lt_of_not_ge (fun h => hx (abs_le.mp h)))

theorem probePrefixDensityComplex_hasCompactSupport (M : ℕ) :
    HasCompactSupport (probePrefixDensityComplex M) :=
  (probePrefixDensity_hasCompactSupport M).comp_left (g:=Complex.ofReal) Complex.ofReal_zero

def probePrefixK (M : ℕ) : ℝ→ℂ := CCM.universalSincDifferential (probePrefixDensityComplex M)
def probePrefixJ (M : ℕ) : ℝ→ℂ := CCM.universalSincDifferential (probePrefixK M)

theorem probePrefixK_contDiff (M : ℕ) (hM : 12≤M) : ContDiff ℝ 6 (probePrefixK M) := by
  have hq := probePrefixDensityComplex_contDiff M hM
  have hd1 : ContDiff ℝ 7 (deriv (probePrefixDensityComplex M)) := hq.deriv'
  have hd2 : ContDiff ℝ 6 (deriv (deriv (probePrefixDensityComplex M))) := hd1.deriv'
  exact hd2.sub (contDiff_const.mul (hq.of_le (by norm_num)))

theorem probePrefixJ_contDiff (M : ℕ) (hM : 12≤M) : ContDiff ℝ 4 (probePrefixJ M) := by
  have hk := probePrefixK_contDiff M hM
  have hd1 : ContDiff ℝ 5 (deriv (probePrefixK M)) := hk.deriv'
  have hd2 : ContDiff ℝ 4 (deriv (deriv (probePrefixK M))) := hd1.deriv'
  exact hd2.sub (contDiff_const.mul (hk.of_le (by norm_num)))

theorem probePrefixK_hasCompactSupport (M : ℕ) : HasCompactSupport (probePrefixK M) :=
  (probePrefixDensityComplex_hasCompactSupport M).deriv.deriv.sub
    (probePrefixDensityComplex_hasCompactSupport M).mul_left

theorem probePrefixJ_hasCompactSupport (M : ℕ) : HasCompactSupport (probePrefixJ M) :=
  (probePrefixK_hasCompactSupport M).deriv.deriv.sub (probePrefixK_hasCompactSupport M).mul_left

theorem probePrefixJ_derivative_hasCompactSupport (M k : ℕ) :
    HasCompactSupport (iteratedDeriv k (probePrefixJ M)) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using probePrefixJ_hasCompactSupport M
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem probePrefixJ_derivative_integrable (M k : ℕ) (hM : 12≤M) (hk : k≤4) :
    Integrable (iteratedDeriv k (probePrefixJ M)) :=
  ((probePrefixJ_contDiff M hM).continuous_iteratedDeriv k (by exact_mod_cast hk)).integrable_of_hasCompactSupport
    (probePrefixJ_derivative_hasCompactSupport M k)

theorem probePrefixJ_derivative_memLp (M k : ℕ) (hM : 12≤M) (hk : k≤4) :
    MemLp (iteratedDeriv k (probePrefixJ M)) 2 volume :=
  ((probePrefixJ_contDiff M hM).continuous_iteratedDeriv k (by exact_mod_cast hk)).memLp_of_hasCompactSupport
    (probePrefixJ_derivative_hasCompactSupport M k)

#print axioms Zeta23.OPICARound2.probePrefixInverse_physical_identity
#print axioms Zeta23.OPICARound2.probePrefixJ_contDiff
#print axioms Zeta23.OPICARound2.probePrefixJ_derivative_memLp

end Zeta23.OPICARound2
namespace Zeta23.OPICARound2

theorem probeDifferential_paperFT {q : ℝ→ℂ} (hq : ContDiff ℝ 2 q) (hc : HasCompactSupport q) (z : ℂ) :
    Zeta23.paperFT (CCM.universalSincDifferential q) z=
      -(z^2+1/4)*Zeta23.paperFT q z := by
  have hd2 : Continuous (deriv (deriv q)) := hq.deriv'.continuous_deriv le_rfl
  have hmul : Continuous (fun x : ℝ => (1/4:ℂ)*q x) := continuous_const.mul hq.continuous
  rw [show CCM.universalSincDifferential q=deriv (deriv q)-(fun x : ℝ => (1/4:ℂ)*q x) by rfl,
    Zeta23.paperFT_sub hd2 hmul hc.deriv.deriv hc.mul_left,Zeta23.paperFT_deriv_deriv hq hc]
  have hconst : Zeta23.paperFT (fun x : ℝ => (1/4:ℂ)*q x) z=(1/4:ℂ)*Zeta23.paperFT q z := by
    rw [Zeta23.paperFT_def,Zeta23.paperFT_def,← Zeta23.integral_const_mul_C]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hconst]
  ring

theorem probePrefixK_paperFT (M : ℕ) (hM : 12≤M) (tau : ℝ) :
    Zeta23.paperFT (probePrefixK M) (tau:ℂ)=
      -((tau:ℂ)^2+1/4)*partialProduct probeSigma tau M := by
  rw [probePrefixK,probeDifferential_paperFT ((probePrefixDensityComplex_contDiff M hM).of_le (by norm_num))
    (probePrefixDensityComplex_hasCompactSupport M)]
  rw [show Zeta23.paperFT (probePrefixDensityComplex M) (tau:ℂ)=partialProduct probeSigma tau M
    from probePrefixDensity_paperFT M (by omega) tau]

theorem probePrefixJ_paperFT (M : ℕ) (hM : 12≤M) (tau : ℝ) :
    Zeta23.paperFT (probePrefixJ M) (tau:ℂ)=
      ((tau:ℂ)^2+1/4)^2*partialProduct probeSigma tau M := by
  rw [probePrefixJ,probeDifferential_paperFT ((probePrefixK_contDiff M hM).of_le (by norm_num))
    (probePrefixK_hasCompactSupport M),probePrefixK_paperFT M hM]
  ring

theorem probeProduct_actual_tail_split (M : ℕ) (tau : ℝ) :
    product probeSigma (tau:ℂ)=partialProduct probeSigma tau M*
      charFun (originalSourceTailLaw probeSigma M) tau := by
  rw [charFun_originalSourceTailLaw probeSigma_pos.le]
  simpa only [partialProduct,product] using
    (Multipliable.prod_mul_tprod_nat_mul'
      (f:=fun n : ℕ => sinc ((width probeSigma n:ℂ)*(tau:ℂ))) (k:=M)
        (multipliable_sinc_tail probeSigma_pos.le M (tau:ℂ))).symm

theorem probeLogFourier_eq_paperFT (f : ℝ→ℂ) (tau : ℝ) :
    OPICAFollowup.logFourier f tau=Zeta23.paperFT f ((-tau:ℝ):ℂ) := by
  unfold OPICAFollowup.logFourier Zeta23.paperFT
  apply integral_congr_ae
  filter_upwards with t
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

def probeCanonicalJ : ℝ→ℂ := CCM.universalSincSecondKernel probeSigma

theorem probeCanonicalJ_actual_source (t : ℝ) : probeCanonicalJ t=(CCM.nativeOriginalSource t:ℂ) := by
  rw [probeCanonicalJ,CCM.universalSincSecondKernel_eq_real probeSigma_pos]
  rfl

theorem probeCanonicalJ_continuous : Continuous probeCanonicalJ :=
  (CCM.universalSincSecondKernel_contDiff probeSigma_pos).continuous

theorem probeCanonicalJ_hasCompactSupport : HasCompactSupport probeCanonicalJ :=
  CCM.universalSincSecondKernel_hasCompactSupport probeSigma_pos

theorem probeCanonicalJ_integrable : Integrable probeCanonicalJ :=
  CCM.universalSincSecondKernel_integrable probeSigma_pos

theorem probeCanonicalJ_memLp : MemLp probeCanonicalJ 2 volume :=
  probeCanonicalJ_continuous.memLp_of_hasCompactSupport probeCanonicalJ_hasCompactSupport

theorem probePrefixJ_actual_fourier_split (M : ℕ) (hM : 12≤M) (tau : ℝ) :
    OPICAFollowup.logFourier probeCanonicalJ tau=
      OPICAFollowup.logFourier (probePrefixJ M) tau*
        charFun (originalSourceTailLaw probeSigma M) (-tau) := by
  rw [probeLogFourier_eq_paperFT,probeLogFourier_eq_paperFT,
    probeCanonicalJ,CCM.paperFT_universalSincSecondKernel probeSigma_pos,
    probePrefixJ_paperFT M hM,probeProduct_actual_tail_split]
  ring

theorem probePrefixJ_derivative_fourier (M k : ℕ) (hM : 12≤M) (hk : k≤4) (tau : ℝ) :
    OPICAFollowup.logFourier (iteratedDeriv k (probePrefixJ M)) tau=
      ((tau:ℂ)*Complex.I)^k*OPICAFollowup.logFourier (probePrefixJ M) tau := by
  induction k with
  | zero => simp only [iteratedDeriv_zero,pow_zero,one_mul]
  | succ k ih =>
    have hk' : k≤4 := by omega
    have hi := probePrefixJ_derivative_integrable M k hM hk'
    have hd := (probePrefixJ_contDiff M hM).differentiable_iteratedDeriv k (by exact_mod_cast (show k<4 by omega))
    have hid : Integrable (deriv (iteratedDeriv k (probePrefixJ M))) := by
      rw [← iteratedDeriv_succ]
      exact probePrefixJ_derivative_integrable M (k+1) hM hk
    rw [iteratedDeriv_succ,OPICAFollowup.logFourier_deriv hi hd hid,ih hk',pow_succ]
    ring

theorem probePrefixJ_derivative_fourier_norm (M k : ℕ) (hM : 12≤M) (hk : k≤4) (tau : ℝ) :
    ‖OPICAFollowup.logFourier (iteratedDeriv k (probePrefixJ M)) tau‖=
      |tau|^k*‖OPICAFollowup.logFourier (probePrefixJ M) tau‖ := by
  rw [probePrefixJ_derivative_fourier M k hM hk,norm_mul,norm_pow,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]

#print axioms Zeta23.OPICARound2.probePrefixJ_actual_fourier_split
#print axioms Zeta23.OPICARound2.probePrefixJ_derivative_fourier_norm

end Zeta23.OPICARound2

/-! Actual original source-tail probability laws, moments and sharp Taylor remainders. -/

noncomputable section

open Set Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

namespace Zeta23.OPICARound2.SourceTailMoments
open CCM.UniversalSinc

def tailRadius (s : ℝ) (N : ℕ) : ℝ := s / ((N : ℝ) + 1)
def tailVariance (s : ℝ) (N : ℕ) : ℝ :=
  (1 / 3) * ∑' n : ℕ, width s (n + N) ^ 2
def partialVariance (s : ℝ) (N K : ℕ) : ℝ :=
  (1 / 3) * ∑ n ∈ range K, width s (n + N) ^ 2

theorem actual_tail_probability {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    IsProbabilityMeasure (originalSourceTailLaw s N) := originalSourceTailLaw_isProbabilityMeasure hs N

theorem actual_tail_support {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    ∀ᵐ u ∂originalSourceTailLaw s N, |u| ≤ tailRadius s N := by
  rw [originalSourceTailLaw, ae_map_iff (measurable_sourceSampleTail hs N).aemeasurable
    (isClosed_le continuous_abs continuous_const).measurableSet]
  exact Filter.Eventually.of_forall fun ω => sourceSampleTail_abs_le hs N ω

theorem centered_box_moment (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂centeredUnitBoxLaw) =
      (1 - (-1 : ℝ) ^ (k + 1)) / (2 * ((k : ℝ) + 1)) := by
  unfold centeredUnitBoxLaw ProbabilityTheory.cond
  rw [integral_smul_measure]
  have hv : ((volume (Icc (-1 : ℝ) 1))⁻¹).toReal = (1 / 2 : ℝ) := by
    rw [Real.volume_Icc]
    norm_num
  rw [hv, smul_eq_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_pow]
  simp only [one_pow]
  push_cast
  field_simp <;> ring

theorem actual_atom_moment (s : ℝ) (n k : ℕ) :
    (∫ ω : ℕ → ℝ, (width s n * unitClamp (ω n)) ^ k ∂sourceCoordinateLaw) =
      width s n ^ k * ((1 - (-1 : ℝ) ^ (k + 1)) / (2 * ((k : ℝ) + 1))) := by
  have hm : Measurable (fun ω : ℕ → ℝ => width s n * unitClamp (ω n)) :=
    measurable_const.mul (continuous_unitClamp.measurable.comp (measurable_pi_apply n))
  have hp : ∀ μ : Measure ℝ, AEStronglyMeasurable (fun x : ℝ => x ^ k) μ :=
    fun _ => (continuous_id.pow k).aestronglyMeasurable
  calc
    _ = ∫ x : ℝ, x ^ k ∂sourceCoordinateLaw.map (fun ω : ℕ → ℝ => width s n * unitClamp (ω n)) :=
      (integral_map hm.aemeasurable (hp _)).symm
    _ = ∫ x : ℝ, x ^ k ∂centeredUnitBoxLaw.map (fun x : ℝ => width s n * x) := by
      rw [sourceSampleAtom_map_eq_scaled_box]
    _ = ∫ x : ℝ, (width s n * x) ^ k ∂centeredUnitBoxLaw :=
      integral_map (measurable_const.mul measurable_id).aemeasurable (hp _)
    _ = width s n ^ k * ∫ x : ℝ, x ^ k ∂centeredUnitBoxLaw := by
      simp_rw [mul_pow]
      rw [integral_const_mul]
    _ = _ := by rw [centered_box_moment]

theorem actual_partial_bound {s : ℝ} (hs : 0 ≤ s) (N K : ℕ) (ω : ℕ → ℝ) :
    |sourceSampleTailPartial s N K ω| ≤ tailRadius s N := by
  change ‖sourceSampleTailPartial s N K ω‖ ≤ _
  calc
    _ ≤ ∑ n ∈ range K, ‖width s (n + N) * unitClamp (ω (n + N))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range K, width s (n + N) := by
      apply Finset.sum_le_sum
      intro n _
      exact sourceSampleAtom_norm_le_width hs ω (n + N)
    _ ≤ ∑' n : ℕ, width s (n + N) :=
      (hasSum_tail_width hs N).summable.sum_le_tsum _ (fun n _ => width_nonneg hs (n + N))
    _ = _ := (hasSum_tail_width hs N).tsum_eq

theorem bounded_power_integrable {f : (ℕ → ℝ) → ℝ} (hf : Measurable f)
    (C : ℝ) (hb : ∀ ω, |f ω| ≤ C) (k : ℕ) :
    Integrable (fun ω => f ω ^ k) sourceCoordinateLaw := by
  apply (integrable_const (C ^ k)).mono' (hf.pow_const k).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) k

theorem actual_tail_moment_tendsto {s : ℝ} (hs : 0 ≤ s) (N k : ℕ) :
    Tendsto (fun K : ℕ => ∫ ω : ℕ → ℝ, sourceSampleTailPartial s N K ω ^ k ∂sourceCoordinateLaw)
      atTop (𝓝 (∫ ω : ℕ → ℝ, sourceSampleTail s N ω ^ k ∂sourceCoordinateLaw)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : ℕ → ℝ => tailRadius s N ^ k)
  · intro K
    exact ((measurable_sourceSampleTailPartial s N K).pow_const k).aestronglyMeasurable
  · exact integrable_const _
  · intro K
    exact Filter.Eventually.of_forall fun ω => by
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (actual_partial_bound hs N K ω) k
  · exact Filter.Eventually.of_forall fun ω => (tendsto_sourceSampleTailPartial hs N ω).pow k

#print axioms actual_tail_probability
#print axioms actual_tail_support
#print axioms actual_atom_moment



theorem independent_sum_moment {f g : (ℕ → ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g sourceCoordinateLaw)
    (hfi : ∀ k : ℕ, Integrable (fun ω => f ω ^ k) sourceCoordinateLaw)
    (hgi : ∀ k : ℕ, Integrable (fun ω => g ω ^ k) sourceCoordinateLaw) (k : ℕ) :
    (∫ ω, (f ω + g ω) ^ k ∂sourceCoordinateLaw) =
      ∑ i ∈ range (k + 1), (∫ ω, f ω ^ i ∂sourceCoordinateLaw) *
        (∫ ω, g ω ^ (k - i) ∂sourceCoordinateLaw) * (k.choose i : ℝ) := by
  have hp (i j : ℕ) : IndepFun (fun ω => f ω ^ i) (fun ω => g ω ^ j) sourceCoordinateLaw := by
    simpa only [Function.comp_def, id_eq] using
      hfg.comp (measurable_id.pow_const i) (measurable_id.pow_const j)
  simp_rw [add_pow]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_mul_const, (hp i (k-i)).integral_fun_mul_eq_mul_integral
      (hf.pow_const i).aestronglyMeasurable (hg.pow_const (k-i)).aestronglyMeasurable]
  · intro i _
    exact ((hp i (k-i)).integrable_mul (hfi i) (hgi (k-i))).mul_const _

theorem actual_tail_atom_measurable (s : ℝ) (N i : ℕ) :
    Measurable (fun ω : ℕ → ℝ => width s (i+N) * unitClamp (ω (i+N))) :=
  measurable_const.mul (continuous_unitClamp.measurable.comp (measurable_pi_apply _))

theorem actual_tail_atoms_independent (s : ℝ) (N : ℕ) :
    iIndepFun (fun i (ω : ℕ → ℝ) => width s (i+N) * unitClamp (ω (i+N)))
      sourceCoordinateLaw := by
  have h : iIndepFun (fun i (ω : ℕ → ℝ) => width s i * unitClamp (ω i)) sourceCoordinateLaw :=
    iIndepFun_infinitePi (fun _ => measurable_const.mul continuous_unitClamp.measurable)
  exact h.precomp (fun i j hij => Nat.add_right_cancel hij :
    Function.Injective (fun i : ℕ => i + N))

theorem actual_partial_step_independent (s : ℝ) (N K : ℕ) :
    IndepFun (sourceSampleTailPartial s N K)
      (fun ω : ℕ → ℝ => width s (K+N) * unitClamp (ω (K+N))) sourceCoordinateLaw := by
  have h := (actual_tail_atoms_independent s N).indepFun_finsetSum_of_notMem
    (actual_tail_atom_measurable s N) (s := range K) (i := K) (by simp)
  have he : (∑ j ∈ range K, (fun ω : ℕ → ℝ => width s (j+N) * unitClamp (ω (j+N)))) =
      sourceSampleTailPartial s N K := by
    funext ω
    simp only [Finset.sum_apply, sourceSampleTailPartial]
  rw [he] at h
  exact h

theorem actual_partial_succ (s : ℝ) (N K : ℕ) (ω : ℕ → ℝ) :
    sourceSampleTailPartial s N (K+1) ω = sourceSampleTailPartial s N K ω +
      width s (K+N) * unitClamp (ω (K+N)) := by
  simp only [sourceSampleTailPartial, Finset.sum_range_succ]

theorem partialVariance_succ (s : ℝ) (N K : ℕ) :
    partialVariance s N (K+1) = partialVariance s N K + width s (K+N)^2 / 3 := by
  simp only [partialVariance, Finset.sum_range_succ]
  ring

theorem actual_partial_step_moment {s : ℝ} (hs : 0 ≤ s) (N K k : ℕ) :
    (∫ ω, sourceSampleTailPartial s N (K+1) ω ^ k ∂sourceCoordinateLaw) =
      ∑ i ∈ range (k+1), (∫ ω, sourceSampleTailPartial s N K ω ^ i ∂sourceCoordinateLaw) *
        (width s (K+N) ^ (k-i) *
          ((1 - (-1 : ℝ)^((k-i)+1)) / (2*((k-i : ℕ):ℝ)+2))) * (k.choose i : ℝ) := by
  simp_rw [actual_partial_succ]
  rw [independent_sum_moment (measurable_sourceSampleTailPartial s N K)
    (actual_tail_atom_measurable s N K) (actual_partial_step_independent s N K)
    (bounded_power_integrable (measurable_sourceSampleTailPartial s N K) _
      (actual_partial_bound hs N K))
    (bounded_power_integrable (actual_tail_atom_measurable s N K) _
      (fun ω => sourceSampleAtom_norm_le_width hs ω (K+N)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [actual_atom_moment]
  congr 3
  ring

theorem actual_partial_moments {s : ℝ} (hs : 0 ≤ s) (N K : ℕ) :
    (∫ ω, sourceSampleTailPartial s N K ω ∂sourceCoordinateLaw) = 0 ∧
    (∫ ω, sourceSampleTailPartial s N K ω ^ 2 ∂sourceCoordinateLaw) = partialVariance s N K ∧
    (∫ ω, sourceSampleTailPartial s N K ω ^ 3 ∂sourceCoordinateLaw) = 0 ∧
    (∫ ω, sourceSampleTailPartial s N K ω ^ 4 ∂sourceCoordinateLaw) ≤ 3 * partialVariance s N K ^ 2 := by
  induction K with
  | zero => simp [sourceSampleTailPartial, partialVariance]
  | succ K ih =>
    rcases ih with ⟨ih1, ih2, ih3, ih4⟩
    have h1 := actual_partial_step_moment hs N K 1
    have h2 := actual_partial_step_moment hs N K 2
    have h3 := actual_partial_step_moment hs N K 3
    have h4 := actual_partial_step_moment hs N K 4
    norm_num [Finset.sum_range_succ, Nat.choose, ih1, ih2, ih3] at h1 h2 h3 h4
    refine ⟨h1, ?_, h3, ?_⟩
    · rw [h2, partialVariance_succ]
      ring
    · rw [h4, partialVariance_succ]
      nlinarith [sq_nonneg (width s (K+N)^2)]

#print axioms actual_partial_moments



theorem width_le_tailRadius {s : ℝ} (hs : 0 ≤ s) (N n : ℕ) :
    width s (n+N) ≤ tailRadius s N := by
  have h := (hasSum_tail_width hs N).summable.sum_le_tsum {n}
    (fun i _ => width_nonneg hs (i+N))
  simpa only [Finset.sum_singleton, (hasSum_tail_width hs N).tsum_eq, tailRadius] using h

theorem tail_squares_summable {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    Summable (fun n : ℕ => width s (n+N)^2) := by
  apply (Summable.mul_left (tailRadius s N) (hasSum_tail_width hs N).summable).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [width_nonneg hs (n+N), width_le_tailRadius hs N n]

theorem partialVariance_tendsto {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    Tendsto (partialVariance s N) atTop (𝓝 (tailVariance s N)) :=
  (tail_squares_summable hs N).hasSum.tendsto_sum_nat.const_mul (1/3)

theorem actual_tail_sample_moments {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    (∫ ω, sourceSampleTail s N ω ∂sourceCoordinateLaw) = 0 ∧
    (∫ ω, sourceSampleTail s N ω ^ 2 ∂sourceCoordinateLaw) = tailVariance s N ∧
    (∫ ω, sourceSampleTail s N ω ^ 3 ∂sourceCoordinateLaw) = 0 ∧
    (∫ ω, sourceSampleTail s N ω ^ 4 ∂sourceCoordinateLaw) ≤ 3 * tailVariance s N ^ 2 := by
  have h1 : (fun K : ℕ => ∫ ω, sourceSampleTailPartial s N K ω ^ 1 ∂sourceCoordinateLaw) =
      fun _ => (0 : ℝ) := by
    funext K
    simpa only [pow_one] using (actual_partial_moments hs N K).1
  have h2 : (fun K : ℕ => ∫ ω, sourceSampleTailPartial s N K ω ^ 2 ∂sourceCoordinateLaw) =
      partialVariance s N := by
    funext K
    exact (actual_partial_moments hs N K).2.1
  have h3 : (fun K : ℕ => ∫ ω, sourceSampleTailPartial s N K ω ^ 3 ∂sourceCoordinateLaw) =
      fun _ => (0 : ℝ) := by
    funext K
    exact (actual_partial_moments hs N K).2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ht := actual_tail_moment_tendsto hs N 1
    rw [h1] at ht
    simpa only [pow_one] using tendsto_nhds_unique ht tendsto_const_nhds
  · have ht := actual_tail_moment_tendsto hs N 2
    rw [h2] at ht
    exact tendsto_nhds_unique ht (partialVariance_tendsto hs N)
  · have ht := actual_tail_moment_tendsto hs N 3
    rw [h3] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  · exact le_of_tendsto_of_tendsto (actual_tail_moment_tendsto hs N 4)
      (((partialVariance_tendsto hs N).pow 2).const_mul 3)
      (Filter.Eventually.of_forall fun K => (actual_partial_moments hs N K).2.2.2)

theorem actual_tail_law_moment_eq_sample {s : ℝ} (hs : 0 ≤ s) (N k : ℕ) :
    (∫ u : ℝ, u ^ k ∂originalSourceTailLaw s N) =
      ∫ ω, sourceSampleTail s N ω ^ k ∂sourceCoordinateLaw :=
  integral_map (measurable_sourceSampleTail hs N).aemeasurable
    (continuous_id.pow k).aestronglyMeasurable

theorem actual_tail_law_moments {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    (∫ u : ℝ, u ∂originalSourceTailLaw s N) = 0 ∧
    (∫ u : ℝ, u ^ 2 ∂originalSourceTailLaw s N) = tailVariance s N ∧
    (∫ u : ℝ, u ^ 3 ∂originalSourceTailLaw s N) = 0 ∧
    (∫ u : ℝ, u ^ 4 ∂originalSourceTailLaw s N) ≤ 3 * tailVariance s N ^ 2 := by
  have h := actual_tail_sample_moments hs N
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ = ∫ ω, sourceSampleTail s N ω ∂sourceCoordinateLaw := by
        simpa only [pow_one] using actual_tail_law_moment_eq_sample hs N 1
      _ = 0 := h.1
  · rw [actual_tail_law_moment_eq_sample hs N 2]
    exact h.2.1
  · rw [actual_tail_law_moment_eq_sample hs N 3]
    exact h.2.2.1
  · rw [actual_tail_law_moment_eq_sample hs N 4]
    exact h.2.2.2

#print axioms actual_tail_law_moments



theorem actual_tail_law_power_integrable {s : ℝ} (hs : 0 ≤ s) (N k : ℕ) :
    Integrable (fun u : ℝ => u ^ k) (originalSourceTailLaw s N) := by
  letI := actual_tail_probability hs N
  apply (integrable_const (tailRadius s N ^ k)).mono' (continuous_id.pow k).aestronglyMeasurable
  filter_upwards [actual_tail_support hs N] with u hu
  change ‖u ^ k‖ ≤ tailRadius s N ^ k
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hu k

theorem actual_tail_variance_pos {s : ℝ} (hs : 0 < s) (N : ℕ) :
    0 < tailVariance s N := by
  have h := (tail_squares_summable hs.le N).sum_le_tsum {0}
    (fun i _ => sq_nonneg (width s (i+N)))
  simp only [Finset.sum_singleton, zero_add] at h
  have hp := sq_pos_of_pos (width_pos hs N)
  dsimp only [tailVariance]
  linarith

/-- Literal unchanged-source specialization, all N (hence the requested public N ≥ 12). -/
theorem probe_tail_law_contract (N : ℕ) :
    IsProbabilityMeasure (originalSourceTailLaw probeSigma N) ∧
    (∀ᵐ u ∂originalSourceTailLaw probeSigma N, |u| ≤ probeSigma / ((N : ℝ)+1)) ∧
    (∫ u : ℝ, u ∂originalSourceTailLaw probeSigma N) = 0 ∧
    (∫ u : ℝ, u ^ 3 ∂originalSourceTailLaw probeSigma N) = 0 ∧
    (∫ u : ℝ, u ^ 2 ∂originalSourceTailLaw probeSigma N) =
      (1/3) * ∑' n : ℕ, width probeSigma (n+N)^2 ∧
    (∫ u : ℝ, u ^ 4 ∂originalSourceTailLaw probeSigma N) ≤
      3 * ((1/3) * ∑' n : ℕ, width probeSigma (n+N)^2)^2 := by
  have h := actual_tail_law_moments probeSigma_pos.le N
  exact ⟨actual_tail_probability probeSigma_pos.le N, actual_tail_support probeSigma_pos.le N,
    h.1, h.2.2.1, h.2.1, h.2.2.2⟩

#print axioms probe_tail_law_contract
#print axioms actual_tail_variance_pos
#print axioms actual_tail_law_power_integrable



theorem complex_exp_real_path_deriv (c : ℂ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => Complex.exp (c*t)) =
      fun t : ℝ => c^k * Complex.exp (c*t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : HasDerivAt (fun u : ℝ => c^k * Complex.exp (c*u))
        (c^k * (Complex.exp (c*t)*c)) t := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
        (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).cexp).const_mul (c^k)
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hd.deriv

theorem imaginary_exp_taylor_bound (x : ℝ) (n : ℕ) :
    ‖Complex.exp (Complex.I*x) - ∑ k ∈ range (n+1),
      (Complex.I*x)^k / (k.factorial : ℂ)‖ ≤ |x|^(n+1) / ((n+1).factorial : ℝ) := by
  let f : ℝ → ℂ := fun t => Complex.exp ((Complex.I*x)*t)
  have ho : ContDiff ℝ ⊤ (fun t : ℝ => (t:ℂ)) := Complex.ofRealCLM.contDiff
  have hf : ContDiff ℝ ⊤ f := Complex.contDiff_exp.comp (contDiff_const.mul ho)
  have hw (k : ℕ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      iteratedDerivWithin k f (Icc (0:ℝ) 1) t =
        (Complex.I*x)^k * Complex.exp ((Complex.I*x)*t) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hf.of_le (by exact_mod_cast le_top)).contDiffAt ht]
    exact congrFun (complex_exp_real_path_deriv (Complex.I*x) k) t
  have htaylor : taylorWithinEval f n (Icc (0:ℝ) 1) 0 1 =
      ∑ k ∈ range (n+1), (Complex.I*x)^k / (k.factorial : ℂ) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [hw k 0 (by norm_num)]
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  have hrem := taylor_integral_remainder (x₀ := (0:ℝ)) (x := 1) (n := n)
    ((hf.of_le (by exact_mod_cast le_top)).contDiffOn)
  simp only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hrem
  rw [htaylor] at hrem
  have heval : f 1 = Complex.exp (Complex.I*x) := by simp [f]
  rw [heval] at hrem
  rw [hrem]
  have hnorm : ∀ t ∈ Ioc (0:ℝ) 1,
      ‖((1-t)^n / (n.factorial : ℝ)) •
        iteratedDerivWithin (n+1) f (Icc (0:ℝ) 1) t‖ =
      ((1-t)^n / (n.factorial : ℝ)) * |x|^(n+1) := by
    intro t ht
    have hnon : 0 ≤ 1-t := sub_nonneg.mpr ht.2
    rw [hw (n+1) t ⟨ht.1.le, ht.2⟩, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    have hre : (((Complex.I*x)*(t:ℂ)) : ℂ).re = 0 := by simp
    rw [Complex.norm_exp, hre, Real.exp_zero, mul_one]
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ((1-t)^n / (n.factorial : ℝ)) * |x|^(n+1) := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      · exact Filter.Eventually.of_forall fun t ht => (hnorm t ht).le
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
        intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^n) 1]
      norm_num only [sub_self, sub_zero, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero n)]
      rw [Nat.factorial_succ]
      push_cast
      field_simp <;> ring

#print axioms imaginary_exp_taylor_bound



def actualTailTaylorPolynomial (τ : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), ((Complex.I*τ)*(u:ℂ))^k / (k.factorial : ℂ)

theorem actual_tail_complex_monomial_integrable {s : ℝ} (hs : 0 ≤ s) (N : ℕ)
    (τ : ℝ) (k : ℕ) :
    Integrable (fun u : ℝ => ((Complex.I*τ)*(u:ℂ))^k / (k.factorial:ℂ))
      (originalSourceTailLaw s N) := by
  have hr : Integrable (fun u : ℝ => ((u^k:ℝ):ℂ)) (originalSourceTailLaw s N) :=
    (actual_tail_law_power_integrable hs N k).ofReal
  have h := hr.const_mul ((Complex.I*τ)^k / (k.factorial:ℂ))
  simpa only [mul_pow, Complex.ofReal_pow, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

theorem actual_tail_taylor_polynomial_integrable {s : ℝ} (hs : 0 ≤ s) (N : ℕ)
    (τ : ℝ) (n : ℕ) :
    Integrable (actualTailTaylorPolynomial τ n) (originalSourceTailLaw s N) :=
  integrable_finsetSum (range (n+1)) (fun k _ => actual_tail_complex_monomial_integrable hs N τ k)

theorem actual_tail_taylor_polynomial_integral {s : ℝ} (hs : 0 ≤ s) (N : ℕ)
    (τ : ℝ) (n : ℕ) :
    (∫ u : ℝ, actualTailTaylorPolynomial τ n u ∂originalSourceTailLaw s N) =
      ∑ k ∈ range (n+1), (Complex.I*τ)^k / (k.factorial:ℂ) *
        (((∫ u : ℝ, (u^k:ℝ) ∂originalSourceTailLaw s N):ℝ):ℂ) := by
  change (∫ u : ℝ, ∑ k ∈ range (n+1), ((Complex.I*τ)*(u:ℂ))^k / (k.factorial:ℂ)
    ∂originalSourceTailLaw s N) = _
  rw [integral_finsetSum (range (n+1))
    (fun k _ => actual_tail_complex_monomial_integrable hs N τ k)]
  apply Finset.sum_congr rfl
  intro k _
  have he : (fun u : ℝ => ((Complex.I*τ)*(u:ℂ))^k / (k.factorial:ℂ)) =
      fun u : ℝ => ((Complex.I*τ)^k / (k.factorial:ℂ)) * ((u^k:ℝ):ℂ) := by
    funext u
    simp only [mul_pow, Complex.ofReal_pow, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [he, integral_const_mul, integral_complex_ofReal]

theorem actual_tail_oscillator_integrable {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (τ : ℝ) :
    Integrable (fun u : ℝ => Complex.exp ((Complex.I*τ)*(u:ℂ))) (originalSourceTailLaw s N) := by
  letI := actual_tail_probability hs N
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun u => by simp [Complex.norm_exp]

theorem actual_tail_charFun_remainder_integral {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (τ : ℝ) (n : ℕ) :
    charFun (originalSourceTailLaw s N) τ -
      ∑ k ∈ range (n+1), (Complex.I*τ)^k / (k.factorial:ℂ) *
        (((∫ u : ℝ, (u^k:ℝ) ∂originalSourceTailLaw s N):ℝ):ℂ) =
      ∫ u : ℝ, Complex.exp ((Complex.I*τ)*(u:ℂ)) - actualTailTaylorPolynomial τ n u
        ∂originalSourceTailLaw s N := by
  rw [integral_sub (actual_tail_oscillator_integrable hs N τ)
    (actual_tail_taylor_polynomial_integrable hs N τ n),
    actual_tail_taylor_polynomial_integral hs N τ n]
  rw [charFun_apply_real]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    congr 1
    push_cast
    ring

#print axioms actual_tail_charFun_remainder_integral



theorem actual_tail_charFun_taylor_bound {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (τ : ℝ) (n : ℕ) :
    ‖charFun (originalSourceTailLaw s N) τ -
      ∑ k ∈ range (n+1), (Complex.I*τ)^k / (k.factorial:ℂ) *
        (((∫ u : ℝ, (u^k:ℝ) ∂originalSourceTailLaw s N):ℝ):ℂ)‖ ≤
      (|τ|^(n+1) / ((n+1).factorial:ℝ)) *
        ∫ u : ℝ, |u|^(n+1) ∂originalSourceTailLaw s N := by
  rw [actual_tail_charFun_remainder_integral hs N τ n]
  have hb : Integrable (fun u : ℝ => |u|^(n+1)) (originalSourceTailLaw s N) := by
    simpa only [norm_pow, Real.norm_eq_abs] using (actual_tail_law_power_integrable hs N (n+1)).norm
  calc
    _ ≤ ∫ u : ℝ, (|τ|^(n+1) / ((n+1).factorial:ℝ)) * |u|^(n+1)
        ∂originalSourceTailLaw s N := by
      apply norm_integral_le_of_norm_le (hb.const_mul _)
      exact Filter.Eventually.of_forall fun u => by
        have h := imaginary_exp_taylor_bound (τ*u) n
        have he : Complex.I*((τ*u:ℝ):ℂ) = (Complex.I*τ)*(u:ℂ) := by push_cast; ring
        rw [he] at h
        calc
          _ ≤ |τ*u|^(n+1) / ((n+1).factorial:ℝ) := h
          _ = _ := by rw [abs_mul, mul_pow]; ring
    _ = _ := integral_const_mul _ _

theorem actual_tail_abs_even_moment {s : ℝ} (hs : 0 ≤ s) (N k : ℕ) :
    (∫ u : ℝ, |u|^(2*k) ∂originalSourceTailLaw s N) =
      ∫ u : ℝ, u^(2*k) ∂originalSourceTailLaw s N := by
  congr 1
  funext u
  rw [pow_mul, pow_mul, sq_abs]

theorem actual_tail_charFun_first_bound {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (τ : ℝ) :
    ‖1 - charFun (originalSourceTailLaw s N) τ‖ ≤ tailRadius s N * |τ| := by
  letI := actual_tail_probability hs N
  have h := actual_tail_charFun_taylor_bound hs N τ 0
  norm_num [Finset.sum_range_succ] at h
  have ha : (∫ u : ℝ, |u| ∂originalSourceTailLaw s N) ≤ tailRadius s N := by
    calc
      _ ≤ ∫ _ : ℝ, tailRadius s N ∂originalSourceTailLaw s N :=
        integral_mono_ae (by simpa only [norm_pow, pow_one, Real.norm_eq_abs] using
          (actual_tail_law_power_integrable hs N 1).norm) (integrable_const _)
          (actual_tail_support hs N)
      _ = _ := by simp
  rw [norm_sub_rev]
  exact h.trans (by nlinarith [abs_nonneg τ])

theorem actual_tail_charFun_second_bound {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (τ : ℝ) :
    ‖1 - charFun (originalSourceTailLaw s N) τ‖ ≤ tailVariance s N * τ^2 / 2 := by
  letI := actual_tail_probability hs N
  have hm := actual_tail_law_moments hs N
  have h := actual_tail_charFun_taylor_bound hs N τ 1
  norm_num [Finset.sum_range_succ, hm.1, actual_tail_abs_even_moment hs N 1, hm.2.1] at h
  rw [norm_sub_rev]
  convert h using 1 <;> ring

theorem actual_tail_charFun_fourth_bound {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (τ : ℝ) :
    ‖charFun (originalSourceTailLaw s N) τ - 1 + ((tailVariance s N * τ^2 / 2 : ℝ):ℂ)‖ ≤
      tailVariance s N ^ 2 * τ^4 / 8 := by
  letI := actual_tail_probability hs N
  have hm := actual_tail_law_moments hs N
  have h := actual_tail_charFun_taylor_bound hs N τ 3
  norm_num [Finset.sum_range_succ, hm.1, hm.2.1, hm.2.2.1,
    actual_tail_abs_even_moment hs N 2, mul_pow, Complex.I_sq] at h
  have he : charFun (originalSourceTailLaw s N) τ - 1 + ((tailVariance s N * τ^2 / 2 : ℝ):ℂ) =
      charFun (originalSourceTailLaw s N) τ -
        (1 + (-((τ:ℂ)^2) / 2) * (tailVariance s N:ℂ)) := by push_cast; ring
  rw [he]
  apply h.trans
  have hcoef : 0 ≤ |τ|^4 / 24 := by positivity
  have hbound := mul_le_mul_of_nonneg_left hm.2.2.2 hcoef
  apply hbound.trans_eq
  have habs : |τ|^4 = τ^4 := by
    calc |τ|^4 = (|τ|^2)^2 := by ring
         _ = (τ^2)^2 := by rw [sq_abs]
         _ = τ^4 := by ring
  rw [habs]
  ring

#print axioms actual_tail_charFun_first_bound
#print axioms actual_tail_charFun_second_bound
#print axioms actual_tail_charFun_fourth_bound

end Zeta23.OPICARound2.SourceTailMoments

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped Topology

namespace Zeta23.OPICARound2

theorem probeFunctionL2_norm_sq (f : ℝ→ℂ) (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖^2=∫ t : ℝ,‖f t‖^2 := by
  rw [OPICAFollowup.L2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]

theorem probeL2_error_of_logFourier_bound (f g : ℝ→ℂ)
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume)
    (C : ℝ) (hC : 0≤C)
    (hFourier : ∀ tau : ℝ, ‖OPICAFollowup.logFourier f tau‖≤C*‖OPICAFollowup.logFourier g tau‖) :
    ‖hf2.toLp f‖≤C*‖hg2.toLp g‖ := by
  obtain ⟨hiF,heF⟩ := OPICAFollowup.logFourier_plancherel hf1 hf2
  obtain ⟨hiG,heG⟩ := OPICAFollowup.logFourier_plancherel hg1 hg2
  have hsq (tau : ℝ) : ‖OPICAFollowup.logFourier f tau‖^2≤
      C^2*‖OPICAFollowup.logFourier g tau‖^2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr (hFourier tau)
    simpa only [mul_pow] using h
  have hint := integral_mono hiF (hiG.const_mul (C^2)) hsq
  rw [integral_const_mul] at hint
  have hscaled := mul_le_mul_of_nonneg_left hint (by positivity : 0≤1/(2*Real.pi))
  rw [← heF] at hscaled
  have hscaled' : (∫ t : ℝ,‖f t‖^2)≤C^2*(∫ t : ℝ,‖g t‖^2) := by
    nlinarith [heG]
  rw [← probeFunctionL2_norm_sq f hf2,← probeFunctionL2_norm_sq g hg2] at hscaled'
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  simpa only [mul_pow] using hscaled'

#print axioms Zeta23.OPICARound2.probeL2_error_of_logFourier_bound

end Zeta23.OPICARound2
namespace Zeta23.OPICARound2
open SourceTailMoments

theorem probeLogFourier_sub {f g : ℝ→ℂ} (hf : Integrable f) (hg : Integrable g) (tau : ℝ) :
    OPICAFollowup.logFourier (f-g) tau=
      OPICAFollowup.logFourier f tau-OPICAFollowup.logFourier g tau := by
  unfold OPICAFollowup.logFourier
  simp only [Pi.sub_apply,mul_sub]
  rw [integral_sub (probeFourierDamping_integrable hf tau) (probeFourierDamping_integrable hg tau)]

theorem probeLogFourier_add {f g : ℝ→ℂ} (hf : Integrable f) (hg : Integrable g) (tau : ℝ) :
    OPICAFollowup.logFourier (f+g) tau=
      OPICAFollowup.logFourier f tau+OPICAFollowup.logFourier g tau := by
  unfold OPICAFollowup.logFourier
  simp only [Pi.add_apply,mul_add]
  rw [integral_add (probeFourierDamping_integrable hf tau) (probeFourierDamping_integrable hg tau)]

theorem probeLogFourier_const_mul (c : ℂ) (f : ℝ→ℂ) (tau : ℝ) :
    OPICAFollowup.logFourier (fun t => c*f t) tau=c*OPICAFollowup.logFourier f tau := by
  unfold OPICAFollowup.logFourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem probePrefixJ_integrable (M : ℕ) (hM : 12≤M) : Integrable (probePrefixJ M) := by
  simpa only [iteratedDeriv_zero] using probePrefixJ_derivative_integrable M 0 hM (by norm_num)

theorem probePrefixJ_memLp (M : ℕ) (hM : 12≤M) : MemLp (probePrefixJ M) 2 volume := by
  simpa only [iteratedDeriv_zero] using probePrefixJ_derivative_memLp M 0 hM (by norm_num)

def probePrefixSourceError (M : ℕ) : ℝ→ℂ := probeCanonicalJ-probePrefixJ M

theorem probePrefixSourceError_integrable (M : ℕ) (hM : 12≤M) :
    Integrable (probePrefixSourceError M) := probeCanonicalJ_integrable.sub (probePrefixJ_integrable M hM)

theorem probePrefixSourceError_memLp (M : ℕ) (hM : 12≤M) :
    MemLp (probePrefixSourceError M) 2 volume := probeCanonicalJ_memLp.sub (probePrefixJ_memLp M hM)

theorem probePrefixSourceError_fourier_norm (M : ℕ) (hM : 12≤M) (tau : ℝ) :
    ‖OPICAFollowup.logFourier (probePrefixSourceError M) tau‖=
      ‖OPICAFollowup.logFourier (probePrefixJ M) tau‖*
        ‖1-charFun (originalSourceTailLaw probeSigma M) (-tau)‖ := by
  rw [probePrefixSourceError,probeLogFourier_sub probeCanonicalJ_integrable (probePrefixJ_integrable M hM),
    probePrefixJ_actual_fourier_split M hM]
  have he : OPICAFollowup.logFourier (probePrefixJ M) tau*
      charFun (originalSourceTailLaw probeSigma M) (-tau)-OPICAFollowup.logFourier (probePrefixJ M) tau=
      OPICAFollowup.logFourier (probePrefixJ M) tau*
        (charFun (originalSourceTailLaw probeSigma M) (-tau)-1) := by ring
  rw [he,norm_mul,norm_sub_rev]

theorem probePrefixSourceError_first_bound (M : ℕ) (hM : 12≤M) :
    ‖(probePrefixSourceError_memLp M hM).toLp (probePrefixSourceError M)‖≤
      tailRadius probeSigma M*
        ‖(probePrefixJ_derivative_memLp M 1 hM (by norm_num)).toLp (iteratedDeriv 1 (probePrefixJ M))‖ := by
  apply probeL2_error_of_logFourier_bound _ _ (probePrefixSourceError_integrable M hM)
    (probePrefixSourceError_memLp M hM) (probePrefixJ_derivative_integrable M 1 hM (by norm_num))
      (probePrefixJ_derivative_memLp M 1 hM (by norm_num)) _
        (by unfold tailRadius; exact div_nonneg probeSigma_pos.le (by positivity))
  intro tau
  rw [probePrefixSourceError_fourier_norm M hM,probePrefixJ_derivative_fourier_norm M 1 hM (by norm_num)]
  have hb := actual_tail_charFun_first_bound probeSigma_pos.le M (-tau)
  rw [abs_neg] at hb
  have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (OPICAFollowup.logFourier (probePrefixJ M) tau))
  simpa only [pow_one,mul_left_comm,mul_comm,mul_assoc] using hm

theorem probePrefixSourceError_second_bound (M : ℕ) (hM : 12≤M) :
    ‖(probePrefixSourceError_memLp M hM).toLp (probePrefixSourceError M)‖≤
      (tailVariance probeSigma M/2)*
        ‖(probePrefixJ_derivative_memLp M 2 hM (by norm_num)).toLp (iteratedDeriv 2 (probePrefixJ M))‖ := by
  apply probeL2_error_of_logFourier_bound _ _ (probePrefixSourceError_integrable M hM)
    (probePrefixSourceError_memLp M hM) (probePrefixJ_derivative_integrable M 2 hM (by norm_num))
      (probePrefixJ_derivative_memLp M 2 hM (by norm_num)) _
        (div_nonneg (actual_tail_variance_pos probeSigma_pos M).le (by norm_num))
  intro tau
  rw [probePrefixSourceError_fourier_norm M hM,probePrefixJ_derivative_fourier_norm M 2 hM (by norm_num),sq_abs]
  have hb := actual_tail_charFun_second_bound probeSigma_pos.le M (-tau)
  rw [neg_sq] at hb
  have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (OPICAFollowup.logFourier (probePrefixJ M) tau))
  exact hm.trans_eq (by ring)

def probePrefixCorrectedJ (M : ℕ) : ℝ→ℂ := probePrefixJ M+
  fun t => ((tailVariance probeSigma M/2:ℝ):ℂ)*iteratedDeriv 2 (probePrefixJ M) t

theorem probePrefixCorrectedJ_integrable (M : ℕ) (hM : 12≤M) : Integrable (probePrefixCorrectedJ M) :=
  (probePrefixJ_integrable M hM).add
    ((probePrefixJ_derivative_integrable M 2 hM (by norm_num)).const_mul _)

theorem probePrefixCorrectedJ_memLp (M : ℕ) (hM : 12≤M) : MemLp (probePrefixCorrectedJ M) 2 volume :=
  (probePrefixJ_memLp M hM).add ((probePrefixJ_derivative_memLp M 2 hM (by norm_num)).const_mul _)

theorem probePrefixCorrectedJ_fourier (M : ℕ) (hM : 12≤M) (tau : ℝ) :
    OPICAFollowup.logFourier (probePrefixCorrectedJ M) tau=
      OPICAFollowup.logFourier (probePrefixJ M) tau-
        ((tailVariance probeSigma M*tau^2/2:ℝ):ℂ)*OPICAFollowup.logFourier (probePrefixJ M) tau := by
  rw [probePrefixCorrectedJ,probeLogFourier_add (probePrefixJ_integrable M hM)
    ((probePrefixJ_derivative_integrable M 2 hM (by norm_num)).const_mul _),
    probeLogFourier_const_mul,probePrefixJ_derivative_fourier M 2 hM (by norm_num)]
  have hi : ((tau:ℂ)*Complex.I)^2= -((tau:ℂ)^2) := by rw [mul_pow,Complex.I_sq]; ring
  rw [hi]
  push_cast
  ring

def probePrefixCorrectedError (M : ℕ) : ℝ→ℂ := probeCanonicalJ-probePrefixCorrectedJ M

theorem probePrefixCorrectedError_integrable (M : ℕ) (hM : 12≤M) : Integrable (probePrefixCorrectedError M) :=
  probeCanonicalJ_integrable.sub (probePrefixCorrectedJ_integrable M hM)

theorem probePrefixCorrectedError_memLp (M : ℕ) (hM : 12≤M) : MemLp (probePrefixCorrectedError M) 2 volume :=
  probeCanonicalJ_memLp.sub (probePrefixCorrectedJ_memLp M hM)

theorem probeAbs_pow_four (t : ℝ) : |t|^4=t^4 := by
  calc
    _=(|t|^2)^2 := by ring
    _=(t^2)^2 := by rw [sq_abs]
    _=_ := by ring

theorem probePrefixCorrectedError_fourth_bound (M : ℕ) (hM : 12≤M) :
    ‖(probePrefixCorrectedError_memLp M hM).toLp (probePrefixCorrectedError M)‖≤
      (tailVariance probeSigma M^2/8)*
        ‖(probePrefixJ_derivative_memLp M 4 hM (by norm_num)).toLp (iteratedDeriv 4 (probePrefixJ M))‖ := by
  apply probeL2_error_of_logFourier_bound _ _ (probePrefixCorrectedError_integrable M hM)
    (probePrefixCorrectedError_memLp M hM) (probePrefixJ_derivative_integrable M 4 hM (by norm_num))
      (probePrefixJ_derivative_memLp M 4 hM (by norm_num)) _ (by positivity)
  intro tau
  rw [probePrefixCorrectedError,probeLogFourier_sub probeCanonicalJ_integrable
    (probePrefixCorrectedJ_integrable M hM),probePrefixJ_actual_fourier_split M hM,
      probePrefixCorrectedJ_fourier M hM,probePrefixJ_derivative_fourier_norm M 4 hM (by norm_num),
        probeAbs_pow_four]
  have he : OPICAFollowup.logFourier (probePrefixJ M) tau*
      charFun (originalSourceTailLaw probeSigma M) (-tau)-
        (OPICAFollowup.logFourier (probePrefixJ M) tau-
          ((tailVariance probeSigma M*tau^2/2:ℝ):ℂ)*OPICAFollowup.logFourier (probePrefixJ M) tau)=
      OPICAFollowup.logFourier (probePrefixJ M) tau*
        (charFun (originalSourceTailLaw probeSigma M) (-tau)-1+
          ((tailVariance probeSigma M*tau^2/2:ℝ):ℂ)) := by ring
  rw [he,norm_mul]
  have hb := actual_tail_charFun_fourth_bound probeSigma_pos.le M (-tau)
  rw [neg_sq,show (-tau)^4=tau^4 by ring] at hb
  have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (OPICAFollowup.logFourier (probePrefixJ M) tau))
  exact hm.trans_eq (by ring)

#print axioms Zeta23.OPICARound2.probePrefixSourceError_first_bound
#print axioms Zeta23.OPICARound2.probePrefixSourceError_second_bound
#print axioms Zeta23.OPICARound2.probePrefixCorrectedError_fourth_bound

end Zeta23.OPICARound2

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace Zeta23.OPICARound2

def probeCoefficientMass {N : ℕ} (x : Fin N→ℂ) : ℝ :=
  ∑ i : Fin N, ‖x i‖/Real.sqrt (i.val+1)

theorem probeCoefficientMass_nonneg {N : ℕ} (x : Fin N→ℂ) : 0≤probeCoefficientMass x := by
  exact Finset.sum_nonneg (fun i _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))

theorem probeJ2_pos : 0<‖probeSource‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have hv : probeTarget=0 := by rw [probeTarget,hzero,map_zero]
  exact probeTarget_ne_zero hv

theorem probeInput_norm (n : ℕ) (hn : n≠0) :
    ‖probeInput n‖=‖probeSource‖/Real.sqrt n := by
  rw [probeInput,dif_neg hn,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by unfold CCM.nativeIntegerCoefficient; positivity),probeDelay_norm]
  unfold CCM.nativeIntegerCoefficient
  ring

theorem probeFiniteInput_norm_le_mass {N : ℕ} (x : Fin N→ℂ) :
    ‖probeFiniteInput x‖≤‖probeSource‖*probeCoefficientMass x := by
  calc
    _≤∑ i : Fin N,‖x i • probeInput (i.val+1)‖ := norm_sum_le _ _
    _=‖probeSource‖*probeCoefficientMass x := by
      simp_rw [norm_smul,probeInput_norm _ (Nat.succ_ne_zero _)]
      rw [probeCoefficientMass,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring

theorem probeFiniteInput_lag_error {N : ℕ} (x : Fin N→ℂ) (Tlag : ℝ) :
    ‖(probeFiniteOutput x:ProbeL2)-kernelL2Operator (probeFloorKernelCutoff Tlag)
      (probeFloorKernelCutoff_integrable Tlag) (probeFiniteInput x:ProbeL2)‖≤
        2*Real.exp (-Tlag/2)*‖probeSource‖*probeCoefficientMass x := by
  rw [probeFiniteOutput_eq_operator]
  change ‖CCM.nativeDampedCompletionL2Operator 0 (le_refl 0) (probeFiniteInput x:ProbeL2)-
    kernelL2Operator (probeFloorKernelCutoff Tlag) (probeFloorKernelCutoff_integrable Tlag)
      (probeFiniteInput x:ProbeL2)‖≤_
  have h := native_floor_physical_cutoff_bound Tlag (probeFiniteInput x:ProbeL2)
  have hb := mul_le_mul_of_nonneg_left (probeFiniteInput_norm_le_mass x)
    (by positivity : 0≤2*Real.exp (-Tlag/2))
  change 2*Real.exp (-Tlag/2)*‖(probeFiniteInput x:ProbeL2)‖≤
    2*Real.exp (-Tlag/2)*(‖probeSource‖*probeCoefficientMass x) at hb
  exact h.trans (hb.trans_eq (by ring))

theorem probeSufficientLagBudget_log (T A theta eta : ℝ)
    (hA : 0<A) (htheta : 0<theta) (heta : 0<eta)
    (budget : 2*Real.exp (-T/2)*A≤theta*eta) :
    2*Real.log (2*A/(theta*eta))≤T := by
  have he : Real.exp (T/2)*Real.exp (-T/2)=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hm := mul_le_mul_of_nonneg_left budget (Real.exp_pos (T/2)).le
  have hrewrite : Real.exp (T/2)*(2*Real.exp (-T/2)*A)=2*A := by
    calc
      _=2*A*(Real.exp (T/2)*Real.exp (-T/2)) := by ring
      _=2*A := by rw [he,mul_one]
  rw [hrewrite] at hm
  have hdiv : 2*A/(theta*eta)≤Real.exp (T/2) := by
    apply (div_le_iff₀ (mul_pos htheta heta)).mpr
    nlinarith [hm]
  have hlog := Real.log_le_log (div_pos (by positivity) (mul_pos htheta heta)) hdiv
  rw [Real.log_exp] at hlog
  linarith

theorem probeVisibleZero_coefficient_mass (rho : zetaZeroConfig.carrier)
    (hcritical : (rho:ℂ).re=1/2) (hvisible : JPlus ((rho:ℂ)-1/2)≠0) :
    ∃ cstar eta0 : ℝ,0<cstar ∧ 0<eta0 ∧
      ∀ eta : ℝ,0<eta → eta≤eta0 → ∀ (N : ℕ) (x : Fin N→ℂ),
        ‖probeResidual x‖≤eta →
          (cstar/eta)^(2*(zeroMult (rho:ℂ):ℝ)-1)≤‖probeSource‖*probeCoefficientMass x := by
  obtain ⟨cstar,eta0,hc,he,hcost⟩ := native_probe_visible_boundary_input_cost rho hcritical hvisible
  refine ⟨cstar,eta0,hc,he,?_⟩
  intro eta heta heta0 N x herr
  have hr : ‖probeTarget-probeOperator (probeFiniteInput x)‖≤eta := by
    rw [← probeFiniteOutput_eq_operator]
    exact herr
  exact (hcost eta heta heta0 (probeFiniteInput x) hr).trans (probeFiniteInput_norm_le_mass x)

def probeShrinkingIdentity (N : ℕ) : CausalProbeL2→L[ℂ] CausalProbeL2 :=
  ((1/2:ℂ)^N) • ContinuousLinearMap.id ℂ CausalProbeL2

theorem probeShrinkingIdentity_norm (N : ℕ) (f : CausalProbeL2) :
    ‖probeShrinkingIdentity N f‖=(1/2:ℝ)^N*‖f‖ := by
  change ‖((1/2:ℂ)^N) • f‖=_
  rw [norm_smul,norm_pow]
  norm_num

theorem probeShrinkingIdentity_residual_tendsto (f : CausalProbeL2) :
    Tendsto (fun N : ℕ => ‖probeShrinkingIdentity N f‖) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => (1/2:ℝ)^N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [probeShrinkingIdentity_norm,zero_mul] using h.mul_const ‖f‖

theorem probeShrinkingIdentity_normalized_witness (N : ℕ) (f : CausalProbeL2)
    (Gamma : ℝ) (hGamma : 0<Gamma) :
    0<(1/2:ℝ)^N*Gamma ∧
      ‖probeShrinkingIdentity N f‖/((1/2:ℝ)^N*Gamma)=‖f‖/Gamma := by
  refine ⟨mul_pos (by positivity) hGamma,?_⟩
  rw [probeShrinkingIdentity_norm]
  field_simp

theorem probeFixedFilter_error_transport (B : CausalProbeL2→L[ℂ] CausalProbeL2)
    (f g : CausalProbeL2) (epsilon : ℝ) (herr : ‖f-g‖≤epsilon) :
    ‖B f-B g‖≤‖B‖*epsilon := by
  rw [← map_sub]
  exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left herr (norm_nonneg B))

theorem probeVariableFilter_normalized_margin (B : CausalProbeL2→L[ℂ] CausalProbeL2)
    (r : CausalProbeL2) (Gamma : ℝ) (hGamma : 0<Gamma) (margin : Gamma≤‖B r‖) :
    1≤‖B r‖/Gamma := (one_le_div₀ hGamma).mpr margin

#print axioms Zeta23.OPICARound2.probeFiniteInput_lag_error
#print axioms Zeta23.OPICARound2.probeVisibleZero_coefficient_mass
#print axioms Zeta23.OPICARound2.probeShrinkingIdentity_normalized_witness

end Zeta23.OPICARound2
namespace Zeta23.OPICARound2
open Matrix

def probeTargetKernelMass : ℝ := ∫ t : ℝ,‖probeC t‖
def probeOutputKernelMass : ℝ := ∫ t : ℝ,‖CCM.nativePositiveCompletion t‖

theorem probeTargetKernelMass_nonneg : 0≤probeTargetKernelMass := integral_nonneg (fun _ => norm_nonneg _)
theorem probeOutputKernelMass_nonneg : 0≤probeOutputKernelMass := integral_nonneg (fun _ => norm_nonneg _)

def probeApproxTarget (g : ProbeL2) : ProbeL2 := kernelL2Operator probeC probeC_integrable g
def probeApproxCompleted (g : ProbeL2) : ProbeL2 :=
  kernelL2Operator CCM.nativePositiveCompletion CCM.nativePositiveCompletion_integrable g

def probeApproxColumn (g : ProbeL2) (n : ℕ) : ProbeL2 :=
  (CCM.nativeIntegerCoefficient n:ℂ) • CCM.nativeCompletionL2Delay (Real.log n) (probeApproxCompleted g)

def probeApproxFiniteOutput {N : ℕ} (g : ProbeL2) (x : Fin N→ℂ) : ProbeL2 :=
  ∑ i : Fin N,x i • probeApproxColumn g (i.val+1)

def probeApproxResidual {N : ℕ} (g : ProbeL2) (x : Fin N→ℂ) : ProbeL2 :=
  probeApproxTarget g-probeApproxFiniteOutput g x

theorem probeTarget_as_approx : (probeTarget:ProbeL2)=probeApproxTarget (probeSource:ProbeL2) := rfl

theorem probeCompleted_as_approx : (probeCompletedSource:ProbeL2)=probeApproxCompleted (probeSource:ProbeL2) :=
  nativeFloorL2Operator_eq_kernel (probeSource:ProbeL2)

theorem probeColumn_as_approx {n : ℕ} (hn : n≠0) :
    (probeColumn n:ProbeL2)=probeApproxColumn (probeSource:ProbeL2) n := by
  rw [probeColumn_eq_delay hn]
  change (CCM.nativeIntegerCoefficient n:ℂ) • CCM.nativeCompletionL2Delay (Real.log n)
    (probeCompletedSource:ProbeL2)=_
  rw [probeCompleted_as_approx]
  rfl

theorem probeApproxTarget_error (g : ProbeL2) (epsilon : ℝ) (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon) :
    ‖(probeTarget:ProbeL2)-probeApproxTarget g‖≤probeTargetKernelMass*epsilon := by
  rw [probeTarget_as_approx,probeApproxTarget,probeApproxTarget,← map_sub]
  exact (kernelL2Value_norm_le probeC probeC_integrable _).trans
    (mul_le_mul_of_nonneg_left herr probeTargetKernelMass_nonneg)

theorem probeApproxCompleted_error (g : ProbeL2) (epsilon : ℝ) (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon) :
    ‖(probeCompletedSource:ProbeL2)-probeApproxCompleted g‖≤probeOutputKernelMass*epsilon := by
  rw [probeCompleted_as_approx,probeApproxCompleted,probeApproxCompleted,← map_sub]
  exact (kernelL2Value_norm_le CCM.nativePositiveCompletion CCM.nativePositiveCompletion_integrable _).trans
    (mul_le_mul_of_nonneg_left herr probeOutputKernelMass_nonneg)

theorem probeApproxColumn_error (g : ProbeL2) (epsilon : ℝ) (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon)
    (n : ℕ) (hn : n≠0) :
    ‖(probeColumn n:ProbeL2)-probeApproxColumn g n‖≤probeOutputKernelMass*epsilon/Real.sqrt n := by
  rw [probeColumn_as_approx hn]
  unfold probeApproxColumn
  rw [← smul_sub,← map_sub,norm_smul,CCM.nativeCompletionL2Delay_norm,
    Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by unfold CCM.nativeIntegerCoefficient; positivity)]
  have h := mul_le_mul_of_nonneg_left (probeApproxCompleted_error g epsilon herr)
    (by unfold CCM.nativeIntegerCoefficient; positivity : 0≤CCM.nativeIntegerCoefficient n)
  rw [probeCompleted_as_approx] at h
  simpa only [CCM.nativeIntegerCoefficient,one_div,div_eq_mul_inv,mul_comm,one_mul] using h

theorem probeApproxFiniteOutput_error {N : ℕ} (g : ProbeL2) (epsilon : ℝ)
    (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon) (x : Fin N→ℂ) :
    ‖(probeFiniteOutput x:ProbeL2)-probeApproxFiniteOutput g x‖≤
      probeOutputKernelMass*epsilon*probeCoefficientMass x := by
  have heq : (probeFiniteOutput x:ProbeL2)=∑ i : Fin N,x i • (probeColumn (i.val+1):ProbeL2) := by
    simp only [probeFiniteOutput,Submodule.coe_sum,Submodule.coe_smul_of_tower]
  rw [heq,probeApproxFiniteOutput,← Finset.sum_sub_distrib]
  calc
    _≤∑ i : Fin N,‖x i • (probeColumn (i.val+1):ProbeL2)-x i • probeApproxColumn g (i.val+1)‖ := norm_sum_le _ _
    _≤∑ i : Fin N,‖x i‖*(probeOutputKernelMass*epsilon/Real.sqrt (i.val+1)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← smul_sub,norm_smul]
      have hi := probeApproxColumn_error g epsilon herr (i.val+1) (Nat.succ_ne_zero i.val)
      exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add,Nat.cast_one] using hi) (norm_nonneg _)
    _=_ := by
      rw [probeCoefficientMass,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring

theorem probeApproxResidual_error {N : ℕ} (g : ProbeL2) (epsilon : ℝ)
    (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon) (x : Fin N→ℂ) :
    ‖(probeResidual x:ProbeL2)-probeApproxResidual g x‖≤
      epsilon*(probeTargetKernelMass+probeOutputKernelMass*probeCoefficientMass x) := by
  have heq : (probeResidual x:ProbeL2)-probeApproxResidual g x=
      ((probeTarget:ProbeL2)-probeApproxTarget g)-((probeFiniteOutput x:ProbeL2)-probeApproxFiniteOutput g x) := by
    change ((probeTarget:ProbeL2)-(probeFiniteOutput x:ProbeL2))-
      (probeApproxTarget g-probeApproxFiniteOutput g x)=_
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add (probeApproxTarget_error g epsilon herr)
    (probeApproxFiniteOutput_error g epsilon herr x)).trans_eq (by ring))

theorem probeInnerDifference_bound (u v uhat vhat : ProbeL2) :
    ‖inner ℂ u v-inner ℂ uhat vhat‖≤‖u-uhat‖*‖v‖+‖uhat‖*‖v-vhat‖ := by
  have he : inner ℂ u v-inner ℂ uhat vhat=inner ℂ (u-uhat) v+inner ℂ uhat (v-vhat) := by
    rw [inner_sub_left,inner_sub_right]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))

theorem probeNormSquaredDifference_bound (u v : ProbeL2) :
    |‖u‖^2-‖v‖^2|≤(‖u‖+‖v‖)*‖u-v‖ := by
  calc
    _=|(‖u‖+‖v‖)*(‖u‖-‖v‖)| := by congr 1; ring
    _=(‖u‖+‖v‖)*|‖u‖-‖v‖| := by rw [abs_mul,abs_of_nonneg (by positivity)]
    _≤_ := mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le u v) (by positivity)

theorem probeEuclidean_norm_le_sum {N : ℕ} (x : ProbeCoefficientSpace N) :
    ‖x‖≤∑ i : Fin N,‖x i‖ := by
  have he : x=∑ i : Fin N,(PiLp.single 2 i (x i):ProbeCoefficientSpace N) := by
    ext j
    simp
  calc
    _=‖∑ i : Fin N,(PiLp.single 2 i (x i):ProbeCoefficientSpace N)‖ := congrArg norm he
    _≤∑ i : Fin N,‖(PiLp.single 2 i (x i):ProbeCoefficientSpace N)‖ := norm_sum_le _ _
    _=_ := by simp only [PiLp.norm_single]

theorem probeEuclidean_matrix_norm_le_entries {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖probeCertificateMatrix A‖≤∑ i : Fin N,∑ j : Fin N,‖A i j‖ := by
  apply (probeCertificateMatrix A).opNorm_le_bound (by positivity)
  intro x
  have ha : probeCertificateMatrix A x=probeCoefficientVector (A *ᵥ WithLp.ofLp x) := rfl
  rw [ha]
  calc
    _≤∑ i : Fin N,‖(A*ᵥWithLp.ofLp x) i‖ := probeEuclidean_norm_le_sum _
    _≤∑ i : Fin N,∑ j : Fin N,‖A i j‖*‖x j‖ := by
      apply Finset.sum_le_sum
      intro i _
      change ‖∑ j : Fin N,A i j*x j‖≤_
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _≤∑ i : Fin N,∑ j : Fin N,‖A i j‖*‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (norm_nonneg _)
    _=(∑ i : Fin N,∑ j : Fin N,‖A i j‖)*‖x‖ := by simp only [Finset.sum_mul]

#print axioms Zeta23.OPICARound2.probeApproxResidual_error
#print axioms Zeta23.OPICARound2.probeEuclidean_matrix_norm_le_entries

end Zeta23.OPICARound2
namespace Zeta23.OPICARound2
open Matrix

def probeApproxQ0 (g : ProbeL2) : ℝ := ‖probeApproxTarget g‖^2
def probeApproxTargetColumn (g : ProbeL2) (N : ℕ) (i : Fin N) : ℂ :=
  inner ℂ (probeApproxColumn g (i.val+1)) (probeApproxTarget g)
def probeApproxGram (g : ProbeL2) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => inner ℂ (probeApproxColumn g (i.val+1)) (probeApproxColumn g (j.val+1))

def probeSourceQBudget (g : ProbeL2) (epsilon : ℝ) : ℝ :=
  (‖probeTarget‖+‖probeApproxTarget g‖)*probeTargetKernelMass*epsilon
def probeSourceBBudget (g : ProbeL2) (epsilon : ℝ) (N : ℕ) : ℝ :=
  ∑ i : Fin N,((probeOutputKernelMass*epsilon/Real.sqrt (i.val+1))*‖probeTarget‖+
    ‖probeApproxColumn g (i.val+1)‖*(probeTargetKernelMass*epsilon))
def probeSourceGramBudget (g : ProbeL2) (epsilon : ℝ) (N : ℕ) : ℝ :=
  ∑ i : Fin N,∑ j : Fin N,((probeOutputKernelMass*epsilon/Real.sqrt (i.val+1))*‖probeColumn (j.val+1)‖+
    ‖probeApproxColumn g (i.val+1)‖*(probeOutputKernelMass*epsilon/Real.sqrt (j.val+1)))

theorem probeSourceQBudget_valid (g : ProbeL2) (epsilon : ℝ)
    (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon) :
    |probeQ0-probeApproxQ0 g|≤probeSourceQBudget g epsilon := by
  have h := probeNormSquaredDifference_bound (probeTarget:ProbeL2) (probeApproxTarget g)
  have he := mul_le_mul_of_nonneg_left (probeApproxTarget_error g epsilon herr)
    (by positivity : 0≤‖(probeTarget:ProbeL2)‖+‖probeApproxTarget g‖)
  change |‖(probeTarget:ProbeL2)‖^2-‖probeApproxTarget g‖^2|≤_
  exact h.trans (he.trans_eq (by change _= (‖(probeTarget:ProbeL2)‖+‖probeApproxTarget g‖)*probeTargetKernelMass*epsilon; ring))

theorem probeSourceBEntry_valid (g : ProbeL2) (epsilon : ℝ)
    (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon) (N : ℕ) (i : Fin N) :
    ‖probeTargetColumn N i-probeApproxTargetColumn g N i‖≤
      (probeOutputKernelMass*epsilon/Real.sqrt (i.val+1))*‖probeTarget‖+
        ‖probeApproxColumn g (i.val+1)‖*(probeTargetKernelMass*epsilon) := by
  have h := probeInnerDifference_bound (probeColumn (i.val+1):ProbeL2) (probeTarget:ProbeL2)
    (probeApproxColumn g (i.val+1)) (probeApproxTarget g)
  have hcol : ‖(probeColumn (i.val+1):ProbeL2)-probeApproxColumn g (i.val+1)‖≤
      probeOutputKernelMass*epsilon/Real.sqrt (i.val+1) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      probeApproxColumn_error g epsilon herr (i.val+1) (Nat.succ_ne_zero i.val)
  have ha := mul_le_mul_of_nonneg_right hcol
    (norm_nonneg (probeTarget:ProbeL2))
  have hb := mul_le_mul_of_nonneg_left (probeApproxTarget_error g epsilon herr)
    (norm_nonneg (probeApproxColumn g (i.val+1)))
  exact h.trans (add_le_add ha hb)

theorem probeSourceBBudget_valid (g : ProbeL2) (epsilon : ℝ)
    (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon) (N : ℕ) :
    ‖probeCoefficientVector (probeTargetColumn N)-probeCoefficientVector (probeApproxTargetColumn g N)‖≤
      probeSourceBBudget g epsilon N := by
  apply (probeEuclidean_norm_le_sum _).trans
  unfold probeSourceBBudget
  apply Finset.sum_le_sum
  intro i _
  exact probeSourceBEntry_valid g epsilon herr N i

theorem probeSourceGramEntry_valid (g : ProbeL2) (epsilon : ℝ)
    (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon) (N : ℕ) (i j : Fin N) :
    ‖probeGram N i j-probeApproxGram g N i j‖≤
      (probeOutputKernelMass*epsilon/Real.sqrt (i.val+1))*‖probeColumn (j.val+1)‖+
        ‖probeApproxColumn g (i.val+1)‖*(probeOutputKernelMass*epsilon/Real.sqrt (j.val+1)) := by
  have h := probeInnerDifference_bound (probeColumn (i.val+1):ProbeL2) (probeColumn (j.val+1):ProbeL2)
    (probeApproxColumn g (i.val+1)) (probeApproxColumn g (j.val+1))
  have hi : ‖(probeColumn (i.val+1):ProbeL2)-probeApproxColumn g (i.val+1)‖≤
      probeOutputKernelMass*epsilon/Real.sqrt (i.val+1) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      probeApproxColumn_error g epsilon herr (i.val+1) (Nat.succ_ne_zero i.val)
  have hj : ‖(probeColumn (j.val+1):ProbeL2)-probeApproxColumn g (j.val+1)‖≤
      probeOutputKernelMass*epsilon/Real.sqrt (j.val+1) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      probeApproxColumn_error g epsilon herr (j.val+1) (Nat.succ_ne_zero j.val)
  have ha := mul_le_mul_of_nonneg_right hi
    (norm_nonneg (probeColumn (j.val+1):ProbeL2))
  have hb := mul_le_mul_of_nonneg_left hj
    (norm_nonneg (probeApproxColumn g (i.val+1)))
  change ‖inner ℂ (probeColumn (i.val+1):ProbeL2) (probeColumn (j.val+1):ProbeL2)-
    inner ℂ (probeApproxColumn g (i.val+1)) (probeApproxColumn g (j.val+1))‖≤_
  exact h.trans (add_le_add ha hb)

theorem probeCertificateMatrix_sub {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) :
    probeCertificateMatrix A-probeCertificateMatrix B=probeCertificateMatrix (A-B) := by
  ext x i
  change (∑ j : Fin N,A i j*x j)-(∑ j : Fin N,B i j*x j)=∑ j : Fin N,(A i j-B i j)*x j
  simp only [sub_mul,Finset.sum_sub_distrib]

theorem probeSourceGramBudget_valid (g : ProbeL2) (epsilon : ℝ)
    (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon) (N : ℕ) :
    ‖probeCertificateMatrix (probeGram N)-probeCertificateMatrix (probeApproxGram g N)‖≤
      probeSourceGramBudget g epsilon N := by
  rw [probeCertificateMatrix_sub]
  apply (probeEuclidean_matrix_norm_le_entries _).trans
  unfold probeSourceGramBudget
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact probeSourceGramEntry_valid g epsilon herr N i j

theorem probeSource_absolute_certificate_budgets (g : ProbeL2) (epsilon : ℝ)
    (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon) (N : ℕ) :
    |probeQ0-probeApproxQ0 g|≤probeSourceQBudget g epsilon ∧
    ‖probeCoefficientVector (probeTargetColumn N)-probeCoefficientVector (probeApproxTargetColumn g N)‖≤
      probeSourceBBudget g epsilon N ∧
    ‖probeCertificateMatrix (probeGram N)-probeCertificateMatrix (probeApproxGram g N)‖≤
      probeSourceGramBudget g epsilon N :=
  ⟨probeSourceQBudget_valid g epsilon herr,probeSourceBBudget_valid g epsilon herr N,
    probeSourceGramBudget_valid g epsilon herr N⟩

#print axioms Zeta23.OPICARound2.probeSource_absolute_certificate_budgets

end Zeta23.OPICARound2
namespace Zeta23.OPICARound2
open SourceTailMoments

def probeCanonicalJL2 : ProbeL2 := probeCanonicalJ_memLp.toLp probeCanonicalJ
def probePrefixJL2 (M : ℕ) (hM : 12≤M) : ProbeL2 := (probePrefixJ_memLp M hM).toLp (probePrefixJ M)
def probePrefixCorrectedJL2 (M : ℕ) (hM : 12≤M) : ProbeL2 :=
  (probePrefixCorrectedJ_memLp M hM).toLp (probePrefixCorrectedJ M)
def probePrefixSourceL2 (M : ℕ) (hM : 12≤M) : ProbeL2 :=
  CCM.nativeCompletionL2Delay probeSigma (probePrefixJL2 M hM)
def probePrefixCorrectedSourceL2 (M : ℕ) (hM : 12≤M) : ProbeL2 :=
  CCM.nativeCompletionL2Delay probeSigma (probePrefixCorrectedJL2 M hM)

theorem probeSource_canonical_delay : (probeSource:ProbeL2)=
    CCM.nativeCompletionL2Delay probeSigma probeCanonicalJL2 := by
  apply Lp.ext
  have hshift := (measurePreserving_sub_right volume probeSigma).quasiMeasurePreserving.ae_eq
    (show probeCanonicalJL2=ᵐ[volume] probeCanonicalJ from probeCanonicalJ_memLp.coeFn_toLp)
  filter_upwards [probeSource_coeFn,CCM.nativeCompletionL2Delay_coeFn probeSigma probeCanonicalJL2,hshift]
    with t hs hd hc
  dsimp only [Function.comp_def] at hc
  rw [hs,hd,hc]
  exact (probeCanonicalJ_actual_source (t-probeSigma)).symm

theorem probeFunctionDifference_toLp (f g : ℝ→ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    hf.toLp f-hg.toLp g=(hf.sub hg).toLp (f-g) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),hf.coeFn_toLp,hg.coeFn_toLp,
    (hf.sub hg).coeFn_toLp] with t hsub hft hgt hdiff
  rw [hsub]
  change (hf.toLp f) t-(hg.toLp g) t=((hf.sub hg).toLp (f-g)) t
  rw [hft,hgt,hdiff]
  rfl

def probePrefixFirstError (M : ℕ) (hM : 12≤M) : ℝ := tailRadius probeSigma M*
  ‖(probePrefixJ_derivative_memLp M 1 hM (by norm_num)).toLp (iteratedDeriv 1 (probePrefixJ M))‖
def probePrefixSecondError (M : ℕ) (hM : 12≤M) : ℝ := (tailVariance probeSigma M/2)*
  ‖(probePrefixJ_derivative_memLp M 2 hM (by norm_num)).toLp (iteratedDeriv 2 (probePrefixJ M))‖
def probePrefixFourthError (M : ℕ) (hM : 12≤M) : ℝ := (tailVariance probeSigma M^2/8)*
  ‖(probePrefixJ_derivative_memLp M 4 hM (by norm_num)).toLp (iteratedDeriv 4 (probePrefixJ M))‖

theorem probePrefixSourceL2_first_error (M : ℕ) (hM : 12≤M) :
    ‖(probeSource:ProbeL2)-probePrefixSourceL2 M hM‖≤probePrefixFirstError M hM := by
  rw [probeSource_canonical_delay,probePrefixSourceL2,← map_sub,CCM.nativeCompletionL2Delay_norm]
  change ‖probeCanonicalJ_memLp.toLp probeCanonicalJ-(probePrefixJ_memLp M hM).toLp (probePrefixJ M)‖≤_
  rw [probeFunctionDifference_toLp]
  exact probePrefixSourceError_first_bound M hM

theorem probePrefixSourceL2_second_error (M : ℕ) (hM : 12≤M) :
    ‖(probeSource:ProbeL2)-probePrefixSourceL2 M hM‖≤probePrefixSecondError M hM := by
  rw [probeSource_canonical_delay,probePrefixSourceL2,← map_sub,CCM.nativeCompletionL2Delay_norm]
  change ‖probeCanonicalJ_memLp.toLp probeCanonicalJ-(probePrefixJ_memLp M hM).toLp (probePrefixJ M)‖≤_
  rw [probeFunctionDifference_toLp]
  exact probePrefixSourceError_second_bound M hM

theorem probePrefixCorrectedSourceL2_fourth_error (M : ℕ) (hM : 12≤M) :
    ‖(probeSource:ProbeL2)-probePrefixCorrectedSourceL2 M hM‖≤probePrefixFourthError M hM := by
  rw [probeSource_canonical_delay,probePrefixCorrectedSourceL2,← map_sub,CCM.nativeCompletionL2Delay_norm]
  change ‖probeCanonicalJ_memLp.toLp probeCanonicalJ-
    (probePrefixCorrectedJ_memLp M hM).toLp (probePrefixCorrectedJ M)‖≤_
  rw [probeFunctionDifference_toLp]
  exact probePrefixCorrectedError_fourth_bound M hM

def ProbeSourceAbsoluteEnclosure (g : ProbeL2) (epsilon : ℝ) : Prop :=
  ‖(probeSource:ProbeL2)-g‖≤epsilon ∧
  ‖(probeTarget:ProbeL2)-probeApproxTarget g‖≤probeTargetKernelMass*epsilon ∧
  ‖(probeCompletedSource:ProbeL2)-probeApproxCompleted g‖≤probeOutputKernelMass*epsilon ∧
  ∀ N : ℕ, |probeQ0-probeApproxQ0 g|≤probeSourceQBudget g epsilon ∧
    ‖probeCoefficientVector (probeTargetColumn N)-probeCoefficientVector (probeApproxTargetColumn g N)‖≤
      probeSourceBBudget g epsilon N ∧
    ‖probeCertificateMatrix (probeGram N)-probeCertificateMatrix (probeApproxGram g N)‖≤
      probeSourceGramBudget g epsilon N

theorem probeSource_absolute_enclosure (g : ProbeL2) (epsilon : ℝ)
    (herr : ‖(probeSource:ProbeL2)-g‖≤epsilon) : ProbeSourceAbsoluteEnclosure g epsilon :=
  ⟨herr,probeApproxTarget_error g epsilon herr,probeApproxCompleted_error g epsilon herr,
    fun N => probeSource_absolute_certificate_budgets g epsilon herr N⟩

/-- All three absolute source errors concern the unchanged canonical source.
The actual first-M box law and the literal P-squared construction are exposed
alongside their target, completed-output and Euclidean Gram budgets. -/
theorem native_source_prefix_error (M : ℕ) (hM : 12≤M) :
    (sourceCoordinateLaw.map (sourceSamplePartialSum probeSigma M)=probePrefixDensityMeasure M) ∧
    ContDiff ℝ 8 (probePrefixDensity M) ∧
    (probePrefixJ M=CCM.universalSincDifferential (CCM.universalSincDifferential (probePrefixDensityComplex M))) ∧
    ProbeSourceAbsoluteEnclosure (probePrefixSourceL2 M hM) (probePrefixFirstError M hM) ∧
    ProbeSourceAbsoluteEnclosure (probePrefixSourceL2 M hM) (probePrefixSecondError M hM) ∧
    ProbeSourceAbsoluteEnclosure (probePrefixCorrectedSourceL2 M hM) (probePrefixFourthError M hM) :=
  ⟨probePrefixDensity_actual_law M (by omega),probePrefixDensity_contDiff M hM,rfl,
    probeSource_absolute_enclosure _ _ (probePrefixSourceL2_first_error M hM),
    probeSource_absolute_enclosure _ _ (probePrefixSourceL2_second_error M hM),
    probeSource_absolute_enclosure _ _ (probePrefixCorrectedSourceL2_fourth_error M hM)⟩

#print axioms Zeta23.OPICARound2.probeSource_canonical_delay
#print axioms Zeta23.OPICARound2.native_source_prefix_error

end Zeta23.OPICARound2

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped Topology

namespace Zeta23.OPICARound2

def probeTargetTailProfile (S : ℝ) : ℝ→ℂ := (Ici S).indicator probeV

theorem probeTargetTailProfile_memLp (S : ℝ) : MemLp (probeTargetTailProfile S) 2 volume :=
  probeV_memLp.indicator measurableSet_Ici

def probeTargetTailL2 (S : ℝ) : ProbeL2 :=
  (probeTargetTailProfile_memLp S).toLp (probeTargetTailProfile S)

theorem probeV_tail_norm_sq (t : ℝ) (ht : 2*probeSigma≤t) :
    ‖probeV t‖^2=4*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*t) := by
  rw [probeV_tail ht,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_exp]
  norm_num [Complex.mul_re]
  have he : Real.exp (-((3/2:ℝ)*t))^2=Real.exp (-(3*t)) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [mul_pow,mul_pow,he]
  ring

theorem probeTargetTail_energy (S : ℝ) (hS : 2*probeSigma≤S) :
    (∫ t : ℝ in Ici S,‖probeV t‖^2)=(4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S) := by
  rw [integral_Ici_eq_integral_Ioi]
  have he : (fun t : ℝ => ‖probeV t‖^2)=ᵐ[volume.restrict (Ioi S)]
      fun t => 4*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact probeV_tail_norm_sq t (hS.trans (le_of_lt ht))
  rw [integral_congr_ae he,integral_const_mul,integral_exp_mul_Ioi (by norm_num : (-3:ℝ)<0) S]
  ring

theorem probeTargetTailL2_norm_sq (S : ℝ) (hS : 2*probeSigma≤S) :
    ‖probeTargetTailL2 S‖^2=(4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S) := by
  rw [OPICAFollowup.L2_norm_sq_eq_integral]
  have he : (fun t : ℝ => ‖probeTargetTailL2 S t‖^2)=ᵐ[volume]
      (Ici S).indicator (fun t : ℝ => ‖probeV t‖^2) := by
    filter_upwards [(probeTargetTailProfile_memLp S).coeFn_toLp] with t ht
    change ‖((probeTargetTailProfile_memLp S).toLp (probeTargetTailProfile S)) t‖^2=_
    rw [ht]
    by_cases hmem : t∈Ici S <;> simp [probeTargetTailProfile,hmem]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ici]
  exact probeTargetTail_energy S hS

theorem probeTargetTailL2_norm (S : ℝ) (hS : 2*probeSigma≤S) :
    ‖probeTargetTailL2 S‖=(2/Real.sqrt 3)*‖JPlus (-3/2:ℂ)‖*Real.exp (-3*S/2) := by
  have he : Real.exp (-3*S/2)^2=Real.exp (-3*S) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hsq : ((2/Real.sqrt 3)*‖JPlus (-3/2:ℂ)‖*Real.exp (-3*S/2))^2=
      (4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S) := by
    rw [mul_pow,mul_pow,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),he]
    ring
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  exact (probeTargetTailL2_norm_sq S hS).trans hsq.symm

#print axioms Zeta23.OPICARound2.probeTargetTailL2_norm
#print axioms Zeta23.OPICARound2.probeTargetTailL2_norm_sq

end Zeta23.OPICARound2


namespace Zeta23.OPICARound2
open Filter

def probeFiniteInputPhysical {N : ℕ} (x : Fin N → ℂ) (t : ℝ) : ℂ :=
  ∑ i : Fin N, x i*((CCM.nativeIntegerCoefficient (i.val+1):ℂ)*(jPlus (t-Real.log (i.val+1:ℕ)):ℂ))

theorem probeFiniteInputPhysical_coeFn {N : ℕ} (x : Fin N → ℂ) :
    (probeFiniteInput x:ProbeL2) =ᵐ[volume] probeFiniteInputPhysical x := by
  have he : (probeFiniteInput x:ProbeL2) = ∑ i : Fin N, x i • (probeInput (i.val+1):ProbeL2) := by
    simp [probeFiniteInput]
  have hterm (i : Fin N) : x i • (probeInput (i.val+1):ProbeL2) =ᵐ[volume]
      fun t : ℝ => x i*((CCM.nativeIntegerCoefficient (i.val+1):ℂ)*(jPlus (t-Real.log (i.val+1:ℕ)):ℂ)) := by
    filter_upwards [Lp.coeFn_smul (x i) (probeInput (i.val+1):ProbeL2),
      probeInput_coeFn (Nat.succ_ne_zero i.val)] with t hsm hi
    rw [hsm,Pi.smul_apply,hi,smul_eq_mul]
  rw [he]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin N => x i • (probeInput (i.val+1):ProbeL2)),
    ae_all_iff.mpr hterm] with t hsum hterms
  rw [hsum]
  exact Finset.sum_congr rfl (fun i hi => hterms i)

theorem probeFiniteInputPhysical_zero_of_neg {N : ℕ} (x : Fin N → ℂ) {t : ℝ} (ht : t<0) :
    probeFiniteInputPhysical x t = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hlog := Real.log_nonneg (show (1:ℝ) ≤ (i.val+1:ℕ) by exact_mod_cast Nat.succ_pos i.val)
  rw [jPlus_zero_of_neg (by linarith : t-Real.log (i.val+1:ℕ)<0)]
  simp

theorem probeFiniteInputPhysical_zero_after {N : ℕ} (x : Fin N → ℂ) {t : ℝ}
    (ht : Real.log (N:ℝ)+2*probeSigma<t) : probeFiniteInputPhysical x t=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hnp : (0:ℝ) < (i.val+1:ℕ) := by exact_mod_cast Nat.succ_pos i.val
  have hnN : (i.val+1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show i.val+1≤N by omega)
  have hlog := Real.log_le_log hnp (show ((i.val+1:ℕ):ℝ)≤N by simpa using hnN)
  have hz : jPlus (t-Real.log (i.val+1:ℕ))=0 :=
    jPlus_zero_outside (fun h => by linarith [h.2])
  have hzR : jPlus (t-Real.log ((i.val:ℝ)+1))=0 := by simpa only [Nat.cast_add,Nat.cast_one] using hz
  simp [hzR]

theorem probeFiniteInputPhysical_support {N : ℕ} (x : Fin N → ℂ) :
    Function.support (probeFiniteInputPhysical x) ⊆ Icc 0 (Real.log (N:ℝ)+2*probeSigma) := by
  intro t ht
  constructor
  · by_contra hh
    exact ht (probeFiniteInputPhysical_zero_of_neg x (lt_of_not_ge hh))
  · by_contra hh
    exact ht (probeFiniteInputPhysical_zero_after x (lt_of_not_ge hh))

theorem probeFloorKernelCutoff_measurable (T : ℝ) : Measurable (probeFloorKernelCutoff T) :=
  CCM.nativePositiveCompletion_measurable.indicator measurableSet_Iic

theorem probeFloorKernelCutoff_memLp (T : ℝ) :
    MemLp (fun t : ℝ => (probeFloorKernelCutoff T t:ℂ)) 2 volume := by
  have ha : MemLp (fun t : ℝ => (CCM.nativePositiveCompletion t:ℂ)) 2 volume := by
    simpa [CCM.nativeDampedCompletionKernel] using
      (CCM.nativeDampedCompletionKernel_complex_memLp_two (epsilon := 0) (by norm_num))
  convert! ha.indicator (s := Iic T) measurableSet_Iic using 1
  funext t
  by_cases ht : t≤T <;> simp [probeFloorKernelCutoff,ht]

theorem probeFloorKernelCutoff_zero_of_neg (T : ℝ) {t : ℝ} (ht : t<0) :
    probeFloorKernelCutoff T t=0 := by
  by_cases htT : t≤T
  · simp [probeFloorKernelCutoff,htT,CCM.nativePositiveCompletion_eq_zero_of_neg ht]
  · simp [probeFloorKernelCutoff,htT]

def probeLagOperator (T : ℝ) : CausalProbeL2 →L[ℂ] CausalProbeL2 :=
  causalKernelOperator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T)
    (fun t ht => probeFloorKernelCutoff_zero_of_neg T ht)

def probeFiniteLagOutputPhysical {N : ℕ} (T : ℝ) (x : Fin N → ℂ) (t : ℝ) : ℂ :=
  ∫ s : ℝ, (probeFloorKernelCutoff T s:ℂ)*probeFiniteInputPhysical x (t-s)

theorem probeFiniteLagOutputPhysical_coeFn {N : ℕ} (T : ℝ) (x : Fin N → ℂ) :
    (probeLagOperator T (probeFiniteInput x):ProbeL2) =ᵐ[volume] probeFiniteLagOutputPhysical T x :=
  kernelL2Operator_coeFn_of_representative (probeFloorKernelCutoff T)
    (probeFloorKernelCutoff_integrable T) (probeFloorKernelCutoff_measurable T)
      (probeFloorKernelCutoff_memLp T) (probeFiniteInput x:ProbeL2) (probeFiniteInputPhysical x)
        (probeFiniteInputPhysical_coeFn x)

theorem probeFiniteLagOutputPhysical_zero_after {N : ℕ} (T : ℝ) (x : Fin N → ℂ) {t : ℝ}
    (ht : T+Real.log (N:ℝ)+2*probeSigma<t) : probeFiniteLagOutputPhysical T x t=0 := by
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro s
  change (probeFloorKernelCutoff T s:ℂ)*probeFiniteInputPhysical x (t-s)=0
  by_cases hs : s≤T
  · rw [probeFiniteInputPhysical_zero_after x (show Real.log (N:ℝ)+2*probeSigma<t-s by linarith),mul_zero]
  · simp [probeFloorKernelCutoff,hs]

theorem probeFiniteLagOutputPhysical_zero_of_neg {N : ℕ} (T : ℝ) (x : Fin N → ℂ) {t : ℝ}
    (ht : t<0) : probeFiniteLagOutputPhysical T x t=0 := by
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro s
  change (probeFloorKernelCutoff T s:ℂ)*probeFiniteInputPhysical x (t-s)=0
  by_cases hs : s<0
  · rw [probeFloorKernelCutoff_zero_of_neg T hs]
    simp
  · rw [probeFiniteInputPhysical_zero_of_neg x (show t-s<0 by linarith),mul_zero]

theorem probeFiniteLagOutputPhysical_support {N : ℕ} (T : ℝ) (x : Fin N → ℂ) :
    Function.support (probeFiniteLagOutputPhysical T x) ⊆ Icc 0 (T+Real.log (N:ℝ)+2*probeSigma) := by
  intro t ht
  constructor
  · by_contra hh
    exact ht (probeFiniteLagOutputPhysical_zero_of_neg T x (lt_of_not_ge hh))
  · by_contra hh
    exact ht (probeFiniteLagOutputPhysical_zero_after T x (lt_of_not_ge hh))

theorem probeLagOutput_ae_zero_after {N : ℕ} (T : ℝ) (x : Fin N → ℂ) :
    ∀ᵐ t : ℝ, T+Real.log (N:ℝ)+2*probeSigma<t → (probeLagOperator T (probeFiniteInput x):ProbeL2) t=0 := by
  filter_upwards [probeFiniteLagOutputPhysical_coeFn T x] with t he ht
  rw [he]
  exact probeFiniteLagOutputPhysical_zero_after T x ht




theorem probeOutputKernelMass_pos : 0<probeOutputKernelMass := by
  unfold probeOutputKernelMass
  rw [integral_pos_iff_support_of_nonneg (fun t => norm_nonneg _)
    CCM.nativePositiveCompletion_integrable.norm]
  have hsub : Ioo (0:ℝ) 1 ⊆ Function.support (fun t => ‖CCM.nativePositiveCompletion t‖) := by
    intro t ht
    exact norm_ne_zero_iff.mpr (ne_of_gt (CCM.nativePositiveCompletion_pos_of_nonneg ht.1.le))
  exact lt_of_lt_of_le (by simp : (0:ENNReal)<volume (Ioo (0:ℝ) 1)) (measure_mono hsub)

/-- A lower bound for this chosen sufficient lag majorant, with its constant explicit. -/
theorem probeSufficientLagBudget_visible_log (m c eta theta T A : ℝ)
    (hc : 0<c) (heta : 0<eta) (htheta : 0<theta)
    (hcost : (c/eta)^(2*m-1)≤A)
    (budget : 2*Real.exp (-T/2)*A≤theta*eta) :
    4*m*Real.log (1/eta)+2*(Real.log (2/theta)+(2*m-1)*Real.log c)≤T := by
  have hp : 0<(c/eta)^(2*m-1) := Real.rpow_pos_of_pos (div_pos hc heta) _
  have hA : 0<A := hp.trans_le hcost
  have hb := probeSufficientLagBudget_log T A theta eta hA htheta heta budget
  have hdiv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost (by norm_num : (0:ℝ)≤2))
    (mul_nonneg htheta.le heta.le)
  have hl := Real.log_le_log (by positivity : 0<2*(c/eta)^(2*m-1)/(theta*eta)) hdiv
  have hid : 2*Real.log (2*(c/eta)^(2*m-1)/(theta*eta))=
      4*m*Real.log (1/eta)+2*(Real.log (2/theta)+(2*m-1)*Real.log c) := by
    rw [Real.log_div (by positivity) (mul_ne_zero htheta.ne' heta.ne'),
      Real.log_mul (by norm_num) (ne_of_gt hp),
      Real.log_rpow (div_pos hc heta),Real.log_div hc.ne' heta.ne',
      Real.log_mul htheta.ne' heta.ne',Real.log_div one_ne_zero heta.ne',
      Real.log_div (by norm_num) htheta.ne',Real.log_one]
    ring
  linarith

/-- The source precision forced by the same sufficient error quota. -/
theorem probeSufficientSourceBudget_visible (m c eta theta J C a A epsilon : ℝ)
    (hc : 0<c) (heta : 0<eta) (hJ : 0<J) (ha : 0<a)
    (hC : 0≤C) (hepsilon : 0≤epsilon)
    (hcost : (c/eta)^(2*m-1)≤J*A)
    (budget : epsilon*(C+a*A)≤theta*eta) :
    epsilon≤(theta*J/(a*c^(2*m-1)))*eta^(2*m) := by
  have hfirst : epsilon*a*(c/eta)^(2*m-1)≤J*(theta*eta) := by
    calc
      _≤epsilon*a*(J*A) := mul_le_mul_of_nonneg_left hcost (mul_nonneg hepsilon ha.le)
      _≤J*(epsilon*(C+a*A)) := by nlinarith [mul_nonneg hJ.le (mul_nonneg hepsilon hC)]
      _≤_ := mul_le_mul_of_nonneg_left budget hJ.le
  have hcp : 0<c^(2*m-1) := Real.rpow_pos_of_pos hc _
  have hep : 0<eta^(2*m-1) := Real.rpow_pos_of_pos heta _
  rw [Real.div_rpow hc.le heta.le] at hfirst
  have hscaled : epsilon*a*c^(2*m-1)≤J*(theta*eta)*eta^(2*m-1) := by
    apply (div_le_iff₀ hep).mp
    simpa only [mul_div_assoc] using hfirst
  have hexp : eta^(2*m)=eta^(2*m-1)*eta := by
    convert Real.rpow_add heta (2*m-1) 1 using 1 <;> simp <;> ring
  rw [hexp]
  have heq : (theta*J/(a*c^(2*m-1)))*(eta^(2*m-1)*eta)=
      (J*(theta*eta)*eta^(2*m-1))/(a*c^(2*m-1)) := by ring
  rw [heq]
  exact (le_div_iff₀ (mul_pos ha hcp)).mpr (by simpa only [mul_assoc] using hscaled)

theorem probeVisibleZero_adaptive_costs (rho : zetaZeroConfig.carrier)
    (hcritical : (rho:ℂ).re=1/2) (hvisible : JPlus ((rho:ℂ)-1/2)≠0)
    (theta : ℝ) (htheta : 0<theta) :
    ∃ cstar eta0 Clag Csource : ℝ,0<cstar ∧ 0<eta0 ∧ 0<Csource ∧
      ∀ eta : ℝ,0<eta → eta≤eta0 → ∀ (N : ℕ) (x : Fin N→ℂ),
        ‖probeResidual x‖≤eta →
        (∀ Tlag : ℝ,2*Real.exp (-Tlag/2)*‖probeSource‖*probeCoefficientMass x≤theta*eta →
          4*(zeroMult (rho:ℂ):ℝ)*Real.log (1/eta)+Clag≤Tlag) ∧
        (∀ epsilon : ℝ,0≤epsilon →
          epsilon*(probeTargetKernelMass+probeOutputKernelMass*probeCoefficientMass x)≤theta*eta →
          epsilon≤Csource*eta^(2*(zeroMult (rho:ℂ):ℝ))) := by
  obtain ⟨c,eta0,hc,he,hcost⟩ := probeVisibleZero_coefficient_mass rho hcritical hvisible
  refine ⟨c,eta0,2*(Real.log (2/theta)+(2*(zeroMult (rho:ℂ):ℝ)-1)*Real.log c),
    theta*‖probeSource‖/(probeOutputKernelMass*c^(2*(zeroMult (rho:ℂ):ℝ)-1)),hc,he,?_,?_⟩
  · exact div_pos (mul_pos htheta probeJ2_pos)
      (mul_pos probeOutputKernelMass_pos (Real.rpow_pos_of_pos hc _))
  intro eta heta heta0 N x herr
  have h := hcost eta heta heta0 N x herr
  constructor
  · intro T hT
    apply probeSufficientLagBudget_visible_log (zeroMult (rho:ℂ):ℝ) c eta theta T
      (‖probeSource‖*probeCoefficientMass x) hc heta htheta h
    simpa only [mul_assoc] using hT
  · intro epsilon hepsilon hquota
    exact probeSufficientSourceBudget_visible _ _ _ _ _ _ _ _ _ hc heta probeJ2_pos
      probeOutputKernelMass_pos probeTargetKernelMass_nonneg hepsilon h hquota

#print axioms probeSufficientLagBudget_visible_log
#print axioms probeSufficientSourceBudget_visible
#print axioms probeOutputKernelMass_pos
#print axioms probeVisibleZero_adaptive_costs



def probeCoveredEnergy (F : CausalProbeL2) (S : ℝ) : ℝ :=
  ∫ t : ℝ in Icc 0 S,‖probeV t-(F:ProbeL2) t‖^2

theorem probeCoveredEnergy_nonneg (F : CausalProbeL2) (S : ℝ) :
    0≤probeCoveredEnergy F S := integral_nonneg (fun _ => sq_nonneg _)

/-- A covering horizon removes the output tail only. The exact target tail remains. -/
theorem probeCoveredResidual_energy (F : CausalProbeL2) (S : ℝ) (hS : 2*probeSigma≤S)
    (hcover : ∀ᵐ t : ℝ, S<t → (F:ProbeL2) t=0) :
    ‖probeTarget-F‖^2=probeCoveredEnergy F S+
      (4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S) := by
  let r : CausalProbeL2 := probeTarget-F
  have hsub : (r:ProbeL2)=ᵐ[volume] fun t => (probeTarget:ProbeL2) t-(F:ProbeL2) t :=
    Lp.coeFn_sub (probeTarget:ProbeL2) (F:ProbeL2)
  have hr0 : ∀ᵐ t : ℝ,t<0 → (r:ProbeL2) t=0 := r.property
  have hi : Integrable (fun t : ℝ => ‖(r:ProbeL2) t‖^2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp (r:ProbeL2)).1).mp (Lp.memLp (r:ProbeL2))
  have hleft : (∫ t : ℝ in Iic S,‖(r:ProbeL2) t‖^2)=probeCoveredEnergy F S := by
    unfold probeCoveredEnergy
    rw [← integral_indicator measurableSet_Iic,← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [hsub,probeTarget_coeFn,hr0] with t ht hv hz
    by_cases hhi : t≤S
    · by_cases hlo : 0≤t
      · simp [Set.indicator,hhi,hlo,ht,hv]
      · simp [Set.indicator,hhi,hlo,hz (lt_of_not_ge hlo)]
    · simp [Set.indicator,hhi]
  have hright : (∫ t : ℝ in Ioi S,‖(r:ProbeL2) t‖^2)=∫ t : ℝ in Ioi S,‖probeV t‖^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hsub,ae_restrict_of_ae probeTarget_coeFn,
      ae_restrict_of_ae hcover,ae_restrict_mem measurableSet_Ioi] with t ht hv hc hm
    rw [ht,hv,hc hm,sub_zero]
  have htail := probeTargetTail_energy S hS
  rw [integral_Ici_eq_integral_Ioi] at htail
  change ‖(r:ProbeL2)‖^2=_
  rw [OPICAFollowup.L2_norm_sq_eq_integral,
    ← intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn,hleft,hright,htail]

theorem probeCoveredResidual_norm (F : CausalProbeL2) (S : ℝ) (hS : 2*probeSigma≤S)
    (hcover : ∀ᵐ t : ℝ,S<t → (F:ProbeL2) t=0) :
    ‖probeTarget-F‖=Real.sqrt (probeCoveredEnergy F S+
      (4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S)) := by
  rw [← probeCoveredResidual_energy F S hS hcover,Real.sqrt_sq (norm_nonneg _)]

theorem probeCoveredResidual_absolute_bound {N : ℕ} (x : Fin N→ℂ)
    (F : CausalProbeL2) (S : ℝ) (hS : 2*probeSigma≤S)
    (hcover : ∀ᵐ t : ℝ,S<t → (F:ProbeL2) t=0) (lagError : ℝ)
    (hlag : ‖probeFiniteOutput x-F‖≤lagError) :
    ‖probeResidual x‖≤Real.sqrt (probeCoveredEnergy F S+
      (4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S))+lagError := by
  have heq : probeResidual x=(probeTarget-F)-(probeFiniteOutput x-F) := by
    unfold probeResidual
    abel
  rw [heq]
  have ht := norm_sub_le (probeTarget-F) (probeFiniteOutput x-F)
  rw [probeCoveredResidual_norm F S hS hcover] at ht
  linarith

theorem probeCoveredResidual_quadrature_bound {N : ℕ} (x : Fin N→ℂ)
    (F : CausalProbeL2) (S : ℝ) (hS : 2*probeSigma≤S)
    (hcover : ∀ᵐ t : ℝ,S<t → (F:ProbeL2) t=0) (lagError Ehat epsilonQ : ℝ)
    (hlag : ‖probeFiniteOutput x-F‖≤lagError)
    (hQ : probeCoveredEnergy F S≤Ehat+epsilonQ) :
    ‖probeResidual x‖≤Real.sqrt (Ehat+epsilonQ+
      (4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S))+lagError := by
  have hb := probeCoveredResidual_absolute_bound x F S hS hcover lagError hlag
  have hs : Real.sqrt (probeCoveredEnergy F S+
      (4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S))≤
      Real.sqrt (Ehat+epsilonQ+(4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S)) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

#print axioms probeCoveredResidual_energy
#print axioms probeCoveredResidual_absolute_bound
#print axioms probeCoveredResidual_quadrature_bound


theorem probeFiniteLagResidual_bound {N : ℕ} (x : Fin N→ℂ) (Tlag S : ℝ)
    (hcover : Tlag+Real.log (N:ℝ)+2*probeSigma≤S) (hS : 2*probeSigma≤S) :
    ‖probeResidual x‖≤Real.sqrt (probeCoveredEnergy (probeLagOperator Tlag (probeFiniteInput x)) S+
      (4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S))+
      2*Real.exp (-Tlag/2)*‖probeSource‖*probeCoefficientMass x := by
  have hz : ∀ᵐ t : ℝ,S<t → (probeLagOperator Tlag (probeFiniteInput x):ProbeL2) t=0 := by
    filter_upwards [probeLagOutput_ae_zero_after Tlag x] with t ht hs
    exact ht (lt_of_le_of_lt hcover hs)
  exact probeCoveredResidual_absolute_bound x _ S hS hz _ (probeFiniteInput_lag_error x Tlag)

def ProbeAdaptiveVisibleCosts (rho : zetaZeroConfig.carrier) (theta : ℝ) : Prop :=
  ∃ cstar eta0 Clag Csource : ℝ,0<cstar ∧ 0<eta0 ∧ 0<Csource ∧
    ∀ eta : ℝ,0<eta → eta≤eta0 → ∀ (N : ℕ) (x : Fin N→ℂ),
      ‖probeResidual x‖≤eta →
      (∀ Tlag : ℝ,2*Real.exp (-Tlag/2)*‖probeSource‖*probeCoefficientMass x≤theta*eta →
        4*(zeroMult (rho:ℂ):ℝ)*Real.log (1/eta)+Clag≤Tlag) ∧
      (∀ epsilon : ℝ,0≤epsilon →
        epsilon*(probeTargetKernelMass+probeOutputKernelMass*probeCoefficientMass x)≤theta*eta →
        epsilon≤Csource*eta^(2*(zeroMult (rho:ℂ):ℝ)))

/-- Complete source-faithful finite-trial error budgets. The two horizons remain
distinct, and the exact target tail is included before any norm comparison. -/
theorem native_probe_adaptive_error_budgets {N : ℕ} (x : Fin N→ℂ) (Tlag S : ℝ)
    (hcover : Tlag+Real.log (N:ℝ)+2*probeSigma≤S) (hS : 2*probeSigma≤S) :
    ‖probeFiniteInput x‖≤‖probeSource‖*probeCoefficientMass x ∧
    ‖probeFiniteOutput x-probeLagOperator Tlag (probeFiniteInput x)‖≤
      2*Real.exp (-Tlag/2)*‖probeSource‖*probeCoefficientMass x ∧
    (∀ᵐ t : ℝ,S<t → (probeLagOperator Tlag (probeFiniteInput x):ProbeL2) t=0) ∧
    ‖probeTargetTailL2 S‖=(2/Real.sqrt 3)*‖JPlus (-3/2:ℂ)‖*Real.exp (-3*S/2) ∧
    ‖probeResidual x‖≤Real.sqrt (probeCoveredEnergy (probeLagOperator Tlag (probeFiniteInput x)) S+
      (4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S))+
      2*Real.exp (-Tlag/2)*‖probeSource‖*probeCoefficientMass x ∧
    (∀ (g : ProbeL2) (epsilon : ℝ),‖(probeSource:ProbeL2)-g‖≤epsilon →
      ‖(probeResidual x:ProbeL2)-probeApproxResidual g x‖≤
        epsilon*(probeTargetKernelMass+probeOutputKernelMass*probeCoefficientMass x)) ∧
    (∀ (rho : zetaZeroConfig.carrier), (rho:ℂ).re=1/2 → JPlus ((rho:ℂ)-1/2)≠0 →
      ∀ theta : ℝ,0<theta → ProbeAdaptiveVisibleCosts rho theta) ∧
    (∀ (B : CausalProbeL2→L[ℂ] CausalProbeL2) (f g : CausalProbeL2) (epsilon : ℝ),
      ‖f-g‖≤epsilon → ‖B f-B g‖≤‖B‖*epsilon) ∧
    (∀ f : CausalProbeL2,Tendsto (fun n : ℕ => ‖probeShrinkingIdentity n f‖) atTop (𝓝 0)) ∧
    (∀ (n : ℕ) (f : CausalProbeL2) (Gamma : ℝ),0<Gamma →
      0<(1/2:ℝ)^n*Gamma ∧
      ‖probeShrinkingIdentity n f‖/((1/2:ℝ)^n*Gamma)=‖f‖/Gamma) ∧
    (∀ (B : CausalProbeL2→L[ℂ] CausalProbeL2) (r : CausalProbeL2) (Gamma : ℝ),
      0<Gamma → Gamma≤‖B r‖ → 1≤‖B r‖/Gamma) := by
  refine ⟨probeFiniteInput_norm_le_mass x,probeFiniteInput_lag_error x Tlag,?_,
    probeTargetTailL2_norm S hS,probeFiniteLagResidual_bound x Tlag S hcover hS,
    fun g epsilon he => probeApproxResidual_error g epsilon he x,?_,
    probeFixedFilter_error_transport,probeShrinkingIdentity_residual_tendsto,
    probeShrinkingIdentity_normalized_witness,probeVariableFilter_normalized_margin⟩
  · filter_upwards [probeLagOutput_ae_zero_after Tlag x] with t ht hs
    exact ht (lt_of_le_of_lt hcover hs)
  · intro rho hcritical hvisible theta htheta
    exact probeVisibleZero_adaptive_costs rho hcritical hvisible theta htheta

#print axioms native_probe_adaptive_error_budgets
#print axioms probeFiniteLagResidual_bound

end Zeta23.OPICARound2
