import Zeta23.OPICARound2.ProbeGram
import Zeta23.OPICARound2.TruncationControls
import Zeta23.CCM.UniversalSincSourceTail
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

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
