import Zeta23.OPICARound2.CertifiedEvaluation

noncomputable section
open Set MeasureTheory Matrix WithLp
open scoped Topology BigOperators ComplexConjugate

namespace Zeta23.OPICARound2.Validation

theorem certificate_expected_primal {N : ℕ} (x : Fin N → ℂ)
    (q : ℝ) (b : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (eq eb eg : ℝ) (hq : |‖probeTarget‖^2-q|≤eq)
    (hb : ‖(toLp 2 (probeTargetColumn N) : EuclideanSpace ℂ (Fin N))-toLp 2 b‖≤eb)
    (hg : ‖(Matrix.toEuclideanLin (probeGram N)).toContinuousLinearMap-
      (Matrix.toEuclideanLin A).toContinuousLinearMap‖≤eg) :
    ‖probeTarget-probeFiniteOutput x‖^2≤q-
      2*(inner ℂ (toLp 2 b : EuclideanSpace ℂ (Fin N)) (toLp 2 x)).re+
      (inner ℂ (toLp 2 x : EuclideanSpace ℂ (Fin N))
        ((Matrix.toEuclideanLin A).toContinuousLinearMap (toLp 2 x))).re+
      eq+2*eb*‖(toLp 2 x : EuclideanSpace ℂ (Fin N))‖+
        eg*‖(toLp 2 x : EuclideanSpace ℂ (Fin N))‖^2 :=
  probeCertificate_primal_upper x q b A eq eb eg hq hb hg

theorem certificate_actual_source_energy {N : ℕ} (x : Fin N → ℂ) :
    ‖probeTarget-probeFiniteOutput x‖^2=‖probeTarget‖^2-
      2*(inner ℂ (probeCoefficientVector (probeTargetColumn N)) (probeCoefficientVector x)).re+
      ‖probeFiniteOutput x‖^2 := by
  rw [probeCertificate_output_norm_sq]
  exact probeCertificate_energy_identity x

theorem certificate_actual_gram_quadratic {N : ℕ} (x : Fin N → ℂ) :
    (inner ℂ (toLp 2 x : EuclideanSpace ℂ (Fin N))
      (toLp 2 (probeGram N*ᵥx))).re=‖probeFiniteOutput x‖^2 :=
  (probeCertificate_output_norm_sq x).symm

theorem certificate_expected_two_sided {N : ℕ} (x : Fin N → ℂ)
    (ell : ℝ) (hell : 0<ell)
    (coercive : ∀ y : Fin N → ℂ, ell*‖(toLp 2 y : EuclideanSpace ℂ (Fin N))‖^2≤
      (inner ℂ (toLp 2 y : EuclideanSpace ℂ (Fin N)) (toLp 2 (probeGram N*ᵥy))).re) :
    ‖probeTarget-probeFiniteOutput x‖^2-
      ‖(toLp 2 (probeTargetColumn N-probeGram N*ᵥx) : EuclideanSpace ℂ (Fin N))‖^2/ell≤
        probeError N^2 ∧ probeError N^2≤‖probeTarget-probeFiniteOutput x‖^2 :=
  probeCertificate_two_sided x ell hell coercive

theorem certificate_estimated_matrix_lower_transfer {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) (ell eg : ℝ)
    (error : ‖(Matrix.toEuclideanLin (probeGram N)).toContinuousLinearMap-
      (Matrix.toEuclideanLin A).toContinuousLinearMap‖≤eg)
    (coercive : ∀ y : Fin N → ℂ, ell*‖(toLp 2 y : EuclideanSpace ℂ (Fin N))‖^2≤
      (inner ℂ (toLp 2 y : EuclideanSpace ℂ (Fin N)) (toLp 2 (A*ᵥy))).re) :
    ∀ y : Fin N → ℂ, (ell-eg)*‖(toLp 2 y : EuclideanSpace ℂ (Fin N))‖^2≤
      ‖probeFiniteOutput y‖^2 := by
  intro y
  rw [probeCertificate_output_norm_sq]
  exact probeCertificate_estimated_gram_lower A ell eg error coercive y

theorem certificate_exact_inputs_no_error {N : ℕ} (x : Fin N → ℂ) :
    ‖probeResidual x‖^2≤probeNominalEnergy probeQ0 (probeTargetColumn N) (probeGram N) x := by
  exact le_of_eq (probeCertificate_energy_identity x)

theorem certificate_negative_budget_rejected {N : ℕ} (q : ℝ) (b : Fin N → ℂ)
    (A : Matrix (Fin N) (Fin N) ℂ) (eq eb eg : ℝ)
    (negative : eq<0 ∨ eb<0 ∨ eg<0) :
    ¬ (|probeQ0-q|≤eq ∧
      ‖probeCoefficientVector (probeTargetColumn N)-probeCoefficientVector b‖≤eb ∧
      ‖probeCertificateMatrix (probeGram N)-probeCertificateMatrix A‖≤eg) := by
  rintro ⟨hq,hb,hg⟩
  obtain ⟨hq',hb',hg'⟩ := probeCertificate_budget_nonnegative q b A eq eb eg hq hb hg
  rcases negative with h|h|h <;> linarith

theorem certificate_nonpositive_ell_cannot_enter (ell : ℝ) (h : ell≤0) : ¬ 0<ell :=
  not_lt_of_ge h

theorem certificate_empty_trial_is_target :
    probeResidual (fun i : Fin 0 => Fin.elim0 i)=probeTarget := by
  simp [probeResidual,probeFiniteOutput]

theorem certificate_empty_gram_has_no_false_rank_condition :
    ∀ ell : ℝ, ProbeCertifiedGramLower 0 ell := by
  intro ell y
  have hy : y=0 := Subsingleton.elim _ _
  subst y
  have hz : probeCoefficientVector (0 : Fin 0 → ℂ)=0 := by
    ext i
    exact Fin.elim0 i
  rw [hz]
  simp

theorem certificate_expected_full_family {N : ℕ} (x : Fin N → ℂ)
    (q : ℝ) (b : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (eq eb eg : ℝ) (hq : |probeQ0-q|≤eq)
    (hb : ‖probeCoefficientVector (probeTargetColumn N)-probeCoefficientVector b‖≤eb)
    (hg : ‖probeCertificateMatrix (probeGram N)-probeCertificateMatrix A‖≤eg) :
    (0≤eq ∧ 0≤eb ∧ 0≤eg) ∧
    ‖probeResidual x‖^2≤q-
      2*(inner ℂ (probeCoefficientVector b) (probeCoefficientVector x)).re+
      (inner ℂ (probeCoefficientVector x) (probeCertificateMatrix A (probeCoefficientVector x))).re+
      eq+2*eb*‖probeCoefficientVector x‖+eg*‖probeCoefficientVector x‖^2 ∧
    (∀ ell : ℝ, 0<ell → ProbeCertifiedGramLower N ell →
      ‖probeResidual x‖^2-‖probeCertificateGradient x‖^2/ell≤probeError N^2 ∧
        probeError N^2≤‖probeResidual x‖^2) :=
  finite_residual_certificate x q b A eq eb eg hq hb hg

#print axioms Zeta23.OPICARound2.finite_residual_certificate
#print axioms Zeta23.OPICARound2.Validation.certificate_expected_primal
#print axioms Zeta23.OPICARound2.Validation.certificate_actual_source_energy
#print axioms Zeta23.OPICARound2.Validation.certificate_expected_two_sided
#print axioms Zeta23.OPICARound2.Validation.certificate_estimated_matrix_lower_transfer
#print axioms Zeta23.OPICARound2.Validation.certificate_negative_budget_rejected
#print axioms Zeta23.OPICARound2.Validation.certificate_empty_trial_is_target
#print axioms Zeta23.OPICARound2.Validation.certificate_empty_gram_has_no_false_rank_condition
#print axioms Zeta23.OPICARound2.Validation.certificate_expected_full_family

open CCM.UniversalSinc

theorem source_prefix_literal_box_law (M : ℕ) (hM : 12≤M) :
    sourceCoordinateLaw.map (sourceSamplePartialSum probeSigma M)=
      volume.withDensity (fun t => ENNReal.ofReal (probePrefixDensity M t)) :=
  probePrefixDensity_actual_law M (by omega)

theorem source_prefix_literal_product (M : ℕ) (hM : 12≤M) (tau : ℝ) :
    Zeta23.paperFT (fun t : ℝ => (probePrefixDensity M t:ℂ)) (tau:ℂ)=
      ∏ n∈Finset.range M,sinc ((width probeSigma n:ℂ)*(tau:ℂ)) :=
  probePrefixDensity_paperFT M (by omega) tau

theorem source_prefix_actual_law_split (M : ℕ) (hM : 12≤M) :
    originalSourceLaw probeSigma=probePrefixDensityMeasure M∗originalSourceTailLaw probeSigma M :=
  probePrefixDensity_actual_tail_split M (by omega)

theorem source_prefix_actual_regularity (M : ℕ) (hM : 12≤M) :
    ContDiff ℝ 8 (probePrefixDensity M) ∧
      ContDiff ℝ 4 (CCM.universalSincDifferential
        (CCM.universalSincDifferential (probePrefixDensityComplex M))) :=
  ⟨probePrefixDensity_contDiff M hM,probePrefixJ_contDiff M hM⟩

theorem source_prefix_true_tail_moments (M : ℕ) :
    (∫ u : ℝ,u ∂originalSourceTailLaw probeSigma M)=0 ∧
    (∫ u : ℝ,u^2 ∂originalSourceTailLaw probeSigma M)=
      (1/3)*∑' n : ℕ,width probeSigma (n+M)^2 ∧
    (∫ u : ℝ,u^3 ∂originalSourceTailLaw probeSigma M)=0 ∧
    (∫ u : ℝ,u^4 ∂originalSourceTailLaw probeSigma M)≤
      3*((1/3)*∑' n : ℕ,width probeSigma (n+M)^2)^2 :=
  SourceTailMoments.actual_tail_law_moments probeSigma_pos.le M

theorem source_prefix_expected_first_error (M : ℕ) (hM : 12≤M) :
    ‖(probeSource:ProbeL2)-probePrefixSourceL2 M hM‖≤
      (probeSigma/((M:ℝ)+1))*
        ‖(probePrefixJ_derivative_memLp M 1 hM (by norm_num)).toLp (iteratedDeriv 1 (probePrefixJ M))‖ :=
  probePrefixSourceL2_first_error M hM

theorem source_prefix_expected_centered_error (M : ℕ) (hM : 12≤M) :
    ‖(probeSource:ProbeL2)-probePrefixSourceL2 M hM‖≤
      (((1/3)*∑' n : ℕ,width probeSigma (n+M)^2)/2)*
        ‖(probePrefixJ_derivative_memLp M 2 hM (by norm_num)).toLp (iteratedDeriv 2 (probePrefixJ M))‖ :=
  probePrefixSourceL2_second_error M hM

theorem source_prefix_expected_corrected_error (M : ℕ) (hM : 12≤M) :
    ‖(probeSource:ProbeL2)-probePrefixCorrectedSourceL2 M hM‖≤
      (((1/3)*∑' n : ℕ,width probeSigma (n+M)^2)^2/8)*
        ‖(probePrefixJ_derivative_memLp M 4 hM (by norm_num)).toLp (iteratedDeriv 4 (probePrefixJ M))‖ :=
  probePrefixCorrectedSourceL2_fourth_error M hM

theorem source_prefix_literal_correction (M : ℕ) (hM : 12≤M) (t : ℝ) :
    probePrefixCorrectedJ M t=probePrefixJ M t+
      ((((1/3)*∑' n : ℕ,width probeSigma (n+M)^2)/2:ℝ):ℂ)*iteratedDeriv 2 (probePrefixJ M) t := rfl

theorem source_prefix_original_source_adapter (t : ℝ) :
    probeCanonicalJ t=(CCM.nativeOriginalSource t:ℂ) := probeCanonicalJ_actual_source t

theorem source_prefix_actual_target_transport (M : ℕ) (hM : 12≤M) :
    ‖(probeTarget:ProbeL2)-kernelL2Operator probeC probeC_integrable (probePrefixSourceL2 M hM)‖≤
      (∫ t : ℝ,‖probeC t‖)*probePrefixFirstError M hM :=
  probeApproxTarget_error _ _ (probePrefixSourceL2_first_error M hM)

theorem source_prefix_actual_completed_transport (M : ℕ) (hM : 12≤M) :
    ‖(probeCompletedSource:ProbeL2)-kernelL2Operator CCM.nativePositiveCompletion
      CCM.nativePositiveCompletion_integrable (probePrefixSourceL2 M hM)‖≤
        (∫ t : ℝ,‖CCM.nativePositiveCompletion t‖)*probePrefixFirstError M hM :=
  probeApproxCompleted_error _ _ (probePrefixSourceL2_first_error M hM)

theorem source_prefix_expected_gram_operator_bound (M : ℕ) (hM : 12≤M) (N : ℕ) :
    ‖probeCertificateMatrix (probeGram N)-
      probeCertificateMatrix (probeApproxGram (probePrefixSourceL2 M hM) N)‖≤
        probeSourceGramBudget (probePrefixSourceL2 M hM) (probePrefixFirstError M hM) N :=
  probeSourceGramBudget_valid _ _ (probePrefixSourceL2_first_error M hM) N

theorem source_prefix_actual_finite_certificate (M : ℕ) (hM : 12≤M) {N : ℕ} (x : Fin N→ℂ) :
    ‖probeResidual x‖^2≤
      probeNominalEnergy (probeApproxQ0 (probePrefixSourceL2 M hM))
        (probeApproxTargetColumn (probePrefixSourceL2 M hM) N)
        (probeApproxGram (probePrefixSourceL2 M hM) N) x+
      probeSourceQBudget (probePrefixSourceL2 M hM) (probePrefixFirstError M hM)+
      2*probeSourceBBudget (probePrefixSourceL2 M hM) (probePrefixFirstError M hM) N*‖probeCoefficientVector x‖+
      probeSourceGramBudget (probePrefixSourceL2 M hM) (probePrefixFirstError M hM) N*‖probeCoefficientVector x‖^2 := by
  obtain ⟨hq,hb,hg⟩ := probeSource_absolute_certificate_budgets _ _
    (probePrefixSourceL2_first_error M hM) N
  exact probeCertificate_primal_upper x _ _ _ _ _ _ hq hb hg

theorem source_prefix_nonvacuous_mass : (∫ t : ℝ,probePrefixDensity 12 t)=1 :=
  probeBoxSmoothedDensity_mass (sourcePrefixBlockLaw 12)

theorem source_prefix_nonzero_tail_variance (M : ℕ) :
    0<(1/3)*∑' n : ℕ,width probeSigma (n+M)^2 :=
  SourceTailMoments.actual_tail_variance_pos probeSigma_pos M

theorem source_prefix_insufficient_regularity_rejected : ¬ 12≤(0:ℕ) := by omega

theorem source_prefix_cannot_replace_original (M : ℕ) (hM : 12≤M) :
    originalSourceLaw probeSigma≠probePrefixDensityMeasure M := by
  intro heq
  let r : ℝ := probeSigma/((M:ℝ)+1)
  have hr : 0<r := div_pos probeSigma_pos (by positivity)
  have hpos := original_source_law_left_mass probeSigma (r/2) probeSigma_pos (by positivity)
  have hzero : probePrefixDensityMeasure M (Ioo (-probeSigma) (-probeSigma+r/2))=0 := by
    rw [← probePrefixDensity_actual_law M (by omega),
      Measure.map_apply (measurable_sourceSamplePartialSum _ _) measurableSet_Ioo]
    have hpre : (sourceSamplePartialSum probeSigma M)⁻¹' Ioo (-probeSigma) (-probeSigma+r/2)=∅ := by
      ext omega
      constructor
      · intro hin
        have hbound := (norm_sum_le (Finset.range M)
          (fun n : ℕ => width probeSigma n*unitClamp (omega n))).trans
            (Finset.sum_le_sum (fun n _ => sourceSampleAtom_norm_le_width probeSigma_pos.le omega n))
        rw [sum_width_range] at hbound
        change |sourceSamplePartialSum probeSigma M omega|≤probeSigma-r at hbound
        have hlo := (abs_le.mp hbound).1
        change sourceSamplePartialSum probeSigma M omega∈Ioo (-probeSigma) (-probeSigma+r/2) at hin
        linarith [hin.2]
      · intro hin
        exact False.elim (notMem_empty _ hin)
    rw [hpre,measure_empty]
  rw [heq,hzero] at hpos
  exact lt_irrefl _ hpos

theorem source_prefix_expected_full_family (M : ℕ) (hM : 12≤M) :
    (sourceCoordinateLaw.map (sourceSamplePartialSum probeSigma M)=probePrefixDensityMeasure M) ∧
    ContDiff ℝ 8 (probePrefixDensity M) ∧
    (probePrefixJ M=CCM.universalSincDifferential (CCM.universalSincDifferential (probePrefixDensityComplex M))) ∧
    ProbeSourceAbsoluteEnclosure (probePrefixSourceL2 M hM) (probePrefixFirstError M hM) ∧
    ProbeSourceAbsoluteEnclosure (probePrefixSourceL2 M hM) (probePrefixSecondError M hM) ∧
    ProbeSourceAbsoluteEnclosure (probePrefixCorrectedSourceL2 M hM) (probePrefixFourthError M hM) :=
  native_source_prefix_error M hM

#print axioms Zeta23.OPICARound2.native_source_prefix_error
#print axioms Zeta23.OPICARound2.Validation.source_prefix_literal_box_law
#print axioms Zeta23.OPICARound2.Validation.source_prefix_expected_first_error
#print axioms Zeta23.OPICARound2.Validation.source_prefix_expected_centered_error
#print axioms Zeta23.OPICARound2.Validation.source_prefix_expected_corrected_error
#print axioms Zeta23.OPICARound2.Validation.source_prefix_actual_finite_certificate
#print axioms Zeta23.OPICARound2.Validation.source_prefix_cannot_replace_original
#print axioms Zeta23.OPICARound2.Validation.source_prefix_expected_full_family

end Zeta23.OPICARound2.Validation

namespace Zeta23.OPICARound2.Validation
open Filter

namespace LagSupportValidation

theorem actual_input_source {N : ℕ} (x : Fin N → ℂ) :
    (probeFiniteInput x:ProbeL2) =ᵐ[volume] fun t : ℝ => ∑ i : Fin N,
      x i*((CCM.nativeIntegerCoefficient (i.val+1):ℂ)*(jPlus (t-Real.log (i.val+1:ℕ)):ℂ)) :=
  probeFiniteInputPhysical_coeFn x

theorem actual_lag_support {N : ℕ} (T : ℝ) (x : Fin N → ℂ) :
    ∀ᵐ t : ℝ, T+Real.log (N:ℝ)+2*probeSigma<t →
      (kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T)
        (probeFiniteInput x:ProbeL2)) t=0 :=
  probeLagOutput_ae_zero_after T x

theorem actual_lag_causal {N : ℕ} (T : ℝ) (x : Fin N → ℂ) :
    ∀ᵐ t : ℝ, t<0 → (probeLagOperator T (probeFiniteInput x):ProbeL2) t=0 := by
  filter_upwards [probeFiniteLagOutputPhysical_coeFn T x] with t he ht
  rw [he]
  exact probeFiniteLagOutputPhysical_zero_of_neg T x ht

theorem zero_dimension_input (x : Fin 0 → ℂ) (t : ℝ) : probeFiniteInputPhysical x t=0 := by
  simp [probeFiniteInputPhysical]

theorem negative_lag_kernel {T : ℝ} (hT : T<0) : probeFloorKernelCutoff T = 0 := by
  funext t
  by_cases ht : t≤T
  · rw [probeFloorKernelCutoff_zero_of_neg T (lt_of_le_of_lt ht hT)]
    rfl
  · simp [probeFloorKernelCutoff,ht]

end LagSupportValidation
theorem adaptive_actual_source_input {N : ℕ} (x : Fin N→ℂ) :
    ‖(∑ i : Fin N,x i • probeInput (i.val+1):CausalProbeL2)‖≤
      ‖probeSource‖*(∑ i : Fin N,‖x i‖/Real.sqrt (i.val+1)) :=
  probeFiniteInput_norm_le_mass x

theorem adaptive_expected_lag_error {N : ℕ} (x : Fin N→ℂ) (T : ℝ) :
    ‖(probeFiniteOutput x:ProbeL2)-kernelL2Operator ((Iic T).indicator CCM.nativePositiveCompletion)
      (probeFloorKernelCutoff_integrable T) (probeFiniteInput x:ProbeL2)‖≤
      2*Real.exp (-T/2)*‖probeSource‖*(∑ i : Fin N,‖x i‖/Real.sqrt (i.val+1)) :=
  probeFiniteInput_lag_error x T

theorem adaptive_expected_chosen_lag_quota (T A theta eta : ℝ)
    (hA : 0<A) (htheta : 0<theta) (heta : 0<eta)
    (hbudget : 2*Real.exp (-T/2)*A≤theta*eta) :
    2*Real.log (2*A/(theta*eta))≤T := probeSufficientLagBudget_log T A theta eta hA htheta heta hbudget

theorem adaptive_expected_visible_costs (rho : zetaZeroConfig.carrier)
    (hcritical : (rho:ℂ).re=1/2) (hvisible : JPlus ((rho:ℂ)-1/2)≠0)
    (theta : ℝ) (htheta : 0<theta) :
    ∃ cstar eta0 Clag Csource : ℝ,0<cstar ∧ 0<eta0 ∧ 0<Csource ∧
      ∀ eta : ℝ,0<eta → eta≤eta0 → ∀ (N : ℕ) (x : Fin N→ℂ),‖probeResidual x‖≤eta →
      (∀ Tlag : ℝ,2*Real.exp (-Tlag/2)*‖probeSource‖*probeCoefficientMass x≤theta*eta →
        4*(zeroMult (rho:ℂ):ℝ)*Real.log (1/eta)+Clag≤Tlag) ∧
      (∀ epsilon : ℝ,0≤epsilon →
        epsilon*(probeTargetKernelMass+probeOutputKernelMass*probeCoefficientMass x)≤theta*eta →
        epsilon≤Csource*eta^(2*(zeroMult (rho:ℂ):ℝ))) :=
  probeVisibleZero_adaptive_costs rho hcritical hvisible theta htheta

theorem adaptive_expected_source_transport {N : ℕ} (x : Fin N→ℂ) (g : ProbeL2) (epsilon : ℝ)
    (hsource : ‖(probeSource:ProbeL2)-g‖≤epsilon) :
    ‖((probeTarget:ProbeL2)-(probeFiniteOutput x:ProbeL2))-
      (probeApproxTarget g-∑ i : Fin N,x i • probeApproxColumn g (i.val+1))‖≤
      epsilon*((∫ t : ℝ,‖probeC t‖)+(∫ t : ℝ,‖CCM.nativePositiveCompletion t‖)*probeCoefficientMass x) :=
  probeApproxResidual_error g epsilon hsource x

theorem adaptive_expected_target_tail (S : ℝ) (hS : 2*probeSigma≤S) :
    ‖((probeV_memLp.indicator measurableSet_Ici).toLp ((Ici S).indicator probeV):ProbeL2)‖=
      (2/Real.sqrt 3)*‖JPlus (-3/2:ℂ)‖*Real.exp (-3*S/2) :=
  probeTargetTailL2_norm S hS

theorem adaptive_expected_whole_line {N : ℕ} (x : Fin N→ℂ) (T S : ℝ)
    (hcover : T+Real.log (N:ℝ)+2*probeSigma≤S) (hS : 2*probeSigma≤S) :
    ‖probeResidual x‖≤Real.sqrt
      ((∫ t : ℝ in Icc 0 S,‖probeV t-probeFiniteLagOutputPhysical T x t‖^2)+
        (4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S))+
        2*Real.exp (-T/2)*‖probeSource‖*probeCoefficientMass x := by
  have he : probeCoveredEnergy (probeLagOperator T (probeFiniteInput x)) S=
      ∫ t : ℝ in Icc 0 S,‖probeV t-probeFiniteLagOutputPhysical T x t‖^2 := by
    unfold probeCoveredEnergy
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (probeFiniteLagOutputPhysical_coeFn T x)] with t ht
    rw [ht]
  simpa only [he] using probeFiniteLagResidual_bound x T S hcover hS

theorem adaptive_expected_quadrature {N : ℕ} (x : Fin N→ℂ) (F : CausalProbeL2) (S : ℝ)
    (hS : 2*probeSigma≤S) (hcover : ∀ᵐ t : ℝ,S<t → (F:ProbeL2) t=0)
    (lag Ehat epsQ : ℝ) (hlag : ‖probeFiniteOutput x-F‖≤lag)
    (hQ : (∫ t : ℝ in Icc 0 S,‖probeV t-(F:ProbeL2) t‖^2)≤Ehat+epsQ) :
    ‖probeResidual x‖≤Real.sqrt (Ehat+epsQ+(4/3)*‖JPlus (-3/2:ℂ)‖^2*Real.exp (-3*S))+lag :=
  probeCoveredResidual_quadrature_bound x F S hS hcover lag Ehat epsQ hlag hQ

theorem adaptive_expected_fixed_filter (B : CausalProbeL2→L[ℂ] CausalProbeL2)
    (f g : CausalProbeL2) (epsilon : ℝ) (h : ‖f-g‖≤epsilon) :
    ‖B f-B g‖≤‖B‖*epsilon := probeFixedFilter_error_transport B f g epsilon h

theorem adaptive_expected_variable_filter (B : CausalProbeL2→L[ℂ] CausalProbeL2)
    (r : CausalProbeL2) (Gamma : ℝ) (hG : 0<Gamma) (hmargin : Gamma≤‖B r‖) :
    1≤‖B r‖/Gamma := probeVariableFilter_normalized_margin B r Gamma hG hmargin

theorem adaptive_shrinking_filter_counterexample (f : CausalProbeL2) (Gamma : ℝ) (hG : 0<Gamma) :
    Tendsto (fun n : ℕ => ‖((1/2:ℂ)^n) • f‖) atTop (𝓝 0) ∧
      (∀ n : ℕ,0<(1/2:ℝ)^n*Gamma ∧
        ‖((1/2:ℂ)^n) • f‖/((1/2:ℝ)^n*Gamma)=‖f‖/Gamma) :=
  ⟨probeShrinkingIdentity_residual_tendsto f,fun n => probeShrinkingIdentity_normalized_witness n f Gamma hG⟩

theorem adaptive_actual_source_norm_positive : 0<‖probeSource‖ := probeJ2_pos

theorem adaptive_actual_output_mass_positive : 0<(∫ t : ℝ,‖CCM.nativePositiveCompletion t‖) :=
  probeOutputKernelMass_pos

theorem adaptive_noncompact_target_control (S : ℝ) (hS : 2*probeSigma≤S) :
    0<‖probeTargetTailL2 S‖ := by
  have hJ : JPlus (-3/2:ℂ)≠0 := by
    rw [JPlus_one_copy_formula]
    apply mul_ne_zero (Complex.exp_ne_zero _)
    apply mul_ne_zero
    · norm_num [mul_pow,Complex.I_sq]
    · exact CCM.UniversalSinc.product_ne_zero_of_im_ne_zero probeSigma_pos (by norm_num)
  rw [probeTargetTailL2_norm S hS]
  exact mul_pos (mul_pos (div_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
    (norm_pos_iff.mpr hJ)) (Real.exp_pos _)

theorem adaptive_negative_quadrature_cannot_enter (F : CausalProbeL2) (S Ehat epsQ : ℝ)
    (h : Ehat+epsQ<0) : ¬ probeCoveredEnergy F S≤Ehat+epsQ := by
  have hn := probeCoveredEnergy_nonneg F S
  linarith

theorem adaptive_zero_witness_rejected : ¬ (0:ℝ)<0 := by norm_num

theorem adaptive_primary_actual_trial {N : ℕ} (x : Fin N→ℂ) (T S : ℝ)
    (hcover : T+Real.log (N:ℝ)+2*probeSigma≤S) (hS : 2*probeSigma≤S) :
    ‖probeFiniteInput x‖≤‖probeSource‖*probeCoefficientMass x ∧
      ‖probeFiniteOutput x-probeLagOperator T (probeFiniteInput x)‖≤
        2*Real.exp (-T/2)*‖probeSource‖*probeCoefficientMass x ∧
      (∀ᵐ t : ℝ,S<t → (probeLagOperator T (probeFiniteInput x):ProbeL2) t=0) := by
  have h := native_probe_adaptive_error_budgets x T S hcover hS
  exact ⟨h.1,h.2.1,h.2.2.1⟩

#print axioms Zeta23.OPICARound2.Validation.adaptive_actual_source_input
#print axioms Zeta23.OPICARound2.Validation.adaptive_expected_lag_error
#print axioms Zeta23.OPICARound2.Validation.adaptive_expected_visible_costs
#print axioms Zeta23.OPICARound2.Validation.adaptive_expected_source_transport
#print axioms Zeta23.OPICARound2.Validation.adaptive_expected_target_tail
#print axioms Zeta23.OPICARound2.Validation.adaptive_expected_whole_line
#print axioms Zeta23.OPICARound2.Validation.adaptive_expected_quadrature
#print axioms Zeta23.OPICARound2.Validation.adaptive_shrinking_filter_counterexample
#print axioms Zeta23.OPICARound2.Validation.adaptive_noncompact_target_control
#print axioms Zeta23.OPICARound2.Validation.adaptive_primary_actual_trial

end Zeta23.OPICARound2.Validation
