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

end Zeta23.OPICARound2.Validation
