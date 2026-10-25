import Zeta23.OPICAFollowup.RenormalizedCoPoisson

/- Independent consumers for the original R1-CP1 root
`Zeta23.OPICAFollowup.renormalized_copoisson_tempered_family`.

Definition audits pin A_t, K_t and the family V_lam to their constructions from the actual
dilated comb distribution and the Dirac delta. The root is restated in full. Domain consumers
check the literal pairing of (CP1.1) on every Schwartz test,
K_t(φ) = e^(t/2) Σ φ(e^t n) + e^(-t/2) Σ φ(e^(-t) n) - e^(t/2) (φ(0) + ∫ φ),
the paper's decay constant 2ζ(N) at N = 2, analyticity of V_lam(φ) on all of ℂ, and the
self-dual pairing V_lam(𝓕φ) = V_lam(φ). -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap
open Zeta23.OPICAFollowup
namespace OPICACoPoissonFamilyIndependent

/-! ### Definition audits -/

theorem audit_coPoissonA (t : ℝ) : coPoissonA t = dilatedCombDistribution t -
    ((Real.exp (t / 2) : ℝ) : ℂ) • TemperedDistribution.delta (0 : ℝ) := rfl

theorem audit_kernel (t : ℝ) : renormalizedCombKernel t = coPoissonA t + 𝓕 (coPoissonA t) := rfl

theorem audit_family (lam : ℂ) : coPoissonFamily lam = coPoissonW lam + 𝓕 (coPoissonW lam) := rfl

theorem audit_W_apply (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonW lam φ = ∫ t in Ioi (0 : ℝ), cexp (-lam * t) * coPoissonA t φ := rfl

/-! ### Restated root -/

theorem expected_renormalized_copoisson_tempered_family :
    (∀ t : ℝ, renormalizedCombKernel t = dilatedCombDistribution t +
      dilatedCombDistribution (-t) - ((Real.exp (t / 2) : ℝ) : ℂ) •
        (TemperedDistribution.delta (0 : ℝ) + 𝓕 (TemperedDistribution.delta (0 : ℝ)))) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (𝓕 (TemperedDistribution.delta (0 : ℝ))) φ = ∫ x, φ x) ∧
    (∀ (t : ℝ) (φ : 𝓢(ℝ, ℂ)), coPoissonA t φ = (Real.exp (t / 2) : ℂ) *
      ∑' n : ℤ, if n = 0 then 0 else φ (Real.exp t * n)) ∧
    (∀ (t : ℝ) (φ : 𝓢(ℝ, ℂ)) (k : ℕ), 2 ≤ k → ‖coPoissonA t φ‖ ≤
      latticeZetaConst k * SchwartzMap.seminorm ℂ k 0 φ * Real.exp ((1 / 2 - k) * t)) ∧
    (∀ k : ℕ, 2 ≤ k → ((latticeZetaConst k : ℝ) : ℂ) = 2 * riemannZeta k) ∧
    (∀ t : ℝ, 𝓕 (renormalizedCombKernel t) = renormalizedCombKernel t) ∧
    (∀ (t : ℝ) (φ : 𝓢(ℝ, ℂ)),
      renormalizedCombKernel t (schwartzReflect φ) = renormalizedCombKernel t φ) ∧
    (∀ (lam : ℂ) (φ : 𝓢(ℝ, ℂ)),
      IntegrableOn (fun t : ℝ => cexp (-lam * t) * renormalizedCombKernel t φ) (Ioi 0)) ∧
    (∀ (lam : ℂ) (φ : 𝓢(ℝ, ℂ)), coPoissonFamily lam φ =
      ∫ t in Ioi (0 : ℝ), cexp (-lam * t) * renormalizedCombKernel t φ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), Differentiable ℂ (fun lam : ℂ => coPoissonFamily lam φ)) ∧
    (∀ lam : ℂ, 𝓕 (coPoissonFamily lam) = coPoissonFamily lam) ∧
    (∀ (lam : ℂ) (φ : 𝓢(ℝ, ℂ)),
      coPoissonFamily lam (schwartzReflect φ) = coPoissonFamily lam φ) :=
  renormalized_copoisson_tempered_family

/-! ### Domain consumers -/

/-- The literal (CP1.1) pairing on every Schwartz test. -/
theorem expected_kernel_pairing (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    renormalizedCombKernel t φ =
      (Real.exp (t / 2) : ℂ) * ∑' n : ℤ, φ (Real.exp t * n) +
      (Real.exp (-t / 2) : ℂ) * ∑' n : ℤ, φ (Real.exp (-t) * n) -
      (Real.exp (t / 2) : ℂ) * (φ 0 + ∫ x, φ x) := by
  rw [(renormalized_copoisson_tempered_family.1 t)]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, TemperedDistribution.delta_apply]
  rw [renormalized_copoisson_tempered_family.2.1 φ, dilatedCombDistribution_apply,
    dilatedCombDistribution_apply, neg_div]

/-- The paper's constant: |⟨A_t, φ⟩| ≤ 2ζ(2) p_2(φ) e^(-3t/2). -/
theorem expected_decay_N2 (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    ‖coPoissonA t φ‖ ≤ latticeZetaConst 2 * SchwartzMap.seminorm ℂ 2 0 φ *
        Real.exp (-(3 / 2) * t) ∧
    ((latticeZetaConst 2 : ℝ) : ℂ) = 2 * riemannZeta 2 := by
  refine ⟨?_, renormalized_copoisson_tempered_family.2.2.2.2.1 2 le_rfl⟩
  have h := renormalized_copoisson_tempered_family.2.2.2.1 t φ 2 le_rfl
  convert h using 3
  norm_num

/-- Entire family: V_lam(φ) is analytic at every complex lam. -/
theorem expected_family_analytic (φ : 𝓢(ℝ, ℂ)) (lam : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => coPoissonFamily z φ) lam :=
  (renormalized_copoisson_tempered_family.2.2.2.2.2.2.2.2.2.1 φ).analyticAt lam

/-- Self-dual pairing on tests, at every lam (including the strip 0 < Re(1/2 + lam) < 1). -/
theorem expected_family_selfdual_pairing (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonFamily lam (𝓕 φ) = coPoissonFamily lam φ := by
  have h := renormalized_copoisson_tempered_family.2.2.2.2.2.2.2.2.2.2.1 lam
  exact congrArg (fun T : TemperedDistribution ℝ ℂ => T φ) h

end OPICACoPoissonFamilyIndependent
#print axioms Zeta23.OPICAFollowup.renormalized_copoisson_tempered_family
#print axioms OPICACoPoissonFamilyIndependent.audit_coPoissonA
#print axioms OPICACoPoissonFamilyIndependent.expected_renormalized_copoisson_tempered_family
#print axioms OPICACoPoissonFamilyIndependent.expected_kernel_pairing
#print axioms OPICACoPoissonFamilyIndependent.expected_decay_N2
#print axioms OPICACoPoissonFamilyIndependent.expected_family_analytic
#print axioms OPICACoPoissonFamilyIndependent.expected_family_selfdual_pairing
