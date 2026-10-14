import Zeta23.ExceptionalZero.UniversalSincOriginalPhaseDepth
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Uniform L1 jet bounds for the actual normalized original phase

The constants use only the fixed original kernel. They are independent of
the aperture and lobe separation, including the second derivative needed
by the existing Weil-continuity estimate.
-/

noncomputable section

open Set MeasureTheory Complex
open scoped Topology

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

theorem fixedOriginalSincKernel_iteratedDeriv_integrable (r : ℕ) :
    Integrable (iteratedDeriv r fixedOriginalSincKernel) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) fixedOriginalSincKernel :=
    contDiff_originalSincTest UniversalSinc.fixedScale_pos
  have hs : ∀ n : ℕ, HasCompactSupport (iteratedDeriv n fixedOriginalSincKernel) := by
    intro n
    induction n with
    | zero => exact hasCompactSupport_originalSincTest UniversalSinc.fixedScale_pos
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hr : (r : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)
  exact (hf.continuous_iteratedDeriv r hr).integrable_of_hasCompactSupport (hs r)

theorem fixedOriginalSincPhaseTrial_contDiff_top (σ a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fixedOriginalSincPhaseTrial σ a) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ =>
      fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter)) :=
    (contDiff_originalSincTest UniversalSinc.fixedScale_pos).comp
      (contDiff_id.sub contDiff_const)
  have heq : fixedOriginalSincPhaseTrial σ a = fun x =>
      (fixedOriginalSincTrialNormalization : ℂ) *
        (fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter) +
          (σ : ℂ) * fixedOriginalSincKernel
            (fixedOriginalSincTrialAperture a - x - fixedOriginalSincLobeCenter)) :=
    funext (fixedOriginalSincPhaseTrial_reflected_formula σ a)
  rw [heq]
  exact contDiff_const.mul (hf.add (contDiff_const.mul
    (hf.comp (contDiff_const.sub contDiff_id))))

theorem fixedOriginalSincPhaseTrial_iteratedDeriv_formula
    (σ a : ℝ) (r : ℕ) (x : ℝ) :
    iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x =
      (fixedOriginalSincTrialNormalization : ℂ) *
        (iteratedDeriv r fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter) +
          (σ : ℂ) * ((-1 : ℝ) ^ r • iteratedDeriv r fixedOriginalSincKernel
            ((fixedOriginalSincTrialAperture a - fixedOriginalSincLobeCenter) - x))) := by
  let f : ℝ → ℂ := fun y => fixedOriginalSincKernel (y - fixedOriginalSincLobeCenter)
  let L := fixedOriginalSincTrialAperture a
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (contDiff_originalSincTest UniversalSinc.fixedScale_pos).comp
      (contDiff_id.sub contDiff_const)
  have href : ContDiff ℝ (⊤ : ℕ∞) (fun y => f (L - y)) :=
    hf.comp (contDiff_const.sub contDiff_id)
  have hr : (r : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)
  have heq : fixedOriginalSincPhaseTrial σ a = fun y =>
      (fixedOriginalSincTrialNormalization : ℂ) * (f y + (σ : ℂ) * f (L - y)) :=
    funext (fixedOriginalSincPhaseTrial_reflected_formula σ a)
  rw [heq, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_add ((hf.of_le hr).contDiffAt)
      (((contDiff_const.mul href).of_le hr).contDiffAt), iteratedDeriv_const_mul_field,
    congrFun (iteratedDeriv_comp_const_sub r f L) x]
  simp only [f, iteratedDeriv_comp_sub_const]
  have harg : L - x - fixedOriginalSincLobeCenter =
      (fixedOriginalSincTrialAperture a - fixedOriginalSincLobeCenter) - x := by
    dsimp [L]
    ring
  rw [harg]

private theorem originalPhaseJet_norm_le (σ a : ℝ) (r : ℕ) (x : ℝ) :
    ‖iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x‖ ≤
      fixedOriginalSincTrialNormalization *
        (‖iteratedDeriv r fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter)‖ +
          |σ| * ‖iteratedDeriv r fixedOriginalSincKernel
            ((fixedOriginalSincTrialAperture a - fixedOriginalSincLobeCenter) - x)‖) := by
  rw [fixedOriginalSincPhaseTrial_iteratedDeriv_formula, norm_mul]
  have hn : ‖(fixedOriginalSincTrialNormalization : ℂ)‖ = fixedOriginalSincTrialNormalization := by
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos fixedOriginalSincTrialNormalization_pos]
  rw [hn]
  refine (mul_le_mul_of_nonneg_left (norm_add_le _ _)
    fixedOriginalSincTrialNormalization_pos.le).trans ?_
  simp only [norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact le_rfl

/-- Actual full-line integrability and aperture-independent jet bound. -/
theorem fixedOriginalSincPhaseTrial_iteratedDeriv_L1_bound (σ a : ℝ) (r : ℕ) :
    Integrable (iteratedDeriv r (fixedOriginalSincPhaseTrial σ a)) ∧
      (∫ x : ℝ, ‖iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x‖) ≤
        fixedOriginalSincTrialNormalization * (1 + |σ|) *
          (∫ x : ℝ, ‖iteratedDeriv r fixedOriginalSincKernel x‖) := by
  let k := iteratedDeriv r fixedOriginalSincKernel
  let c := fixedOriginalSincLobeCenter
  let T := fixedOriginalSincTrialAperture a - fixedOriginalSincLobeCenter
  have hk : Integrable k := fixedOriginalSincKernel_iteratedDeriv_integrable r
  have hl := hk.norm.comp_sub_right c
  have hr := hk.norm.comp_sub_left T
  have hsum : Integrable (fun x : ℝ => fixedOriginalSincTrialNormalization *
      (‖k (x - c)‖ + |σ| * ‖k (T - x)‖)) :=
    (hl.add (hr.const_mul |σ|)).const_mul fixedOriginalSincTrialNormalization
  have horder : (r : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)
  have hmeas : AEStronglyMeasurable
      (iteratedDeriv r (fixedOriginalSincPhaseTrial σ a)) volume :=
    ((fixedOriginalSincPhaseTrial_contDiff_top σ a).continuous_iteratedDeriv r
      horder).aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ ∂volume,
      ‖iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x‖ ≤
        fixedOriginalSincTrialNormalization * (‖k (x - c)‖ + |σ| * ‖k (T - x)‖) :=
    Filter.Eventually.of_forall (originalPhaseJet_norm_le σ a r)
  have hphase := hsum.mono' hmeas hbound
  refine ⟨hphase, ?_⟩
  have hleft : (∫ x : ℝ, ‖k (x - c)‖) = ∫ x : ℝ, ‖k x‖ :=
    integral_sub_right_eq_self (fun x : ℝ => ‖k x‖) c
  have hright : (∫ x : ℝ, ‖k (T - x)‖) = ∫ x : ℝ, ‖k x‖ :=
    integral_sub_left_eq_self (fun x : ℝ => ‖k x‖) volume T
  calc
    _ ≤ ∫ x : ℝ, fixedOriginalSincTrialNormalization *
        (‖k (x - c)‖ + |σ| * ‖k (T - x)‖) :=
      integral_mono_ae hphase.norm hsum hbound
    _ = _ := by
      rw [integral_const_mul, integral_add hl (hr.const_mul |σ|), integral_const_mul,
        hleft, hright]
      dsimp [k]
      ring

def originalDetectorOriginalPhaseL1JetBudget (r : ℕ) : ℝ :=
  2 * fixedOriginalSincTrialNormalization *
    (∫ x : ℝ, ‖iteratedDeriv r fixedOriginalSincKernel x‖)

theorem fixedOriginalSincPhaseTrial_originalPhase_L1_bound
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (a : ℝ) (r : ℕ) :
    (∫ x : ℝ, ‖iteratedDeriv r (fixedOriginalSincPhaseTrial σ a) x‖) ≤
      originalDetectorOriginalPhaseL1JetBudget r := by
  have hs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have h := (fixedOriginalSincPhaseTrial_iteratedDeriv_L1_bound σ a r).2
  rw [hs] at h
  convert h using 1 <;> unfold originalDetectorOriginalPhaseL1JetBudget <;> ring

end Zeta23.CCM

#print axioms Zeta23.CCM.fixedOriginalSincKernel_iteratedDeriv_integrable
#print axioms Zeta23.CCM.fixedOriginalSincPhaseTrial_contDiff_top
#print axioms Zeta23.CCM.fixedOriginalSincPhaseTrial_iteratedDeriv_formula
#print axioms Zeta23.CCM.fixedOriginalSincPhaseTrial_iteratedDeriv_L1_bound
#print axioms Zeta23.CCM.fixedOriginalSincPhaseTrial_originalPhase_L1_bound
