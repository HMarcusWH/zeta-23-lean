import Zeta23.CCM.OriginalDetectorFinitePhasePlane

/-!
# Actual same-source finite approximation to the original normalized phase

The physical normalization is the original source's proved L2 factor.
The finite vector is not yet asserted to have unit native norm.
-/

noncomputable section

open Set Complex
open scoped Topology

namespace Zeta23.CCM

/-- Literal coefficient reversal is exactly physical reflection about
the midpoint of the same aperture. -/
theorem localizedFiniteFunction_reverseCoefficients_reflected
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ) (x : ℝ) :
    localizedFiniteFunction L K (reverseCoefficients K u) x =
      localizedFiniteFunction L K u (L - x) := by
  unfold localizedFiniteFunction
  rw [← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply, reverseCoefficients, Fin.rev_rev, centeredIndex_rev]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hneg : localizedMode L (-centeredIndex K i) x = localizedMode L (centeredIndex K i) (-x) := by
    unfold localizedMode
    congr 2
    push_cast
    ring
  rw [hneg]
  convert (localizedMode_add_period L (centeredIndex K i) (-x) hL.ne').symm using 1 <;>
    congr 1 <;> ring

theorem originalDetectorFinitePhaseVector_physical_formula
    (σ L c : ℝ) (hL : 0 < L) (x : ℝ) :
    localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
        (originalDetectorFinitePhaseVector σ L c hL)) x =
      localizedFiniteFunction L (originalDetectorQuarticCutoff L)
        (originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale L c hL) x +
      (σ : ℂ) * localizedFiniteFunction L (originalDetectorQuarticCutoff L)
        (originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale L c hL) (L - x) := by
  change (∑ i, (_ + (σ : ℂ) * _) * _) = _
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [← localizedFiniteFunction_reverseCoefficients_reflected hL]
  rfl

private theorem iteratedDeriv_reflectionCombination
    {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (σ L : ℝ) (r : ℕ) (x : ℝ) :
    iteratedDeriv r (fun y => f y + (σ : ℂ) * f (L - y)) x =
      iteratedDeriv r f x + (σ : ℂ) * ((-1 : ℝ) ^ r • iteratedDeriv r f (L - x)) := by
  have hr : (r : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)
  have hreflect : ContDiff ℝ (⊤ : ℕ∞) (fun y => f (L - y)) :=
    hf.comp (contDiff_const.sub contDiff_id)
  rw [iteratedDeriv_fun_add ((hf.of_le hr).contDiffAt)
    (((contDiff_const.mul hreflect).of_le hr).contDiffAt), iteratedDeriv_const_mul_field]
  rw [congrFun (iteratedDeriv_comp_const_sub r f L) x]

private theorem contDiff_finitePoleFunction (L c : ℝ) (hL : 0 < L) :
    ContDiff ℝ (⊤ : ℕ∞) (localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      (originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale L c hL)) := by
  unfold localizedFiniteFunction
  apply ContDiff.sum
  intro i hi
  exact contDiff_const.mul ((contDiff_localizedMode L _).of_le le_top)

/-- The finite approximation with precisely the original physical L2
normalization. The native norm will be paid separately from this definition. -/
def originalDetectorFiniteOriginalPhaseApprox (σ a : ℝ)
    (hL : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) : ℝ → ℂ :=
  fun x => (Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ) *
    localizedFiniteFunction (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a))
      ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff
        (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) + 1)) ℂ)
          (originalDetectorFinitePhaseVector σ
            (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
            Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hL)) x

/-- Actual source-derived uniform jet control for the fixed original
normalized phase and its literal finite reflected approximation. This
holds at every finite order, including the required first three jets. -/
theorem originalDetectorFiniteOriginalPhaseApprox_iteratedDeriv_error_le
    {a : ℝ} (ha : 0 ≤ a) (σ : ℝ) (r : ℕ) {x : ℝ}
    (hx : x ∈ Icc 0 (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)) :
    let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
    let hLp : 0 < L := by
      dsimp [L, Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture,
        Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter]
      linarith [UniversalSinc.fixedScale_pos]
    ‖iteratedDeriv r (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) x -
      iteratedDeriv r (originalDetectorFiniteOriginalPhaseApprox σ a hLp) x‖ ≤
        Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization * (1 + |σ|) *
          originalDetectorFinitePoleImageJetBudget UniversalSinc.fixedScale L r := by
  dsimp only
  let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
  let c := Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter
  have hL2 : 2 ≤ L := by
    dsimp [L, c, Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture,
      Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter]
    linarith [UniversalSinc.fixedScale_pos]
  have hLp : 0 < L := by linarith
  change ‖iteratedDeriv r (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) x -
    iteratedDeriv r (originalDetectorFiniteOriginalPhaseApprox σ a hLp) x‖ ≤
      Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization * (1 + |σ|) *
        originalDetectorFinitePoleImageJetBudget UniversalSinc.fixedScale L r
  let f : ℝ → ℂ := fun y => Zeta23.ExceptionalZero.originalSincTest UniversalSinc.fixedScale (y - c)
  let g := localizedFiniteFunction L (originalDetectorQuarticCutoff L)
    (originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale L c hLp)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Zeta23.ExceptionalZero.contDiff_originalSincTest UniversalSinc.fixedScale_pos).comp
      (contDiff_id.sub contDiff_const)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_finitePoleFunction L c hLp
  have htrial : Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a =
      fun y => (Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ) *
        (f y + (σ : ℂ) * f (L - y)) := by
    funext y
    exact Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_reflected_formula σ a y
  have hfinite : originalDetectorFiniteOriginalPhaseApprox σ a hLp =
      fun y => (Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ) *
        (g y + (σ : ℂ) * g (L - y)) := by
    funext y
    unfold originalDetectorFiniteOriginalPhaseApprox
    rw [originalDetectorFinitePhaseVector_physical_formula]
  have hleft : 1 + UniversalSinc.fixedScale ≤ c := le_rfl
  have hright : c + UniversalSinc.fixedScale ≤ L - 1 := by
    dsimp [L, c, Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture,
      Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter]
    linarith
  have hx' : L - x ∈ Icc (0 : ℝ) L := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h1 := originalDetectorFinitePoleImage_iteratedDeriv_error_le_budget
    UniversalSinc.fixedScale_pos hL2 hleft hright r hx
  have h2 := originalDetectorFinitePoleImage_iteratedDeriv_error_le_budget
    UniversalSinc.fixedScale_pos hL2 hleft hright r hx'
  rw [htrial, hfinite, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_reflectionCombination hf, iteratedDeriv_reflectionCombination hg, ← mul_sub,
    norm_mul]
  have heq : (iteratedDeriv r f x + (σ : ℂ) * ((-1 : ℝ) ^ r • iteratedDeriv r f (L - x))) -
      (iteratedDeriv r g x + (σ : ℂ) * ((-1 : ℝ) ^ r • iteratedDeriv r g (L - x))) =
      (iteratedDeriv r f x - iteratedDeriv r g x) +
      (σ : ℂ) * ((-1 : ℝ) ^ r • (iteratedDeriv r f (L - x) - iteratedDeriv r g (L - x))) := by
    simp only [smul_sub]
    ring
  rw [heq]
  have hnorm : ‖(Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ)‖ =
      Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization := by
    simp [abs_of_pos Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization_pos]
  rw [hnorm]
  refine (mul_le_mul_of_nonneg_left (norm_add_le _ _)
    Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization_pos.le).trans ?_
  rw [norm_mul, norm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hh := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg σ))
  have hh' := mul_le_mul_of_nonneg_left hh
    Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization_pos.le
  convert! hh' using 1 <;> ring

end Zeta23.CCM

#print axioms Zeta23.CCM.localizedFiniteFunction_reverseCoefficients_reflected
#print axioms Zeta23.CCM.originalDetectorFinitePhaseVector_physical_formula
#print axioms Zeta23.CCM.originalDetectorFiniteOriginalPhaseApprox_iteratedDeriv_error_le
