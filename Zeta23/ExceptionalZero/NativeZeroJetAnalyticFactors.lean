import Zeta23.ExceptionalZero.NativeOriginalSourceLaplaceVisibility
import Zeta23.ExceptionalZero.WeilZeroSideEvenization
import Zeta23.CCM.NativeCompletionComplexLaplace
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual zeta multiplicity and the fixed source factors for the native zero jet

These analytic expressions use the actual fixed source and actual zeta
function. Their orders differ by exactly one, including at multiple zeros.
Identifying these expressions with the actual physical transforms is an
independent integral theorem and is not assumed here.
-/

noncomputable section

open Complex Set Filter
open scoped Topology BigOperators

namespace Zeta23.ExceptionalZero

def nativeZeroJetKernelMultiplier (w : ℂ) : ℂ :=
  CCM.nativeCompletionRationalMultiplier w * riemannZeta (w + 1 / 2)

def nativeZeroJetInputMultiplier (w : ℂ) : ℂ :=
  -(CCM.nativeCompletionRationalMultiplier w * CCM.nativeOriginalSourceLaplace w) *
    deriv riemannZeta (w + 1 / 2)

theorem nativeZeroMultiplicity_order (rho : zetaZeroConfig.carrier) :
    analyticOrderAt riemannZeta (rho : ℂ) = (zeroMult (rho : ℂ) : ℕ∞) := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  exact (ENat.natCast_toNat (analyticOrderAt_riemannZeta_ne_top hrho.not_trivial.2)).symm

theorem nativeZeroMultiplicity_deriv_order (rho : zetaZeroConfig.carrier) :
    analyticOrderAt (deriv riemannZeta) (rho : ℂ) =
      (zeroMult (rho : ℂ) - 1 : ℕ) := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  have hm : 1 ≤ zeroMult (rho : ℂ) := zetaZeroConfig.one_le_mult _ rho.property
  have hord : analyticOrderAt riemannZeta (rho : ℂ) =
      ((zeroMult (rho : ℂ) - 1 : ℕ) : ℕ∞) + 1 := by
    rw [nativeZeroMultiplicity_order, ← Nat.cast_add_one]
    congr 1
    omega
  exact analyticOrderAt_deriv_of_pos
    (riemannZeta_analyticOnNhd_compl_one _ hrho.not_trivial.2) hord

theorem nativeOriginalSourceLaplace_analyticAt (w : ℂ) :
    AnalyticAt ℂ CCM.nativeOriginalSourceLaplace w := by
  have heq : CCM.nativeOriginalSourceLaplace = fun z : ℂ =>
      ((I * z) ^ 2 + 1 / 4) ^ 2 *
        CCM.UniversalSinc.product CCM.UniversalSinc.fixedScale (I * z) :=
    funext nativeOriginalSourceLaplace_formula
  rw [heq]
  apply AnalyticAt.mul (by fun_prop)
  exact (CCM.UniversalSinc.analyticAt_product CCM.UniversalSinc.fixedScale_pos.le (I * w)).comp
    (by fun_prop)

theorem nativeCompletionRationalMultiplier_at_zero_analyticAt (rho : zetaZeroConfig.carrier) :
    AnalyticAt ℂ CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  have hzero : (rho : ℂ) ≠ 0 := by
    intro h
    have hpos := hrho.2.1
    simpa only [h, Complex.zero_re, lt_self_iff_false] using hpos
  have hnegone : (rho : ℂ) + 1 ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hreal
    linarith [hrho.2.1]
  unfold CCM.nativeCompletionRationalMultiplier
  apply AnalyticAt.div (by fun_prop) (by fun_prop)
  convert mul_ne_zero hzero hnegone using 1 <;> congr 1 <;> ring

theorem nativeCompletionRationalMultiplier_at_zero_ne_zero (rho : zetaZeroConfig.carrier) :
    CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) ≠ 0 := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  have hnum : (rho : ℂ) - 1 / 2 - 1 / 2 ≠ 0 := by
    intro h
    apply hrho.not_trivial.2
    calc (rho : ℂ) = (rho : ℂ) - 1 / 2 - 1 / 2 + 1 := by ring
         _ = 1 := by rw [h, zero_add]
  have hd1 : (rho : ℂ) - 1 / 2 + 1 / 2 ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num at hreal
    linarith [hrho.2.1]
  have hd2 : (rho : ℂ) - 1 / 2 + 3 / 2 ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num at hreal
    linarith [hrho.2.1]
  exact div_ne_zero hnum (mul_ne_zero hd1 hd2)

private theorem shifted_zeta_order (rho : zetaZeroConfig.carrier) :
    analyticOrderAt (fun z : ℂ => riemannZeta (z + 1 / 2)) ((rho : ℂ) - 1 / 2) =
      (zeroMult (rho : ℂ) : ℕ∞) := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) ((rho : ℂ) - 1 / 2) := by fun_prop
  have hd : deriv (fun z : ℂ => z + 1 / 2) ((rho : ℂ) - 1 / 2) ≠ 0 := by
    simp only [deriv_add_const, deriv_id'']
    exact one_ne_zero
  simpa only [Function.comp_def, sub_add_cancel] using
    (analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) hshift hd).trans
      (by simpa only [sub_add_cancel] using nativeZeroMultiplicity_order rho)

private theorem shifted_zeta_deriv_order (rho : zetaZeroConfig.carrier) :
    analyticOrderAt (fun z : ℂ => deriv riemannZeta (z + 1 / 2)) ((rho : ℂ) - 1 / 2) =
      (zeroMult (rho : ℂ) - 1 : ℕ) := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) ((rho : ℂ) - 1 / 2) := by fun_prop
  have hd : deriv (fun z : ℂ => z + 1 / 2) ((rho : ℂ) - 1 / 2) ≠ 0 := by
    simp only [deriv_add_const, deriv_id'']
    exact one_ne_zero
  simpa only [Function.comp_def, sub_add_cancel] using
    (analyticOrderAt_comp_of_deriv_ne_zero (f := deriv riemannZeta) hshift hd).trans
      (by simpa only [sub_add_cancel] using nativeZeroMultiplicity_deriv_order rho)

theorem nativeZeroJetKernelMultiplier_order (rho : zetaZeroConfig.carrier) :
    analyticOrderAt nativeZeroJetKernelMultiplier ((rho : ℂ) - 1 / 2) =
      (zeroMult (rho : ℂ) : ℕ∞) := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  have hzeta : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z + 1 / 2))
      ((rho : ℂ) - 1 / 2) := by
    have hz : AnalyticAt ℂ riemannZeta ((rho : ℂ) - 1 / 2 + 1 / 2) := by
      simpa only [sub_add_cancel] using
        riemannZeta_analyticOnNhd_compl_one _ hrho.not_trivial.2
    have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) ((rho : ℂ) - 1 / 2) := by fun_prop
    exact hz.comp (f := fun z : ℂ => z + 1 / 2) (x := (rho : ℂ) - 1 / 2) hshift
  change analyticOrderAt (CCM.nativeCompletionRationalMultiplier *
    (fun z : ℂ => riemannZeta (z + 1 / 2))) _ = _
  rw [analyticOrderAt_mul (nativeCompletionRationalMultiplier_at_zero_analyticAt rho) hzeta,
    (nativeCompletionRationalMultiplier_at_zero_analyticAt rho).analyticOrderAt_eq_zero.mpr
      (nativeCompletionRationalMultiplier_at_zero_ne_zero rho), zero_add, shifted_zeta_order]

theorem nativeZeroJetInputMultiplier_order (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    analyticOrderAt nativeZeroJetInputMultiplier ((rho : ℂ) - 1 / 2) =
      (zeroMult (rho : ℂ) - 1 : ℕ) := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  have hfactor : AnalyticAt ℂ (fun z : ℂ =>
      -(CCM.nativeCompletionRationalMultiplier z * CCM.nativeOriginalSourceLaplace z))
      ((rho : ℂ) - 1 / 2) :=
    ((nativeCompletionRationalMultiplier_at_zero_analyticAt rho).mul
      (nativeOriginalSourceLaplace_analyticAt _)).neg
  have hfactorne : -(CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
      CCM.nativeOriginalSourceLaplace ((rho : ℂ) - 1 / 2)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (nativeCompletionRationalMultiplier_at_zero_ne_zero rho)
      (nativeOriginalSourceLaplace_ne_zero_at_off_line_zero rho hoff))
  have hzeta : AnalyticAt ℂ (fun z : ℂ => deriv riemannZeta (z + 1 / 2))
      ((rho : ℂ) - 1 / 2) := by
    have hz : AnalyticAt ℂ (deriv riemannZeta) ((rho : ℂ) - 1 / 2 + 1 / 2) := by
      simpa only [sub_add_cancel] using
        (riemannZeta_analyticOnNhd_compl_one _ hrho.not_trivial.2).deriv
    have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) ((rho : ℂ) - 1 / 2) := by fun_prop
    exact hz.comp (f := fun z : ℂ => z + 1 / 2) (x := (rho : ℂ) - 1 / 2) hshift
  change analyticOrderAt ((fun z : ℂ =>
      -(CCM.nativeCompletionRationalMultiplier z * CCM.nativeOriginalSourceLaplace z)) *
    (fun z : ℂ => deriv riemannZeta (z + 1 / 2))) _ = _
  rw [analyticOrderAt_mul hfactor hzeta, hfactor.analyticOrderAt_eq_zero.mpr hfactorne,
    zero_add, shifted_zeta_deriv_order]

private theorem iteratedDeriv_mul_leading {g h : ℂ → ℂ} {z : ℂ} (k : ℕ)
    (hg : AnalyticAt ℂ g z) (hh : AnalyticAt ℂ h z)
    (hzero : ∀ j < k, iteratedDeriv j h z = 0) :
    iteratedDeriv k (fun q : ℂ => g q * h q) z = g z * iteratedDeriv k h z := by
  rw [iteratedDeriv_fun_mul hg.contDiffAt hh.contDiffAt, Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, one_mul, tsub_zero]
  · intro j hj hjne
    have hjle := Finset.mem_range.mp hj
    rw [hzero (k - j) (by omega), mul_zero]
  · simp only [Finset.mem_range, Nat.zero_lt_succ, not_true_eq_false, false_implies]

/-- The leading input-multiplier jet contains exactly the actual source,
the nonzero correction factor, and the m-th zeta derivative. The derivative
of zeta has order m−1; this formula includes multiple zeros. -/
theorem nativeZeroJetInputMultiplier_jet (rho : zetaZeroConfig.carrier) :
    iteratedDeriv (zeroMult (rho : ℂ) - 1) nativeZeroJetInputMultiplier
        ((rho : ℂ) - 1 / 2) =
      -(CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        CCM.nativeOriginalSourceLaplace ((rho : ℂ) - 1 / 2)) *
          iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (rho : ℂ) := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  have hm : 1 ≤ zeroMult (rho : ℂ) := zetaZeroConfig.one_le_mult _ rho.property
  let g : ℂ → ℂ := fun z =>
    -(CCM.nativeCompletionRationalMultiplier z * CCM.nativeOriginalSourceLaplace z)
  let h : ℂ → ℂ := fun z => deriv riemannZeta (z + 1 / 2)
  have hg : AnalyticAt ℂ g ((rho : ℂ) - 1 / 2) :=
    ((nativeCompletionRationalMultiplier_at_zero_analyticAt rho).mul
      (nativeOriginalSourceLaplace_analyticAt _)).neg
  have hh : AnalyticAt ℂ h ((rho : ℂ) - 1 / 2) := by
    have hz : AnalyticAt ℂ (deriv riemannZeta) ((rho : ℂ) - 1 / 2 + 1 / 2) := by
      simpa only [sub_add_cancel] using
        (riemannZeta_analyticOnNhd_compl_one _ hrho.not_trivial.2).deriv
    have hs : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) ((rho : ℂ) - 1 / 2) := by fun_prop
    exact hz.comp (f := fun z : ℂ => z + 1 / 2) (x := (rho : ℂ) - 1 / 2) hs
  have hzero := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hh).mp
    (shifted_zeta_deriv_order rho)
  change iteratedDeriv (zeroMult (rho : ℂ) - 1) (fun z : ℂ => g z * h z) _ = _
  rw [iteratedDeriv_mul_leading _ hg hh hzero.1]
  have hder : iteratedDeriv (zeroMult (rho : ℂ) - 1) h ((rho : ℂ) - 1 / 2) =
      iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (rho : ℂ) := by
    dsimp only [h]
    simp only [iteratedDeriv_comp_add_const, sub_add_cancel, ← iteratedDeriv_succ']
    congr 1
    omega
  rw [hder]

/-- The exact phase-corrected source factor which will occur in the
physical degree-(m−1) moment is nonzero without a simple-zero premise. -/
theorem nativeZeroJetSourceFactor_ne_zero (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    (-1 : ℂ) ^ zeroMult (rho : ℂ) *
      CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
      CCM.nativeOriginalSourceLaplace ((rho : ℂ) - 1 / 2) *
      iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (rho : ℂ) ≠ 0 := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  have hzeta := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (riemannZeta_analyticOnNhd_compl_one _ hrho.not_trivial.2)).mp
      (nativeZeroMultiplicity_order rho)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)))
    (nativeCompletionRationalMultiplier_at_zero_ne_zero rho))
    (nativeOriginalSourceLaplace_ne_zero_at_off_line_zero rho hoff)) hzeta.2

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.nativeZeroMultiplicity_order
#print axioms Zeta23.ExceptionalZero.nativeZeroMultiplicity_deriv_order
#print axioms Zeta23.ExceptionalZero.nativeOriginalSourceLaplace_analyticAt
#print axioms Zeta23.ExceptionalZero.nativeCompletionRationalMultiplier_at_zero_ne_zero
#print axioms Zeta23.ExceptionalZero.nativeZeroJetKernelMultiplier_order
#print axioms Zeta23.ExceptionalZero.nativeZeroJetInputMultiplier_order
#print axioms Zeta23.ExceptionalZero.nativeZeroJetInputMultiplier_jet
#print axioms Zeta23.ExceptionalZero.nativeZeroJetSourceFactor_ne_zero
