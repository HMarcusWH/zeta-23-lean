import Zeta23.CCM.DictionaryTentMollifierTransform

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution Topology Pointwise

/-!
# Common support and convergence for the mollified dictionary tent

This module is the M3 architecture gate for Route M.  It proves that every
mollified tent lives in one physical-space support envelope independent of the
mollification index, and records pointwise convergence in the complex codomain
used by `paperFT`.

No explicit-formula limit passage is performed here.
-/

/-- M3: every mollified tent is supported inside one envelope independent of
the mollification index. -/
theorem dictionaryTentMollified_support_abs_le
    {L : ℝ} (hL : 0 < L) (n : ℕ) {x : ℝ}
    (hx : dictionaryTentMollified L n x ≠ 0) :
    |x| ≤ L + 1 := by
  have hxconv :
      x ∈ Function.support
        (dictionaryTentMollifierComplex n ⋆[mul ℂ ℂ, volume] dictionaryTent L) := by
    rw [← dictionaryTentMollified_eq_complexConvolution L n]
    exact hx
  have hxsum :
      x ∈ Function.support (dictionaryTentMollifierComplex n) +
        Function.support (dictionaryTent L) :=
    (support_convolution_subset (mul ℂ ℂ)) hxconv
  rcases Set.mem_add.mp hxsum with ⟨u, hu, v, hv, huv⟩
  have huabs : |u| ≤ 1 :=
    dictionaryTentMollifierComplex_support_abs_le_one n hu
  have hvIcc : v ∈ Icc (-L) L :=
    dictionaryTent_support_subset_Icc hL hv
  have hvabs : |v| ≤ L := abs_le.mpr hvIcc
  rw [← huv]
  calc
    |u + v| ≤ |u| + |v| := abs_add u v
    _ ≤ 1 + L := add_le_add huabs hvabs
    _ = L + 1 := by ring

/-- Closed-interval form of the common M3 support envelope. -/
theorem dictionaryTentMollified_support_subset_Icc
    {L : ℝ} (hL : 0 < L) (n : ℕ) :
    Function.support (dictionaryTentMollified L n) ⊆
      Icc (-(L + 1)) (L + 1) := by
  intro x hx
  exact abs_le.mp (dictionaryTentMollified_support_abs_le hL n hx)

/-- M3: pointwise convergence to the literal canonical tent, in the complex
codomain used by the Fourier-transform and explicit-formula interfaces. -/
theorem dictionaryTentMollified_tendsto
    (L y : ℝ) :
    Tendsto (fun n : ℕ => dictionaryTentMollified L n y) atTop
      (𝓝 (dictionaryTent L y)) := by
  have hreal := dictionaryTentMollifiedReal_tendsto L y
  have hmap :=
    Complex.ofRealCLM.continuous.continuousAt.tendsto.comp hreal
  simpa [dictionaryTentMollified, dictionaryTent, Function.comp_def] using hmap

/-- Compiler-facing M0--M3 Route-M architecture package.

This packages exactly the properties needed to regard mollification as a
local adapter into the existing `C²` explicit-formula interface: smoothness,
one common physical support envelope, convergence to the literal tent, exact
complex-frequency factorization, and a uniform critical-strip quadratic
transform bound.  It does not perform any explicit-formula limit passage. -/
theorem dictionaryTent_mollifier_architecture_package
    {L : ℝ} (hL : 0 < L) :
    (∀ n : ℕ, ContDiff ℝ 2 (dictionaryTentMollified L n)) ∧
    (∀ n : ℕ, ∀ x : ℝ, dictionaryTentMollified L n x ≠ 0 → |x| ≤ L + 1) ∧
    (∀ y : ℝ,
      Tendsto (fun n : ℕ => dictionaryTentMollified L n y) atTop
        (𝓝 (dictionaryTent L y))) ∧
    (∀ n : ℕ, ∀ z : ℂ,
      Zeta23.paperFT (dictionaryTentMollified L n) z =
        dictionaryTentMollifierTransform n z *
          Zeta23.paperFT (dictionaryTent L) z) ∧
    (∀ n : ℕ, ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖Zeta23.paperFT (dictionaryTentMollified L n) z‖ * ‖z‖ ^ 2
        ≤ Real.exp (1 / 2) *
          (2 * (1 + Real.exp (L / 2)) / L)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact contDiff_two_dictionaryTentMollified L n
  · intro n x hx
    exact dictionaryTentMollified_support_abs_le hL n hx
  · intro y
    exact dictionaryTentMollified_tendsto L y
  · intro n z
    exact paperFT_dictionaryTentMollified_factor hL n z
  · intro n z hstrip
    exact norm_paperFT_dictionaryTentMollified_mul_sq_le hL n z hstrip

end Zeta23.CCM

#print axioms Zeta23.CCM.dictionaryTentMollified_support_abs_le
#print axioms Zeta23.CCM.dictionaryTentMollified_tendsto
#print axioms Zeta23.CCM.dictionaryTent_mollifier_architecture_package
