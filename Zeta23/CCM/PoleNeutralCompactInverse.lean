import Zeta23.CCM.PoleNeutralCompactH2Uniqueness

/-!
# The compact pole inverse on its exact general L2 source class

The core finite primitives construct a unique compact H2 solution, with
clamped continuous representatives and actual global weak derivative
identities. The sharp inverse bound is four. No source continuity, inverse,
Sobolev equation or energy estimate is a premise.
-/

noncomputable section

open Set MeasureTheory

namespace Zeta23.CCM

theorem poleNeutral_compactInverse_exists_unique {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ x, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    ∃! u : NativeCompactPoleH2 s f, True :=
  nativePoleCompactH2_exists_unique hs hf hsupport hplus hminus

theorem poleNeutral_compactInverse_support {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ x, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    tsupport (nativePoleCompactH2 hs hf hsupport hplus hminus).value ⊆ Icc (-s) s := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  exact hx ((nativePoleCompactH2 hs hf hsupport hplus hminus).value_support x hnot)

theorem poleNeutral_compactInverse_norm_bound {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ x, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    (eLpNorm (nativePoleCompactH2 hs hf hsupport hplus hminus).value 2 volume).toReal ≤
      4 * (eLpNorm f 2 volume).toReal :=
  nativePoleCompactH2_norm_bound hs hf hsupport hplus hminus

end Zeta23.CCM

#print axioms Zeta23.CCM.poleNeutral_compactInverse_exists_unique
#print axioms Zeta23.CCM.poleNeutral_compactInverse_support
#print axioms Zeta23.CCM.poleNeutral_compactInverse_norm_bound
