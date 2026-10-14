import Zeta23.CCM.PoleNeutralCompactH2SourceCongruence
import Zeta23.CCM.NativeWeilResponse

/-!
# Compact weak-H2 inverse duality: physical integration by parts

For an actual compact pole-neutral L2 source, its CONSTRUCTED weak-H2
inverse is dual to the unchanged constant-coefficient P=∂²-1/4 on
every compact smooth test. This theorem does not assert that the full
unbounded causal prime history is compactly supported; localizing that
history and paying the physical boundary traces remains an additional
source-specific T11 obligation.

No global X∈L2, artificial inverse, spectral positivity or RH premise
is introduced.
-/

noncomputable section

open MeasureTheory Set Complex

namespace Zeta23.CCM

theorem nativePoleCompactInverse_compactTest_duality
    {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume)
    (hfs : ∀ x, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hφs : HasCompactSupport φ) :
    (∫ x : ℝ, f x * φ x) =
      ∫ x : ℝ, (nativePoleCompactH2 hs hf hfs hplus hminus).value x *
        (deriv (deriv φ) x - (1 / 4 : ℂ) * φ x) := by
  let u := nativePoleCompactH2 hs hf hfs hplus hminus
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hφd : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hφ2 : Continuous (deriv (deriv φ)) :=
    hφd.continuous_deriv (by norm_num)
  have hφL2 : MemLp φ 2 volume :=
    hφ.continuous.memLp_of_hasCompactSupport hφs
  have hφd2L2 : MemLp (deriv (deriv φ)) 2 volume :=
    hφ2.memLp_of_hasCompactSupport hφs.deriv.deriv
  have hUf : Integrable (fun x : ℝ => u.value x * φ x) :=
    u.value_l2.integrable_mul hφL2
  have hFf : Integrable (fun x : ℝ => f x * φ x) :=
    hf.integrable_mul hφL2
  have hUdd : Integrable (fun x : ℝ => u.value x * deriv (deriv φ) x) :=
    u.value_l2.integrable_mul hφd2L2
  have hFirst := u.weak_first hs hφd hφs.deriv
  have hSecond := u.weak_second hs hfs hφ1 hφs
  have hExpand :
      (∫ x : ℝ, ((1 / 4 : ℂ) * u.value x + f x) * φ x) =
        (1 / 4 : ℂ) * (∫ x : ℝ, u.value x * φ x) +
          (∫ x : ℝ, f x * φ x) := by
    have heq :
        (fun x : ℝ => ((1 / 4 : ℂ) * u.value x + f x) * φ x) =
        fun x : ℝ => (1 / 4 : ℂ) * (u.value x * φ x) + f x * φ x := by
      funext x
      ring
    rw [heq, integral_add (hUf.const_mul _) hFf, integral_const_mul]
  have hDual :
      (∫ x : ℝ, u.value x * deriv (deriv φ) x) =
        (1 / 4 : ℂ) * (∫ x : ℝ, u.value x * φ x) +
          (∫ x : ℝ, f x * φ x) := by
    calc
      _ = -(∫ x : ℝ, u.first x * deriv φ x) := hFirst
      _ = (∫ x : ℝ, ((1 / 4 : ℂ) * u.value x + f x) * φ x) := by
        rw [hSecond]
        simp
      _ = _ := hExpand
  change (∫ x : ℝ, f x * φ x) = ∫ x : ℝ,
    u.value x * (deriv (deriv φ) x - (1 / 4 : ℂ) * φ x)
  calc
    (∫ x : ℝ, f x * φ x) =
        (∫ x : ℝ, u.value x * deriv (deriv φ) x) -
          (1 / 4 : ℂ) * (∫ x : ℝ, u.value x * φ x) := by
            rw [hDual]
            ring
    _ = ∫ x : ℝ, u.value x *
        (deriv (deriv φ) x - (1 / 4 : ℂ) * φ x) := by
      have hfun :
          (fun x : ℝ => u.value x *
            (deriv (deriv φ) x - (1 / 4 : ℂ) * φ x)) =
            fun x : ℝ => u.value x * deriv (deriv φ) x -
              (1 / 4 : ℂ) * (u.value x * φ x) := by
        funext x
        ring
      rw [hfun, integral_sub hUdd (hUf.const_mul _), integral_const_mul]

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePoleCompactInverse_compactTest_duality
