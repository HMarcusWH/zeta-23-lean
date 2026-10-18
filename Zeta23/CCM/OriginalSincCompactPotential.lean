import Zeta23.CCM.PoleNeutralCompactInverseCore
import Zeta23.CCM.UniversalSincSourceFacade
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# The explicit compact potential of the actual twice pole-killed source

Both elementary moments are filled from the actual complex Fourier
transform, with their signs retained. The potential is the finite-primitive
construction, not an independently supplied inverse. It is compact, C2
and L2 and solves P u=j. Identification with k, the general compact-L2
inverse and its operator norm, and the native detector forcing bridge
remain separate obligations.
-/

noncomputable section

open Set MeasureTheory

namespace Zeta23.CCM

theorem nativePoleMoment_eq_paperFT (r : ℝ) (f : ℝ → ℂ) :
    (∫ y : ℝ, nativePoleExponential r y * f y) =
      Zeta23.paperFT f (-(r : ℂ) * Complex.I) := by
  rw [Zeta23.paperFT_def]
  apply integral_congr_ae
  filter_upwards with y
  have heq : Complex.I * (-(r : ℂ) * Complex.I) * (y : ℂ) =
      ((r * y : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul]
    calc
      _ = -(Complex.I ^ 2) * (r : ℂ) * (y : ℂ) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [heq]
  unfold nativePoleExponential
  rw [Complex.ofReal_exp]
  ring

theorem universalSincSecondKernel_elementary_moments {s : ℝ} (hs : 0 < s) :
    (∫ y : ℝ, nativePoleExponential (1 / 2) y * universalSincSecondKernel s y) = 0 ∧
      (∫ y : ℝ, nativePoleExponential (-1 / 2) y * universalSincSecondKernel s y) = 0 := by
  constructor
  all_goals
    rw [nativePoleMoment_eq_paperFT, paperFT_universalSincSecondKernel hs]
    have hz : (-(↑(1 / 2 : ℝ) : ℂ) * Complex.I) ^ 2 + (1 / 4 : ℂ) = 0 := by
      norm_num [mul_pow, Complex.I_sq]
    have hmz : (-(↑(-1 / 2 : ℝ) : ℂ) * Complex.I) ^ 2 + (1 / 4 : ℂ) = 0 := by
      norm_num [mul_pow, Complex.I_sq]
    simp only [hz, hmz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]

def originalSincCompactPotential (s : ℝ) : ℝ → ℂ :=
  nativePoleCompactInverse s (universalSincSecondKernel s)

theorem originalSincCompactPotential_contDiff_two {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 2 (originalSincCompactPotential s) :=
  nativePoleCompactInverse_contDiff_two s (universalSincSecondKernel_contDiff hs).continuous

theorem originalSincCompactPotential_pole_equation {s : ℝ} (hs : 0 < s) (x : ℝ) :
    deriv (deriv (originalSincCompactPotential s)) x -
      (1 / 4 : ℂ) * originalSincCompactPotential s x = universalSincSecondKernel s x :=
  nativePoleCompactInverse_pole_equation s (universalSincSecondKernel_contDiff hs).continuous x

theorem originalSincCompactPotential_zero_outside {s : ℝ} (hs : 0 < s) {x : ℝ}
    (hx : x ∉ Icc (-s) s) : originalSincCompactPotential s x = 0 := by
  have hm := universalSincSecondKernel_elementary_moments hs
  exact nativePoleCompactInverse_zero_outside hs.le
    (fun y hy => universalSincSecondKernel_zero_outside hs hy) hm.1 hm.2 hx

theorem originalSincCompactPotential_hasCompactSupport {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (originalSincCompactPotential s) := by
  apply HasCompactSupport.intro (K := Icc (-s) s) isCompact_Icc
  exact fun x hx => originalSincCompactPotential_zero_outside hs hx

theorem originalSincCompactPotential_clamped_traces {s : ℝ} (hs : 0 < s) :
    originalSincCompactPotential s (-s) = 0 ∧ originalSincCompactPotential s s = 0 ∧
      deriv (originalSincCompactPotential s) (-s) = 0 ∧
      deriv (originalSincCompactPotential s) s = 0 := by
  have hm := universalSincSecondKernel_elementary_moments hs
  exact nativePoleCompactInverse_clamped_traces hs.le
    (universalSincSecondKernel_contDiff hs).continuous
    (fun y hy => universalSincSecondKernel_zero_outside hs hy) hm.1 hm.2

theorem originalSincCompactPotential_memLp_two {s : ℝ} (hs : 0 < s) :
    MemLp (originalSincCompactPotential s) 2 volume :=
  (originalSincCompactPotential_contDiff_two hs).continuous.memLp_of_hasCompactSupport
    (originalSincCompactPotential_hasCompactSupport hs)

theorem originalSincCompactPotentialDerivative_memLp_two {s : ℝ} (hs : 0 < s) :
    MemLp (deriv (originalSincCompactPotential s)) 2 volume := by
  have hfirst : deriv (originalSincCompactPotential s) =
      nativePoleCompactInverseDerivative s (universalSincSecondKernel s) := by
    funext x
    exact (nativePoleCompactInverse_hasDerivAt s
      (universalSincSecondKernel_contDiff hs).continuous x).deriv
  rw [hfirst]
  have hm := universalSincSecondKernel_elementary_moments hs
  exact (nativePoleCompactInverseDerivative_continuous s
    (universalSincSecondKernel_contDiff hs).continuous).memLp_of_hasCompactSupport
      (nativePoleCompactInverseDerivative_hasCompactSupport hs.le
        (fun y hy => universalSincSecondKernel_zero_outside hs hy) hm.1 hm.2)

theorem originalSincCompactPotentialSecondDerivative_memLp_two {s : ℝ} (hs : 0 < s) :
    MemLp (deriv (deriv (originalSincCompactPotential s))) 2 volume := by
  have heq : deriv (deriv (originalSincCompactPotential s)) =
      fun x => (1 / 4 : ℂ) * originalSincCompactPotential s x + universalSincSecondKernel s x := by
    funext x
    have h := originalSincCompactPotential_pole_equation hs x
    exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)
  rw [heq]
  have hj : MemLp (universalSincSecondKernel s) 2 volume :=
    (universalSincSecondKernel_contDiff hs).continuous.memLp_of_hasCompactSupport
      (universalSincSecondKernel_hasCompactSupport hs)
  exact ((originalSincCompactPotential_memLp_two hs).const_mul (1 / 4 : ℂ)).add hj

end Zeta23.CCM

#print axioms Zeta23.CCM.universalSincSecondKernel_elementary_moments
#print axioms Zeta23.CCM.originalSincCompactPotential_pole_equation
#print axioms Zeta23.CCM.originalSincCompactPotential_hasCompactSupport
#print axioms Zeta23.CCM.originalSincCompactPotential_clamped_traces
#print axioms Zeta23.CCM.originalSincCompactPotential_memLp_two
#print axioms Zeta23.CCM.originalSincCompactPotentialDerivative_memLp_two
#print axioms Zeta23.CCM.originalSincCompactPotentialSecondDerivative_memLp_two
