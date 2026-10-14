import Zeta23.CCM.OriginalDetectorLocalDuality
import Zeta23.CCM.NativeOriginalExteriorHistory

/-!
# Four authentic signed original-prime histories: compact-inverse local duality

The native source field F_k is the actual fixed universal-sinc product
prime field.  The four physical arguments are precisely x-c, c-x,
L-x-c, and x+c-L, all on the same fixed original phase/aperture.

The compact inverse's clamped boundary values give local P-duality for
each of the four histories, WITHOUT global X∈L² and WITHOUT assuming
the desired pairing. Local integrability follows here from actual
continuity of the finite source and smoothness of the fixed field.
The identification P(F_k∘reflection)=X∘reflection and the final 16κ
estimate are independent subsequent mathematical obligations.
-/

noncomputable section

open MeasureTheory Set Complex

namespace Zeta23.CCM

/-- With a continuous physical source, the five local integrability
conditions of the actual weak-H2 inverse follow from ordinary continuity
on a finite interval; no L2 assumption on the prime observation. -/
theorem NativeCompactPoleH2.localP_duality_of_continuous
    {s : ℝ} {f F : ℝ → ℂ}
    (u : NativeCompactPoleH2 s f)
    (hf : Continuous f) (hF : ContDiff ℝ 2 F) :
    (∫ x in (-s)..s, f x * F x) =
      ∫ x in (-s)..s, u.value x *
        (deriv (deriv F) x - (1 / 4 : ℂ) * F x) := by
  have hFC : Continuous F := hF.continuous
  have hFd : Continuous (deriv F) := hF.continuous_deriv (by norm_num)
  have hFdd : Continuous (deriv (deriv F)) :=
    (hF.deriv').continuous_deriv (by norm_num)
  have h0 : IntervalIntegrable
      (fun x : ℝ => ((1 / 4 : ℂ) * u.value x + f x) * F x)
      volume (-s) s := by
    have h :
        Continuous (fun x : ℝ => ((1 / 4 : ℂ) * u.value x + f x) * F x) :=
      ((continuous_const.mul u.value_continuous).add hf).mul hFC
    exact h.intervalIntegrable _ _
  have h1 : IntervalIntegrable
      (fun x : ℝ => u.first x * deriv F x) volume (-s) s :=
    (u.first_continuous.mul hFd).intervalIntegrable _ _
  have h2 : IntervalIntegrable
      (fun x : ℝ => u.value x * deriv (deriv F) x) volume (-s) s :=
    (u.value_continuous.mul hFdd).intervalIntegrable _ _
  have hu : IntervalIntegrable (fun x : ℝ => u.value x * F x)
      volume (-s) s :=
    (u.value_continuous.mul hFC).intervalIntegrable _ _
  have hfI : IntervalIntegrable (fun x : ℝ => f x * F x)
      volume (-s) s :=
    (hf.mul hFC).intervalIntegrable _ _
  exact u.localP_duality hF h0 h1 h2 hu hfI

/-- The single actual unsifted prime field transfers to its P-image
on the same finite integration interval. The five integrability
assumptions are DISCHARGED by smoothness of the genuine finite source. -/
theorem NativeCompactPoleH2.originalKernelPrimeField_localPairing_of_continuous
    {s : ℝ} {f : ℝ → ℂ} (u : NativeCompactPoleH2 s f)
    (hf : Continuous f) :
    (∫ x in (-s)..s, f x * nativeOriginalKernelPrimeField x) =
      ∫ x in (-s)..s, u.value x * (nativeOriginalPrimeField x : ℂ) := by
  have hF : ContDiff ℝ 2 nativeOriginalKernelPrimeField :=
    nativeOriginalKernelPrimeField_contDiff.of_le le_top
  rw [u.localP_duality_of_continuous hf hF]
  apply intervalIntegral.integral_congr
  intro x _
  have hP := congrFun nativeOriginalKernelPrimeField_poleImage x
  change deriv (deriv nativeOriginalKernelPrimeField) x -
      (1 / 4 : ℂ) * nativeOriginalKernelPrimeField x =
      (nativeOriginalPrimeField x : ℂ) at hP
  change u.value x * (deriv (deriv nativeOriginalKernelPrimeField) x -
      (1 / 4 : ℂ) * nativeOriginalKernelPrimeField x) =
    u.value x * (nativeOriginalPrimeField x : ℂ)
  exact congrArg (fun z : ℂ => u.value x * z) hP

/-- Four original reflected prime-history components, each with its
actual compact P-duality. Nothing asserts that the interior response
vanishes or that the original detector equals the chosen eigenvector. -/
theorem NativeCompactPoleH2.originalFourHistories_localP_dualities
    {s : ℝ} {f : ℝ → ℂ} (u : NativeCompactPoleH2 s f)
    (hf : Continuous f) (a : ℝ) :
    let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
    let c := Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter
    let F := nativeOriginalKernelPrimeField
    (∫ x in (-s)..s, f x * F (x - c)) =
      ∫ x in (-s)..s, u.value x *
        (deriv (deriv (fun t : ℝ => F (t - c))) x -
          (1 / 4 : ℂ) * F (x - c)) ∧
    (∫ x in (-s)..s, f x * F (c - x)) =
      ∫ x in (-s)..s, u.value x *
        (deriv (deriv (fun t : ℝ => F (c - t))) x -
          (1 / 4 : ℂ) * F (c - x)) ∧
    (∫ x in (-s)..s, f x * F (L - x - c)) =
      ∫ x in (-s)..s, u.value x *
        (deriv (deriv (fun t : ℝ => F (L - t - c))) x -
          (1 / 4 : ℂ) * F (L - x - c)) ∧
    (∫ x in (-s)..s, f x * F (x + c - L)) =
      ∫ x in (-s)..s, u.value x *
        (deriv (deriv (fun t : ℝ => F (t + c - L))) x -
          (1 / 4 : ℂ) * F (x + c - L)) := by
  dsimp only
  let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
  let c := Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter
  have hF : ContDiff ℝ 2 nativeOriginalKernelPrimeField :=
    nativeOriginalKernelPrimeField_contDiff.of_le le_top
  have h1 : ContDiff ℝ 2
      (fun t : ℝ => nativeOriginalKernelPrimeField (t - c)) :=
    hF.comp (by fun_prop)
  have h2 : ContDiff ℝ 2
      (fun t : ℝ => nativeOriginalKernelPrimeField (c - t)) :=
    hF.comp (by fun_prop)
  have h3 : ContDiff ℝ 2
      (fun t : ℝ => nativeOriginalKernelPrimeField (L - t - c)) :=
    hF.comp (by fun_prop)
  have h4 : ContDiff ℝ 2
      (fun t : ℝ => nativeOriginalKernelPrimeField (t + c - L)) :=
    hF.comp (by fun_prop)
  exact ⟨u.localP_duality_of_continuous hf h1,
         u.localP_duality_of_continuous hf h2,
         u.localP_duality_of_continuous hf h3,
         u.localP_duality_of_continuous hf h4⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.NativeCompactPoleH2.localP_duality_of_continuous
#print axioms Zeta23.CCM.NativeCompactPoleH2.originalKernelPrimeField_localPairing_of_continuous
#print axioms Zeta23.CCM.NativeCompactPoleH2.originalFourHistories_localP_dualities
