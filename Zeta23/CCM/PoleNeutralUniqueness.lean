import Zeta23.CCM.OriginalSincCompactPotential
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniqueness for the elementary pole equation

Two integrating factors prove that a C2 solution of h''-h/4=0 with
vanishing value and first derivative at one point is zero. Consequently
the actual finite-primitive potential of j=P²q is the literal kernel k=Pq:
both solve the same equation and their clamped jets follow from support.

No uniqueness, inverse identity, or derivative trace is a caller premise
in the actual-source identification. Operator norm bounds and the native
forcing bridge remain separate obligations.
-/

noncomputable section

open Set
open scoped Topology

namespace Zeta23.CCM

private theorem hasDerivAt_uniquenessExponential (r x : ℝ) :
    HasDerivAt (nativePoleExponential r)
      ((r : ℂ) * nativePoleExponential r x) x := by
  have h := (((hasDerivAt_id x).const_mul r).exp).ofReal_comp
  simpa only [nativePoleExponential, mul_one, Complex.ofReal_mul, mul_comm] using h

private theorem uniquenessExponential_ne_zero (r x : ℝ) :
    nativePoleExponential r x ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (r * x))

/-- C2 homogeneous solutions with clamped jets at one point vanish. -/
theorem poleNeutral_homogeneous_eq_zero {h : ℝ → ℂ} {x0 : ℝ}
    (hh : ContDiff ℝ 2 h)
    (heq : ∀ x : ℝ, deriv (deriv h) x - (1 / 4 : ℂ) * h x = 0)
    (hvalue : h x0 = 0) (hjet : deriv h x0 = 0) : h = 0 := by
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv h) := hh.differentiable_deriv_two
  let W : ℝ → ℂ := fun x => nativePoleExponential (-1 / 2) x *
    (deriv h x + (1 / 2 : ℂ) * h x)
  have hW (x : ℝ) : HasDerivAt W 0 x := by
    have hprod := (hasDerivAt_uniquenessExponential (-1 / 2) x).mul
      ((hdd x).hasDerivAt.add ((hd x).hasDerivAt.const_mul (1 / 2 : ℂ)))
    convert hprod using 1
    · rfl
    · dsimp only [W]
      push_cast
      symm
      linear_combination nativePoleExponential (-1 / 2) x * heq x
  have hWzero (x : ℝ) : W x = 0 := by
    have hconst := is_const_of_deriv_eq_zero
      (fun y => (hW y).differentiableAt) (fun y => (hW y).deriv) x x0
    simpa only [W, hvalue, hjet, mul_zero, add_zero] using hconst
  have hfirst (x : ℝ) : deriv h x + (1 / 2 : ℂ) * h x = 0 := by
    exact (mul_eq_zero.mp (hWzero x)).resolve_left
      (uniquenessExponential_ne_zero (-1 / 2) x)
  let V : ℝ → ℂ := fun x => nativePoleExponential (1 / 2) x * h x
  have hV (x : ℝ) : HasDerivAt V 0 x := by
    have hprod := (hasDerivAt_uniquenessExponential (1 / 2) x).mul (hd x).hasDerivAt
    convert hprod using 1
    · rfl
    · dsimp only [V]
      push_cast
      symm
      linear_combination nativePoleExponential (1 / 2) x * hfirst x
  funext x
  have hconst := is_const_of_deriv_eq_zero
    (fun y => (hV y).differentiableAt) (fun y => (hV y).deriv) x x0
  have hVzero : V x = 0 := by
    simpa only [V, hvalue, mul_zero] using hconst
  exact (mul_eq_zero.mp hVzero).resolve_left
    (uniquenessExponential_ne_zero (1 / 2) x)

/-- Equal forcing and equal clamped jets determine a C2 solution uniquely. -/
theorem poleNeutral_eq_of_clamped_jets {u v : ℝ → ℂ} {x0 : ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (heq : ∀ x : ℝ, deriv (deriv u) x - (1 / 4 : ℂ) * u x =
      deriv (deriv v) x - (1 / 4 : ℂ) * v x)
    (hvalue : u x0 = v x0) (hjet : deriv u x0 = deriv v x0) : u = v := by
  have huD : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hvD : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hfirst : deriv (fun x => u x - v x) = fun x => deriv u x - deriv v x := by
    funext x
    exact deriv_sub (huD x) (hvD x)
  have hsecond (x : ℝ) :
      deriv (deriv (fun y => u y - v y)) x =
        deriv (deriv u) x - deriv (deriv v) x := by
    rw [hfirst]
    exact deriv_sub (hu.differentiable_deriv_two x) (hv.differentiable_deriv_two x)
  have hzero : (fun x => u x - v x) = (0 : ℝ → ℂ) := by
    apply poleNeutral_homogeneous_eq_zero (hu.sub hv)
    · intro x
      rw [hsecond]
      linear_combination heq x
    · exact sub_eq_zero.mpr hvalue
    · rw [hfirst]
      exact sub_eq_zero.mpr hjet
  funext x
  exact sub_eq_zero.mp (congr_fun hzero x)

/-- The constructed compact potential of the actual j is k=Pq. Exact
support fills both clamped jets internally at the point s+1. -/
theorem originalSincCompactPotential_eq_universalSincKernel {s : ℝ} (hs : 0 < s) :
    originalSincCompactPotential s = universalSincKernel s := by
  have hsupport : tsupport (originalSincCompactPotential s) ⊆ Icc (-s) s := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hnot
    exact hx (originalSincCompactPotential_zero_outside hs hnot)
  have hout : s + 1 ∉ Icc (-s) s := by
    intro hmem
    linarith [hmem.2]
  have huout : s + 1 ∉ tsupport (originalSincCompactPotential s) :=
    fun hmem => hout (hsupport hmem)
  have hkout : s + 1 ∉ tsupport (universalSincKernel s) :=
    fun hmem => hout (universalSincKernel_support hs hmem)
  apply poleNeutral_eq_of_clamped_jets (x0 := s + 1)
    (originalSincCompactPotential_contDiff_two hs)
    ((universalSincKernel_contDiff hs).of_le (by norm_num))
  · intro x
    simpa only [universalSincSecondKernel, universalSincDifferential] using
      originalSincCompactPotential_pole_equation hs x
  · rw [image_eq_zero_of_notMem_tsupport huout, image_eq_zero_of_notMem_tsupport hkout]
  · rw [deriv_of_notMem_tsupport huout, deriv_of_notMem_tsupport hkout]

end Zeta23.CCM

#print axioms Zeta23.CCM.poleNeutral_homogeneous_eq_zero
#print axioms Zeta23.CCM.poleNeutral_eq_of_clamped_jets
#print axioms Zeta23.CCM.originalSincCompactPotential_eq_universalSincKernel
