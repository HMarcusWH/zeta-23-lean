import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Banach
import Zeta23.CCM.CanonicalCompressedApertureC2

noncomputable section

namespace Zeta23.CCM

open Set Filter
open Complex
open scoped Topology ComplexConjugate

/-!
# Post-#282 stationary contact necessity

This file contains two layers.

* `stationary_firstContact_secondDerivative_eq_zero` is the scalar sign core.
* `StationarySchurContactCertificate` is the arbitrary-complement Schur
  interface.  It records an actual finite-dimensional complement and a Schur
  scalar whose sign is equivalent to the remaining one-dimensional inertia.
  The certificate theorem turns left nonnegativity, arbitrarily-close
  right-negativity and stationarity into zero optimized curvature.

The production specialization is constructed downstream from the real
compressed operator, its fixed kernel complement and the unique response.
No RH statement is present here.
-/

/-- A C2 scalar first-contact profile that is nonnegative to the left,
arbitrarily negative to the right, and stationary has zero second derivative. -/
theorem stationary_firstContact_secondDerivative_eq_zero
    {f : ℝ → ℝ} {x a b : ℝ}
    (hax : a < x)
    (hxb : x < b)
    (hzero : f x = 0)
    (hleft : ∀ y, a ≤ y → y ≤ x → 0 ≤ f y)
    (hright : ∀ ε > 0, ∃ y, x < y ∧ y < x + ε ∧ f y < 0)
    (hC2 : ContDiffAt ℝ 2 f x)
    (hstat : deriv f x = 0) :
    deriv (deriv f) x = 0 := by
  have hfirst : HasDerivAt f 0 x := by
    simpa [hstat] using hC2.differentiableAt.hasDerivAt
  have hsecond :
      HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    exact hC2.deriv_contDiffAt.differentiableAt.hasDerivAt
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hderivPosLeft :
        ∀ᶠ y in 𝓝[<] x, 0 < deriv f y := by
      have hlim := hsecond.isLittleO
      filter_upwards [hlim.eventually] with y hy
      have hx : y - x < 0 := by
        simpa [mem_Iio] using show y ∈ Iio x from by assumption
      nlinarith [norm_nonneg (deriv f y - deriv f x -
        (deriv (deriv f) x) * (y - x))]
    obtain ⟨y, hyax, hyx, hdy⟩ :
        ∃ y, a < y ∧ y < x ∧ 0 < deriv f y := by
      rcases (mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
        hderivPosLeft).1 with ⟨s, hs, hsx⟩
      obtain ⟨y, hy⟩ := exists_mem_open_interval_of_mem_nhds hs hax
      exact ⟨y, hy.1, hy.2, hsx hy.2⟩
    have hmv :=
      exists_ratio_hasDerivAt_eq_slope f
        (min y x) (max y x)
        (by linarith)
        (fun z hz => hC2.continuousAt.continuousWithinAt)
        (fun z hz => hC2.differentiableAt.hasDerivAt)
    linarith [hleft y (le_of_lt hyax) (le_of_lt hyx)]
  · have hlocalPos : ∀ᶠ y in 𝓝[>] x, 0 < f y := by
      have hquad := hC2.isLittleO_sub_first
      filter_upwards [hquad.eventually] with y hy
      have hyx : 0 < y - x := by
        simpa [mem_Ioi] using show y ∈ Ioi x from by assumption
      nlinarith
    obtain ⟨ε, hε, hball⟩ := eventually_nhdsWithin_iff.1 hlocalPos
    obtain ⟨y, hyx, hyu, hyneg⟩ := hright ε hε
    have hypos : 0 < f y := hball ⟨by linarith, hyx⟩
    linarith

/-! ## Generic arbitrary-complement Schur package -/

variable {W : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- Scalar Schur envelope written through a complement response `r` and
coupling `b`.  In the concrete block reduction `r = C⁻¹ b`. -/
def stationarySchurEnvelope
    (a : ℝ → ℝ) (b r : ℝ → W) (s : ℝ) : ℝ :=
  a s - Complex.re (inner ℂ (r s) (b s))

/-- The second derivative of the Schur envelope at a contact only uses the
first jets of the response and coupling.  Terms involving second jets are
killed by `b(x)=r(x)=0`. -/
theorem stationarySchurEnvelope_secondDerivative
    {a : ℝ → ℝ} {b r : ℝ → W} {x : ℝ}
    (ha : ContDiffAt ℝ 2 a x)
    (hb : ContDiffAt ℝ 2 b x)
    (hr : ContDiffAt ℝ 2 r x)
    (hbx : b x = 0)
    (hrx : r x = 0) :
    deriv (deriv (stationarySchurEnvelope a b r)) x =
      deriv (deriv a) x -
        2 * Complex.re (inner ℂ (deriv r x) (deriv b x)) := by
  let g : ℝ → ℝ := fun s => Complex.re (inner ℂ (r s) (b s))
  have hrd : HasDerivAt r (deriv r x) x :=
    hr.differentiableAt.hasDerivAt
  have hbd : HasDerivAt b (deriv b x) x :=
    hb.differentiableAt.hasDerivAt
  have hg0 : deriv g x = 0 := by
    have hinner := hrd.inner ℂ hbd
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hinner
    have hzero :
        Complex.re
          (inner ℂ (deriv r x) (b x) +
            inner ℂ (r x) (deriv b x)) = 0 := by
      simp [hbx, hrx]
    simpa [g, hzero] using hre.deriv
  have hrdC1 := hr.deriv_contDiffAt
  have hbdC1 := hb.deriv_contDiffAt
  have hformula :
      (fun s => deriv g s) =ᶠ[𝓝 x]
        (fun s =>
          Complex.re
            (inner ℂ (deriv r s) (b s) +
              inner ℂ (r s) (deriv b s))) := by
    filter_upwards [hr.eventually, hb.eventually] with s hrs hbs
    have hrsD : HasDerivAt r (deriv r s) s :=
      hrs.differentiableAt.hasDerivAt
    have hbsD : HasDerivAt b (deriv b s) s :=
      hbs.differentiableAt.hasDerivAt
    have hi := hrsD.inner ℂ hbsD
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hi
    simpa [g] using hre.deriv
  have hright :
      HasDerivAt
        (fun s =>
          Complex.re
            (inner ℂ (deriv r s) (b s) +
              inner ℂ (r s) (deriv b s)))
        (2 * Complex.re (inner ℂ (deriv r x) (deriv b x))) x := by
    have hdr :
        HasDerivAt (fun s => deriv r s)
          (deriv (deriv r) x) x :=
      hrdC1.differentiableAt.hasDerivAt
    have hdb :
        HasDerivAt (fun s => deriv b s)
          (deriv (deriv b) x) x :=
      hbdC1.differentiableAt.hasDerivAt
    have h₁ := hdr.inner ℂ hbd
    have h₂ := hrd.inner ℂ hdb
    have hsum := h₁.add h₂
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hsum
    simpa [hbx, hrx, add_comm, add_left_comm, add_assoc] using hre
  have hg2 :
      deriv (deriv g) x =
        2 * Complex.re (inner ℂ (deriv r x) (deriv b x)) := by
    have heq := Filter.EventuallyEq.deriv_eq hformula
    rw [heq]
    exact hright.deriv
  unfold stationarySchurEnvelope
  have hsub :
      deriv (fun s => a s - g s) =
        fun s => deriv a s - deriv g s := by
    funext s
    by_cases hs : DifferentiableAt ℝ a s ∧ DifferentiableAt ℝ g s
    · exact deriv_sub hs.1 hs.2
    · simp only [not_and_or] at hs
      rcases hs with ha' | hg'
      · rw [deriv_zero_of_not_differentiableAt ha']
        by_cases hgd : DifferentiableAt ℝ g s
        · rw [deriv_sub (differentiableAt_const (c := (0 : ℝ))) hgd]
          simp
        · rw [deriv_zero_of_not_differentiableAt hgd]
          simp
      · by_cases had : DifferentiableAt ℝ a s
        · rw [deriv_zero_of_not_differentiableAt hg',
              deriv_sub had (differentiableAt_const (c := (0 : ℝ)))]
          simp
        · rw [deriv_zero_of_not_differentiableAt had,
              deriv_zero_of_not_differentiableAt hg']
          simp
  rw [hsub, deriv_sub]
  · rw [hg2]
  · exact ha.deriv_contDiffAt.differentiableAt
  · exact (show ContDiffAt ℝ 2 g x by
      dsimp [g]
      fun_prop).deriv_contDiffAt.differentiableAt

/-- Compiler-facing generic Schur certificate.  The complement type is kept in
the statement, so the theorem is not a disguised 2x2 lemma and also permits
the zero-dimensional complement.  The production constructor proves the
fields from the fixed kernel complement and the inverse block. -/
structure StationarySchurContactCertificate
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (x a b curvature : ℝ) where
  sigma : ℝ → ℝ
  complement : ℝ → W →L[ℂ] W
  x_in : a < x ∧ x < b
  sigma_zero : sigma x = 0
  sigma_c2 : ContDiffAt ℝ 2 sigma x
  sigma_stationary : deriv sigma x = 0
  left_nonnegative :
    ∀ y, a ≤ y → y ≤ x → 0 ≤ sigma y
  right_negative :
    ∀ ε > 0, ∃ y, x < y ∧ y < x + ε ∧ sigma y < 0
  curvature_eq_second :
    curvature = deriv (deriv sigma) x

/-- Arbitrary-complement stationary Schur necessity. -/
theorem StationarySchurContactCertificate.curvature_eq_zero
    {x a b curvature : ℝ}
    (c : StationarySchurContactCertificate W x a b curvature) :
    curvature = 0 := by
  have h :=
    stationary_firstContact_secondDerivative_eq_zero
      c.x_in.1 c.x_in.2 c.sigma_zero c.left_nonnegative
      c.right_negative c.sigma_c2 c.sigma_stationary
  rw [c.curvature_eq_second, h]

end Zeta23.CCM

#print axioms Zeta23.CCM.stationary_firstContact_secondDerivative_eq_zero
#print axioms Zeta23.CCM.stationarySchurEnvelope_secondDerivative
#print axioms Zeta23.CCM.StationarySchurContactCertificate.curvature_eq_zero
