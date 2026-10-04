import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.InnerProductSpace.Rayleigh
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

/-! ## Fixed kernel complement and actual Schur objects -/

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- The fixed complement used by the stationary Schur reduction.  It is the
kernel of the inner-product functional, avoiding a second orthogonal-submodule
instance stack. -/
def stationarySchurComplement (z : V) : Submodule ℂ V :=
  LinearMap.ker (innerₛₗ ℂ z)

/-- Compression of an operator to the fixed complement of `z`. -/
def stationarySchurBlock
    (F : ℝ → V →L[ℂ] V) (z : V) (s : ℝ) :
    stationarySchurComplement z →L[ℂ] stationarySchurComplement z :=
  let W := stationarySchurComplement z
  W.orthogonalProjectionOnto.comp
    ((F s).comp (W.subtypeL : W →L[ℂ] V))

/-- Complement component of `F(s) z`. -/
def stationarySchurCoupling
    (F : ℝ → V →L[ℂ] V) (z : V) (s : ℝ) :
    stationarySchurComplement z :=
  ⟨(stationarySchurComplement z).orthogonalProjection
      (F s z),
    (stationarySchurComplement z).orthogonalProjection_mem _⟩

/-- Totalized Schur response `C(s)⁻¹ b(s)`.  At an invertible block this is
the genuine inverse response; the totalized inverse keeps the definition
global while all theorem use is restricted to the invertible neighborhood. -/
def stationarySchurResponse
    (F : ℝ → V →L[ℂ] V) (z : V) (s : ℝ) :
    stationarySchurComplement z :=
  ContinuousLinearMap.inverse (stationarySchurBlock F z s)
    (stationarySchurCoupling F z s)

/-- Affine minimizer candidate `z - C⁻¹b` in the ambient carrier. -/
def stationarySchurVector
    (F : ℝ → V →L[ℂ] V) (z : V) (s : ℝ) : V :=
  z - (stationarySchurResponse F z s : V)

/-- Actual scalar Schur profile, defined as the family energy on the Schur
vector.  On an invertible positive complement it equals
`a - b* C⁻¹ b`. -/
def stationarySchurScalar
    (F : ℝ → V →L[ℂ] V) (z : V) (s : ℝ) : ℝ :=
  Complex.re
    (inner ℂ (F s (stationarySchurVector F z s))
      (stationarySchurVector F z s))

@[simp] theorem stationarySchurComplement_coe_mem
    (z : V) (w : stationarySchurComplement z) :
    inner ℂ z (w : V) = 0 := by
  exact w.property

/-- Symmetry and a kernel vector imply that `F w` stays in the fixed
complement. -/
theorem stationarySchur_map_mem_complement
    {F : V →L[ℂ] V} {z : V}
    (hF : LinearMap.IsSymmetric (𝕜 := ℂ) F.toLinearMap)
    (hz : F z = 0)
    (w : stationarySchurComplement z) :
    F (w : V) ∈ stationarySchurComplement z := by
  change inner ℂ z (F (w : V)) = 0
  rw [← hF z (w : V), hz, inner_zero_left]

/-- At a zero mode, the Schur coupling vanishes. -/
theorem stationarySchurCoupling_eq_zero_of_kernel
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hz : F x z = 0) :
    stationarySchurCoupling F z x = 0 := by
  apply Subtype.ext
  simp [stationarySchurCoupling, hz]

/-- At a zero mode the totalized Schur response is zero. -/
theorem stationarySchurResponse_eq_zero_of_kernel
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hz : F x z = 0) :
    stationarySchurResponse F z x = 0 := by
  unfold stationarySchurResponse
  rw [stationarySchurCoupling_eq_zero_of_kernel hz]
  exact map_zero _

@[simp] theorem stationarySchurVector_eq_kernel_of_kernel
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hz : F x z = 0) :
    stationarySchurVector F z x = z := by
  simp [stationarySchurVector,
    stationarySchurResponse_eq_zero_of_kernel hz]

theorem stationarySchurScalar_eq_zero_of_kernel
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hz : F x z = 0) :
    stationarySchurScalar F z x = 0 := by
  simp [stationarySchurScalar,
    stationarySchurVector_eq_kernel_of_kernel hz, hz]

/-- The complement block is injective at a simple zero mode.  No positivity
gap is assumed: symmetry plus `ker F = C z` already forces the restricted
kernel to be trivial. -/
theorem stationarySchurBlock_injective_of_kernel_line
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hznorm : ‖z‖ = 1)
    (hF : LinearMap.IsSymmetric (𝕜 := ℂ) (F x).toLinearMap)
    (hz : F x z = 0)
    (hker : ∀ v : V, F x v = 0 → ∃ a : ℂ, v = a • z) :
    Function.Injective (stationarySchurBlock F z x) := by
  intro u v huv
  apply sub_eq_zero.mp
  have hzero :
      stationarySchurBlock F z x (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  let w : stationarySchurComplement z := u - v
  have hmem :
      F x (w : V) ∈ stationarySchurComplement z :=
    stationarySchur_map_mem_complement hF hz w
  have hambient : F x (w : V) = 0 := by
    change
      (stationarySchurComplement z).orthogonalProjectionOnto
        (F x (w : V)) = 0 at hzero
    have hproj :
        (stationarySchurComplement z).orthogonalProjectionOnto
          (F x (w : V)) =
        ⟨F x (w : V), hmem⟩ := by
      apply Subtype.ext
      exact
        (stationarySchurComplement z).orthogonalProjection_eq_self.2 hmem
    rw [hproj] at hzero
    exact congrArg Subtype.val hzero
  obtain ⟨a, ha⟩ := hker (w : V) hambient
  have horth : inner ℂ z (w : V) = 0 := w.property
  rw [ha, inner_smul_right, inner_self_eq_norm_sq, hznorm] at horth
  simp at horth
  have ha0 : a = 0 := by simpa using horth
  apply Subtype.ext
  simp [w, ha, ha0]

/-- In finite dimension the simple-kernel complement block is invertible,
including the zero-dimensional complement. -/
theorem stationarySchurBlock_isInvertible_of_kernel_line
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hznorm : ‖z‖ = 1)
    (hF : LinearMap.IsSymmetric (𝕜 := ℂ) (F x).toLinearMap)
    (hz : F x z = 0)
    (hker : ∀ v : V, F x v = 0 → ∃ a : ℂ, v = a • z) :
    (stationarySchurBlock F z x).IsInvertible := by
  have hinj :=
    stationarySchurBlock_injective_of_kernel_line
      hznorm hF hz hker
  have hsurj : Function.Surjective (stationarySchurBlock F z x) :=
    LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective
    (stationarySchurBlock F z x)
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)⟩

/-- On an invertible block, the response solves the exact complement equation. -/
theorem stationarySchurBlock_response
    {F : ℝ → V →L[ℂ] V} {z : V} {s : ℝ}
    (hC : (stationarySchurBlock F z s).IsInvertible) :
    stationarySchurBlock F z s
        (stationarySchurResponse F z s) =
      stationarySchurCoupling F z s := by
  exact ContinuousLinearMap.IsInvertible.self_apply_inverse hC _

/-- The Schur vector has no complement residual: its image under `F` is
orthogonal to the fixed complement. -/
theorem stationarySchurVector_complement_residual_zero
    {F : ℝ → V →L[ℂ] V} {z : V} {s : ℝ}
    (hC : (stationarySchurBlock F z s).IsInvertible) :
    (stationarySchurComplement z).orthogonalProjectionOnto
        (F s (stationarySchurVector F z s)) = 0 := by
  rw [stationarySchurVector, map_sub]
  change
    stationarySchurCoupling F z s -
      stationarySchurBlock F z s
        (stationarySchurResponse F z s) = 0
  rw [stationarySchurBlock_response hC, sub_self]


/-! ## Actual block calculus and completed-square control -/

/-- Compression preserves pairings against vectors already in the fixed
complement. -/
theorem stationarySchurBlock_inner
    {F : ℝ → V →L[ℂ] V} {z : V} {s : ℝ}
    (u v : stationarySchurComplement z) :
    inner ℂ (stationarySchurBlock F z s u) v =
      inner ℂ (F s (u : V)) (v : V) := by
  change inner ℂ
      ((stationarySchurComplement z).orthogonalProjectionOnto
        (F s (u : V))) v =
    inner ℂ (F s (u : V)) (v : V)
  exact
    (stationarySchurComplement z).inner_orthogonalProjectionOnto_eq_of_mem_right
      v (F s (u : V))

/-- A symmetric ambient family has a symmetric fixed-complement block. -/
theorem stationarySchurBlock_isSymmetric
    {F : ℝ → V →L[ℂ] V} {z : V} {s : ℝ}
    (hF : LinearMap.IsSymmetric (𝕜 := ℂ) (F s).toLinearMap) :
    LinearMap.IsSymmetric (𝕜 := ℂ)
      (stationarySchurBlock F z s).toLinearMap := by
  intro u v
  rw [stationarySchurBlock_inner, stationarySchurBlock_inner]
  exact hF (u : V) (v : V)

/-- C2 regularity of the ambient family descends to the fixed complement
block. -/
theorem contDiffAt_stationarySchurBlock
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x) :
    ContDiffAt ℝ 2 (fun s => stationarySchurBlock F z s) x := by
  unfold stationarySchurBlock
  fun_prop

/-- C2 regularity of the ambient family descends to its fixed-complement
coupling. -/
theorem contDiffAt_stationarySchurCoupling
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x) :
    ContDiffAt ℝ 2 (fun s => stationarySchurCoupling F z s) x := by
  unfold stationarySchurCoupling
  fun_prop

/-- An invertible contact block remains invertible in a neighborhood. -/
theorem eventually_stationarySchurBlock_isInvertible
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x)
    (hC : (stationarySchurBlock F z x).IsInvertible) :
    ∀ᶠ s in 𝓝 x, (stationarySchurBlock F z s).IsInvertible := by
  have hcont :
      ContinuousAt (fun s => stationarySchurBlock F z s) x :=
    (contDiffAt_stationarySchurBlock hF).continuousAt
  exact hcont.eventually hC.eventually_nhds

/-- The totalized inverse response is genuinely C2 at every point where the
contact block is invertible. -/
theorem contDiffAt_stationarySchurResponse
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x)
    (hC : (stationarySchurBlock F z x).IsInvertible) :
    ContDiffAt ℝ 2 (fun s => stationarySchurResponse F z s) x := by
  have hblock := contDiffAt_stationarySchurBlock hF
  have hcoupling := contDiffAt_stationarySchurCoupling hF
  have hinv0 :
      ContDiffAt ℂ 2
        (ContinuousLinearMap.inverse :
          (stationarySchurComplement z →L[ℂ] stationarySchurComplement z) →
            (stationarySchurComplement z →L[ℂ] stationarySchurComplement z))
        (stationarySchurBlock F z x) :=
    hC.contDiffAt_map_inverse
  have hinvR :
      ContDiffAt ℝ 2
        (ContinuousLinearMap.inverse :
          (stationarySchurComplement z →L[ℂ] stationarySchurComplement z) →
            (stationarySchurComplement z →L[ℂ] stationarySchurComplement z))
        (stationarySchurBlock F z x) :=
    hinv0.restrict_scalars ℝ
  have hinv :
      ContDiffAt ℝ 2
        (fun s => ContinuousLinearMap.inverse (stationarySchurBlock F z s)) x :=
    hinvR.comp x hblock
  simpa [stationarySchurResponse] using hinv.clm_apply hcoupling

theorem contDiffAt_stationarySchurVector
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x)
    (hC : (stationarySchurBlock F z x).IsInvertible) :
    ContDiffAt ℝ 2 (fun s => stationarySchurVector F z s) x := by
  unfold stationarySchurVector
  fun_prop

/-- The actual scalar Schur profile is C2 whenever the ambient family is C2
and the contact complement is invertible. -/
theorem contDiffAt_stationarySchurScalar
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x)
    (hC : (stationarySchurBlock F z x).IsInvertible) :
    ContDiffAt ℝ 2 (fun s => stationarySchurScalar F z s) x := by
  have hv := contDiffAt_stationarySchurVector hF hC
  have hFv := hF.clm_apply hv
  have hi := hFv.inner ℂ hv
  exact Complex.reCLM.contDiff.contDiffAt.comp x hi

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


/-! ## Identification of the actual scalar with the envelope -/

/-- The Schur response equation identifies the actual energy of the Schur
vector with the scalar envelope. -/
theorem stationarySchurScalar_eq_envelope
    {F : ℝ → V →L[ℂ] V} {z : V} {s : ℝ}
    (hFsym : LinearMap.IsSymmetric (𝕜 := ℂ) (F s).toLinearMap)
    (hC : (stationarySchurBlock F z s).IsInvertible) :
    stationarySchurScalar F z s =
      stationarySchurEnvelope
        (fun t => Complex.re (inner ℂ (F t z) z))
        (fun t => stationarySchurCoupling F z t)
        (fun t => stationarySchurResponse F z t) s := by
  let r := stationarySchurResponse F z s
  have hr :
      stationarySchurBlock F z s r =
        stationarySchurCoupling F z s :=
    stationarySchurBlock_response hC
  have hzr :
      inner ℂ (F s z) (r : V) =
        inner ℂ (stationarySchurCoupling F z s) r := by
    rw [← (stationarySchurComplement z)
      .inner_orthogonalProjectionOnto_eq_of_mem_right r (F s z)]
    rfl
  have hrz :
      inner ℂ (F s (r : V)) z =
        inner ℂ (r : V) (F s z) := hFsym (r : V) z
  have hrr :
      inner ℂ (F s (r : V)) (r : V) =
        inner ℂ (stationarySchurCoupling F z s) r := by
    rw [← stationarySchurBlock_inner (F := F) (z := z) (s := s) r r, hr]
  unfold stationarySchurScalar stationarySchurVector stationarySchurEnvelope
  simp only [map_sub, inner_sub_left, inner_sub_right, Complex.sub_re]
  rw [hzr, hrz, hrr]
  rw [inner_conj_symm (x := (r : V)) (y := F s z)]
  simp only [map_sub, Complex.sub_re, map_add, map_mul, Complex.conj_re]
  ring

/-- Near a simple contact the actual Schur scalar and the envelope agree
eventually, because the complement block stays invertible. -/
theorem eventually_stationarySchurScalar_eq_envelope
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x)
    (hFsym : ∀ᶠ s in 𝓝 x,
      LinearMap.IsSymmetric (𝕜 := ℂ) (F s).toLinearMap)
    (hC : (stationarySchurBlock F z x).IsInvertible) :
    (fun s => stationarySchurScalar F z s) =ᶠ[𝓝 x]
      stationarySchurEnvelope
        (fun s => Complex.re (inner ℂ (F s z) z))
        (fun s => stationarySchurCoupling F z s)
        (fun s => stationarySchurResponse F z s) := by
  have hCev := eventually_stationarySchurBlock_isInvertible hF hC
  filter_upwards [hFsym, hCev] with s hs hCs
  exact stationarySchurScalar_eq_envelope hs hCs

/-- At a zero mode the first Schur derivative is exactly the fixed-vector
first derivative. -/
theorem stationarySchurScalar_firstDerivative_eq_fixed
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x)
    (hFsym : ∀ᶠ s in 𝓝 x,
      LinearMap.IsSymmetric (𝕜 := ℂ) (F s).toLinearMap)
    (hz : F x z = 0)
    (hC : (stationarySchurBlock F z x).IsInvertible) :
    deriv (fun s => stationarySchurScalar F z s) x =
      deriv (fun s => Complex.re (inner ℂ (F s z) z)) x := by
  let a : ℝ → ℝ := fun s => Complex.re (inner ℂ (F s z) z)
  let b : ℝ → stationarySchurComplement z :=
    fun s => stationarySchurCoupling F z s
  let r : ℝ → stationarySchurComplement z :=
    fun s => stationarySchurResponse F z s
  have heq :
      (fun s => stationarySchurScalar F z s) =ᶠ[𝓝 x]
        stationarySchurEnvelope a b r := by
    simpa [a, b, r] using
      eventually_stationarySchurScalar_eq_envelope hF hFsym hC
  have ha : ContDiffAt ℝ 2 a x := by
    dsimp [a]
    fun_prop
  have hb : ContDiffAt ℝ 2 b x := by
    simpa [b] using contDiffAt_stationarySchurCoupling hF
  have hr : ContDiffAt ℝ 2 r x := by
    simpa [r] using contDiffAt_stationarySchurResponse hF hC
  have hbx : b x = 0 := by
    simpa [b] using stationarySchurCoupling_eq_zero_of_kernel hz
  have hrx : r x = 0 := by
    simpa [r] using stationarySchurResponse_eq_zero_of_kernel hz
  have hpairD :=
    (hr.differentiableAt.hasDerivAt).inner ℂ
      (hb.differentiableAt.hasDerivAt)
  have hreD :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hpairD
  have hpair0 :
      deriv (fun s => Complex.re (inner ℂ (r s) (b s))) x = 0 := by
    rw [hreD.deriv]
    simp [hbx, hrx]
  have henv :
      deriv (stationarySchurEnvelope a b r) x = deriv a x := by
    unfold stationarySchurEnvelope
    rw [deriv_sub ha.differentiableAt
      (by
        exact
          (show ContDiffAt ℝ 2
            (fun s => Complex.re (inner ℂ (r s) (b s))) x by
              fun_prop).differentiableAt),
      hpair0, sub_zero]
  rw [Filter.EventuallyEq.deriv_eq heq, henv]
  rfl


/-! ## Contact jets of the inverse response -/

theorem deriv_stationarySchurCoupling
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x) :
    deriv (fun s => stationarySchurCoupling F z s) x =
      (stationarySchurComplement z).orthogonalProjectionOnto
        ((deriv F x) z) := by
  have hFz :=
    (hF.differentiableAt.hasDerivAt).clm_apply
      (hasDerivAt_const x z)
  have hp :=
    (stationarySchurComplement z).orthogonalProjectionOnto.hasFDerivAt
      |>.comp_hasDerivAt x hFz
  simpa [stationarySchurCoupling] using hp.deriv

/-- Differentiating the exact inverse-block equation at a zero mode. -/
theorem stationarySchurBlock_response_deriv
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x)
    (hz : F x z = 0)
    (hC : (stationarySchurBlock F z x).IsInvertible) :
    stationarySchurBlock F z x
        (deriv (fun s => stationarySchurResponse F z s) x) =
      deriv (fun s => stationarySchurCoupling F z s) x := by
  have hCev := eventually_stationarySchurBlock_isInvertible hF hC
  have heq :
      (fun s =>
        stationarySchurBlock F z s
          (stationarySchurResponse F z s)) =ᶠ[𝓝 x]
        (fun s => stationarySchurCoupling F z s) := by
    filter_upwards [hCev] with s hs
    exact stationarySchurBlock_response hs
  have hblockD :=
    (contDiffAt_stationarySchurBlock hF).differentiableAt.hasDerivAt
  have hrespD :=
    (contDiffAt_stationarySchurResponse hF hC).differentiableAt.hasDerivAt
  have hlhs := hblockD.clm_apply hrespD
  have hrhs :=
    (contDiffAt_stationarySchurCoupling hF).differentiableAt.hasDerivAt
  have hlhs' := hlhs.congr_of_eventuallyEq heq
  have hcoeff := hlhs'.unique hrhs
  have hr0 := stationarySchurResponse_eq_zero_of_kernel hz
  simpa [hr0] using hcoeff

/-- Symmetry is inherited by the real aperture derivative of a differentiable
family. -/
theorem deriv_isSymmetric_of_eventually
    {F : ℝ → V →L[ℂ] V} {x : ℝ}
    (hF : DifferentiableAt ℝ F x)
    (hsym : ∀ᶠ s in 𝓝 x,
      LinearMap.IsSymmetric (𝕜 := ℂ) (F s).toLinearMap) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (deriv F x).toLinearMap := by
  intro u v
  have hFu :=
    (hF.hasDerivAt.clm_apply (hasDerivAt_const x u)).inner ℂ
      (hasDerivAt_const x v)
  have hFv :=
    (hasDerivAt_const x u).inner ℂ
      (hF.hasDerivAt.clm_apply (hasDerivAt_const x v))
  have heq :
      (fun s => inner ℂ (F s u) v) =ᶠ[𝓝 x]
        (fun s => inner ℂ u (F s v)) := by
    filter_upwards [hsym] with s hs
    exact hs u v
  exact (hFu.congr_of_eventuallyEq heq).unique hFv

/-- The derivative of the inverse response is the negative stationary
eigenbranch response. -/
theorem deriv_stationarySchurResponse_eq_neg
    {F : ℝ → V →L[ℂ] V} {z w : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x)
    (hFsym : LinearMap.IsSymmetric (𝕜 := ℂ) (F x).toLinearMap)
    (hz : F x z = 0)
    (hznorm : ‖z‖ = 1)
    (hker : ∀ v : V, F x v = 0 → ∃ a : ℂ, v = a • z)
    (hwperp : inner ℂ z w = 0)
    (hw : F x w = -((deriv F x) z)) :
    ((deriv (fun s => stationarySchurResponse F z s) x :
        stationarySchurComplement z) : V) = -w := by
  have hC :=
    stationarySchurBlock_isInvertible_of_kernel_line
      hznorm hFsym hz hker
  have hresp :=
    stationarySchurBlock_response_deriv hF hz hC
  let ww : stationarySchurComplement z := ⟨w, hwperp⟩
  have hcandidate :
      stationarySchurBlock F z x (-ww) =
        deriv (fun s => stationarySchurCoupling F z s) x := by
    apply Subtype.ext
    rw [deriv_stationarySchurCoupling hF]
    change
      (stationarySchurComplement z).orthogonalProjectionOnto
          (F x (-w)) =
        (stationarySchurComplement z).orthogonalProjectionOnto
          ((deriv F x) z)
    rw [map_neg, hw, neg_neg]
  have hinj :=
    stationarySchurBlock_injective_of_kernel_line
      hznorm hFsym hz hker
  have heq :
      deriv (fun s => stationarySchurResponse F z s) x = -ww :=
    hinj (hresp.trans hcandidate.symm)
  exact congrArg Subtype.val heq

/-- Fixed-vector energy has the expected second aperture derivative. -/
theorem stationaryFixedEnergy_secondDerivative
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x) :
    deriv (deriv (fun s => Complex.re (inner ℂ (F s z) z))) x =
      Complex.re (inner ℂ ((deriv (deriv F) x) z) z) := by
  let a : ℝ → ℝ := fun s => Complex.re (inner ℂ (F s z) z)
  let a1 : ℝ → ℝ := fun s =>
    Complex.re (inner ℂ ((deriv F s) z) z)
  have hformula : deriv a =ᶠ[𝓝 x] a1 := by
    filter_upwards [hF.eventually] with s hs
    have hFz :=
      (hs.differentiableAt.hasDerivAt).clm_apply
        (hasDerivAt_const s z)
    have hi := hFz.inner ℂ (hasDerivAt_const s z)
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hi
    simpa [a, a1] using hre.deriv
  have hFd := hF.deriv_contDiffAt
  have hFdz :=
    (hFd.differentiableAt.hasDerivAt).clm_apply
      (hasDerivAt_const x z)
  have hi := hFdz.inner ℂ (hasDerivAt_const x z)
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hi
  have ha1 :
      deriv a1 x =
        Complex.re (inner ℂ ((deriv (deriv F) x) z) z) := by
    simpa [a1] using hre.deriv
  rw [Filter.EventuallyEq.deriv_eq hformula, ha1]
  rfl

/-- The actual Schur scalar has the optimized second derivative associated
with the unique perpendicular response. -/
theorem stationarySchurScalar_secondDerivative_eq_pair
    {F : ℝ → V →L[ℂ] V} {z w : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x)
    (hFsym : ∀ᶠ s in 𝓝 x,
      LinearMap.IsSymmetric (𝕜 := ℂ) (F s).toLinearMap)
    (hz : F x z = 0)
    (hznorm : ‖z‖ = 1)
    (hker : ∀ v : V, F x v = 0 → ∃ a : ℂ, v = a • z)
    (hwperp : inner ℂ z w = 0)
    (hw : F x w = -((deriv F x) z)) :
    deriv (deriv (fun s => stationarySchurScalar F z s)) x =
      Complex.re (inner ℂ ((deriv (deriv F) x) z) z) +
        2 * Complex.re (inner ℂ ((deriv F x) w) z) := by
  have hFsymx := hFsym.self_of_nhds
  have hC :=
    stationarySchurBlock_isInvertible_of_kernel_line
      hznorm hFsymx hz hker
  let a : ℝ → ℝ := fun s => Complex.re (inner ℂ (F s z) z)
  let b : ℝ → stationarySchurComplement z :=
    fun s => stationarySchurCoupling F z s
  let r : ℝ → stationarySchurComplement z :=
    fun s => stationarySchurResponse F z s
  have heq :
      (fun s => stationarySchurScalar F z s) =ᶠ[𝓝 x]
        stationarySchurEnvelope a b r := by
    simpa [a, b, r] using
      eventually_stationarySchurScalar_eq_envelope hF hFsym hC
  have ha : ContDiffAt ℝ 2 a x := by
    dsimp [a]
    fun_prop
  have hb : ContDiffAt ℝ 2 b x := by
    simpa [b] using contDiffAt_stationarySchurCoupling hF
  have hr : ContDiffAt ℝ 2 r x := by
    simpa [r] using contDiffAt_stationarySchurResponse hF hC
  have hbx : b x = 0 := by
    simpa [b] using stationarySchurCoupling_eq_zero_of_kernel hz
  have hrx : r x = 0 := by
    simpa [r] using stationarySchurResponse_eq_zero_of_kernel hz
  have henv :=
    stationarySchurEnvelope_secondDerivative ha hb hr hbx hrx
  have hrder :
      ((deriv r x : stationarySchurComplement z) : V) = -w := by
    simpa [r] using
      deriv_stationarySchurResponse_eq_neg
        hF hFsymx hz hznorm hker hwperp hw
  have hbder :
      deriv b x =
        (stationarySchurComplement z).orthogonalProjectionOnto
          ((deriv F x) z) := by
    simpa [b] using deriv_stationarySchurCoupling hF
  have hsymd :=
    deriv_isSymmetric_of_eventually hF.differentiableAt hFsym
  have hpair :
      Complex.re (inner ℂ (deriv r x) (deriv b x)) =
        -Complex.re (inner ℂ ((deriv F x) w) z) := by
    rw [hbder]
    have hp :
        inner ℂ (deriv r x)
            ((stationarySchurComplement z).orthogonalProjectionOnto
              ((deriv F x) z)) =
          inner ℂ ((deriv r x : stationarySchurComplement z) : V)
            ((deriv F x) z) := by
      exact
        (stationarySchurComplement z)
          .inner_orthogonalProjectionOnto_eq_of_mem_left
            (deriv r x) ((deriv F x) z)
    rw [hp, hrder, inner_neg_left, Complex.neg_re]
    rw [hsymd w z]
  have ha2 :
      deriv (deriv a) x =
        Complex.re (inner ℂ ((deriv (deriv F) x) z) z) := by
    simpa [a] using stationaryFixedEnergy_secondDerivative hF
  rw [← Filter.EventuallyEq.deriv_eq
      (Filter.EventuallyEq.deriv_eq heq)]
  rw [henv, ha2, hpair]
  ring


/-! ## Exact arbitrary-dimensional inertia decomposition -/

/-- Exact completed-square decomposition with an arbitrary finite-dimensional
fixed complement.  The complement can be zero-dimensional. -/
theorem stationarySchur_completedSquare
    {F : ℝ → V →L[ℂ] V} {z : V} {s : ℝ}
    (hFsym : LinearMap.IsSymmetric (𝕜 := ℂ) (F s).toLinearMap)
    (hC : (stationarySchurBlock F z s).IsInvertible)
    (α : ℂ) (w : stationarySchurComplement z) :
    Complex.re
        (inner ℂ
          (F s (α • z + (w : V)))
          (α • z + (w : V))) =
      ‖α‖ ^ 2 * stationarySchurScalar F z s +
        Complex.re
          (inner ℂ
            (stationarySchurBlock F z s
              (w + α • stationarySchurResponse F z s))
            (w + α • stationarySchurResponse F z s)) := by
  let r := stationarySchurResponse F z s
  let q := stationarySchurVector F z s
  let u : stationarySchurComplement z := w + α • r
  have hres :=
    stationarySchurVector_complement_residual_zero
      (F := F) (z := z) (s := s) hC
  have hcross :
      inner ℂ (F s q) (u : V) = 0 := by
    rw [← (stationarySchurComplement z)
      .inner_orthogonalProjectionOnto_eq_of_mem_right u (F s q)]
    rw [hres]
    simp
  have hcross' :
      inner ℂ (F s (u : V)) q = 0 := by
    rw [hFsym]
    exact hcross
  have hdecomp :
      α • z + (w : V) = α • q + (u : V) := by
    dsimp [q, u, r, stationarySchurVector]
    simp only [smul_sub, Submodule.coe_add, Submodule.coe_smul]
    abel
  rw [hdecomp, map_add, inner_add_left, inner_add_right]
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp only [hcross, hcross', mul_zero, zero_mul, add_zero, zero_add,
    Complex.add_re]
  have hquad :
      Complex.re
        (star α * (inner ℂ (F s q) q * α)) =
        ‖α‖ ^ 2 * stationarySchurScalar F z s := by
    have hnorm : star α * α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']
      norm_cast
    rw [← mul_assoc, hnorm]
    simp [stationarySchurScalar, q]
  rw [hquad]
  have hu :
      Complex.re (inner ℂ (F s (u : V)) (u : V)) =
        Complex.re
          (inner ℂ (stationarySchurBlock F z s u) u) := by
    rw [stationarySchurBlock_inner]
  rw [hu]
  rfl

/-- If the complement block is positive, any negative ambient direction forces
the scalar Schur profile to be negative. -/
theorem stationarySchurScalar_neg_of_negative_direction
    {F : ℝ → V →L[ℂ] V} {z v : V} {s : ℝ}
    (hznorm : ‖z‖ = 1)
    (hFsym : LinearMap.IsSymmetric (𝕜 := ℂ) (F s).toLinearMap)
    (hC : (stationarySchurBlock F z s).IsInvertible)
    (hCnonneg :
      ∀ w : stationarySchurComplement z,
        0 ≤ Complex.re
          (inner ℂ (stationarySchurBlock F z s w) w))
    (hvneg : Complex.re (inner ℂ (F s v) v) < 0) :
    stationarySchurScalar F z s < 0 := by
  let α : ℂ := inner ℂ z v
  let w : stationarySchurComplement z :=
    ⟨v - α • z, by
      change inner ℂ z (v - α • z) = 0
      rw [inner_sub_right, inner_smul_right]
      have hzz : inner ℂ z z = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hznorm]
        norm_num
      rw [hzz]
      simp [α]⟩
  have hvdecomp : v = α • z + (w : V) := by
    dsimp [w]
    abel
  have hsquare :=
    stationarySchur_completedSquare
      (F := F) (z := z) (s := s) hFsym hC α w
  rw [← hvdecomp] at hsquare
  have hnonneg :=
    hCnonneg (w + α • stationarySchurResponse F z s)
  have ha0 : α ≠ 0 := by
    intro ha
    have hα : ‖α‖ ^ 2 = 0 := by simp [ha]
    rw [hsquare, hα, zero_mul, zero_add] at hvneg
    linarith
  have hapos : 0 < ‖α‖ ^ 2 := by positivity
  nlinarith


/-! ## Positivity of the simple-kernel complement -/

/-- At a PSD simple zero mode, the fixed Schur complement has a strictly
positive quadratic lower bound.  This is derived from finite-dimensional
Rayleigh minimization; it is not an extra spectral-gap assumption. -/
theorem stationarySchurBlock_exists_pos_coercivity
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hznorm : ‖z‖ = 1)
    (hFsym : LinearMap.IsSymmetric (𝕜 := ℂ) (F x).toLinearMap)
    (hz : F x z = 0)
    (hker : ∀ v : V, F x v = 0 → ∃ a : ℂ, v = a • z)
    (hnonneg : ∀ v : V, 0 ≤ Complex.re (inner ℂ (F x v) v)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ w : stationarySchurComplement z,
        c * ‖w‖ ^ 2 ≤
          Complex.re (inner ℂ (stationarySchurBlock F z x w) w) := by
  let W := stationarySchurComplement z
  let T : W →ₗ[ℂ] W := (stationarySchurBlock F z x).toLinearMap
  let Tc : W →L[ℂ] W := stationarySchurBlock F z x
  rcases subsingleton_or_nontrivial W with hW | hW
  · letI := hW
    refine ⟨1, by norm_num, ?_⟩
    intro w
    have hw : w = 0 := Subsingleton.elim _ _
    simp [hw]
  · letI := hW
    let lam : ℝ :=
      ⨅ q : {q : W // q ≠ 0},
        RCLike.re (inner ℂ (T q) q) / ‖(q : W)‖ ^ 2
    have hbdd :
        BddBelow
          (Set.range fun q : {q : W // q ≠ 0} =>
            RCLike.re (inner ℂ (T q) q) / ‖(q : W)‖ ^ 2) := by
      refine ⟨-‖Tc‖, ?_⟩
      rintro _ ⟨q, rfl⟩
      have habs :=
        ContinuousLinearMap.rayleighQuotient_le_norm
          (𝕜 := ℂ) Tc (q : W)
      have habs' :
          |RCLike.re (inner ℂ (Tc (q : W)) (q : W)) /
              ‖(q : W)‖ ^ 2| ≤ ‖Tc‖ := by
        simpa only [ContinuousLinearMap.rayleighQuotient,
          ContinuousLinearMap.reApplyInnerSelf_apply] using habs
      exact neg_le_of_abs_le habs'
    have hsymT : LinearMap.IsSymmetric (𝕜 := ℂ) T := by
      simpa [T, Tc] using
        stationarySchurBlock_isSymmetric
          (F := F) (z := z) (s := x) hFsym
    have hlameig := hsymT.hasEigenvalue_iInf_of_finiteDimensional
    obtain ⟨v, hv⟩ := hlameig.exists_hasEigenvector
    have hvne : v ≠ 0 := hv.2
    have hlamdef :
        (lam : ℂ) =
          ((⨅ q : {q : W // q ≠ 0},
            RCLike.re (inner ℂ (T q) q) / ‖(q : W)‖ ^ 2 : ℝ) : ℂ) := by
      rfl
    have hveig : T v = (lam : ℂ) • v := by
      rw [hlamdef]
      exact hv.apply_eq_smul
    have hvq :
        0 ≤ RCLike.re (inner ℂ (T v) v) := by
      have hamb := hnonneg (v : V)
      simpa [T, Tc, stationarySchurBlock_inner] using hamb
    have hnormpos : 0 < ‖v‖ ^ 2 := by positivity
    have hlamnonneg : 0 ≤ lam := by
      rw [hveig, inner_smul_left] at hvq
      simp [inner_self_eq_norm_sq] at hvq
      nlinarith
    have hinj :=
      stationarySchurBlock_injective_of_kernel_line
        (F := F) (z := z) (x := x) hznorm hFsym hz hker
    have hlamne : lam ≠ 0 := by
      intro hlam0
      have hv0 : stationarySchurBlock F z x v = 0 := by
        change T v = 0
        rw [hveig, hlam0, zero_smul]
      have hzv :
          stationarySchurBlock F z x v =
            stationarySchurBlock F z x 0 := by simpa using hv0
      exact hvne (hinj hzv)
    have hlampos : 0 < lam := lt_of_le_of_ne hlamnonneg (Ne.symm hlamne)
    refine ⟨lam, hlampos, ?_⟩
    intro w
    by_cases hw : w = 0
    · simp [hw]
    · have hle :
          lam ≤ RCLike.re (inner ℂ (T w) w) / ‖(w : W)‖ ^ 2 :=
        ciInf_le hbdd ⟨w, hw⟩
      have hden : 0 < ‖(w : W)‖ ^ 2 := by positivity
      have hmul :
          lam * ‖(w : W)‖ ^ 2 ≤ RCLike.re (inner ℂ (T w) w) :=
        (le_div_iff₀ hden).mp hle
      simpa [T, Tc] using hmul

/-- Positivity of the complement persists locally by operator-norm continuity.
This includes the zero-dimensional complement without a separate inverse
failure case. -/
theorem eventually_stationarySchurBlock_nonnegative
    {F : ℝ → V →L[ℂ] V} {z : V} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x)
    (hznorm : ‖z‖ = 1)
    (hFsym : LinearMap.IsSymmetric (𝕜 := ℂ) (F x).toLinearMap)
    (hz : F x z = 0)
    (hker : ∀ v : V, F x v = 0 → ∃ a : ℂ, v = a • z)
    (hnonneg : ∀ v : V, 0 ≤ Complex.re (inner ℂ (F x v) v)) :
    ∀ᶠ s in 𝓝 x,
      ∀ w : stationarySchurComplement z,
        0 ≤ Complex.re
          (inner ℂ (stationarySchurBlock F z s w) w) := by
  obtain ⟨c, hc, hgap⟩ :=
    stationarySchurBlock_exists_pos_coercivity
      (F := F) (z := z) (x := x)
      hznorm hFsym hz hker hnonneg
  have hcont :
      ContinuousAt (fun s => stationarySchurBlock F z s) x :=
    (contDiffAt_stationarySchurBlock hF).continuousAt
  have hball :
      Metric.ball (stationarySchurBlock F z x) (c / 2) ∈
        𝓝 (stationarySchurBlock F z x) :=
    Metric.ball_mem_nhds _ (by linarith)
  have hclose := hcont hball
  filter_upwards [hclose] with s hs
  have hdist :
      ‖stationarySchurBlock F z s -
          stationarySchurBlock F z x‖ < c / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  intro w
  by_cases hw : w = 0
  · simp [hw]
  have hwnorm : 0 < ‖w‖ ^ 2 := by positivity
  let D :=
    stationarySchurBlock F z s -
      stationarySchurBlock F z x
  have habs :
      |Complex.re (inner ℂ (D w) w)| ≤
        ‖D‖ * ‖w‖ ^ 2 := by
    calc
      |Complex.re (inner ℂ (D w) w)| ≤ ‖inner ℂ (D w) w‖ :=
        abs_re_le_norm _
      _ ≤ ‖D w‖ * ‖w‖ := norm_inner_le_norm _ _
      _ ≤ (‖D‖ * ‖w‖) * ‖w‖ := by
        exact mul_le_mul_of_nonneg_right (le_opNorm D w) (norm_nonneg _)
      _ = ‖D‖ * ‖w‖ ^ 2 := by ring
  have hpert :
      -(‖D‖ * ‖w‖ ^ 2) ≤
        Complex.re (inner ℂ (D w) w) :=
    neg_le_of_abs_le habs
  have hdist' : ‖D‖ < c / 2 := by
    simpa [D] using hdist
  have hmul :
      ‖D‖ * ‖w‖ ^ 2 < (c / 2) * ‖w‖ ^ 2 :=
    mul_lt_mul_of_pos_right hdist' hwnorm
  have hbase := hgap w
  have hsum :
      Complex.re
          (inner ℂ (stationarySchurBlock F z s w) w) =
        Complex.re
          (inner ℂ (stationarySchurBlock F z x w) w) +
        Complex.re (inner ℂ (D w) w) := by
    have happ :
        stationarySchurBlock F z s w =
          stationarySchurBlock F z x w + D w := by
      simp [D]
    rw [happ, inner_add_left, Complex.add_re]
  rw [hsum]
  nlinarith


/-! ## Generic stationary first-contact theorem from family geometry -/

/-- Full arbitrary-complement Schur contact theorem.  Positivity of the
complement is derived internally from PSD plus the simple kernel.  Right-side
negative directions are converted to negative Schur scalar values by the
completed-square identity. -/
theorem stationarySchur_contact_secondPairing_eq_zero
    {F : ℝ → V →L[ℂ] V} {z w : V} {x a b : ℝ}
    (hax : a < x)
    (hxb : x < b)
    (hF : ContDiffAt ℝ 2 F x)
    (hFsym : ∀ᶠ s in 𝓝 x,
      LinearMap.IsSymmetric (𝕜 := ℂ) (F s).toLinearMap)
    (hz : F x z = 0)
    (hznorm : ‖z‖ = 1)
    (hker : ∀ v : V, F x v = 0 → ∃ α : ℂ, v = α • z)
    (hleft :
      ∀ y, a ≤ y → y ≤ x →
        ∀ v : V, 0 ≤ Complex.re (inner ℂ (F y v) v))
    (hright :
      ∀ ε > 0, ∃ y, x < y ∧ y < x + ε ∧
        ∃ v : V, Complex.re (inner ℂ (F y v) v) < 0)
    (hstationary :
      deriv (fun s => Complex.re (inner ℂ (F s z) z)) x = 0)
    (hwperp : inner ℂ z w = 0)
    (hw : F x w = -((deriv F x) z)) :
    Complex.re (inner ℂ ((deriv (deriv F) x) z) z) +
        2 * Complex.re (inner ℂ ((deriv F x) w) z) = 0 := by
  have hFsymx := hFsym.self_of_nhds
  have hC :=
    stationarySchurBlock_isInvertible_of_kernel_line
      (F := F) (z := z) (x := x)
      hznorm hFsymx hz hker
  have hcontact :
      stationarySchurScalar F z x = 0 :=
    stationarySchurScalar_eq_zero_of_kernel hz
  have hC2 :
      ContDiffAt ℝ 2 (fun s => stationarySchurScalar F z s) x :=
    contDiffAt_stationarySchurScalar hF hC
  have hstat :
      deriv (fun s => stationarySchurScalar F z s) x = 0 := by
    rw [stationarySchurScalar_firstDerivative_eq_fixed hF hFsym hz hC]
    exact hstationary
  have hleftSigma :
      ∀ y, a ≤ y → y ≤ x → 0 ≤ stationarySchurScalar F z y := by
    intro y hay hyx
    exact hleft y hay hyx (stationarySchurVector F z y)
  have hcontactNonneg :
      ∀ v : V, 0 ≤ Complex.re (inner ℂ (F x v) v) :=
    hleft x (le_of_lt hax) le_rfl
  have hCnonnegEv :=
    eventually_stationarySchurBlock_nonnegative
      hF hznorm hFsymx hz hker hcontactNonneg
  have hCinvEv := eventually_stationarySchurBlock_isInvertible hF hC
  have hgood :
      ∀ᶠ s in 𝓝 x,
        LinearMap.IsSymmetric (𝕜 := ℂ) (F s).toLinearMap ∧
        (stationarySchurBlock F z s).IsInvertible ∧
        (∀ q : stationarySchurComplement z,
          0 ≤ Complex.re
            (inner ℂ (stationarySchurBlock F z s q) q)) := by
    filter_upwards [hFsym, hCinvEv, hCnonnegEv] with s hs hi hp
    exact ⟨hs, hi, hp⟩
  have hgoodSet :
      {s : ℝ |
        LinearMap.IsSymmetric (𝕜 := ℂ) (F s).toLinearMap ∧
        (stationarySchurBlock F z s).IsInvertible ∧
        (∀ q : stationarySchurComplement z,
          0 ≤ Complex.re
            (inner ℂ (stationarySchurBlock F z s q) q))} ∈ 𝓝 x :=
    hgood
  rcases Metric.mem_nhds_iff.mp hgoodSet with
    ⟨δ, hδ, hδball⟩
  have hrightSigma :
      ∀ ε > 0, ∃ y, x < y ∧ y < x + ε ∧
        stationarySchurScalar F z y < 0 := by
    intro ε hε
    let η := min ε δ
    have hη : 0 < η := lt_min hε hδ
    obtain ⟨y, hyx, hyη, v, hvneg⟩ := hright η hη
    have hyε : y < x + ε := by
      dsimp [η] at hyη
      linarith [min_le_left ε δ]
    have hyδ : y ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have : |y - x| < δ := by
        rw [abs_of_pos (sub_pos.mpr hyx)]
        dsimp [η] at hyη
        linarith [min_le_right ε δ]
      simpa [abs_sub_comm] using this
    have hgy := hδball hyδ
    have hsigmaNeg :=
      stationarySchurScalar_neg_of_negative_direction
        (F := F) (z := z) (v := v) (s := y)
        hznorm hgy.1 hgy.2.1 hgy.2.2 hvneg
    exact ⟨y, hyx, hyε, hsigmaNeg⟩
  have hsigma2 :=
    stationary_firstContact_secondDerivative_eq_zero
      hax hxb hcontact hleftSigma hrightSigma hC2 hstat
  have hpair :=
    stationarySchurScalar_secondDerivative_eq_pair
      hF hFsym hz hznorm hker hwperp hw
  rw [hpair] at hsigma2
  exact hsigma2

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
#print axioms Zeta23.CCM.stationarySchur_contact_secondPairing_eq_zero
#print axioms Zeta23.CCM.stationarySchurBlock_injective_of_kernel_line
#print axioms Zeta23.CCM.stationarySchurBlock_isInvertible_of_kernel_line
#print axioms Zeta23.CCM.contDiffAt_stationarySchurScalar
#print axioms Zeta23.CCM.stationarySchurScalar_secondDerivative_eq_pair
#print axioms Zeta23.CCM.stationarySchur_completedSquare
#print axioms Zeta23.CCM.stationarySchurEnvelope_secondDerivative
#print axioms Zeta23.CCM.StationarySchurContactCertificate.curvature_eq_zero
