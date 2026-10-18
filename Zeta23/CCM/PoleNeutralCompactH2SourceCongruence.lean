import Zeta23.CCM.PoleNeutralCompactInverse
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Representative-independent use of the actual compact weak-H2 inverse.
No continuity of the source is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace Zeta23.CCM

theorem nativePolePrimitive_congr_ae (s r : ℝ) {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) (x : ℝ) :
    nativePolePrimitive s r f x = nativePolePrimitive s r g x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hfg] with y hy _
  rw [hy]

theorem nativePoleCompactInverse_congr_ae (s : ℝ) {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) :
    nativePoleCompactInverse s f = nativePoleCompactInverse s g := by
  funext x
  simp only [nativePoleCompactInverse, nativePolePrimitive_congr_ae s _ hfg]

theorem nativePoleCompactInverseDerivative_congr_ae (s : ℝ) {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) :
    nativePoleCompactInverseDerivative s f = nativePoleCompactInverseDerivative s g := by
  funext x
  simp only [nativePoleCompactInverseDerivative, nativePolePrimitive_congr_ae s _ hfg]

/-- Transport only the source in the a.e. equation; both continuous jets
and every trace/support/AC field are the identical functions. -/
def NativeCompactPoleH2.congrSource {s : ℝ} {f g : ℝ → ℂ}
    (u : NativeCompactPoleH2 s f) (hfg : f =ᵐ[volume] g) :
    NativeCompactPoleH2 s g where
  value := u.value
  first := u.first
  value_continuous := u.value_continuous
  first_continuous := u.first_continuous
  value_ac := u.value_ac
  first_ac := u.first_ac
  value_l2 := u.value_l2
  first_l2 := u.first_l2
  second_l2 := (memLp_congr_ae (by filter_upwards [hfg] with x hx; rw [hx])).mp u.second_l2
  value_support := u.value_support
  first_support := u.first_support
  value_clamped := u.value_clamped
  first_clamped := u.first_clamped
  value_derivative := u.value_derivative
  first_derivative := by
    filter_upwards [u.first_derivative, hfg] with x hx h
    simpa only [h] using hx

/-- Every representative-level solution agrees, not just a newly selected
integral solution. The source equality is only almost everywhere. -/
theorem NativeCompactPoleH2.unique_of_source_ae {s : ℝ} (hs : 0 ≤ s)
    {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g)
    (u : NativeCompactPoleH2 s f) (v : NativeCompactPoleH2 s g) :
    u.value = v.value ∧ u.first = v.first := by
  have h := (u.congrSource hfg).unique hs v
  exact ⟨congrArg NativeCompactPoleH2.value h, congrArg NativeCompactPoleH2.first h⟩

/-- A source supported almost everywhere admits the actual supported
representative, without imposing any extra regularity. -/
def nativePoleSupportedRepresentative (s : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (Icc (-s) s).indicator f

theorem nativePoleSupportedRepresentative_ae {s : ℝ} {f : ℝ → ℂ}
    (hf : ∀ᵐ x : ℝ, x ∉ Icc (-s) s → f x = 0) :
    nativePoleSupportedRepresentative s f =ᵐ[volume] f := by
  filter_upwards [hf] with x hx
  by_cases hmem : x ∈ Icc (-s) s
  · simp [nativePoleSupportedRepresentative, hmem]
  · simp [nativePoleSupportedRepresentative, hmem, hx hmem]

theorem nativePoleSupportedRepresentative_support (s : ℝ) (f : ℝ → ℂ)
    (x : ℝ) (hx : x ∉ Icc (-s) s) :
    nativePoleSupportedRepresentative s f x = 0 := by
  simp [nativePoleSupportedRepresentative, hx]

/-- The actual general compact L2 construction accepts support as an a.e.
property; the returned object solves the original source equation. -/
theorem poleNeutral_compactInverse_exists_of_ae_support {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ᵐ x : ℝ, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1/2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1/2) x * f x) = 0) :
    ∃ u : NativeCompactPoleH2 s f,
      (eLpNorm u.value 2 volume).toReal ≤ 4 * (eLpNorm f 2 volume).toReal := by
  let g := nativePoleSupportedRepresentative s f
  have hgf : g =ᵐ[volume] f := nativePoleSupportedRepresentative_ae hsupport
  have hg : MemLp g 2 volume := (memLp_congr_ae hgf).mpr hf
  have hm (r : ℝ) : (∫ x, nativePoleExponential r x * g x) =
      ∫ x, nativePoleExponential r x * f x := by
    apply integral_congr_ae
    filter_upwards [hgf] with x hx
    rw [hx]
  let u := nativePoleCompactH2 hs hg
    (nativePoleSupportedRepresentative_support s f)
    ((hm (1/2)).trans hplus) ((hm (-1/2)).trans hminus)
  refine ⟨u.congrSource hgf, ?_⟩
  change (eLpNorm u.value 2 volume).toReal ≤ _
  have hb := nativePoleCompactH2_norm_bound hs hg
    (nativePoleSupportedRepresentative_support s f)
    ((hm (1/2)).trans hplus) ((hm (-1/2)).trans hminus)
  simpa only [eLpNorm_congr_ae hgf] using hb

/-- Translation to [0,2s] preserves the exact support, both L2 jets and the
sharp norm4. This is the [0,L] adapter with s=L/2. -/
theorem nativePoleCompactH2_translate_support_norm {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ x, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x, nativePoleExponential (1/2) x * f x) = 0)
    (hminus : (∫ x, nativePoleExponential (-1/2) x * f x) = 0) :
    let u := nativePoleCompactH2 hs hf hsupport hplus hminus
    (∀ x, x ∉ Icc 0 (2*s) → u.value (x-s) = 0 ∧ u.first (x-s) = 0) ∧
    MemLp (fun x => u.value (x-s)) 2 volume ∧
    MemLp (fun x => u.first (x-s)) 2 volume ∧
    (eLpNorm (fun x => u.value (x-s)) 2 volume).toReal ≤
      4 * (eLpNorm (fun x => f (x-s)) 2 volume).toReal := by
  dsimp only
  let u := nativePoleCompactH2 hs hf hsupport hplus hminus
  have mp := measurePreserving_sub_right volume s
  refine ⟨?_, u.value_l2.comp_measurePreserving mp,
    u.first_l2.comp_measurePreserving mp, ?_⟩
  · intro x hx
    have hnot : x-s ∉ Icc (-s) s := by
      intro hmem
      apply hx
      constructor <;> linarith [hmem.1, hmem.2]
    exact ⟨u.value_support _ hnot, u.first_support _ hnot⟩
  · have h1 := eLpNorm_comp_measurePreserving (p := 2) u.value_l2.aestronglyMeasurable mp
    have h2 := eLpNorm_comp_measurePreserving (p := 2) hf.aestronglyMeasurable mp
    change eLpNorm (fun x => u.value (x-s)) 2 volume = eLpNorm u.value 2 volume at h1
    change eLpNorm (fun x => f (x-s)) 2 volume = eLpNorm f 2 volume at h2
    rw [h1, h2]
    exact nativePoleCompactH2_norm_bound hs hf hsupport hplus hminus


/-- Translation preserves the actual global a.e. differential equations,
rather than postulating classical second derivatives of an L2 source. -/
theorem NativeCompactPoleH2.translated_ae_equations {s : ℝ} {f : ℝ → ℂ}
    (u : NativeCompactPoleH2 s f) (t : ℝ) :
    (∀ᵐ x : ℝ, HasDerivAt (fun y => u.value (y-t)) (u.first (x-t)) x) ∧
    (∀ᵐ x : ℝ, HasDerivAt (fun y => u.first (y-t))
      ((1/4 : ℂ) * u.value (x-t) + f (x-t)) x) := by
  have mp := (measurePreserving_sub_right volume t).quasiMeasurePreserving
  constructor
  · filter_upwards [mp.ae u.value_derivative] with x hx
    simpa only [Function.comp_def, id_eq, one_smul] using
      hx.scomp x ((hasDerivAt_id x).sub_const t)
  · filter_upwards [mp.ae u.first_derivative] with x hx
    simpa only [Function.comp_def, id_eq, one_smul] using
      hx.scomp x ((hasDerivAt_id x).sub_const t)

/-- Literal [0,L] version. The source in the translated equation is
x ↦ f(x-L/2); f remains an arbitrary compact L2 source with both moments. -/
theorem poleNeutral_compactInverse_zero_interval_support_norm {L : ℝ} (hL : 0 ≤ L)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ x, x ∉ Icc (-(L/2)) (L/2) → f x = 0)
    (hplus : (∫ x, nativePoleExponential (1/2) x * f x) = 0)
    (hminus : (∫ x, nativePoleExponential (-1/2) x * f x) = 0) :
    let u := nativePoleCompactH2 (s := L/2) (by positivity) hf hsupport hplus hminus
    (∀ x, x ∉ Icc 0 L → u.value (x-L/2) = 0 ∧ u.first (x-L/2) = 0) ∧
    MemLp (fun x => u.value (x-L/2)) 2 volume ∧
    MemLp (fun x => u.first (x-L/2)) 2 volume ∧
    (eLpNorm (fun x => u.value (x-L/2)) 2 volume).toReal ≤
      4 * (eLpNorm (fun x => f (x-L/2)) 2 volume).toReal := by
  have htwo : 2*(L/2) = L := by ring
  simpa only [htwo] using
    nativePoleCompactH2_translate_support_norm (s := L/2) (by positivity)
      hf hsupport hplus hminus

end Zeta23.CCM
#print axioms Zeta23.CCM.nativePoleCompactInverse_congr_ae
#print axioms Zeta23.CCM.nativePoleCompactInverseDerivative_congr_ae
#print axioms Zeta23.CCM.NativeCompactPoleH2.congrSource
#print axioms Zeta23.CCM.NativeCompactPoleH2.unique_of_source_ae
#print axioms Zeta23.CCM.poleNeutral_compactInverse_exists_of_ae_support
#print axioms Zeta23.CCM.nativePoleCompactH2_translate_support_norm
#print axioms Zeta23.CCM.NativeCompactPoleH2.translated_ae_equations
#print axioms Zeta23.CCM.poleNeutral_compactInverse_zero_interval_support_norm

