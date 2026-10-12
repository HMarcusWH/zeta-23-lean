import Zeta23.CCM.CanonicalLocalBirdfishie
import Mathlib.Analysis.Convex.Deriv

noncomputable section

namespace Zeta23.CCM

open Set Filter Topology
open scoped ContDiff

/-!
# WP1: reciprocal-aperture calculus

For the fixed-vector energy `E`, define `G(s) = E(1/s)`.  The exact identity

  `G''(s) = (1/s)^4 * (E''(1/s) + 2 s E'(1/s))`

transports the *already established* M66 prime-free Euler-curvature sign
to reciprocal-aperture concavity.  This adds no sign beyond the M66 radius,
does not assume or prove RH, and says nothing about a moving eigenvector.
-/

/-- First reciprocal derivative, with the necessary aperture domain explicit. -/
theorem reciprocalAperture_first_derivative
    (f : ℝ → ℝ) (s : ℝ) (hs : 0 < s)
    (hf : DifferentiableAt ℝ f s⁻¹) :
    deriv (fun t : ℝ => f t⁻¹) s =
      deriv f s⁻¹ * (-(s⁻¹)^2) := by
  have hInv : HasDerivAt (fun t : ℝ => t⁻¹) (-(s ^ 2)⁻¹) s :=
    hasDerivAt_inv (ne_of_gt hs)
  have h := hf.hasDerivAt.comp s hInv
  simpa only [Function.comp_def, inv_pow] using h.deriv

/-- The second reciprocal derivative, using differentiability of both `f`
and its ordinary derivative throughout the positive aperture domain. -/
theorem reciprocalAperture_second_derivative
    (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hf2 : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (deriv f) x)
    (s : ℝ) (hs : 0 < s) :
    deriv (deriv (fun t : ℝ => f t⁻¹)) s =
      (s⁻¹)^4 * (deriv (deriv f) s⁻¹ + 2 * s * deriv f s⁻¹) := by
  have hInv : HasDerivAt (fun t : ℝ => t⁻¹) (-(s ^ 2)⁻¹) s :=
    hasDerivAt_inv (ne_of_gt hs)
  have hMain : HasDerivAt
      (fun t : ℝ => (deriv f t⁻¹) * (-(t⁻¹)^2))
      (deriv (deriv f) s⁻¹ * (-(s ^ 2)⁻¹) * (-(s⁻¹)^2) +
        deriv f s⁻¹ * (-(2 * (s⁻¹) * (-(s ^ 2)⁻¹)))) s := by
    convert (((hf2 s⁻¹ (inv_pos.mpr hs)).hasDerivAt.comp s hInv).mul
      ((hInv.pow 2).neg)) using 1 <;>
      try simp only [Function.comp_def] <;> ring
  have hEq : (deriv (fun t : ℝ => f t⁻¹)) =ᶠ[𝓝 s]
      (fun t : ℝ => deriv f t⁻¹ * (-(t⁻¹)^2)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact reciprocalAperture_first_derivative f t ht (hf t⁻¹ (inv_pos.mpr ht))
  have hDerivative := (hMain.congr_of_eventuallyEq hEq).deriv
  rw [hDerivative]
  have hne : s ≠ 0 := ne_of_gt hs
  field_simp [hne] <;> ring

/-- Euler form of the reciprocal chain rule, with `L=s⁻¹`.
Neither the sign nor positivity at endpoints is built into this identity. -/
theorem reciprocalAperture_euler_chain
    (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hf2 : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (deriv f) x)
    (s : ℝ) (hs : 0 < s) :
    deriv (deriv (fun t : ℝ => f t⁻¹)) s =
      (s⁻¹)^4 * (deriv (deriv f) s⁻¹ +
        2 * deriv f s⁻¹ / (s⁻¹)) := by
  rw [reciprocalAperture_second_derivative f hf hf2 s hs]
  have hne : s ≠ 0 := ne_of_gt hs
  field_simp [hne] <;> ring

/-- Strict concavity on the reciprocal positive-aperture region where the
physical Euler-corrected second derivative is independently strictly
negative. The stated curvature hypothesis is essential. -/
theorem reciprocalAperture_strictConcaveOn
    (f : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hf2 : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (deriv f) x)
    (hCurv : ∀ x : ℝ, 0 < x → x < R →
      deriv (deriv f) x + 2 * deriv f x / x < 0) :
    StrictConcaveOn ℝ (Set.Ioi R⁻¹) (fun s : ℝ => f s⁻¹) := by
  have hCont : ContinuousOn (fun s : ℝ => f s⁻¹) (Set.Ioi R⁻¹) := by
    intro s hs
    have hspos : 0 < s := (inv_pos.mpr hR).trans hs
    have hpos : 0 < s⁻¹ := inv_pos.mpr hspos
    have hInvCont : ContinuousAt (fun t : ℝ => t⁻¹) s :=
      continuousAt_inv₀ (ne_of_gt hspos)
    exact ((hf s⁻¹ hpos).continuousAt.comp hInvCont).continuousWithinAt
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi _) hCont
  intro s hsInt
  have hs : R⁻¹ < s := interior_subset hsInt
  have hspos : 0 < s := (inv_pos.mpr hR).trans hs
  have hpos : 0 < s⁻¹ := inv_pos.mpr hspos
  have hSR : (1 : ℝ) / R < s := by simpa [one_div] using hs
  have hmul : 1 < s * R := (div_lt_iff₀ hR).mp hSR
  have hless : s⁻¹ < R := by
    have hsDiv : 1 / s < R := by
      apply (div_lt_iff₀ hspos).mpr
      nlinarith [hmul]
    simpa only [one_div] using hsDiv
  change deriv (deriv (fun t : ℝ => f t⁻¹)) s < 0
  rw [reciprocalAperture_euler_chain f hf hf2 s hspos]
  exact mul_neg_of_pos_of_neg (pow_pos hpos 4) (hCurv s⁻¹ hpos hless)

/-- A scalar concave energy is bounded below between two apertures by
the minimum of its endpoint values. This is the lemma used when passing
fixed-vector reciprocal concavity to an infimum of Rayleigh quotients. -/
theorem concave_on_Icc_ge_min_endpoints
    (f : ℝ → ℝ) {a b x : ℝ} (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b)
    (hconc : ConcaveOn ℝ (Set.Icc a b) f) :
    min (f a) (f b) ≤ f x := by
  have hseg : x ∈ segment ℝ a b := by
    rw [segment_eq_uIcc, uIcc_of_le hab]
    exact hx
  exact hconc.ge_on_segment
    (by simp [hab]) (by simp [hab]) hseg

/-- Uniform endpoint bounds are preserved by a family of concave scalar
energies on a common interval. This avoids any assumption of positivity
of a matrix, and leaves a later Rayleigh-infimum application well typed. -/
theorem concave_family_ge_of_endpoint_ge
    {I : Type*} (f : I → ℝ → ℝ) {a b x m : ℝ}
    (hab : a ≤ b) (hx : x ∈ Set.Icc a b)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Icc a b) (f i))
    (ha : ∀ i, m ≤ f i a) (hb : ∀ i, m ≤ f i b) :
    ∀ i, m ≤ f i x := by
  intro i
  exact le_trans (le_min (ha i) (hb i))
    (concave_on_Icc_ge_min_endpoints (f i) hab hx (hconc i))

/-- WP1 canonical bottom interpolation in reciprocal aperture.  This theorem
does **not** assume positivity, a contact, or RH.  Its mathematical input is
strictly the per-vector concavity of the *actual canonical* normalized Rayleigh
energy; the conclusion is an endpoint lower bound for the genuine iInf
Rayleigh bottom, not for a substitute scalar functional. -/

/-- The even legal Rayleigh carrier is nonzero as soon as K >= 2. -/
private theorem evenRayleigh_nonempty_nonzero
    (K : ℕ) (hK : 2 ≤ K) :
    Nonempty {z : euclideanEvenBoundaryFlatSubspace K // z ≠ 0} := by
  have hfin : 0 < Module.finrank ℂ (euclideanEvenBoundaryFlatSubspace K) := by
    rw [finrank_euclideanEvenBoundaryFlatSubspace K (by omega)]
    omega
  letI : Nontrivial (euclideanEvenBoundaryFlatSubspace K) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) hfin
  obtain ⟨z, hz⟩ := exists_ne (0 : euclideanEvenBoundaryFlatSubspace K)
  exact ⟨⟨z, hz⟩⟩

theorem evenRayleighBottom_ge_endpoint_min_of_reciprocal_concavity
    {K : ℕ} {a L b : ℝ} (hK : 2 ≤ K)
    (ha : 0 < a) (haL : a ≤ L) (hLb : L ≤ b)
    (hConcave : ∀ z : euclideanEvenBoundaryFlatSubspace K, z ≠ 0 →
      ConcaveOn ℝ (Set.Icc b⁻¹ a⁻¹)
        (fun s : ℝ =>
          productionContactFixedEnergy .even s⁻¹ K z / ‖z‖ ^ 2)) :
    min (parityRayleighBottom .even a K)
        (parityRayleighBottom .even b K) ≤
      parityRayleighBottom .even L K := by
  have hL : 0 < L := lt_of_lt_of_le ha haL
  have hb : 0 < b := lt_of_lt_of_le hL hLb
  have hab : a ≤ b := le_trans haL hLb
  have hba : b⁻¹ ≤ a⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le ha hab)
  have hinside : L⁻¹ ∈ Set.Icc b⁻¹ a⁻¹ := by
    constructor
    · simpa only [one_div] using
        (one_div_le_one_div_of_le hL hLb)
    · simpa only [one_div] using
        (one_div_le_one_div_of_le ha haL)
  have hpoint (z : euclideanEvenBoundaryFlatSubspace K) (hz : z ≠ 0) :
      min (parityRayleighBottom .even a K)
          (parityRayleighBottom .even b K) ≤
        productionContactFixedEnergy .even L K z / ‖z‖ ^ 2 := by
    let F : ℝ → ℝ := fun s =>
      productionContactFixedEnergy .even s⁻¹ K z / ‖z‖ ^ 2
    have hconc : ConcaveOn ℝ (Set.Icc b⁻¹ a⁻¹) F :=
      hConcave z hz
    have hchord : min (F b⁻¹) (F a⁻¹) ≤ F L⁻¹ :=
      concave_on_Icc_ge_min_endpoints F hba hinside hconc
    have hleft : parityRayleighBottom .even a K ≤ F a⁻¹ := by
      simpa only [F, inv_inv, productionContactFixedEnergy] using
        (parityRayleighBottom_le_rayleigh .even a K z hz)
    have hright : parityRayleighBottom .even b K ≤ F b⁻¹ := by
      simpa only [F, inv_inv, productionContactFixedEnergy] using
        (parityRayleighBottom_le_rayleigh .even b K z hz)
    calc
      min (parityRayleighBottom .even a K)
          (parityRayleighBottom .even b K) ≤
          min (F a⁻¹) (F b⁻¹) := min_le_min hleft hright
      _ = min (F b⁻¹) (F a⁻¹) := min_comm _ _
      _ ≤ F L⁻¹ := hchord
      _ = productionContactFixedEnergy .even L K z / ‖z‖ ^ 2 := by
        simp [F]
  letI : Nonempty {z : euclideanEvenBoundaryFlatSubspace K // z ≠ 0} :=
    evenRayleigh_nonempty_nonzero K hK
  unfold parityRayleighBottom
  refine le_ciInf fun z => ?_
  simpa only [productionContactFixedEnergy] using hpoint z.1 z.2

/-- The more economical WP1 bridge: it is enough to know *unnormalized*
fixed-vector source-energy concavity on reciprocal aperture.  The positive
norm-square denominator is independent of aperture, so the true canonical
Rayleigh bottom inherits the same endpoint lower bound.  No separate
positivity assumption is used. -/
theorem evenRayleighBottom_ge_endpoint_min_of_raw_reciprocal_concavity
    {K : ℕ} {a L b : ℝ} (hK : 2 ≤ K)
    (ha : 0 < a) (haL : a ≤ L) (hLb : L ≤ b)
    (hConcave : ∀ z : euclideanEvenBoundaryFlatSubspace K, z ≠ 0 →
      ConcaveOn ℝ (Set.Icc b⁻¹ a⁻¹)
        (fun s : ℝ => productionContactFixedEnergy .even s⁻¹ K z)) :
    min (parityRayleighBottom .even a K)
        (parityRayleighBottom .even b K) ≤
      parityRayleighBottom .even L K := by
  have hL : 0 < L := lt_of_lt_of_le ha haL
  have hb : 0 < b := lt_of_lt_of_le hL hLb
  have hab : a ≤ b := le_trans haL hLb
  have hba : b⁻¹ ≤ a⁻¹ := by
    simpa only [one_div] using (one_div_le_one_div_of_le ha hab)
  have hinside : L⁻¹ ∈ Set.Icc b⁻¹ a⁻¹ := by
    constructor
    · simpa only [one_div] using (one_div_le_one_div_of_le hL hLb)
    · simpa only [one_div] using (one_div_le_one_div_of_le ha haL)
  have hpoint (z : euclideanEvenBoundaryFlatSubspace K) (hz : z ≠ 0) :
      min (parityRayleighBottom .even a K)
          (parityRayleighBottom .even b K) ≤
        productionContactFixedEnergy .even L K z / ‖z‖ ^ 2 := by
    let F : ℝ → ℝ := fun s => productionContactFixedEnergy .even s⁻¹ K z
    have hchord : min (F b⁻¹) (F a⁻¹) ≤ F L⁻¹ :=
      concave_on_Icc_ge_min_endpoints F hba hinside (hConcave z hz)
    have hc : 0 < ‖z‖ ^ 2 := by positivity
    have hscaled :
        min (F b⁻¹ / ‖z‖ ^ 2) (F a⁻¹ / ‖z‖ ^ 2) ≤
          F L⁻¹ / ‖z‖ ^ 2 := by
      rcases le_total (F b⁻¹) (F a⁻¹) with h | h
      · have he : F b⁻¹ ≤ F L⁻¹ := by
          simpa [min_eq_left h] using hchord
        exact le_trans (min_le_left _ _) ((div_le_div_iff_of_pos_right hc).2 he)
      · have he : F a⁻¹ ≤ F L⁻¹ := by
          simpa [min_eq_right h] using hchord
        exact le_trans (min_le_right _ _) ((div_le_div_iff_of_pos_right hc).2 he)
    have hleft : parityRayleighBottom .even a K ≤ F a⁻¹ / ‖z‖ ^ 2 := by
      simpa only [F, inv_inv, productionContactFixedEnergy] using
        (parityRayleighBottom_le_rayleigh .even a K z hz)
    have hright : parityRayleighBottom .even b K ≤ F b⁻¹ / ‖z‖ ^ 2 := by
      simpa only [F, inv_inv, productionContactFixedEnergy] using
        (parityRayleighBottom_le_rayleigh .even b K z hz)
    calc
      min (parityRayleighBottom .even a K)
          (parityRayleighBottom .even b K) ≤
          min (F a⁻¹ / ‖z‖ ^ 2) (F b⁻¹ / ‖z‖ ^ 2) :=
        min_le_min hleft hright
      _ = min (F b⁻¹ / ‖z‖ ^ 2) (F a⁻¹ / ‖z‖ ^ 2) := min_comm _ _
      _ ≤ F L⁻¹ / ‖z‖ ^ 2 := hscaled
      _ = productionContactFixedEnergy .even L K z / ‖z‖ ^ 2 := by
        simp [F]
  letI : Nonempty {z : euclideanEvenBoundaryFlatSubspace K // z ≠ 0} :=
    evenRayleigh_nonempty_nonzero K hK
  unfold parityRayleighBottom
  refine le_ciInf fun z => ?_
  simpa only [productionContactFixedEnergy] using hpoint z.1 z.2

/-- Native production-Euler inequality implies genuine even-bottom endpoint
interpolation on every interval strictly inside the *already PROVED* M66
radius. The scalar C² premise is deliberately typed as the existing
seam-safe fixed-vector realization, not as an RH/positivity assumption.
This lemma never enlarges the M66 radius. -/
theorem evenRayleighBottom_ge_endpoint_min_of_nativeEuler
    (K : ℕ) (hK : 2 ≤ K)
    (hSmooth : ∀ z : euclideanEvenBoundaryFlatSubspace K,
      ContDiffOn ℝ 2
        (fun x : ℝ => productionContactFixedEnergy .even x K z)
        (Set.Ioi (0 : ℝ)))
    {a L b : ℝ} (ha : 0 < a) (haL : a ≤ L) (hLb : L ≤ b)
    (hbR : b < primeFreeRadius K) :
    min (parityRayleighBottom .even a K)
        (parityRayleighBottom .even b K) ≤
      parityRayleighBottom .even L K := by
  have hR : 0 < primeFreeRadius K := by
    unfold primeFreeRadius
    have hk : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    positivity
  have hb : 0 < b := lt_of_lt_of_le ha (le_trans haL hLb)
  have hrb : (primeFreeRadius K)⁻¹ < b⁻¹ := by
    have hd : (1 : ℝ) / primeFreeRadius K < 1 / b := by
      apply (div_lt_div_iff₀ hR hb).2
      simpa using hbR
    simpa only [one_div] using hd
  have hRaw :
      ∀ z : euclideanEvenBoundaryFlatSubspace K, z ≠ 0 →
        ConcaveOn ℝ (Set.Icc b⁻¹ a⁻¹)
          (fun s : ℝ => productionContactFixedEnergy .even s⁻¹ K z) := by
    intro z hz
    let f : ℝ → ℝ := fun x =>
      productionContactFixedEnergy .even x K z
    have hC : ContDiffOn ℝ 2 f (Set.Ioi (0 : ℝ)) := hSmooth z
    have hdiff1 : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x := by
      intro x hx
      exact (hC.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)
    have hC1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioi (0 : ℝ)) := by
      have h := hC
      rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num,
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi] at h
      exact h.2.2
    have hdiff2 : ∀ x : ℝ, 0 < x →
        DifferentiableAt ℝ (deriv f) x := by
      intro x hx
      exact (hC1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)
    have hK1 : 1 ≤ K := by omega
    have hEuler : ∀ x : ℝ, 0 < x → x < primeFreeRadius K →
        deriv (deriv f) x + 2 * deriv f x / x < 0 := by
      intro x hx hxR
      simpa [f, productionContactFirstVariation,
        productionContactFixedSecondVariation] using
        (productionContactEulerCurvature_neg K hK1 hx hxR z hz)
    have hStrict := reciprocalAperture_strictConcaveOn f
      (primeFreeRadius K) hR hdiff1 hdiff2 hEuler
    have hsubset : Set.Icc b⁻¹ a⁻¹ ⊆
        Set.Ioi (primeFreeRadius K)⁻¹ := by
      intro t ht
      exact lt_of_lt_of_le hrb ht.1
    exact hStrict.concaveOn.subset hsubset (convex_Icc _ _)
  exact evenRayleighBottom_ge_endpoint_min_of_raw_reciprocal_concavity
    hK ha haL hLb hRaw

/-- WP1: fixed legal-even physical source energy is genuinely C² on every
positive aperture, as an unconditional consequence of the already formally
proved seam-safe compressed canonical CLM family.  No F04 hypothesis or
zero-free assumption appears here. -/
theorem canonical_evenFixedEnergy_contDiffOn_two (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    ContDiffOn ℝ 2
      (fun L : ℝ => productionContactFixedEnergy .even L K z)
      (Set.Ioi (0 : ℝ)) := by
  intro L hL
  have hfamily : ContDiffAt ℝ 2
      (canonicalParityCompressedFamilyCLM .even K) L :=
    (canonicalParityCompressedC2_proved .even K).contDiffAt
      (isOpen_Ioi.mem_nhds hL)
  have hvalue : ContDiffAt ℝ 2
      (fun t : ℝ => (canonicalParityCompressedFamilyCLM .even K t) z) L :=
    contDiffAt_complexCLM_apply_const_real hfamily z
  have hpair : ContDiffAt ℝ 2
      (fun t : ℝ =>
        inner ℂ ((canonicalParityCompressedFamilyCLM .even K t) z) z) L :=
    hvalue.inner ℂ contDiffAt_const
  have hRe : ContDiff ℝ 2 (fun w : ℂ => w.re) := by
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.contDiff (n := (2 : ℕ∞ω)))
  have hscalar := hRe.contDiffAt.comp L hpair
  simpa only [productionContactFixedEnergy,
    canonicalParityCompressedFamilyCLM, parityCompressedCanonicalCLM,
    Complex.reCLM_apply] using hscalar.contDiffWithinAt

/-- The M66 native Euler curvature inequality and the globally C²
compressed production family now supply **unconditional** endpoint
interpolation on the real canonical even Rayleigh bottom inside the
established prime-free radius.  The finite M51 window is not used. -/
theorem evenRayleighBottom_ge_endpoint_min_of_M66
    (K : ℕ) (hK : 2 ≤ K)
    {a L b : ℝ} (ha : 0 < a) (haL : a ≤ L) (hLb : L ≤ b)
    (hbR : b < primeFreeRadius K) :
    min (parityRayleighBottom .even a K)
        (parityRayleighBottom .even b K) ≤
      parityRayleighBottom .even L K :=
  evenRayleighBottom_ge_endpoint_min_of_nativeEuler K hK
    (canonical_evenFixedEnergy_contDiffOn_two K)
    ha haL hLb hbR

end Zeta23.CCM

#print axioms Zeta23.CCM.reciprocalAperture_first_derivative
#print axioms Zeta23.CCM.reciprocalAperture_second_derivative
#print axioms Zeta23.CCM.reciprocalAperture_euler_chain
#print axioms Zeta23.CCM.reciprocalAperture_strictConcaveOn
#print axioms Zeta23.CCM.concave_on_Icc_ge_min_endpoints
#print axioms Zeta23.CCM.concave_family_ge_of_endpoint_ge

#print axioms Zeta23.CCM.evenRayleighBottom_ge_endpoint_min_of_reciprocal_concavity

#print axioms Zeta23.CCM.evenRayleighBottom_ge_endpoint_min_of_raw_reciprocal_concavity

#print axioms Zeta23.CCM.evenRayleighBottom_ge_endpoint_min_of_nativeEuler

#print axioms Zeta23.CCM.canonical_evenFixedEnergy_contDiffOn_two
#print axioms Zeta23.CCM.evenRayleighBottom_ge_endpoint_min_of_M66
