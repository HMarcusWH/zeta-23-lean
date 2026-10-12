import Zeta23.CCM.CanonicalLocalBirdfishie
import Mathlib.Analysis.Convex.Deriv

noncomputable section

namespace Zeta23.CCM

open Set Filter Topology

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
      simp only [Function.comp_def] <;> ring
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
  field_simp
  ring

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
    exact ((hf s⁻¹ hpos).continuousAt.comp s
      (continuousAt_inv₀ (ne_of_gt hspos))).continuousWithinAt
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi _) hCont
  intro s hsInt
  have hs : R⁻¹ < s := interior_subset hsInt
  have hspos : 0 < s := (inv_pos.mpr hR).trans hs
  have hpos : 0 < s⁻¹ := inv_pos.mpr hspos
  have hSR : (1 : ℝ) / R < s := by simpa [one_div] using hs
  have hmul : 1 < s * R := (div_lt_iff₀ hR).mp hSR
  have hless : s⁻¹ < R := by
    change 1 / s < R
    apply (div_lt_iff₀ hspos).mpr
    nlinarith [hmul]
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
theorem evenRayleighBottom_ge_endpoint_min_of_reciprocal_concavity
    {K : ℕ} {a L b : ℝ}
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
      simpa [F, productionContactFixedEnergy] using
        (parityRayleighBottom_le_rayleigh .even a K z hz)
    have hright : parityRayleighBottom .even b K ≤ F b⁻¹ := by
      simpa [F, productionContactFixedEnergy] using
        (parityRayleighBottom_le_rayleigh .even b K z hz)
    calc
      min (parityRayleighBottom .even a K)
          (parityRayleighBottom .even b K) ≤
          min (F a⁻¹) (F b⁻¹) := min_le_min hleft hright
      _ = min (F b⁻¹) (F a⁻¹) := min_comm _ _
      _ ≤ F L⁻¹ := hchord
      _ = productionContactFixedEnergy .even L K z / ‖z‖ ^ 2 := by
        simp [F]
  unfold parityRayleighBottom
  refine le_ciInf fun z => ?_
  simpa [productionContactFixedEnergy] using hpoint z.1 z.2

/-- The more economical WP1 bridge: it is enough to know *unnormalized*
fixed-vector source-energy concavity on reciprocal aperture.  The positive
norm-square denominator is independent of aperture, so the true canonical
Rayleigh bottom inherits the same endpoint lower bound.  No separate
positivity assumption is used. -/
theorem evenRayleighBottom_ge_endpoint_min_of_raw_reciprocal_concavity
    {K : ℕ} {a L b : ℝ}
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
        exact le_trans (min_le_left _ _) ((div_le_div_iff₀ hc).2 he)
      · have he : F a⁻¹ ≤ F L⁻¹ := by
          simpa [min_eq_right h] using hchord
        exact le_trans (min_le_right _ _) ((div_le_div_iff₀ hc).2 he)
    have hleft : parityRayleighBottom .even a K ≤ F a⁻¹ / ‖z‖ ^ 2 := by
      simpa [F, productionContactFixedEnergy] using
        (parityRayleighBottom_le_rayleigh .even a K z hz)
    have hright : parityRayleighBottom .even b K ≤ F b⁻¹ / ‖z‖ ^ 2 := by
      simpa [F, productionContactFixedEnergy] using
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
  unfold parityRayleighBottom
  refine le_ciInf fun z => ?_
  simpa [productionContactFixedEnergy] using hpoint z.1 z.2

end Zeta23.CCM

#print axioms Zeta23.CCM.reciprocalAperture_first_derivative
#print axioms Zeta23.CCM.reciprocalAperture_second_derivative
#print axioms Zeta23.CCM.reciprocalAperture_euler_chain
#print axioms Zeta23.CCM.reciprocalAperture_strictConcaveOn
#print axioms Zeta23.CCM.concave_on_Icc_ge_min_endpoints
#print axioms Zeta23.CCM.concave_family_ge_of_endpoint_ge

#print axioms Zeta23.CCM.evenRayleighBottom_ge_endpoint_min_of_reciprocal_concavity

#print axioms Zeta23.CCM.evenRayleighBottom_ge_endpoint_min_of_raw_reciprocal_concavity
