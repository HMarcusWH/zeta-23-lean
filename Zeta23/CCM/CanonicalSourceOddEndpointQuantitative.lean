import Zeta23.CCM.SourceFourierConvolution
import Zeta23.CCM.ConstrainedParity
import Zeta23.CCM.CanonicalPolePrimeDiscrepancy
import Zeta23.CCM.SourceLatticeCoordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section

namespace Zeta23.CCM

open Finset
open scoped BigOperators ComplexConjugate

/-!
# POST284 follow-up M45: quantitative endpoint negativity of the odd source (Step 82)

Let `u` be a legal odd coefficient vector on `[-K, K]` (`u ∈ oddBoundaryFlatSubspace K`,
so `M₁(u) = 0` and the cosine profile vanishes), write `m = |M₃(u)|` and
`T_u(t) = ∑ uₙ sin(n t)`.  The fifth-order sine Taylor bound
`|sin x - x + x³/6| ≤ |x|⁵/120` gives, for complex coefficients,

`T_u(t) = -(M₃(u)/6) t³ + R_u(t)`,  `|R_u(t)| ≤ B(u) |t|⁵ / 120`,

with `B(u) = ∑ |n|⁵ |uₙ| ≤ A_K ‖u‖`, `A_K = (2 ∑_{n=1}^K n¹⁰)^{1/2}` (finite-sum
Cauchy–Schwarz).  When `a² B(u) ≤ 5m` the remainder is at most a quarter of the
cubic term on `[0, a]`, so `Re(conj T_u(t) T_u(a - t)) ≥ (7/16)(m²/36) t³(a - t)³`.
Since `∫₀ᵃ t³(a - t)³ = a⁷/140` and the source energy is
`-(1/π) ∫₀^{2πω} conj T_u(t) T_u(2πω - t)` (the existing convolution theorem), for
`0 ≤ ω` with `(2πω)² B(u) ≤ 5m`

`Re e_u(ω) ≤ -(π⁶/90) m² ω⁷`,

and in particular for `0 ≤ ω ≤ θ(u) = (1/2π) √(5m / (A_K ‖u‖))` on the actual
`sourceAtomRealEnergy`.  The aperture form is `Re e_u(a/2π) ≤ -7 m² a⁷ / (80640 π)`.

Scope: the elementary `sourceMatrix` only.  The strict sign needs `M₃(u) ≠ 0`
and `ω > 0`; the higher-moment filtrations (`M₃ = 0`, e.g. the `K = 3` odd
fifth-moment witness) make the bound vacuous.  Nothing here is a sign of the
canonical arithmetic test, a contact estimate, or an exclusion theorem; the
contact transfer (M46's `θ_*`) and the prime estimates are separate obligations.
-/

/-! ## Fifth-order sine Taylor bound -/

/-- `cos x ≤ 1 - x²/2 + x⁴/24` for `0 ≤ x`. -/
theorem cos_le_one_sub_sq_div_two_add_pow_four {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv (t : ℝ) : deriv f t = -t + t ^ 3 / 6 + Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    have := Real.sin_ge_sub_cube (le_of_lt ht)
    linarith
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [f] at h
  norm_num at h
  linarith

/-- `sin x ≤ x - x³/6 + x⁵/120` for `0 ≤ x`. -/
theorem sin_le_sub_cube_add_pow_five {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hderiv (t : ℝ) : deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    have := cos_le_one_sub_sq_div_two_add_pow_four (le_of_lt ht)
    linarith
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [f] at h
  norm_num at h
  linarith

/-- **Fifth-order sine Taylor bound** `|sin x - (x - x³/6)| ≤ |x|⁵/120` for every real `x`. -/
theorem abs_sin_sub_sub_cube_le (x : ℝ) :
    |Real.sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 / 120 := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_le]
    have h1 := Real.sin_ge_sub_cube hx
    have h2 := sin_le_sub_cube_add_pow_five hx
    have h5 : 0 ≤ x ^ 5 := pow_nonneg hx 5
    constructor <;> linarith
  · have hx' : 0 ≤ -x := neg_nonneg.mpr hx
    rw [abs_of_nonpos hx, abs_le]
    have h1 := Real.sin_ge_sub_cube hx'
    have h2 := sin_le_sub_cube_add_pow_five hx'
    have h5 : 0 ≤ (-x) ^ 5 := pow_nonneg hx' 5
    have e3 : (-x) ^ 3 = -x ^ 3 := by ring
    have e5 : (-x) ^ 5 = -x ^ 5 := by ring
    rw [Real.sin_neg, e3] at h1 h2
    rw [e5] at h2 h5
    constructor <;> linarith

/-! ## Odd profiles -/

/-- The cosine profile of a raw odd coefficient vector vanishes identically. -/
theorem sourceCosProfile_eq_zero_of_mem_odd {K : ℕ} {u : Fin (2 * K + 1) → ℂ}
    (hu : u ∈ oddCoefficientSubspace K) (t : ℝ) : sourceCosProfile K u t = 0 := by
  have hrev := (mem_oddCoefficientSubspace_iff K u).mp hu
  have hS : sourceCosProfile K u t = -sourceCosProfile K u t := by
    unfold sourceCosProfile
    conv_lhs => rw [← Equiv.sum_comp Fin.revPerm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi : u i.rev = -u i := by simpa [reverseCoefficients] using congrFun hrev i
    simp only [Fin.revPerm_apply, centeredIndex_rev, hi]
    push_cast
    simp only [neg_mul, Complex.cos_neg]
  linear_combination hS / 2

/-- Fifth-order Taylor remainder of the sine profile after the linear and cubic terms. -/
def sourceSinTaylorRemainder (K : ℕ) (u : Fin (2 * K + 1) → ℂ) (t : ℝ) : ℂ :=
  ∑ i, u i * ((Real.sin ((centeredIndex K i : ℝ) * t) -
    ((centeredIndex K i : ℝ) * t - ((centeredIndex K i : ℝ) * t) ^ 3 / 6) : ℝ) : ℂ)

/-- With `M₁(u) = 0`, `T_u(t) = -(M₃(u)) t³/6 + R_u(t)`. -/
theorem sourceSinProfile_eq_cubic_add_remainder {K : ℕ} {u : Fin (2 * K + 1) → ℂ}
    (h1 : centeredMoment K 1 u = 0) (t : ℝ) :
    sourceSinProfile K u t =
      -(centeredMoment K 3 u * ((t ^ 3 / 6 : ℝ) : ℂ)) + sourceSinTaylorRemainder K u t := by
  have key : sourceSinProfile K u t -
      (-(centeredMoment K 3 u * ((t ^ 3 / 6 : ℝ) : ℂ)) + sourceSinTaylorRemainder K u t) =
      centeredMoment K 1 u * (t : ℂ) := by
    unfold sourceSinProfile sourceSinTaylorRemainder centeredMoment
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [h1, zero_mul, sub_eq_zero] at key
  exact key

/-- The weighted coefficient mass `B(u) = ∑ |n|⁵ |uₙ|`. -/
def sourceOddTaylorWeight (K : ℕ) (u : Fin (2 * K + 1) → ℂ) : ℝ :=
  ∑ i, |(centeredIndex K i : ℝ)| ^ 5 * ‖u i‖

theorem sourceOddTaylorWeight_nonneg (K : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    0 ≤ sourceOddTaylorWeight K u :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- `|R_u(t)| ≤ B(u) |t|⁵ / 120`, for complex coefficients. -/
theorem norm_sourceSinTaylorRemainder_le (K : ℕ) (u : Fin (2 * K + 1) → ℂ) (t : ℝ) :
    ‖sourceSinTaylorRemainder K u t‖ ≤ sourceOddTaylorWeight K u * |t| ^ 5 / 120 := by
  unfold sourceSinTaylorRemainder sourceOddTaylorWeight
  calc ‖∑ i, u i * ((Real.sin ((centeredIndex K i : ℝ) * t) -
          ((centeredIndex K i : ℝ) * t - ((centeredIndex K i : ℝ) * t) ^ 3 / 6) : ℝ) : ℂ)‖
      ≤ ∑ i, ‖u i * ((Real.sin ((centeredIndex K i : ℝ) * t) -
          ((centeredIndex K i : ℝ) * t - ((centeredIndex K i : ℝ) * t) ^ 3 / 6) : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, |(centeredIndex K i : ℝ)| ^ 5 * ‖u i‖ * |t| ^ 5 / 120 := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h : |Real.sin ((centeredIndex K i : ℝ) * t) -
              ((centeredIndex K i : ℝ) * t - ((centeredIndex K i : ℝ) * t) ^ 3 / 6)| ≤
            |(centeredIndex K i : ℝ)| ^ 5 * |t| ^ 5 / 120 := by
          calc _ ≤ |(centeredIndex K i : ℝ) * t| ^ 5 / 120 := abs_sin_sub_sub_cube_le _
            _ = _ := by rw [abs_mul, mul_pow]
        calc ‖u i‖ * |Real.sin ((centeredIndex K i : ℝ) * t) -
              ((centeredIndex K i : ℝ) * t - ((centeredIndex K i : ℝ) * t) ^ 3 / 6)|
            ≤ ‖u i‖ * (|(centeredIndex K i : ℝ)| ^ 5 * |t| ^ 5 / 120) :=
              mul_le_mul_of_nonneg_left h (norm_nonneg _)
          _ = |(centeredIndex K i : ℝ)| ^ 5 * ‖u i‖ * |t| ^ 5 / 120 := by ring
    _ = (∑ i, |(centeredIndex K i : ℝ)| ^ 5 * ‖u i‖) * |t| ^ 5 / 120 := by
        rw [Finset.sum_mul, Finset.sum_div]

/-! ## Product lower bound and the beta integral -/

/-- Two complex perturbations of at most a quarter each keep `7/16` of an aligned product. -/
theorem seven_sixteenths_le_re_conj_add_mul_add {c d r s : ℂ}
    (hcd : (conj c * d).re = ‖c‖ * ‖d‖) (hr : ‖r‖ ≤ ‖c‖ / 4) (hs : ‖s‖ ≤ ‖d‖ / 4) :
    7 / 16 * (‖c‖ * ‖d‖) ≤ (conj (c + r) * (d + s)).re := by
  have e : conj (c + r) * (d + s) = conj c * d + conj c * s + conj r * d + conj r * s := by
    rw [map_add]
    ring
  have b : ∀ z w : ℂ, -(‖z‖ * ‖w‖) ≤ (conj z * w).re := by
    intro z w
    have h := Complex.abs_re_le_norm (conj z * w)
    rw [norm_mul, Complex.norm_conj] at h
    linarith [neg_abs_le (conj z * w).re]
  rw [e, Complex.add_re, Complex.add_re, Complex.add_re, hcd]
  have b1 := b c s
  have b2 := b r d
  have b3 := b r s
  have hc := norm_nonneg c
  have hd := norm_nonneg d
  have p1 : ‖c‖ * ‖s‖ ≤ ‖c‖ * (‖d‖ / 4) := mul_le_mul_of_nonneg_left hs hc
  have p2 : ‖r‖ * ‖d‖ ≤ ‖c‖ / 4 * ‖d‖ := mul_le_mul_of_nonneg_right hr hd
  have p3 : ‖r‖ * ‖s‖ ≤ ‖c‖ / 4 * (‖d‖ / 4) :=
    mul_le_mul hr hs (norm_nonneg s) (by positivity)
  nlinarith

/-- `∫₀ᵃ t³ (a - t)³ dt = a⁷ / 140`. -/
theorem integral_cube_mul_cube (a : ℝ) :
    ∫ t in (0 : ℝ)..a, t ^ 3 * (a - t) ^ 3 = a ^ 7 / 140 := by
  let F : ℝ → ℝ := fun t =>
    a ^ 3 / 4 * t ^ 4 - 3 * a ^ 2 / 5 * t ^ 5 + a / 2 * t ^ 6 - 1 / 7 * t ^ 7
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) a, HasDerivAt F (x ^ 3 * (a - x) ^ 3) x := by
    intro x _
    have h := ((((hasDerivAt_pow 4 x).const_mul (a ^ 3 / 4)).sub
      ((hasDerivAt_pow 5 x).const_mul (3 * a ^ 2 / 5))).add
        ((hasDerivAt_pow 6 x).const_mul (a / 2))).sub ((hasDerivAt_pow 7 x).const_mul (1 / 7))
    have e : a ^ 3 / 4 * ((4 : ℕ) * x ^ (4 - 1)) - 3 * a ^ 2 / 5 * ((5 : ℕ) * x ^ (5 - 1)) +
        a / 2 * ((6 : ℕ) * x ^ (6 - 1)) - 1 / 7 * ((7 : ℕ) * x ^ (7 - 1)) =
        x ^ 3 * (a - x) ^ 3 := by
      push_cast
      ring
    rw [e] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun t : ℝ => t ^ 3 * (a - t) ^ 3).intervalIntegrable _ _)]
  simp only [F]
  ring

/-! ## The quantitative odd endpoint bound -/

/-- Pointwise lower bound on the odd convolution integrand. -/
theorem re_conj_sourceSinProfile_mul_ge {K : ℕ} {u : Fin (2 * K + 1) → ℂ}
    (h1 : centeredMoment K 1 u = 0) {a t : ℝ} (ht0 : 0 ≤ t) (hta : t ≤ a)
    (hθ : a ^ 2 * sourceOddTaylorWeight K u ≤ 5 * ‖centeredMoment K 3 u‖) :
    7 / 16 * (‖centeredMoment K 3 u‖ ^ 2 / 36) * (t ^ 3 * (a - t) ^ 3) ≤
      (conj (sourceSinProfile K u t) * sourceSinProfile K u (a - t)).re := by
  set M := centeredMoment K 3 u with hM
  set m := ‖M‖ with hm
  set B := sourceOddTaylorWeight K u with hB
  have hB0 : 0 ≤ B := sourceOddTaylorWeight_nonneg K u
  have hm0 : 0 ≤ m := norm_nonneg M
  have hs0 : 0 ≤ a - t := by linarith
  rw [sourceSinProfile_eq_cubic_add_remainder h1 t,
    sourceSinProfile_eq_cubic_add_remainder h1 (a - t)]
  have hnorm : ∀ x : ℝ, 0 ≤ x → ‖-(M * ((x ^ 3 / 6 : ℝ) : ℂ))‖ = m * (x ^ 3 / 6) := by
    intro x hx
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hrem : ∀ x : ℝ, 0 ≤ x → x ≤ a →
      ‖sourceSinTaylorRemainder K u x‖ ≤ ‖-(M * ((x ^ 3 / 6 : ℝ) : ℂ))‖ / 4 := by
    intro x hx hxa
    rw [hnorm x hx]
    have h := norm_sourceSinTaylorRemainder_le K u x
    rw [abs_of_nonneg hx] at h
    have hx2 : x ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hx hxa 2
    have hBx : B * x ^ 2 ≤ 5 * m := by nlinarith
    have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx 3
    have : B * x ^ 5 ≤ 5 * m * x ^ 3 := by
      have e : B * x ^ 5 = (B * x ^ 2) * x ^ 3 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hBx hx3
    calc ‖sourceSinTaylorRemainder K u x‖ ≤ B * x ^ 5 / 120 := h
      _ ≤ 5 * m * x ^ 3 / 120 := by linarith
      _ = m * (x ^ 3 / 6) / 4 := by ring
  have hcd : (conj (-(M * ((t ^ 3 / 6 : ℝ) : ℂ))) * -(M * (((a - t) ^ 3 / 6 : ℝ) : ℂ))).re =
      ‖-(M * ((t ^ 3 / 6 : ℝ) : ℂ))‖ * ‖-(M * (((a - t) ^ 3 / 6 : ℝ) : ℂ))‖ := by
    rw [hnorm t ht0, hnorm (a - t) hs0]
    have e : conj (-(M * ((t ^ 3 / 6 : ℝ) : ℂ))) * -(M * (((a - t) ^ 3 / 6 : ℝ) : ℂ)) =
        (conj M * M) * (((t ^ 3 / 6) * ((a - t) ^ 3 / 6) : ℝ) : ℂ) := by
      simp only [map_neg, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [e, Complex.conj_mul', ← hm]
    have e2 : ((m : ℂ) ^ 2 * (((t ^ 3 / 6) * ((a - t) ^ 3 / 6) : ℝ) : ℂ)) =
        ((m ^ 2 * ((t ^ 3 / 6) * ((a - t) ^ 3 / 6)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e2, Complex.ofReal_re]
    ring
  have hmain := seven_sixteenths_le_re_conj_add_mul_add hcd (hrem t ht0 hta)
    (hrem (a - t) hs0 (by linarith))
  rw [hnorm t ht0, hnorm (a - t) hs0] at hmain
  calc 7 / 16 * (m ^ 2 / 36) * (t ^ 3 * (a - t) ^ 3)
      = 7 / 16 * (m * (t ^ 3 / 6) * (m * ((a - t) ^ 3 / 6))) := by ring
    _ ≤ _ := hmain

/-- **M45 (Step 82).**  For a legal odd `u` and `0 ≤ ω` with `(2πω)² B(u) ≤ 5 |M₃(u)|`,
`Re e_u(ω) ≤ -(π⁶/90) |M₃(u)|² ω⁷` on the actual elementary `sourceMatrix`. -/
theorem re_quadraticForm_sourceMatrix_le_of_mem_oddBoundaryFlat
    {K : ℕ} {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ oddBoundaryFlatSubspace K)
    {ω : ℝ} (hω : 0 ≤ ω)
    (hθ : (2 * Real.pi * ω) ^ 2 * sourceOddTaylorWeight K u ≤ 5 * ‖centeredMoment K 3 u‖) :
    (quadraticForm (sourceMatrix ω K) u).re ≤
      -(Real.pi ^ 6 / 90) * ‖centeredMoment K 3 u‖ ^ 2 * ω ^ 7 := by
  obtain ⟨hflat, hodd⟩ := Submodule.mem_inf.mp hu
  have h1 : centeredMoment K 1 u = 0 := ((mem_boundaryFlatSubspace_iff K u).mp hflat).2.1
  rw [quadraticForm_sourceMatrix_eq_convolution]
  set a := 2 * Real.pi * ω with ha
  set m := ‖centeredMoment K 3 u‖ with hm
  have hpi := Real.pi_pos
  have ha0 : 0 ≤ a := by positivity
  have hT : Continuous (sourceSinProfile K u) := by
    unfold sourceSinProfile
    fun_prop
  have hg : Continuous fun t : ℝ =>
      conj (sourceSinProfile K u t) * sourceSinProfile K u (a - t) :=
    (Complex.continuous_conj.comp hT).mul (hT.comp (continuous_const.sub continuous_id))
  have hint : ∀ t : ℝ,
      (conj (sourceCosProfile K u t) * sourceCosProfile K u (a - t) -
        conj (sourceSinProfile K u t) * sourceSinProfile K u (a - t)) =
        -(conj (sourceSinProfile K u t) * sourceSinProfile K u (a - t)) := by
    intro t
    rw [sourceCosProfile_eq_zero_of_mem_odd hodd t,
      sourceCosProfile_eq_zero_of_mem_odd hodd (a - t)]
    simp
  simp_rw [hint]
  rw [intervalIntegral.integral_neg, Complex.re_ofReal_mul, Complex.neg_re]
  have hre : (∫ t in (0 : ℝ)..a,
      conj (sourceSinProfile K u t) * sourceSinProfile K u (a - t)).re =
      ∫ t in (0 : ℝ)..a, (conj (sourceSinProfile K u t) * sourceSinProfile K u (a - t)).re := by
    have h := Complex.reCLM.intervalIntegral_comp_comm
      (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 a)
    simpa using h.symm
  rw [hre]
  have hmono : ∫ t in (0 : ℝ)..a, 7 / 16 * (m ^ 2 / 36) * (t ^ 3 * (a - t) ^ 3) ≤
      ∫ t in (0 : ℝ)..a, (conj (sourceSinProfile K u t) * sourceSinProfile K u (a - t)).re := by
    apply intervalIntegral.integral_mono_on ha0
    · exact (by fun_prop : Continuous fun t : ℝ =>
        7 / 16 * (m ^ 2 / 36) * (t ^ 3 * (a - t) ^ 3)).intervalIntegrable _ _
    · exact (Complex.continuous_re.comp hg).intervalIntegrable _ _
    · intro t ht
      exact re_conj_sourceSinProfile_mul_ge h1 ht.1 ht.2 hθ
  rw [intervalIntegral.integral_const_mul, integral_cube_mul_cube] at hmono
  have hinv : 0 ≤ 1 / Real.pi := by positivity
  calc 1 / Real.pi * -(∫ t in (0 : ℝ)..a,
        (conj (sourceSinProfile K u t) * sourceSinProfile K u (a - t)).re)
      ≤ 1 / Real.pi * -(7 / 16 * (m ^ 2 / 36) * (a ^ 7 / 140)) :=
        mul_le_mul_of_nonneg_left (neg_le_neg hmono) hinv
    _ = -(Real.pi ^ 6 / 90) * m ^ 2 * ω ^ 7 := by
        rw [ha]
        field_simp
        ring

/-- Strict form: with `M₃(u) ≠ 0` and `ω > 0` the source energy is strictly negative. -/
theorem re_quadraticForm_sourceMatrix_neg_of_mem_oddBoundaryFlat
    {K : ℕ} {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ oddBoundaryFlatSubspace K)
    (hM : centeredMoment K 3 u ≠ 0) {ω : ℝ} (hω : 0 < ω)
    (hθ : (2 * Real.pi * ω) ^ 2 * sourceOddTaylorWeight K u ≤ 5 * ‖centeredMoment K 3 u‖) :
    (quadraticForm (sourceMatrix ω K) u).re < 0 := by
  have h := re_quadraticForm_sourceMatrix_le_of_mem_oddBoundaryFlat hu hω.le hθ
  have hpos : 0 < Real.pi ^ 6 / 90 * ‖centeredMoment K 3 u‖ ^ 2 * ω ^ 7 := by
    have := norm_pos_iff.mpr hM
    have := Real.pi_pos
    positivity
  linarith

/-- Aperture form `Re e_u(a/2π) ≤ -7 m² a⁷ / (80640 π)` for `0 ≤ a`, `a² B(u) ≤ 5m`. -/
theorem re_quadraticForm_sourceMatrix_aperture_le_of_mem_oddBoundaryFlat
    {K : ℕ} {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ oddBoundaryFlatSubspace K)
    {a : ℝ} (ha : 0 ≤ a)
    (hθ : a ^ 2 * sourceOddTaylorWeight K u ≤ 5 * ‖centeredMoment K 3 u‖) :
    (quadraticForm (sourceMatrix (a / (2 * Real.pi)) K) u).re ≤
      -(7 * ‖centeredMoment K 3 u‖ ^ 2 * a ^ 7 / (80640 * Real.pi)) := by
  have hpi := Real.pi_pos
  have hω : 2 * Real.pi * (a / (2 * Real.pi)) = a := by field_simp
  have h := re_quadraticForm_sourceMatrix_le_of_mem_oddBoundaryFlat hu
    (ω := a / (2 * Real.pi)) (by positivity) (by rw [hω]; exact hθ)
  calc _ ≤ _ := h
    _ = -(7 * ‖centeredMoment K 3 u‖ ^ 2 * a ^ 7 / (80640 * Real.pi)) := by
        field_simp
        ring

/-! ## Cauchy–Schwarz constant `A_K` and the Euclidean angle `θ(u)` -/

/-- `A_K = (∑_{|n| ≤ K} n¹⁰)^{1/2}`; see `sourceOddTaylorConstant_sq`. -/
def sourceOddTaylorConstant (K : ℕ) : ℝ :=
  Real.sqrt (∑ i : Fin (2 * K + 1), (centeredIndex K i : ℝ) ^ 10)

theorem sourceOddTaylorConstant_nonneg (K : ℕ) : 0 ≤ sourceOddTaylorConstant K :=
  Real.sqrt_nonneg _

/-- `A_K² = 2 ∑_{n=1}^K n¹⁰`. -/
theorem sourceOddTaylorConstant_sq (K : ℕ) :
    sourceOddTaylorConstant K ^ 2 = 2 * ∑ n ∈ Finset.range (K + 1), (n : ℝ) ^ 10 := by
  unfold sourceOddTaylorConstant
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  rw [sum_centeredIndex_eq_sum_latticeBox K (fun n : ℤ => (n : ℝ) ^ 10)]
  induction K with
  | zero => simp [latticeBox]
  | succ K ih =>
    have hbox : latticeBox (K + 1) =
        insert (-((K + 1 : ℕ) : ℤ)) (insert ((K + 1 : ℕ) : ℤ) (latticeBox K)) := by
      ext n
      simp only [mem_latticeBox, Finset.mem_insert]
      push_cast
      omega
    rw [hbox, Finset.sum_insert, Finset.sum_insert, ih, Finset.sum_range_succ _ (K + 1)]
    · push_cast
      ring
    · rw [mem_latticeBox]; omega
    · rw [Finset.mem_insert, mem_latticeBox]; omega

/-- Finite-sum Cauchy–Schwarz: `B(u) ≤ A_K ‖u‖₂`. -/
theorem sourceOddTaylorWeight_le (K : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    sourceOddTaylorWeight K u ≤
      sourceOddTaylorConstant K * Real.sqrt (∑ i, ‖u i‖ ^ 2) := by
  unfold sourceOddTaylorWeight sourceOddTaylorConstant
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => |(centeredIndex K i : ℝ)| ^ 5) (fun i => ‖u i‖)
  have e : ∑ i : Fin (2 * K + 1), (|(centeredIndex K i : ℝ)| ^ 5) ^ 2 =
      ∑ i : Fin (2 * K + 1), (centeredIndex K i : ℝ) ^ 10 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_mul, Even.pow_abs ⟨5, rfl⟩]
  rw [e] at h
  exact h

/-- **M45 on the actual `sourceAtomRealEnergy`.**  For `x` in the legal odd carrier and
`0 ≤ ω ≤ θ(x) = (1/2π) √(5 |M₃(x)| / (A_K ‖x‖))`,
`e_x(ω) ≤ -(π⁶/90) |M₃(x)|² ω⁷`. -/
theorem sourceAtomRealEnergy_le_of_le_oddEndpointAngle
    {K : ℕ} {x : EuclideanSpace ℂ (Fin (2 * K + 1))}
    (hx : (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x ∈ oddBoundaryFlatSubspace K)
    {ω : ℝ} (hω0 : 0 ≤ ω)
    (hω : ω ≤ 1 / (2 * Real.pi) *
      Real.sqrt (5 * ‖centeredMoment K 3 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)‖ /
        (sourceOddTaylorConstant K * ‖x‖))) :
    sourceAtomRealEnergy K x ω ≤
      -(Real.pi ^ 6 / 90) *
        ‖centeredMoment K 3 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)‖ ^ 2 * ω ^ 7 := by
  set u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x with hu
  set m := ‖centeredMoment K 3 u‖ with hm
  set A := sourceOddTaylorConstant K with hA
  have hpi := Real.pi_pos
  have hm0 : 0 ≤ m := norm_nonneg _
  have hA0 : 0 ≤ A := sourceOddTaylorConstant_nonneg K
  have hN : ‖x‖ = Real.sqrt (∑ i, ‖u i‖ ^ 2) := EuclideanSpace.norm_eq x
  have hB : sourceOddTaylorWeight K u ≤ A * ‖x‖ := by
    rw [hN]
    exact sourceOddTaylorWeight_le K u
  have hB0 := sourceOddTaylorWeight_nonneg K u
  have hθ : (2 * Real.pi * ω) ^ 2 * sourceOddTaylorWeight K u ≤ 5 * m := by
    rcases (mul_nonneg hA0 (norm_nonneg x)).eq_or_lt with h0 | hpos
    · have : sourceOddTaylorWeight K u ≤ 0 := by rw [← h0] at hB; exact hB
      have : sourceOddTaylorWeight K u = 0 := le_antisymm this hB0
      rw [this, mul_zero]
      positivity
    · have hq : 0 ≤ 5 * m / (A * ‖x‖) := by positivity
      have hle : 2 * Real.pi * ω ≤ Real.sqrt (5 * m / (A * ‖x‖)) := by
        have := mul_le_mul_of_nonneg_left hω (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
        calc 2 * Real.pi * ω ≤ 2 * Real.pi * (1 / (2 * Real.pi) *
              Real.sqrt (5 * m / (A * ‖x‖))) := this
          _ = Real.sqrt (5 * m / (A * ‖x‖)) := by field_simp
      have hsq : (2 * Real.pi * ω) ^ 2 ≤ 5 * m / (A * ‖x‖) := by
        have := pow_le_pow_left₀ (by positivity) hle 2
        rwa [Real.sq_sqrt hq] at this
      calc (2 * Real.pi * ω) ^ 2 * sourceOddTaylorWeight K u
          ≤ (2 * Real.pi * ω) ^ 2 * (A * ‖x‖) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
        _ ≤ 5 * m / (A * ‖x‖) * (A * ‖x‖) :=
            mul_le_mul_of_nonneg_right hsq hpos.le
        _ = 5 * m := div_mul_cancel₀ _ hpos.ne'
  exact re_quadraticForm_sourceMatrix_le_of_mem_oddBoundaryFlat hx hω0 hθ

end Zeta23.CCM

#print axioms Zeta23.CCM.cos_le_one_sub_sq_div_two_add_pow_four
#print axioms Zeta23.CCM.sin_le_sub_cube_add_pow_five
#print axioms Zeta23.CCM.abs_sin_sub_sub_cube_le
#print axioms Zeta23.CCM.sourceCosProfile_eq_zero_of_mem_odd
#print axioms Zeta23.CCM.sourceSinProfile_eq_cubic_add_remainder
#print axioms Zeta23.CCM.sourceOddTaylorWeight_nonneg
#print axioms Zeta23.CCM.norm_sourceSinTaylorRemainder_le
#print axioms Zeta23.CCM.seven_sixteenths_le_re_conj_add_mul_add
#print axioms Zeta23.CCM.integral_cube_mul_cube
#print axioms Zeta23.CCM.re_conj_sourceSinProfile_mul_ge
#print axioms Zeta23.CCM.re_quadraticForm_sourceMatrix_le_of_mem_oddBoundaryFlat
#print axioms Zeta23.CCM.re_quadraticForm_sourceMatrix_neg_of_mem_oddBoundaryFlat
#print axioms Zeta23.CCM.re_quadraticForm_sourceMatrix_aperture_le_of_mem_oddBoundaryFlat
#print axioms Zeta23.CCM.sourceOddTaylorConstant_nonneg
#print axioms Zeta23.CCM.sourceOddTaylorConstant_sq
#print axioms Zeta23.CCM.sourceOddTaylorWeight_le
#print axioms Zeta23.CCM.sourceAtomRealEnergy_le_of_le_oddEndpointAngle
