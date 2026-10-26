import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Topology
import Zeta23.OPICAFollowup.FiniteSpanSeparation
import Zeta23.OPICAFollowup.SquareDefect
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Actual-profile research controls

Witnesses in this file are actual strict-strip zeros. Source density and
canonical Jordan measures remain the inherited objects. Generic finite
linear algebra and normalized smooth tests are helpers; they do not assert
the missing arithmetic observations or complete the profile contracts.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped Topology ENNReal BigOperators SchwartzMap Manifold ContDiff InnerProductSpace RealInnerProductSpace
namespace Zeta23.OPICARound2

/-- One fixed actual off-critical witness, retained before any horizon varies. -/
structure ProfileWitness where
  rho : ℂ
  isZero : riemannZeta rho = 0
  right : (1 / 2 : ℝ) < rho.re
  strip : rho.re < 1
  upper : 0 < rho.im

def profileDelta (w : ProfileWitness) : ℝ := w.rho.re - 1 / 2
def profileGamma (w : ProfileWitness) : ℝ := w.rho.im
def profileQ (w : ProfileWitness) : ℂ := w.rho - 1 / 2
def profileKappa (w : ProfileWitness) : ℂ := OPICAFollowup.coPoissonKappa w.rho
def profileZ (w : ProfileWitness) : ℂ := profileKappa w / profileQ w

theorem profileDelta_pos (w : ProfileWitness) : 0 < profileDelta w := by
  unfold profileDelta
  linarith [w.right]

theorem profileDelta_lt_half (w : ProfileWitness) : profileDelta w < 1 / 2 := by
  unfold profileDelta
  linarith [w.strip]

theorem profileGamma_pos (w : ProfileWitness) : 0 < profileGamma w := w.upper

theorem profileQ_eq (w : ProfileWitness) :
    profileQ w = (profileDelta w : ℂ) + (profileGamma w : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [profileQ, profileDelta, profileGamma]

theorem profileRho_native (w : ProfileWitness) :
    OPICAFollowup.coPoissonRho (profileDelta w) (profileGamma w) = w.rho := by
  apply Complex.ext <;> simp [OPICAFollowup.coPoissonRho, profileDelta, profileGamma]

theorem profileKappa_eq (w : ProfileWitness) :
    profileKappa w = 1 / 4 - profileQ w ^ 2 := by
  unfold profileKappa OPICAFollowup.coPoissonKappa profileQ
  ring

theorem profileQ_ne_zero (w : ProfileWitness) : profileQ w ≠ 0 := by
  intro h
  have h := congrArg Complex.re h
  simp [profileQ] at h
  linarith [w.right]

theorem profileKappa_ne_zero (w : ProfileWitness) : profileKappa w ≠ 0 := by
  unfold profileKappa OPICAFollowup.coPoissonKappa
  apply mul_ne_zero
  · intro h
    have h := congrArg Complex.re h
    norm_num at h
    linarith [w.right]
  · intro h
    have h := congrArg Complex.re h
    norm_num at h
    linarith [w.strip]

theorem profileZ_ne_zero (w : ProfileWitness) : profileZ w ≠ 0 :=
  div_ne_zero (profileKappa_ne_zero w) (profileQ_ne_zero w)

/-- Literal inherited first-cell density, with its actual witness parameter. -/
def profileDensity (w : ProfileWitness) : ℝ → ℂ :=
  OPICAFollowup.coPoissonComplexDensity w.rho

theorem profileDensity_first_cell (w : ProfileWitness) {u : ℝ}
    (hu : 0 < u) (hu2 : u < Real.log 2) :
    profileDensity w (Real.exp u) = (Real.exp (-u / 2) : ℂ) * profileZ w *
      Complex.sinh (profileQ w * (u : ℂ)) := by
  have h := OPICAFollowup.coPoisson_first_cell_exp (profileDelta w) (profileGamma w) u
    (profileGamma_pos w).ne' hu hu2
  rw [profileRho_native, ← profileQ_eq, ← profileKappa_eq] at h
  exact h

def profileR (w : ProfileWitness) : ℝ := ‖profileQ w‖ ^ 2 + ‖profileKappa w‖
def profileUStar (w : ProfileWitness) : ℝ :=
  min (Real.log 2 / 2) (1 / Real.sqrt (profileR w))
def profileXStar (w : ProfileWitness) : ℝ := Real.exp (profileUStar w)
def profileMStar (w : ProfileWitness) : ℝ :=
  2 * profileDelta w * profileGamma w * profileUStar w * Real.exp (-profileUStar w / 2) *
    (1 - 1 / (2 * Real.exp 1))
def profileDerivativeBudget (w : ProfileWitness) : ℝ :=
  ‖profileZ w‖ * (‖profileQ w‖ + 1 / 2) * Real.cosh (profileDelta w * Real.log 2)

theorem profileR_pos (w : ProfileWitness) : 0 < profileR w := by
  unfold profileR
  have h := norm_pos_iff.mpr (profileQ_ne_zero w)
  nlinarith [norm_nonneg (profileKappa w)]

theorem profileUStar_pos (w : ProfileWitness) : 0 < profileUStar w := by
  unfold profileUStar
  apply lt_min
  · positivity
  · exact div_pos one_pos (Real.sqrt_pos.2 (profileR_pos w))

theorem profileUStar_lt_log_two (w : ProfileWitness) : profileUStar w < Real.log 2 := by
  have h := min_le_left (Real.log 2 / 2) (1 / Real.sqrt (profileR w))
  change profileUStar w ≤ _ at h
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

theorem profileXStar_mem (w : ProfileWitness) : profileXStar w ∈ Ioo (1 : ℝ) 2 := by
  constructor
  · exact Real.one_lt_exp_iff.mpr (profileUStar_pos w)
  · exact (Real.exp_lt_exp.mpr (profileUStar_lt_log_two w)).trans_eq
      (Real.exp_log (by norm_num))

theorem profileMStar_pos (w : ProfileWitness) : 0 < profileMStar w := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have ht : 0 < 1 - 1 / (2 * Real.exp 1) := by
    have hn : 0 < 2 * Real.exp 1 := by positivity
    apply sub_pos.mpr
    exact (div_lt_one hn).mpr (by linarith)
  unfold profileMStar
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (profileDelta_pos w))
    (profileGamma_pos w)) (profileUStar_pos w)) (Real.exp_pos _)) ht

theorem profileDerivativeBudget_pos (w : ProfileWitness) : 0 < profileDerivativeBudget w := by
  unfold profileDerivativeBudget
  exact mul_pos (mul_pos (norm_pos_iff.mpr (profileZ_ne_zero w))
    (by nlinarith [norm_nonneg (profileQ w)])) (Real.cosh_pos _)

def profileTestRadius (w : ProfileWitness) : ℝ :=
  min ((profileXStar w - 1) / 2)
    (min ((2 - profileXStar w) / 2) (profileMStar w / (4 * profileDerivativeBudget w)))

theorem profileTestRadius_pos (w : ProfileWitness) : 0 < profileTestRadius w := by
  have hx := profileXStar_mem w
  unfold profileTestRadius
  apply lt_min
  · linarith [hx.1]
  · apply lt_min
    · linarith [hx.2]
    · exact div_pos (profileMStar_pos w) (by have hd := profileDerivativeBudget_pos w; positivity)

def profileUnitBump (w : ProfileWitness) : ContDiffBump (profileXStar w) :=
  ⟨profileTestRadius w / 2, profileTestRadius w,
    half_pos (profileTestRadius_pos w), half_lt_self (profileTestRadius_pos w)⟩

def profileUnitTest (w : ProfileWitness) : 𝓢(ℝ, ℝ) :=
  ((profileUnitBump w).hasCompactSupport_normed (μ := volume)).toSchwartzMap
    ((profileUnitBump w).contDiff_normed (μ := volume))

theorem profileUnitTest_nonneg (w : ProfileWitness) (x : ℝ) : 0 ≤ profileUnitTest w x :=
  (profileUnitBump w).nonneg_normed (μ := volume) x

theorem profileUnitTest_integral (w : ProfileWitness) : (∫ x : ℝ, profileUnitTest w x) = 1 :=
  (profileUnitBump w).integral_normed (μ := volume)

theorem profileUnitTest_compact (w : ProfileWitness) : HasCompactSupport (profileUnitTest w) :=
  (profileUnitBump w).hasCompactSupport_normed (μ := volume)

theorem profileUnitTest_support (w : ProfileWitness) : tsupport (profileUnitTest w) ⊆ Ioo (1 : ℝ) 2 := by
  intro x hx
  have hb : x ∈ Metric.closedBall (profileXStar w) (profileTestRadius w) := by
    change x ∈ tsupport ((profileUnitBump w).normed volume) at hx
    rw [ContDiffBump.tsupport_normed_eq] at hx
    exact hx
  have hr1 := min_le_left ((profileXStar w - 1) / 2)
    (min ((2 - profileXStar w) / 2) (profileMStar w / (4 * profileDerivativeBudget w)))
  have hr2 := (min_le_right ((profileXStar w - 1) / 2)
    (min ((2 - profileXStar w) / 2) (profileMStar w / (4 * profileDerivativeBudget w)))).trans
      (min_le_left ((2 - profileXStar w) / 2) (profileMStar w / (4 * profileDerivativeBudget w)))
  change profileTestRadius w ≤ _ at hr1 hr2
  have hd : |x - profileXStar w| ≤ profileTestRadius w := by
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hb
  have ha := abs_le.mp hd
  have hc := profileXStar_mem w
  constructor <;> linarith [ha.1, ha.2, hc.1, hc.2]

/-- Conditional error threshold for the same fixed observation; this lemma
constructs neither a nonnegative arithmetic observation nor its error bound. -/
theorem profile_fixed_negative_pairing_contradiction (m P v : ℝ) (hm : 0 < m)
    (hneg : v ≤ -3 * m / 4) (hP : 0 ≤ P) (herr : |P - v| < 3 * m / 4) : False := by
  have hab := (le_abs_self (P - v)).trans_lt herr
  linarith

/-- Sharp failure of n one-sided real linear tests on a nonzero n-dimensional
space. This is exactly the linear task, with no point-sampling claim. -/
theorem profile_n_linear_tests_cannot_exclude {n : ℕ} (hn : 1 ≤ n)
    (F : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    ∃ a : Fin n → ℝ, a ≠ 0 ∧ ∀ i : Fin n, 0 ≤ F a i := by
  by_cases hi : Function.Injective F
  · have hs := LinearMap.injective_iff_surjective.mp hi
    obtain ⟨a, ha⟩ := hs (fun _ : Fin n => (1 : ℝ))
    refine ⟨a, ?_, ?_⟩
    · intro hz
      have h0 := congrFun ha ⟨0, by omega⟩
      rw [hz, map_zero] at h0
      norm_num at h0
    · intro i
      rw [ha]
      norm_num
  · rw [Function.Injective] at hi
    push_neg at hi
    obtain ⟨a, b, hab, hne⟩ := hi
    refine ⟨a - b, sub_ne_zero.mpr hne, ?_⟩
    intro i
    rw [map_sub, hab, sub_self]
    exact le_rfl


theorem profile_imaginary_product_bound (a b : ℂ) :
    |(a * b).im| ≤ ‖a‖ * |b.im| + |a.im| * ‖b‖ := by
  rw [Complex.mul_im]
  calc
    _ ≤ |a.re * b.im| + |a.im * b.re| := abs_add_le _ _
    _ = |a.re| * |b.im| + |a.im| * |b.re| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm a) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm b) (abs_nonneg _))

theorem profile_imaginary_power_bound (z : ℂ) (n : ℕ) :
    |(z ^ n).im| ≤ (n : ℝ) * ‖z‖ ^ (n - 1) * |z.im| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp := profile_imaginary_product_bound (z ^ n) z
    rw [norm_pow] at hp
    calc
      _ ≤ ‖z‖ ^ n * |z.im| + |(z ^ n).im| * ‖z‖ := hp
      _ ≤ ‖z‖ ^ n * |z.im| + ((n : ℝ) * ‖z‖ ^ (n - 1) * |z.im|) * ‖z‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right ih (norm_nonneg z))
      _ = ((n + 1 : ℕ) : ℝ) * ‖z‖ ^ ((n + 1) - 1) * |z.im| := by
        by_cases hn : n = 0
        · subst n; simp
        · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
          have he : ‖z‖ ^ (n - 1) * ‖z‖ = ‖z‖ ^ n := by
            rw [← pow_succ, Nat.sub_add_cancel hn1]
          rw [Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one]
          calc
            _ = ‖z‖ ^ n * |z.im| + (n : ℝ) * (‖z‖ ^ (n - 1) * ‖z‖) * |z.im| := by ring
            _ = _ := by rw [he]; ring

theorem profile_imaginary_coefficient_bound (w : ProfileWitness) (n : ℕ) :
    |(profileKappa w * (profileQ w ^ 2) ^ n).im| ≤
      |(profileKappa w).im| *
        ((‖profileQ w‖ ^ 2) ^ n + (n : ℝ) * ‖profileKappa w‖ * (‖profileQ w‖ ^ 2) ^ (n - 1)) := by
  have hk : (profileKappa w).im = -(profileQ w ^ 2).im := by
    rw [profileKappa_eq]
    norm_num
  have hi : |(profileQ w ^ 2).im| = |(profileKappa w).im| := by rw [hk, abs_neg]
  have hp := profile_imaginary_product_bound (profileKappa w) ((profileQ w ^ 2) ^ n)
  have hn := profile_imaginary_power_bound (profileQ w ^ 2) n
  rw [norm_pow, hi] at hn
  rw [norm_pow, norm_pow] at hp
  calc
    _ ≤ ‖profileKappa w‖ * |((profileQ w ^ 2) ^ n).im| +
      |(profileKappa w).im| * (‖profileQ w‖ ^ 2) ^ n := hp
    _ ≤ ‖profileKappa w‖ * ((n : ℝ) * (‖profileQ w‖ ^ 2) ^ (n - 1) * |(profileKappa w).im|) +
      |(profileKappa w).im| * (‖profileQ w‖ ^ 2) ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left hn (norm_nonneg (profileKappa w))) le_rfl
    _ = _ := by ring

/-- The exact entire-series coefficient sum used by the height-free margin. -/
theorem profile_factorial_margin_series :
    HasSum (fun n : ℕ => (n : ℝ) / ((2 * n + 1).factorial : ℝ))
      (1 / (2 * Real.exp 1)) := by
  have hc := Real.hasSum_cosh (1 : ℝ)
  have hs := Real.hasSum_sinh (1 : ℝ)
  simp only [one_pow] at hc hs
  have hdiff := (hc.sub hs).div_const 2
  have he (n : ℕ) :
      ((1 : ℝ) / ((2 * n).factorial : ℝ) - 1 / ((2 * n + 1).factorial : ℝ)) / 2 =
        (n : ℝ) / ((2 * n + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    have hf : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * n)
    have hn : (2 : ℝ) * n + 1 ≠ 0 := by positivity
    field_simp [hf, hn]
    <;> ring
  have hconst : (Real.cosh 1 - Real.sinh 1) / 2 = 1 / (2 * Real.exp 1) := by
    rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
    have hx := Real.exp_ne_zero (1 : ℝ)
    field_simp
    <;> ring
  simpa only [he, hconst] using hdiff


theorem profileR_uStar_sq_le_one (w : ProfileWitness) : profileR w * profileUStar w ^ 2 ≤ 1 := by
  have hu : profileUStar w ≤ 1 / Real.sqrt (profileR w) := min_le_right _ _
  have hsq : profileUStar w ^ 2 ≤ (1 / Real.sqrt (profileR w)) ^ 2 :=
    pow_le_pow_left₀ (profileUStar_pos w).le hu 2
  have hr := profileR_pos w
  have hs : Real.sqrt (profileR w) ^ 2 = profileR w := Real.sq_sqrt hr.le
  have hmul := mul_le_mul_of_nonneg_left hsq hr.le
  have he : profileR w * (1 / Real.sqrt (profileR w)) ^ 2 = 1 := by
    rw [one_div_pow, hs, mul_one_div_cancel hr.ne']
  exact hmul.trans_eq he

theorem profileQ_uStar_sq_le_one (w : ProfileWitness) :
    ‖profileQ w‖ ^ 2 * profileUStar w ^ 2 ≤ 1 := by
  have hr : ‖profileQ w‖ ^ 2 ≤ profileR w := by
    unfold profileR
    exact le_add_of_nonneg_right (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_right hr (sq_nonneg _)).trans (profileR_uStar_sq_le_one w)

theorem profile_sinh_norm_bound (a b : ℝ) :
    ‖Complex.sinh ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ Real.cosh a := by
  let z := Complex.sinh ((a : ℂ) + (b : ℂ) * Complex.I)
  obtain ⟨hr, hi⟩ := OPICAFollowup.coPoisson_sinh_re_im a b
  have hn : ‖z‖ ^ 2 = (Real.cosh a)^2 - (Real.cos b)^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    change z.re * z.re + z.im * z.im = _
    dsimp only [z]
    rw [hr, hi]
    have hh : Real.sinh a ^ 2 = Real.cosh a ^ 2 - 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq a]
    have ht : Real.sin b ^ 2 = 1 - Real.cos b ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq b]
    nlinarith [mul_self_nonneg (Real.cosh a), Real.sin_sq_add_cos_sq b,
      Real.cosh_sq_sub_sinh_sq a]
  change ‖z‖ ≤ _
  nlinarith [norm_nonneg z, Real.cosh_pos a, sq_nonneg (Real.cos b)]

theorem profile_cosh_re_im (a b : ℝ) :
    (Complex.cosh ((a : ℂ) + (b : ℂ) * Complex.I)).re = Real.cosh a * Real.cos b ∧
    (Complex.cosh ((a : ℂ) + (b : ℂ) * Complex.I)).im = Real.sinh a * Real.sin b := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [Complex.mul_re, Complex.mul_im, Complex.cosh_ofReal_re,
    Complex.sinh_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem profile_cosh_norm_bound (a b : ℝ) :
    ‖Complex.cosh ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ Real.cosh a := by
  let z := Complex.cosh ((a : ℂ) + (b : ℂ) * Complex.I)
  obtain ⟨hr, hi⟩ := profile_cosh_re_im a b
  have hn : ‖z‖ ^ 2 = (Real.cosh a)^2 - (Real.sin b)^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    change z.re * z.re + z.im * z.im = _
    dsimp only [z]
    rw [hr, hi]
    nlinarith [Real.sin_sq_add_cos_sq b, Real.cosh_sq_sub_sinh_sq a]
  change ‖z‖ ≤ _
  nlinarith [norm_nonneg z, Real.cosh_pos a, sq_nonneg (Real.sin b)]

def profileDensitySeriesTerm (w : ProfileWitness) (u : ℝ) (n : ℕ) : ℂ :=
  profileKappa w * (profileQ w ^ 2) ^ n * (u : ℂ) ^ (2 * n + 1) /
    ((2 * n + 1).factorial : ℂ)

theorem profileDensity_hasSum (w : ProfileWitness) (u : ℝ) :
    HasSum (profileDensitySeriesTerm w u)
      (profileZ w * Complex.sinh (profileQ w * (u : ℂ))) := by
  have h := (Complex.hasSum_sinh (profileQ w * (u : ℂ))).mul_left (profileZ w)
  apply h.congr_fun
  intro n
  have hp : (profileQ w * (u : ℂ)) ^ (2 * n + 1) =
      profileQ w * (profileQ w ^ 2) ^ n * (u : ℂ) ^ (2 * n + 1) := by
    rw [mul_pow, pow_succ, ← pow_mul]
    ring
  unfold profileDensitySeriesTerm profileZ
  rw [hp]
  have hq := profileQ_ne_zero w
  have hf : ((2 * n + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n + 1)
  field_simp [hq, hf]
  <;> ring


theorem profile_scaled_coefficient_bound (w : ProfileWitness) (u : ℝ)
    (hu : 0 ≤ u) (hR : profileR w * u ^ 2 ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    (((‖profileQ w‖ ^ 2) ^ n + (n : ℝ) * ‖profileKappa w‖ * (‖profileQ w‖ ^ 2) ^ (n - 1)) *
      u ^ (2 * n)) ≤ (n : ℝ) := by
  let Q : ℝ := ‖profileQ w‖ ^ 2
  let a : ℝ := Q * u ^ 2
  have hQ : 0 ≤ Q := sq_nonneg _
  have ha : 0 ≤ a := mul_nonneg hQ (sq_nonneg _)
  have hQle : Q ≤ profileR w := by
    unfold Q profileR
    exact le_add_of_nonneg_right (norm_nonneg _)
  have ha1 : a ≤ 1 := (mul_le_mul_of_nonneg_right hQle (sq_nonneg _)).trans hR
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hid : (Q ^ n + (n : ℝ) * ‖profileKappa w‖ * Q ^ (n - 1)) * u ^ (2 * n) =
      (a + (n : ℝ) * ‖profileKappa w‖ * u ^ 2) * a ^ (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn))
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    rw [show 2 * (k + 1) = 2 * k + 2 by omega,
      pow_add u (2 * k) 2, pow_mul u 2 k, pow_succ Q k]
    dsimp only [a]
    rw [mul_pow]
    ring
  change (Q ^ n + (n : ℝ) * ‖profileKappa w‖ * Q ^ (n - 1)) * u ^ (2 * n) ≤ _
  rw [hid]
  have hbase : 0 ≤ a + (n : ℝ) * ‖profileKappa w‖ * u ^ 2 := by positivity
  have hpow : a ^ (n - 1) ≤ 1 := pow_le_one₀ ha ha1
  have hlin : a + (n : ℝ) * ‖profileKappa w‖ * u ^ 2 ≤ (n : ℝ) * profileR w * u ^ 2 := by
    have hna := mul_le_mul_of_nonneg_right hnreal ha
    unfold profileR
    dsimp only [a, Q] at *
    nlinarith
  calc
    _ ≤ (a + (n : ℝ) * ‖profileKappa w‖ * u ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hpow hbase
    _ = a + (n : ℝ) * ‖profileKappa w‖ * u ^ 2 := mul_one _
    _ ≤ (n : ℝ) * profileR w * u ^ 2 := hlin
    _ ≤ (n : ℝ) := by nlinarith [mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg (α := ℝ) n)]

theorem profileDensitySeriesTerm_im_bound (w : ProfileWitness) (u : ℝ)
    (hu : 0 ≤ u) (hR : profileR w * u ^ 2 ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    |(profileDensitySeriesTerm w u n).im| ≤
      (u * |(profileKappa w).im|) * ((n : ℝ) / ((2 * n + 1).factorial : ℝ)) := by
  have hterm : (profileDensitySeriesTerm w u n).im =
      (profileKappa w * (profileQ w ^ 2) ^ n).im * u ^ (2 * n + 1) /
        ((2 * n + 1).factorial : ℝ) := by
    unfold profileDensitySeriesTerm
    rw [← Complex.ofReal_pow]
    rw [show ((2 * n + 1).factorial : ℂ) = (((2 * n + 1).factorial : ℝ) : ℂ) by simp]
    simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add]
  rw [hterm, abs_div, abs_mul, abs_of_nonneg (pow_nonneg hu _),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  have hc := profile_imaginary_coefficient_bound w n
  have hs := profile_scaled_coefficient_bound w u hu hR hn
  have hp : |(profileKappa w * (profileQ w ^ 2) ^ n).im| * u ^ (2 * n) ≤
      |(profileKappa w).im| * (n : ℝ) := by
    calc
      _ ≤ (|(profileKappa w).im| *
        ((‖profileQ w‖ ^ 2) ^ n + (n : ℝ) * ‖profileKappa w‖ * (‖profileQ w‖ ^ 2) ^ (n - 1))) *
          u ^ (2 * n) := mul_le_mul_of_nonneg_right hc (pow_nonneg hu _)
      _ = |(profileKappa w).im| *
        (((‖profileQ w‖ ^ 2) ^ n + (n : ℝ) * ‖profileKappa w‖ * (‖profileQ w‖ ^ 2) ^ (n - 1)) *
          u ^ (2 * n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  have hpu := mul_le_mul_of_nonneg_right hp hu
  have hf : 0 < ((2 * n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  calc
    _ = (|(profileKappa w * (profileQ w ^ 2) ^ n).im| * u ^ (2 * n) * u) /
      ((2 * n + 1).factorial : ℝ) := by rw [pow_succ]; ring
    _ ≤ (|(profileKappa w).im| * n * u) / ((2 * n + 1).factorial : ℝ) :=
      div_le_div_of_nonneg_right hpu hf.le
    _ = _ := by ring

def profileImaginaryRemainderTerm (w : ProfileWitness) (u : ℝ) (n : ℕ) : ℝ :=
  (profileDensitySeriesTerm w u n).im - if n = 0 then (profileKappa w).im * u else 0

theorem profileImaginaryRemainder_hasSum (w : ProfileWitness) (u : ℝ) :
    HasSum (profileImaginaryRemainderTerm w u)
      ((profileZ w * Complex.sinh (profileQ w * (u : ℂ))).im - (profileKappa w).im * u) := by
  have h := Complex.hasSum_im (profileDensity_hasSum w u)
  have h0 := hasSum_ite_eq (0 : ℕ) ((profileKappa w).im * u)
  simpa only [profileImaginaryRemainderTerm] using! h.sub h0

theorem profile_imaginary_remainder_bound (w : ProfileWitness) (u : ℝ)
    (hu : 0 ≤ u) (hR : profileR w * u ^ 2 ≤ 1) :
    |(profileZ w * Complex.sinh (profileQ w * (u : ℂ))).im - (profileKappa w).im * u| ≤
      u * |(profileKappa w).im| / (2 * Real.exp 1) := by
  have hb := (profileImaginaryRemainder_hasSum w u).norm_le_of_bounded
    (profile_factorial_margin_series.mul_left (u * |(profileKappa w).im|))
  have hpoint (n : ℕ) : ‖profileImaginaryRemainderTerm w u n‖ ≤
      (u * |(profileKappa w).im|) * ((n : ℝ) / ((2 * n + 1).factorial : ℝ)) := by
    by_cases hn : n = 0
    · subst n
      simp [profileImaginaryRemainderTerm, profileDensitySeriesTerm, Complex.mul_im]
    · simp only [profileImaginaryRemainderTerm, if_neg hn, sub_zero, Real.norm_eq_abs]
      exact profileDensitySeriesTerm_im_bound w u hu hR (Nat.one_le_iff_ne_zero.mpr hn)
  simpa only [Real.norm_eq_abs, div_eq_mul_inv, one_mul] using hb hpoint

theorem profileKappa_im (w : ProfileWitness) :
    (profileKappa w).im = -2 * profileDelta w * profileGamma w := by
  rw [profileKappa_eq, profileQ_eq]
  simp only [Complex.sub_im, Complex.div_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.mul_im, Complex.mul_re, Complex.I_im, Complex.I_re, pow_two]
  norm_num
  ring

/-- The explicit first-cell margin has no positive lower-height hypothesis. -/
theorem profile_height_free_point_margin (w : ProfileWitness) :
    profileMStar w ≤ -(profileDensity w (profileXStar w)).im := by
  have hr := profile_imaginary_remainder_bound w (profileUStar w)
    (profileUStar_pos w).le (profileR_uStar_sq_le_one w)
  have hk := profileKappa_im w
  have hsign : (profileKappa w).im < 0 := by rw [hk]; nlinarith [profileDelta_pos w, profileGamma_pos w]
  have ht := (le_abs_self ((profileZ w * Complex.sinh (profileQ w * (profileUStar w : ℂ))).im -
    (profileKappa w).im * profileUStar w)).trans hr
  rw [abs_of_neg hsign, hk] at ht
  have hm := mul_le_mul_of_nonneg_left ht (Real.exp_nonneg (-profileUStar w / 2))
  rw [profileXStar, profileDensity_first_cell w (profileUStar_pos w) (profileUStar_lt_log_two w), mul_assoc]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  unfold profileMStar
  simp only [Complex.mul_im] at hm
  ring_nf at hm ⊢
  linarith


def profileCellFunction (w : ProfileWitness) (x : ℝ) : ℂ :=
  (Real.exp (-Real.log x / 2) : ℂ) * profileZ w *
    Complex.sinh (profileQ w * (Real.log x : ℂ))

def profileCellDerivative (w : ProfileWitness) (x : ℝ) : ℂ :=
  (Real.exp (-Real.log x / 2) : ℂ) * profileZ w / (x : ℂ) *
    (profileQ w * Complex.cosh (profileQ w * (Real.log x : ℂ)) -
      (1 / 2 : ℂ) * Complex.sinh (profileQ w * (Real.log x : ℂ)))

theorem profileDensity_eq_cell (w : ProfileWitness) {x : ℝ} (hx : x ∈ Ioo (1 : ℝ) 2) :
    profileDensity w x = profileCellFunction w x := by
  have hx0 : 0 < x := lt_trans one_pos hx.1
  have h := profileDensity_first_cell w (Real.log_pos hx.1) (Real.log_lt_log hx0 hx.2)
  rw [Real.exp_log hx0] at h
  exact h

theorem profileCell_hasDerivAt (w : ProfileWitness) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (profileCellFunction w) (profileCellDerivative w x) x := by
  let e := Real.exp (-Real.log x / 2)
  let z := profileQ w * (Real.log x : ℂ)
  have hl := Real.hasDerivAt_log hx.ne'
  have he := ((Real.hasDerivAt_exp (-Real.log x / 2)).comp x (hl.neg.div_const 2)).ofReal_comp
  have ha := hl.ofReal_comp.const_mul (profileQ w)
  have hs := (Complex.hasDerivAt_sinh z).comp x ha
  have hh : HasDerivAt (profileCellFunction w)
      (((e * (-x⁻¹ / 2) : ℝ) : ℂ) * profileZ w * Complex.sinh z +
        ((e : ℂ) * profileZ w) * (Complex.cosh z * (profileQ w * (x⁻¹ : ℝ)))) x := by
    simpa only [profileCellFunction, e, z] using! (he.mul_const (profileZ w)).mul hs
  apply hh.congr_deriv
  unfold profileCellDerivative
  dsimp only [e, z]
  push_cast
  have hc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp [hc]
  <;> ring

theorem profileDensity_hasDerivAt (w : ProfileWitness) {x : ℝ} (hx : x ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (profileDensity w) (profileCellDerivative w x) x := by
  apply (profileCell_hasDerivAt w (lt_trans one_pos hx.1)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact profileDensity_eq_cell w hy

theorem profileCell_hyperbolic_bounds (w : ProfileWitness) {x : ℝ} (hx : x ∈ Ioo (1 : ℝ) 2) :
    ‖Complex.sinh (profileQ w * (Real.log x : ℂ))‖ ≤ Real.cosh (profileDelta w * Real.log 2) ∧
    ‖Complex.cosh (profileQ w * (Real.log x : ℂ))‖ ≤ Real.cosh (profileDelta w * Real.log 2) := by
  have hx0 : 0 < x := lt_trans one_pos hx.1
  have hxlog : 0 < Real.log x := Real.log_pos hx.1
  have hlog : Real.log x ≤ Real.log 2 := (Real.log_lt_log hx0 hx.2).le
  have ha : profileQ w * (Real.log x : ℂ) =
      ((profileDelta w * Real.log x : ℝ) : ℂ) +
        ((profileGamma w * Real.log x : ℝ) : ℂ) * Complex.I := by
    rw [profileQ_eq]
    push_cast
    ring
  have hc : Real.cosh (profileDelta w * Real.log x) ≤ Real.cosh (profileDelta w * Real.log 2) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg (profileDelta_pos w).le hxlog.le),
      abs_of_nonneg (mul_nonneg (profileDelta_pos w).le (Real.log_pos (by norm_num)).le)]
    exact mul_le_mul_of_nonneg_left hlog (profileDelta_pos w).le
  rw [ha]
  exact ⟨(profile_sinh_norm_bound _ _).trans hc, (profile_cosh_norm_bound _ _).trans hc⟩

theorem profileCellDerivative_norm_le (w : ProfileWitness) {x : ℝ} (hx : x ∈ Ioo (1 : ℝ) 2) :
    ‖profileCellDerivative w x‖ ≤ profileDerivativeBudget w := by
  have hx0 : 0 < x := lt_trans one_pos hx.1
  let e : ℝ := Real.exp (-Real.log x / 2)
  let c : ℝ := Real.cosh (profileDelta w * Real.log 2)
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.log_pos hx.1])
  have hef : e / x ≤ 1 := (div_le_one hx0).mpr (he1.trans hx.1.le)
  obtain ⟨hs, hc⟩ := profileCell_hyperbolic_bounds w hx
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  have hb : ‖profileQ w * Complex.cosh (profileQ w * (Real.log x : ℂ)) -
      (1 / 2 : ℂ) * Complex.sinh (profileQ w * (Real.log x : ℂ))‖ ≤
        (‖profileQ w‖ + 1 / 2) * c := by
    calc
      _ ≤ ‖profileQ w * Complex.cosh (profileQ w * (Real.log x : ℂ))‖ +
        ‖(1 / 2 : ℂ) * Complex.sinh (profileQ w * (Real.log x : ℂ))‖ := norm_sub_le _ _
      _ = ‖profileQ w‖ * ‖Complex.cosh (profileQ w * (Real.log x : ℂ))‖ +
        (1 / 2 : ℝ) * ‖Complex.sinh (profileQ w * (Real.log x : ℂ))‖ := by
          rw [norm_mul, norm_mul, hhalf]
      _ ≤ ‖profileQ w‖ * c + (1 / 2 : ℝ) * c := add_le_add
        (mul_le_mul_of_nonneg_left hc (norm_nonneg _)) (mul_le_mul_of_nonneg_left hs (by norm_num))
      _ = _ := by ring
  unfold profileCellDerivative
  simp only [norm_mul, norm_div, Complex.norm_real]
  rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_of_nonneg hx0.le]
  change e * ‖profileZ w‖ / x * _ ≤ _
  calc
    _ ≤ e * ‖profileZ w‖ / x * ((‖profileQ w‖ + 1 / 2) * c) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (e / x) * profileDerivativeBudget w := by unfold profileDerivativeBudget c; ring
    _ ≤ 1 * profileDerivativeBudget w :=
      mul_le_mul_of_nonneg_right hef (profileDerivativeBudget_pos w).le
    _ = _ := one_mul _

theorem profileDensity_cell_lipschitz (w : ProfileWitness) {x y : ℝ}
    (hx : x ∈ Ioo (1 : ℝ) 2) (hy : y ∈ Ioo (1 : ℝ) 2) :
    ‖profileDensity w y - profileDensity w x‖ ≤ profileDerivativeBudget w * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (ht : t ∈ Ioo (1 : ℝ) 2) =>
      (profileCell_hasDerivAt w (lt_trans one_pos ht.1)).hasDerivWithinAt)
    (fun t ht => profileCellDerivative_norm_le w ht) (convex_Ioo (1 : ℝ) 2) hx hy
  rw [← profileDensity_eq_cell w hx, ← profileDensity_eq_cell w hy] at h
  simpa only [Real.norm_eq_abs] using h


def profileComplexTest (phi : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℂ) := phi.postcompCLM Complex.ofRealCLM

theorem profileComplexTest_apply (phi : 𝓢(ℝ, ℝ)) (x : ℝ) :
    profileComplexTest phi x = (phi x : ℂ) := rfl

def profileImaginaryPairing (w : ProfileWitness) (phi : 𝓢(ℝ, ℝ)) : ℝ :=
  (OPICAFollowup.zeroMeasure w.rho).imPart.integral phi

theorem profile_integral_im_real_test (mu : OPICAFollowup.LocallyFiniteComplexMeasure)
    (phi : ℝ → ℝ) :
    (mu.integral (fun x : ℝ => (phi x : ℂ))).im = mu.imPart.integral phi := by
  simp only [OPICAFollowup.LocallyFiniteComplexMeasure.integral,
    Zeta23.OPICA.LocallyFiniteSignedMeasure.integral, integral_complex_ofReal,
    Complex.add_im, Complex.sub_im, Complex.sub_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, sub_zero, add_zero, zero_add]

theorem profile_cell_test_integer_zero (phi : 𝓢(ℝ, ℝ))
    (hsupp : tsupport phi ⊆ Ioo (1 : ℝ) 2) (n : ℤ) : phi (n : ℝ) = 0 := by
  by_contra hn
  have hs := hsupp (subset_closure (show (n : ℝ) ∈ Function.support phi from hn))
  have h1 : (1 : ℤ) < n := by exact_mod_cast hs.1
  have h2 : n < (2 : ℤ) := by exact_mod_cast hs.2
  omega

theorem profile_cell_pairing_eq_density (w : ProfileWitness) (phi : 𝓢(ℝ, ℝ))
    (hsupp : tsupport phi ⊆ Ioo (1 : ℝ) 2) :
    profileImaginaryPairing w phi = ∫ x : ℝ, phi x * (profileDensity w x).im := by
  have h0 : 0 < w.rho.re := by linarith [w.right]
  have hpair := OPICAFollowup.zeroMeasure_integral h0 w.strip (profileComplexTest phi)
  have hatom : (∑' n : ℤ, if n = 0 then (0 : ℂ) else profileComplexTest phi n) = 0 := by
    have hz (n : ℤ) : profileComplexTest phi n = 0 := by
      rw [profileComplexTest_apply, profile_cell_test_integer_zero phi hsupp n]
      rfl
    simp [hz]
  rw [hatom, sub_zero] at hpair
  have hfun : (profileComplexTest phi : ℝ → ℂ) = fun x : ℝ => (phi x : ℂ) := rfl
  have him := congrArg Complex.im hpair
  rw [hfun, profile_integral_im_real_test] at him
  change profileImaginaryPairing w phi =
    (∫ x : ℝ, profileDensity w x * (phi x : ℂ)).im at him
  have hg : Integrable (fun x : ℝ => profileDensity w x * (phi x : ℂ)) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => profileDensity w x * (phi x : ℂ)) volume :=
      (OPICAFollowup.measurable_coPoissonComplexDensity w.rho).aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp phi.continuous).aestronglyMeasurable
    apply ((profileComplexTest phi).integrable.norm.const_mul
      (OPICAFollowup.finiteSumSrhoBound w.rho / ‖OPICAFollowup.coPoissonOriginNormalizer w.rho‖)).mono' hm
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (OPICAFollowup.coPoissonComplexDensity_norm_le h0 w.strip x) (norm_nonneg _)
  have hcomm := Complex.imCLM.integral_comp_comm hg
  change (∫ x : ℝ, (profileDensity w x * (phi x : ℂ)).im) =
      (∫ x : ℝ, profileDensity w x * (phi x : ℂ)).im at hcomm
  rw [him, ← hcomm]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
  ring


theorem profileDensity_test_integrable (w : ProfileWitness) (phi : 𝓢(ℝ, ℝ)) :
    Integrable (fun x : ℝ => profileDensity w x * (phi x : ℂ)) := by
  have h0 : 0 < w.rho.re := by linarith [w.right]
  have hm : AEStronglyMeasurable (fun x : ℝ => profileDensity w x * (phi x : ℂ)) volume :=
    (OPICAFollowup.measurable_coPoissonComplexDensity w.rho).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp phi.continuous).aestronglyMeasurable
  apply ((profileComplexTest phi).integrable.norm.const_mul
    (OPICAFollowup.finiteSumSrhoBound w.rho / ‖OPICAFollowup.coPoissonOriginNormalizer w.rho‖)).mono' hm
  filter_upwards with x
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (OPICAFollowup.coPoissonComplexDensity_norm_le h0 w.strip x) (norm_nonneg _)

theorem profileTestRadius_budget (w : ProfileWitness) :
    profileDerivativeBudget w * profileTestRadius w ≤ profileMStar w / 4 := by
  have hr := (min_le_right ((profileXStar w - 1) / 2)
    (min ((2 - profileXStar w) / 2) (profileMStar w / (4 * profileDerivativeBudget w)))).trans
      (min_le_right ((2 - profileXStar w) / 2) (profileMStar w / (4 * profileDerivativeBudget w)))
  change profileTestRadius w ≤ _ at hr
  have hp : 0 < 4 * profileDerivativeBudget w := mul_pos (by norm_num) (profileDerivativeBudget_pos w)
  have hm := (le_div_iff₀ hp).mp hr
  nlinarith

theorem profileTestBall_subset_cell (w : ProfileWitness) :
    Metric.closedBall (profileXStar w) (profileTestRadius w) ⊆ Ioo (1 : ℝ) 2 := by
  intro x hx
  have hd : |x - profileXStar w| ≤ profileTestRadius w := by simpa only [Metric.mem_closedBall, Real.dist_eq] using hx
  have ha := abs_le.mp hd
  have hc := profileXStar_mem w
  have hr1 := min_le_left ((profileXStar w - 1) / 2)
    (min ((2 - profileXStar w) / 2) (profileMStar w / (4 * profileDerivativeBudget w)))
  have hr2 := (min_le_right ((profileXStar w - 1) / 2)
    (min ((2 - profileXStar w) / 2) (profileMStar w / (4 * profileDerivativeBudget w)))).trans
      (min_le_left ((2 - profileXStar w) / 2) (profileMStar w / (4 * profileDerivativeBudget w)))
  change profileTestRadius w ≤ _ at hr1 hr2
  constructor <;> linarith [ha.1, ha.2, hc.1, hc.2]

theorem profile_positive_test_margin (w : ProfileWitness) (phi : 𝓢(ℝ, ℝ))
    (hphi : ∀ x : ℝ, 0 ≤ phi x) (hunit : (∫ x : ℝ, phi x) = 1)
    (hsupp : tsupport phi ⊆ Metric.closedBall (profileXStar w) (profileTestRadius w)) :
    profileImaginaryPairing w phi ≤ -3 * profileMStar w / 4 := by
  have hcell := hsupp.trans (profileTestBall_subset_cell w)
  have hp (x : ℝ) : phi x * (profileDensity w x).im ≤ phi x * (-3 * profileMStar w / 4) := by
    by_cases hz : phi x = 0
    · simp [hz]
    · have hx : x ∈ Metric.closedBall (profileXStar w) (profileTestRadius w) :=
        hsupp (subset_closure (show x ∈ Function.support phi from hz))
      have hxc := profileTestBall_subset_cell w hx
      have hn := profileDensity_cell_lipschitz w (profileXStar_mem w) hxc
      have hd : |x - profileXStar w| ≤ profileTestRadius w := by
        simpa only [Metric.mem_closedBall, Real.dist_eq] using hx
      have hi : (profileDensity w x).im - (profileDensity w (profileXStar w)).im ≤
          ‖profileDensity w x - profileDensity w (profileXStar w)‖ := by
        rw [← Complex.sub_im]
        exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
      have ht := (mul_le_mul_of_nonneg_left hd (profileDerivativeBudget_pos w).le).trans
        (profileTestRadius_budget w)
      have hpoint : (profileDensity w x).im ≤ -3 * profileMStar w / 4 := by
        linarith [profile_height_free_point_margin w]
      exact mul_le_mul_of_nonneg_left hpoint (hphi x)
  have hg : Integrable (fun x : ℝ => phi x * (profileDensity w x).im) := by
    apply (profileDensity_test_integrable w phi).im.congr
    filter_upwards with x
    change (profileDensity w x * (phi x : ℂ)).im = phi x * (profileDensity w x).im
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
    ring
  calc
    _ = ∫ x : ℝ, phi x * (profileDensity w x).im := profile_cell_pairing_eq_density w phi hcell
    _ ≤ ∫ x : ℝ, phi x * (-3 * profileMStar w / 4) :=
      integral_mono hg (phi.integrable.mul_const _) hp
    _ = _ := by rw [integral_mul_const, hunit, one_mul]

theorem profileUnitTest_ball (w : ProfileWitness) :
    tsupport (profileUnitTest w) = Metric.closedBall (profileXStar w) (profileTestRadius w) := by
  change tsupport ((profileUnitBump w).normed volume) = _
  rw [ContDiffBump.tsupport_normed_eq]
  rfl

theorem profileUnitTest_pairing_margin (w : ProfileWitness) :
    profileImaginaryPairing w (profileUnitTest w) ≤ -3 * profileMStar w / 4 :=
  profile_positive_test_margin w (profileUnitTest w) (profileUnitTest_nonneg w)
    (profileUnitTest_integral w) (by rw [profileUnitTest_ball])

/-- Fixed actual zero, fixed imaginary direction, fixed positive unit test.
The positive native arithmetic observation and a smaller comparison error
are the unproved antecedents of the last conditional consumer. -/
theorem fixed_imaginary_direction_positive_test_margin (w : ProfileWitness) :
    0 < profileMStar w ∧
    profileMStar w ≤ -(profileDensity w (profileXStar w)).im ∧
    (∀ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
      HasDerivAt (profileDensity w) (profileCellDerivative w x) x ∧
        ‖profileCellDerivative w x‖ ≤ profileDerivativeBudget w) ∧
    (∃ phi : 𝓢(ℝ, ℝ), HasCompactSupport phi ∧ (∀ x : ℝ, 0 ≤ phi x) ∧
      (∫ x : ℝ, phi x) = 1 ∧ tsupport phi ⊆ Ioo (1 : ℝ) 2 ∧
      profileImaginaryPairing w phi ≤ -3 * profileMStar w / 4 ∧
      (∀ P : ℝ, 0 ≤ P → |P - profileImaginaryPairing w phi| < 3 * profileMStar w / 4 → False)) := by
  refine ⟨profileMStar_pos w, profile_height_free_point_margin w,
    fun _ hx => ⟨profileDensity_hasDerivAt w hx, profileCellDerivative_norm_le w hx⟩, profileUnitTest w,
    profileUnitTest_compact w, profileUnitTest_nonneg w, profileUnitTest_integral w,
    profileUnitTest_support w, profileUnitTest_pairing_margin w, ?_⟩
  intro P hP herr
  exact profile_fixed_negative_pairing_contradiction _ _ _ (profileMStar_pos w)
    (profileUnitTest_pairing_margin w) hP herr


/-- The imaginary-direction detector vanishes on the critical-line control.
No strict off-line margin is transported to delta zero. -/
theorem profile_critical_imaginary_density_zero (gamma u : ℝ) (hg : gamma ≠ 0)
    (hu : 0 < u) (hu2 : u < Real.log 2) :
    (OPICAFollowup.coPoissonComplexDensity (OPICAFollowup.coPoissonRho 0 gamma) (Real.exp u)).im = 0 := by
  have he := OPICAFollowup.coPoisson_first_cell_exp 0 gamma u hg hu hu2
  have hz : (((1 / 4 : ℂ) - (((0 : ℝ) : ℂ) + (gamma : ℂ) * Complex.I) ^ 2) /
      (((0 : ℝ) : ℂ) + (gamma : ℂ) * Complex.I)).re = 0 := by
    simpa only [zero_mul] using (OPICAFollowup.coPoisson_quotient_re_im 0 gamma hg).1
  have harg : (((0 : ℝ) : ℂ) + (gamma : ℂ) * Complex.I) * (u : ℂ) =
      ((0 : ℝ) : ℂ) + ((gamma * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hs : (Complex.sinh (((0 : ℝ) : ℂ) + ((gamma * u : ℝ) : ℂ) * Complex.I)).re = 0 := by
    simpa only [Real.sinh_zero, zero_mul] using
      (OPICAFollowup.coPoisson_sinh_re_im 0 (gamma * u)).1
  rw [harg] at he
  have hi := congrArg Complex.im he
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero] at hi
  rw [hz, hs] at hi
  simpa using hi


/-- The four explicit phase samples retain their strict height hypothesis. -/
def profileQuarterU (w : ProfileWitness) (j : Fin 4) : ℝ :=
  ((j.val + 1 : ℕ) : ℝ) * Real.pi / (2 * profileGamma w)

def profileQuarterX (w : ProfileWitness) (j : Fin 4) : ℝ := Real.exp (profileQuarterU w j)

def profileQuarterP (w : ProfileWitness) (j : Fin 4) : ℝ :=
  Real.exp (-profileQuarterU w j / 2) *
    (if j.val % 2 = 0 then Real.cosh (profileDelta w * profileQuarterU w j)
     else Real.sinh (profileDelta w * profileQuarterU w j))

def profileQuarterDirection (j : Fin 4) : ℂ :=
  if j.val = 0 then Complex.I else if j.val = 1 then -1 else if j.val = 2 then -Complex.I else 1

theorem profileQuarterU_pos (w : ProfileWitness) (j : Fin 4) : 0 < profileQuarterU w j := by
  unfold profileQuarterU
  exact div_pos (mul_pos (by positivity) Real.pi_pos) (by have h := profileGamma_pos w; positivity)

theorem profileQuarterU_lt_log_two (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) :
    profileQuarterU w j < Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh' := (div_lt_iff₀ hl).mp hh
  have hj : ((j.val + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show j.val + 1 ≤ 4 by omega)
  unfold profileQuarterU
  apply (div_lt_iff₀ (by have h := profileGamma_pos w; positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hj Real.pi_pos.le]

theorem profileQuarterX_mem (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) :
    profileQuarterX w j ∈ Ioo (1 : ℝ) 2 := by
  exact ⟨Real.one_lt_exp_iff.mpr (profileQuarterU_pos w j),
    (Real.exp_lt_exp.mpr (profileQuarterU_lt_log_two w hh j)).trans_eq (Real.exp_log (by norm_num))⟩

theorem profileQuarterP_pos (w : ProfileWitness) (j : Fin 4) : 0 < profileQuarterP w j := by
  unfold profileQuarterP
  apply mul_pos (Real.exp_pos _)
  split_ifs
  · exact Real.cosh_pos _
  · exact Real.sinh_pos_iff.mpr (mul_pos (profileDelta_pos w) (profileQuarterU_pos w j))

theorem profileQuarter_trig (w : ProfileWitness) (j : Fin 4) :
    profileGamma w * profileQuarterU w j = ((j.val + 1 : ℕ) : ℝ) * Real.pi / 2 := by
  unfold profileQuarterU
  field_simp [(profileGamma_pos w).ne']

theorem profileQuarter_sinh (w : ProfileWitness) (j : Fin 4) :
    Complex.sinh (profileQ w * (profileQuarterU w j : ℂ)) =
      profileQuarterDirection j *
        ((if j.val % 2 = 0 then Real.cosh (profileDelta w * profileQuarterU w j)
          else Real.sinh (profileDelta w * profileQuarterU w j) : ℝ) : ℂ) := by
  have harg : profileQ w * (profileQuarterU w j : ℂ) =
      ((profileDelta w * profileQuarterU w j : ℝ) : ℂ) +
        ((profileGamma w * profileQuarterU w j : ℝ) : ℂ) * Complex.I := by
    rw [profileQ_eq]; push_cast; ring
  rw [harg]
  obtain ⟨hr, hi⟩ := OPICAFollowup.coPoisson_sinh_re_im
    (profileDelta w * profileQuarterU w j) (profileGamma w * profileQuarterU w j)
  apply Complex.ext
  · rw [hr, profileQuarter_trig]
    fin_cases j <;> norm_num [profileQuarterDirection, Real.cos_pi_div_two, Real.cos_pi,
      show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring,
      show 4 * Real.pi / 2 = 2 * Real.pi by ring, Real.cos_add_pi, Real.cos_two_pi] <;>
      simp only [← Complex.ofReal_mul, Complex.cosh_ofReal_im, Complex.sinh_ofReal_re,
        Complex.cosh_ofReal_re, Complex.sinh_ofReal_im]
  · rw [hi, profileQuarter_trig]
    fin_cases j <;> norm_num [profileQuarterDirection, Real.sin_pi_div_two, Real.sin_pi,
      show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring,
      show 4 * Real.pi / 2 = 2 * Real.pi by ring, Real.sin_add_pi, Real.sin_two_pi] <;>
      simp only [← Complex.ofReal_mul, Complex.cosh_ofReal_im, Complex.sinh_ofReal_re,
        Complex.cosh_ofReal_re, Complex.sinh_ofReal_im]

theorem profileQuarter_density (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) :
    profileDensity w (profileQuarterX w j) =
      profileQuarterDirection j * profileZ w * (profileQuarterP w j : ℂ) := by
  rw [profileQuarterX, profileDensity_first_cell w (profileQuarterU_pos w j)
    (profileQuarterU_lt_log_two w hh j), profileQuarter_sinh]
  unfold profileQuarterP
  push_cast
  ring

def profileQuarterMin (w : ProfileWitness) : ℝ :=
  min (profileQuarterP w 0) (min (profileQuarterP w 1)
    (min (profileQuarterP w 2) (profileQuarterP w 3)))

def profileQuarterEta (w : ProfileWitness) : ℝ :=
  ‖profileZ w‖ * profileQuarterMin w / Real.sqrt 2

theorem profileQuarterMin_pos (w : ProfileWitness) : 0 < profileQuarterMin w := by
  exact lt_min (profileQuarterP_pos w 0) (lt_min (profileQuarterP_pos w 1)
    (lt_min (profileQuarterP_pos w 2) (profileQuarterP_pos w 3)))

theorem profileQuarterMin_le (w : ProfileWitness) (j : Fin 4) :
    profileQuarterMin w ≤ profileQuarterP w j := by
  unfold profileQuarterMin
  fin_cases j
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem profileQuarterEta_pos (w : ProfileWitness) : 0 < profileQuarterEta w :=
  div_pos (mul_pos (norm_pos_iff.mpr (profileZ_ne_zero w)) (profileQuarterMin_pos w))
    (Real.sqrt_pos.mpr (by norm_num))

/-- Elementary two-coordinate estimate, with the Euclidean normalization explicit. -/
theorem profile_complex_coordinate_large (z : ℂ) :
    ‖z‖ / Real.sqrt 2 ≤ |z.re| ∨ ‖z‖ / Real.sqrt 2 ≤ |z.im| := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  by_contra h
  push_neg at h
  have hr := (lt_div_iff₀ hs).mp h.1
  have hi := (lt_div_iff₀ hs).mp h.2
  have har : 0 ≤ |z.re| := abs_nonneg _
  have hai : 0 ≤ |z.im| := abs_nonneg _
  have ha : (|z.re| * Real.sqrt 2) ^ 2 < ‖z‖ ^ 2 :=
    sq_lt_sq₀ (mul_nonneg har hs.le) (norm_nonneg _) |>.mpr hr
  have hb : (|z.im| * Real.sqrt 2) ^ 2 < ‖z‖ ^ 2 :=
    sq_lt_sq₀ (mul_nonneg hai hs.le) (norm_nonneg _) |>.mpr hi
  rw [mul_pow, sq_abs, hs2] at ha hb
  nlinarith

theorem profileQuarter_point_margin (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (c : ℂ) :
    ∃ j : Fin 4, (c * profileDensity w (profileQuarterX w j)).re ≤
      -profileQuarterEta w * ‖c‖ := by
  let z := c * profileZ w
  have hnorm : ‖c‖ * ‖profileZ w‖ / Real.sqrt 2 = ‖z‖ / Real.sqrt 2 := by rw [← norm_mul]
  have hscale : profileQuarterEta w * ‖c‖ =
      profileQuarterMin w * (‖z‖ / Real.sqrt 2) := by
    unfold profileQuarterEta
    rw [show ‖z‖ = ‖c‖ * ‖profileZ w‖ from norm_mul _ _]
    ring
  have hval (j : Fin 4) : (c * profileDensity w (profileQuarterX w j)).re =
      (z * profileQuarterDirection j).re * profileQuarterP w j := by
    rw [profileQuarter_density w hh]
    change (c * (profileQuarterDirection j * profileZ w * (profileQuarterP w j : ℂ))).re = _
    rw [show c * (profileQuarterDirection j * profileZ w * (profileQuarterP w j : ℂ)) =
      (z * profileQuarterDirection j) * (profileQuarterP w j : ℂ) by dsimp [z]; ring]
    simp
  have hmul (j : Fin 4) (a : ℝ) (ha : 0 ≤ a) :
      profileQuarterMin w * a ≤ profileQuarterP w j * a :=
    mul_le_mul_of_nonneg_right (profileQuarterMin_le w j) ha
  rcases profile_complex_coordinate_large z with hr | hi
  · by_cases hs : 0 ≤ z.re
    · refine ⟨1, ?_⟩
      rw [hval, neg_mul, hscale]
      norm_num [profileQuarterDirection]
      rw [abs_of_nonneg hs] at hr
      have h := mul_le_mul_of_nonneg_left hr (profileQuarterMin_pos w).le
      nlinarith [hmul 1 z.re hs]
    · refine ⟨3, ?_⟩
      rw [hval, neg_mul, hscale]
      norm_num [profileQuarterDirection]
      rw [abs_of_neg (lt_of_not_ge hs)] at hr
      have h := mul_le_mul_of_nonneg_left hr (profileQuarterMin_pos w).le
      nlinarith [hmul 3 (-z.re) (by linarith)]
  · by_cases hs : 0 ≤ z.im
    · refine ⟨0, ?_⟩
      rw [hval, neg_mul, hscale]
      norm_num [profileQuarterDirection, Complex.mul_re]
      rw [abs_of_nonneg hs] at hi
      have h := mul_le_mul_of_nonneg_left hi (profileQuarterMin_pos w).le
      nlinarith [hmul 0 z.im hs]
    · refine ⟨2, ?_⟩
      rw [hval, neg_mul, hscale]
      norm_num [profileQuarterDirection, Complex.mul_re]
      rw [abs_of_neg (lt_of_not_ge hs)] at hi
      have h := mul_le_mul_of_nonneg_left hi (profileQuarterMin_pos w).le
      nlinarith [hmul 2 (-z.im) (by linarith)]


def profilePhasePairing (w : ProfileWitness) (c : ℂ) (phi : 𝓢(ℝ, ℝ)) : ℝ :=
  ((OPICAFollowup.zeroMeasure w.rho).scale c).rePart.integral phi

theorem profile_integral_re_real_test (mu : OPICAFollowup.LocallyFiniteComplexMeasure)
    (phi : ℝ → ℝ) :
    (mu.integral (fun x : ℝ => (phi x : ℂ))).re = mu.rePart.integral phi := by
  simp only [OPICAFollowup.LocallyFiniteComplexMeasure.integral,
    Zeta23.OPICA.LocallyFiniteSignedMeasure.integral, integral_complex_ofReal,
    Complex.add_re, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, sub_zero, add_zero, zero_add, sub_self]

theorem profile_cell_phase_pairing_eq_density (w : ProfileWitness) (c : ℂ) (phi : 𝓢(ℝ, ℝ))
    (hsupp : tsupport phi ⊆ Ioo (1 : ℝ) 2) :
    profilePhasePairing w c phi = ∫ x : ℝ, phi x * (c * profileDensity w x).re := by
  have h0 : 0 < w.rho.re := by linarith [w.right]
  have hpair := OPICAFollowup.zeroMeasure_integral h0 w.strip (profileComplexTest phi)
  have hatom : (∑' n : ℤ, if n = 0 then (0 : ℂ) else profileComplexTest phi n) = 0 := by
    have hz (n : ℤ) : profileComplexTest phi n = 0 := by
      rw [profileComplexTest_apply, profile_cell_test_integer_zero phi hsupp n]
      rfl
    simp [hz]
  rw [hatom, sub_zero] at hpair
  have hscale := OPICAFollowup.FiniteSpan.complex_integral_scale
    (OPICAFollowup.zeroMeasure w.rho) (OPICAFollowup.zeroMeasure_hasLinearGrowth h0 w.strip)
    c (profileComplexTest phi)
  have hr := congrArg Complex.re hscale
  change (((OPICAFollowup.zeroMeasure w.rho).scale c).integral
    (fun x : ℝ => (phi x : ℂ))).re = _ at hr
  rw [profile_integral_re_real_test, hpair] at hr
  have hg := (profileDensity_test_integrable w phi).const_mul c
  have hcomm := Complex.reCLM.integral_comp_comm hg
  change (∫ x : ℝ, (c * (profileDensity w x * (phi x : ℂ))).re) =
    (∫ x : ℝ, c * (profileDensity w x * (phi x : ℂ))).re at hcomm
  calc
    _ = (c * ∫ x : ℝ, profileDensity w x * (phi x : ℂ)).re := hr
    _ = (∫ x : ℝ, c * (profileDensity w x * (phi x : ℂ))).re := by rw [integral_const_mul]
    _ = ∫ x : ℝ, (c * (profileDensity w x * (phi x : ℂ))).re := hcomm.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [show c * (profileDensity w x * (phi x : ℂ)) =
        (c * profileDensity w x) * (phi x : ℂ) by ring]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring

def profileQuarterPointRadius (w : ProfileWitness) (j : Fin 4) : ℝ :=
  min ((profileQuarterX w j - 1) / 2) ((2 - profileQuarterX w j) / 2)

def profileQuarterRadius (w : ProfileWitness) : ℝ :=
  min (profileQuarterPointRadius w 0)
    (min (profileQuarterPointRadius w 1) (min (profileQuarterPointRadius w 2)
      (min (profileQuarterPointRadius w 3) (profileQuarterEta w / (4 * profileDerivativeBudget w)))))

theorem profileQuarterRadius_pos (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) : 0 < profileQuarterRadius w := by
  have hp (j : Fin 4) : 0 < profileQuarterPointRadius w j := by
    have hx := profileQuarterX_mem w hh j
    exact lt_min (by linarith [hx.1]) (by linarith [hx.2])
  exact lt_min (hp 0) (lt_min (hp 1) (lt_min (hp 2) (lt_min (hp 3)
    (div_pos (profileQuarterEta_pos w) (by have hd := profileDerivativeBudget_pos w; positivity)))))

theorem profileQuarterRadius_le (w : ProfileWitness) (j : Fin 4) :
    profileQuarterRadius w ≤ profileQuarterPointRadius w j := by
  unfold profileQuarterRadius
  fin_cases j
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))

theorem profileQuarterRadius_budget (w : ProfileWitness) :
    profileDerivativeBudget w * profileQuarterRadius w ≤ profileQuarterEta w / 4 := by
  have hr : profileQuarterRadius w ≤ profileQuarterEta w / (4 * profileDerivativeBudget w) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hp : 0 < 4 * profileDerivativeBudget w := by have h := profileDerivativeBudget_pos w; positivity
  have hb := (le_div_iff₀ hp).mp hr
  nlinarith

theorem profileQuarterBall_subset_cell (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) :
    Metric.closedBall (profileQuarterX w j) (profileQuarterRadius w) ⊆ Ioo (1 : ℝ) 2 := by
  intro x hx
  have ha : |x - profileQuarterX w j| ≤ profileQuarterRadius w := by
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hx
  have hl := (profileQuarterRadius_le w j).trans
    (min_le_left ((profileQuarterX w j - 1) / 2) ((2 - profileQuarterX w j) / 2))
  have hr := (profileQuarterRadius_le w j).trans
    (min_le_right ((profileQuarterX w j - 1) / 2) ((2 - profileQuarterX w j) / 2))
  have hc := profileQuarterX_mem w hh j
  constructor <;> linarith [(abs_le.mp ha).1, (abs_le.mp ha).2, hc.1, hc.2]

def profileQuarterBump (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) :
    ContDiffBump (profileQuarterX w j) :=
  ⟨profileQuarterRadius w / 2, profileQuarterRadius w,
    half_pos (profileQuarterRadius_pos w hh), half_lt_self (profileQuarterRadius_pos w hh)⟩

def profileQuarterTest (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) : 𝓢(ℝ, ℝ) :=
  ((profileQuarterBump w hh j).hasCompactSupport_normed (μ := volume)).toSchwartzMap
    ((profileQuarterBump w hh j).contDiff_normed (μ := volume))

theorem profileQuarterTest_nonneg (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) (x : ℝ) :
    0 ≤ profileQuarterTest w hh j x := (profileQuarterBump w hh j).nonneg_normed (μ := volume) x

theorem profileQuarterTest_integral (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) :
    (∫ x : ℝ, profileQuarterTest w hh j x) = 1 := (profileQuarterBump w hh j).integral_normed (μ := volume)

theorem profileQuarterTest_compact (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) :
    HasCompactSupport (profileQuarterTest w hh j) := (profileQuarterBump w hh j).hasCompactSupport_normed (μ := volume)

theorem profileQuarterTest_ball (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) :
    tsupport (profileQuarterTest w hh j) = Metric.closedBall (profileQuarterX w j) (profileQuarterRadius w) := by
  change tsupport ((profileQuarterBump w hh j).normed volume) = _
  rw [ContDiffBump.tsupport_normed_eq]
  rfl

theorem profileQuarterTest_support (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) :
    tsupport (profileQuarterTest w hh j) ⊆ Ioo (1 : ℝ) 2 := by
  rw [profileQuarterTest_ball]
  exact profileQuarterBall_subset_cell w hh j

theorem profileQuarter_test_margin (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (c : ℂ) :
    ∃ j : Fin 4, profilePhasePairing w c (profileQuarterTest w hh j) ≤
      -profileQuarterEta w * ‖c‖ / 2 := by
  obtain ⟨j, hj⟩ := profileQuarter_point_margin w hh c
  refine ⟨j, ?_⟩
  let phi := profileQuarterTest w hh j
  have hcell := profileQuarterTest_support w hh j
  have hp (x : ℝ) : phi x * (c * profileDensity w x).re ≤
      phi x * (-3 * profileQuarterEta w * ‖c‖ / 4) := by
    by_cases hz : phi x = 0
    · simp [hz]
    · have hx : x ∈ Metric.closedBall (profileQuarterX w j) (profileQuarterRadius w) := by
        rw [← profileQuarterTest_ball w hh j]
        exact subset_closure (show x ∈ Function.support phi from hz)
      have hxc := profileQuarterBall_subset_cell w hh j hx
      have hn := profileDensity_cell_lipschitz w (profileQuarterX_mem w hh j) hxc
      have hd : |x - profileQuarterX w j| ≤ profileQuarterRadius w := by
        simpa only [Metric.mem_closedBall, Real.dist_eq] using hx
      have hr : (c * profileDensity w x).re - (c * profileDensity w (profileQuarterX w j)).re ≤
          ‖c‖ * ‖profileDensity w x - profileDensity w (profileQuarterX w j)‖ := by
        rw [← Complex.sub_re, ← mul_sub, ← norm_mul]
        exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
      have hb := (mul_le_mul_of_nonneg_left hd (profileDerivativeBudget_pos w).le).trans
        (profileQuarterRadius_budget w)
      have hs := mul_le_mul_of_nonneg_left (hn.trans hb) (norm_nonneg c)
      have hm : (c * profileDensity w x).re ≤ -3 * profileQuarterEta w * ‖c‖ / 4 := by nlinarith
      exact mul_le_mul_of_nonneg_left hm (profileQuarterTest_nonneg w hh j x)
  have hg : Integrable (fun x : ℝ => phi x * (c * profileDensity w x).re) := by
    apply ((profileDensity_test_integrable w phi).const_mul c).re.congr
    filter_upwards with x
    change (c * (profileDensity w x * (phi x : ℂ))).re = phi x * (c * profileDensity w x).re
    rw [show c * (profileDensity w x * (phi x : ℂ)) = (c * profileDensity w x) * (phi x : ℂ) by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  calc
    _ = ∫ x : ℝ, phi x * (c * profileDensity w x).re := profile_cell_phase_pairing_eq_density w c phi hcell
    _ ≤ ∫ x : ℝ, phi x * (-3 * profileQuarterEta w * ‖c‖ / 4) :=
      integral_mono hg (phi.integrable.mul_const _) hp
    _ = -3 * profileQuarterEta w * ‖c‖ / 4 := by rw [integral_mul_const, profileQuarterTest_integral, one_mul]
    _ ≤ _ := by have hp := profileQuarterEta_pos w; nlinarith [norm_nonneg c]

/-- The same four physical pairings must be approximated by the nonnegative observations. -/
theorem profileQuarter_observation_error_floor (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (c : ℂ)
    (a0 epsilon : ℝ) (ha0 : 0 < a0) (hc : a0 ≤ ‖c‖) (P : Fin 4 → ℝ)
    (hP : ∀ j, 0 ≤ P j)
    (herr : ∀ j, |P j - profilePhasePairing w c (profileQuarterTest w hh j)| ≤ epsilon) :
    profileQuarterEta w * a0 / 2 ≤ epsilon := by
  obtain ⟨j, hj⟩ := profileQuarter_test_margin w hh c
  have he := le_trans (le_abs_self (P j - profilePhasePairing w c (profileQuarterTest w hh j))) (herr j)
  have hmul := mul_le_mul_of_nonneg_left hc (profileQuarterEta_pos w).le
  linarith [hP j]


/-- Fixed four physical tests, quantitative phase-complete margin, and a
conditional error floor. This theorem retains the explicit height premise. -/
theorem profile_four_positive_test_observability (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) :
    0 < profileQuarterEta w ∧ 0 < profileQuarterRadius w ∧
    (∀ j : Fin 4, profileQuarterX w j ∈ Ioo (1 : ℝ) 2 ∧
      profileDensity w (profileQuarterX w j) =
        profileQuarterDirection j * profileZ w * (profileQuarterP w j : ℂ) ∧
      HasCompactSupport (profileQuarterTest w hh j) ∧
      (∀ x : ℝ, 0 ≤ profileQuarterTest w hh j x) ∧
      (∫ x : ℝ, profileQuarterTest w hh j x) = 1 ∧
      tsupport (profileQuarterTest w hh j) ⊆ Ioo (1 : ℝ) 2) ∧
    (∀ c : ℂ, ∃ j : Fin 4, profilePhasePairing w c (profileQuarterTest w hh j) ≤
      -profileQuarterEta w * ‖c‖ / 2) ∧
    (∀ c : ℂ, ∀ a0 epsilon : ℝ, 0 < a0 → a0 ≤ ‖c‖ → ∀ P : Fin 4 → ℝ,
      (∀ j, 0 ≤ P j) →
      (∀ j, |P j - profilePhasePairing w c (profileQuarterTest w hh j)| ≤ epsilon) →
      profileQuarterEta w * a0 / 2 ≤ epsilon) := by
  exact ⟨profileQuarterEta_pos w, profileQuarterRadius_pos w hh,
    fun j => ⟨profileQuarterX_mem w hh j, profileQuarter_density w hh j,
      profileQuarterTest_compact w hh j, profileQuarterTest_nonneg w hh j,
      profileQuarterTest_integral w hh j, profileQuarterTest_support w hh j⟩,
    profileQuarter_test_margin w hh, profileQuarter_observation_error_floor w hh⟩

/-- Zero padding proves the same obstruction for every m at most n.
This is a one-sided real-linear test statement, not a point-sample theorem. -/
theorem profile_at_most_n_linear_tests_cannot_exclude {m n : ℕ} (hn : 1 ≤ n) (hm : m ≤ n)
    (F : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    ∃ a : Fin n → ℝ, a ≠ 0 ∧ ∀ i : Fin m, 0 ≤ F a i := by
  let G : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun a i => if h : i.val < m then F a ⟨i.val, h⟩ else 0
      map_add' := by
        intro a b
        funext i
        split_ifs with h <;> simp [h, map_add]
      map_smul' := by
        intro t a
        funext i
        split_ifs with h <;> simp [h, map_smul] }
  obtain ⟨a, ha, hG⟩ := profile_n_linear_tests_cannot_exclude hn G
  refine ⟨a, ha, fun i => ?_⟩
  have h := hG ⟨i.val, lt_of_lt_of_le i.isLt hm⟩
  simpa [G, i.isLt] using h



/-- Positivity on every smooth positive compact test in an open set detects
the actual negative Jordan measure there. No closed image-cone hypothesis
or finite total mass is imposed. -/
theorem profile_signed_nonnegative_of_positive_tests
    (nu : Zeta23.OPICA.LocallyFiniteSignedMeasure) (U : Set ℝ) (hU : IsOpen U)
    (htest : ∀ phi : 𝓢(ℝ, ℝ), HasCompactSupport phi → tsupport phi ⊆ U →
      (∀ x, 0 ≤ phi x) → 0 ≤ nu.integral phi) : nu.negative U = 0 := by
  by_contra hn
  let S := nu.mutuallySingular.nullSet
  have hS : MeasurableSet S := nu.mutuallySingular.measurableSet_nullSet
  have hposS : nu.positive S = 0 := nu.mutuallySingular.measure_nullSet
  have hnegSc : nu.negative Sᶜ = 0 := nu.mutuallySingular.measure_compl_nullSet
  have hUS : 0 < nu.negative (U ∩ S) := by
    rw [measure_inter_conull hnegSc]
    exact pos_iff_ne_zero.mpr hn
  obtain ⟨K, hKUS, hK, hnegK⟩ := (hU.measurableSet.inter hS).exists_lt_isCompact hUS
  have hKU : K ⊆ U := hKUS.trans inter_subset_left
  have hposK : nu.positive K = 0 := measure_mono_null (hKUS.trans inter_subset_right) hposS
  obtain ⟨O, hKO, hO, hposO⟩ := K.exists_isOpen_lt_of_lt (μ := nu.positive)
    (nu.negative K) (by rw [hposK]; exact hnegK)
  obtain ⟨W, hW, hKW, hWc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨V, hV, hKV, hVc⟩ := hK.exists_isOpen_closure_subset
    ((hO.inter (hU.inter hW)).mem_nhdsSet.mpr (fun x hx => ⟨hKO hx, hKU hx, hKW hx⟩))
  have hVcK : IsCompact (closure V) := hWc.of_isClosed_subset isClosed_closure
    (hVc.trans (inter_subset_right.trans inter_subset_right) |>.trans subset_closure)
  obtain ⟨f, hfdiff, hf01, hfsupp, hf1⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ, ℝ)) (n := (⊤ : ℕ∞)) hV hK.isClosed hKV
  have hfcomp : HasCompactSupport f := by
    change IsCompact (tsupport f)
    rw [tsupport, hfsupp]
    exact hVcK
  let phi : 𝓢(ℝ, ℝ) := hfcomp.toSchwartzMap hfdiff.contDiff
  have hphi : ∀ x, 0 ≤ phi x := fun x => (hf01 (mem_range_self x)).1
  have hphi1 : ∀ x, phi x ≤ 1 := fun x => (hf01 (mem_range_self x)).2
  have hsphi : tsupport phi = closure V := by change tsupport f = _; rw [tsupport, hfsupp]
  have hphiU : tsupport phi ⊆ U := by rw [hsphi]; exact hVc.trans (inter_subset_right.trans inter_subset_left)
  have hIpos : Integrable (phi : ℝ → ℝ) nu.positive := phi.continuous.integrable_of_hasCompactSupport hfcomp
  have hIneg : Integrable (phi : ℝ → ℝ) nu.negative := phi.continuous.integrable_of_hasCompactSupport hfcomp
  have hIcl : Integrable ((closure V).indicator (fun _ : ℝ => (1 : ℝ))) nu.positive := by
    exact by
      have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (closure V) nu.positive :=
        integrableOn_const hVcK.measure_lt_top.ne
      exact hi.integrable_indicator isClosed_closure.measurableSet
  have hIK : Integrable (K.indicator (fun _ : ℝ => (1 : ℝ))) nu.negative := by
    exact by
      have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) K nu.negative :=
        integrableOn_const hK.measure_lt_top.ne
      exact hi.integrable_indicator hK.measurableSet
  have hpos : (∫ x, phi x ∂nu.positive) ≤ nu.positive.real (closure V) := by
    rw [← integral_indicator_one isClosed_closure.measurableSet]
    apply integral_mono hIpos hIcl
    intro x
    by_cases hx : x ∈ closure V
    · rw [indicator_of_mem hx]; exact hphi1 x
    · rw [indicator_of_notMem hx]
      have hz : phi x = 0 := image_eq_zero_of_notMem_tsupport (by rwa [hsphi])
      rw [hz]
  have hneg : nu.negative.real K ≤ ∫ x, phi x ∂nu.negative := by
    rw [← integral_indicator_one hK.measurableSet]
    apply integral_mono hIK hIneg
    intro x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact (hf1 x).mp hx |>.ge
    · rw [indicator_of_notMem hx]; exact hphi x
  have hstrict : nu.positive.real (closure V) < nu.negative.real K := by
    apply ENNReal.toReal_lt_toReal (hVcK.measure_lt_top.ne) (hK.measure_lt_top.ne) |>.mpr
    exact (measure_mono (hVc.trans inter_subset_left)).trans_lt hposO
  have ht := htest phi hfcomp hphiU hphi
  change 0 ≤ (∫ x, phi x ∂nu.positive) - ∫ x, phi x ∂nu.negative at ht
  linarith


/-- A finite-dimensional cone with trivial positive polar is the whole
space, even when its image presentation is not closed. -/
theorem profile_finite_cone_eq_univ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (C : PointedCone ℝ E)
    (hdual : ∀ y : E, (∀ x : E, x ∈ C → 0 ≤ ⟪x, y⟫_ℝ) → y = 0) :
    (C : Set E) = univ := by
  let K : ProperCone ℝ E := ⟨C.closure, isClosed_closure⟩
  have hcl : closure (C : Set E) = univ := by
    apply eq_univ_of_forall
    intro x
    by_contra hx
    obtain ⟨y, hy, hxy⟩ := K.hyperplane_separation' hx
    have hz : y = 0 := hdual y (fun t ht => hy t (subset_closure ht))
    simpa [hz] using hxy
  have hA : (affineSpan ℝ (C : Set E) : Set E) = univ := by
    apply eq_univ_of_univ_subset
    rw [← hcl]
    exact closure_minimal (subset_affineSpan ℝ (C : Set E))
      (affineSpan ℝ (C : Set E)).closed_of_finiteDimensional
  have hAtop : affineSpan ℝ (C : Set E) = ⊤ := by
    apply SetLike.coe_injective
    simpa using hA
  have hi := C.convex.interior_nonempty_iff_affineSpan_eq_top.mpr hAtop
  have h := C.convex.interior_closure_eq_interior_of_nonempty_interior hi
  rw [hcl, interior_univ] at h
  apply eq_univ_of_univ_subset
  rw [h]
  exact interior_subset

open OPICAFollowup.FiniteSpan
open scoped InnerProductSpace

def profilePositiveOffLatticeTest (phi : 𝓢(ℝ, ℝ)) : Prop :=
  HasCompactSupport phi ∧ tsupport phi ⊆ Zeta23.OPICA.integerLatticeᶜ ∧ ∀ x, 0 ≤ phi x

def profileSignedObservation (nu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (hg : nu.HasLinearGrowth) : 𝓢(ℝ, ℝ) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((nu.distributionOfLinearGrowth hg).restrictScalars ℝ |>.comp
    (SchwartzMap.postcompCLM Complex.ofRealCLM))

theorem profileSignedObservation_apply (nu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (hg : nu.HasLinearGrowth) (phi : 𝓢(ℝ, ℝ)) :
    profileSignedObservation nu hg phi = nu.integral phi := by
  change ((nu.distributionOfLinearGrowth hg) (profileComplexTest phi)).re = nu.integral phi
  rw [Zeta23.OPICA.LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply]
  change ((∫ x, (phi x : ℂ) ∂nu.positive) - ∫ x, (phi x : ℂ) ∂nu.negative).re = _
  rw [integral_complex_ofReal, integral_complex_ofReal]
  rfl

def profileBasisObservation {n : ℕ} (basis : Fin n → List JetDatum)
    (hv : ∀ i, ∀ j ∈ basis i, ValidJet j) :
    𝓢(ℝ, ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi fun i => (profileSignedObservation (zeroJetRealSpan (basis i))
      (zeroJetRealSpan_growth _ (hv i))).toLinearMap)

theorem profileBasisObservation_apply {n : ℕ} (basis : Fin n → List JetDatum)
    (hv : ∀ i, ∀ j ∈ basis i, ValidJet j) (phi : 𝓢(ℝ, ℝ)) (i : Fin n) :
    profileBasisObservation basis hv phi i = (zeroJetRealSpan (basis i)).integral phi :=
  profileSignedObservation_apply (zeroJetRealSpan (basis i)) (zeroJetRealSpan_growth _ (hv i)) phi

def profilePositiveObservationCone {n : ℕ}
    (L : 𝓢(ℝ, ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) : PointedCone ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := {v | ∃ phi : 𝓢(ℝ, ℝ), profilePositiveOffLatticeTest phi ∧ L phi = v}
  zero_mem' := by
    refine ⟨0, ⟨?_, ?_, ?_⟩, map_zero L⟩
    · simp [HasCompactSupport]
    · simp
    · simp
  add_mem' := by
    rintro x y ⟨phi, hp, rfl⟩ ⟨psi, hq, rfl⟩
    refine ⟨phi + psi, ⟨hp.1.add hq.1, ?_, ?_⟩, map_add L phi psi⟩
    · exact (tsupport_add _ _).trans (union_subset hp.2.1 hq.2.1)
    · intro x; exact add_nonneg (hp.2.2 x) (hq.2.2 x)
  smul_mem' := by
    rintro t x ⟨phi, hp, rfl⟩
    refine ⟨(t.val : ℝ) • phi, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact hp.1.smul_left
    · exact (tsupport_smul_subset_right (fun _ : ℝ => t.val) (phi : ℝ → ℝ)).trans hp.2.1
    · intro x; exact mul_nonneg t.property (hp.2.2 x)
    · exact map_smul L t.val phi

theorem profile_combination_real_pairing {n : ℕ} (basis : Fin n → List JetDatum)
    (hv : ∀ i, ∀ j ∈ basis i, ValidJet j) (a : EuclideanSpace ℝ (Fin n))
    (phi : 𝓢(ℝ, ℝ)) :
    (zeroJetRealSpan (realBasisCombinationData basis (fun i => a i))).integral phi =
      ⟪profileBasisObservation basis hv phi, a⟫_ℝ := by
  have hd := realBasisCombination_distribution basis hv (fun i => a i)
  have he := congrArg (fun T : TemperedDistribution ℝ ℂ =>
    (T (profileComplexTest phi)).re) hd
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Complex.real_smul,
    map_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  rw [Complex.re_sum] at he
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  have hh (nu : Zeta23.OPICA.LocallyFiniteSignedMeasure) (hg : nu.HasLinearGrowth) :
      (nu.distributionOfLinearGrowth hg (profileComplexTest phi)).re = nu.integral phi := by
    exact profileSignedObservation_apply nu hg phi
  simp only [hh] at he
  rw [he, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [profileBasisObservation_apply]
  rfl

theorem profile_actual_basis_positive_test_realization {n : ℕ}
    (basis : Fin n → List JetDatum) (hv : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (hind : LinearIndependent ℝ (fun i => (zeroJetRealSpan (basis i)).distributionOfLinearGrowth
      (zeroJetRealSpan_growth _ (hv i)))) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ phi : 𝓢(ℝ, ℝ), profilePositiveOffLatticeTest phi ∧
      ∀ i, (zeroJetRealSpan (basis i)).integral phi = v i := by
  let L := profileBasisObservation basis hv
  let C := profilePositiveObservationCone L
  have hcone : (C : Set (EuclideanSpace ℝ (Fin n))) = univ := by
    apply profile_finite_cone_eq_univ
    intro a ha
    have hoff : (zeroJetRealSpan (realBasisCombinationData basis (fun i => a i))).OffLatticeNonnegative := by
      apply profile_signed_nonnegative_of_positive_tests _ _ (show IsClosed Zeta23.OPICA.integerLattice from Int.isClosedEmbedding_coe_real.isClosed_range).isOpen_compl
      intro phi hpc hpu hpn
      rw [profile_combination_real_pairing basis hv a phi]
      exact ha (L phi) ⟨phi, ⟨hpc, hpu, hpn⟩, rfl⟩
    have haz := independent_real_span_basis_coefficients_zero basis hv hind (fun i => a i) hoff
    ext i
    exact congrFun haz i
  have hvC : v ∈ C := by
    change v ∈ (C : Set (EuclideanSpace ℝ (Fin n)))
    rw [hcone]; trivial
  obtain ⟨phi, hp, hL⟩ := hvC
  refine ⟨phi, hp, fun i => ?_⟩
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) hL
  exact (profileBasisObservation_apply basis hv phi i).symm.trans hi


/-- Compactness is applied to one fixed finite family of real linear observations. -/
theorem profile_finite_linear_negative_margin {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ} (hm : 0 < m)
    (L : Fin m → E →L[ℝ] ℝ)
    (hneg : ∀ a : E, a ≠ 0 → ∃ j, L j a < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : E, ∃ j, L j a ≤ -c * ‖a‖ := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  let f : E → ℝ := fun a => Finset.univ.sup' hne (fun j => -L j a)
  have hf : Continuous f := Continuous.finset_sup'_apply hne (fun j _ => (L j).continuous.neg)
  have hp : ∀ a : E, a ≠ 0 → 0 < f a := by
    intro a ha
    obtain ⟨j, hj⟩ := hneg a ha
    exact (neg_pos.mpr hj).trans_le (Finset.le_sup' (fun j => -L j a) (Finset.mem_univ j))
  have hh : ∀ (r : ℝ), 0 ≤ r → ∀ a : E, f (r • a) = r * f a := by
    intro r hr a
    apply le_antisymm
    · apply Finset.sup'_le
      intro j hj
      change -(L j (r • a)) ≤ _
      rw [map_smul, smul_eq_mul, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun j => -L j a) hj) hr
    · obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' hne (fun j => -L j a)
      change r * Finset.univ.sup' hne (fun j => -L j a) ≤ _
      rw [he]
      have hb := Finset.le_sup' (fun j => -L j (r • a)) hj
      simpa only [f, map_smul, smul_eq_mul, ← mul_neg] using hb
  obtain ⟨c, hc, hb⟩ := OPICAFollowup.FixedBasisSupport.fixed_space_positive_homogeneous_budget f hf hp hh
  refine ⟨c, hc, fun a => ?_⟩
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' hne (fun j => -L j a)
  refine ⟨j, ?_⟩
  have h := hb a
  change c * ‖a‖ ≤ Finset.univ.sup' hne (fun j => -L j a) at h
  rw [he] at h
  linarith

def profileSimplexDirection (n : ℕ) (j : Fin (n + 1)) : EuclideanSpace ℝ (Fin n) :=
  if h : j.val < n then EuclideanSpace.single ⟨j.val, h⟩ 1
  else WithLp.toLp 2 (fun _ : Fin n => (-1 : ℝ))

theorem profileSimplexDirection_first (n : ℕ) (i : Fin n) :
    profileSimplexDirection n ⟨i.val, by omega⟩ = EuclideanSpace.single i 1 := by
  simp [profileSimplexDirection, i.isLt]

theorem profileSimplexDirection_last (n : ℕ) :
    profileSimplexDirection n (Fin.last n) = WithLp.toLp 2 (fun _ : Fin n => (-1 : ℝ)) := by
  simp [profileSimplexDirection]

theorem profileSimplex_negative {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) (ha : a ≠ 0) :
    ∃ j : Fin (n + 1), ⟪profileSimplexDirection n j, a⟫_ℝ < 0 := by
  by_contra h
  push_neg at h
  have hp (i : Fin n) : 0 ≤ a i := by
    have hi := h ⟨i.val, by omega⟩
    rw [profileSimplexDirection_first] at hi
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using hi
  have hs : (∑ i, a i) ≤ 0 := by
    have hi := h (Fin.last n)
    rw [profileSimplexDirection_last, PiLp.inner_apply] at hi
    simpa using hi
  have hz : ∀ i : Fin n, a i = 0 := by
    have he : (∑ i, a i) = 0 := le_antisymm hs (Finset.sum_nonneg fun i _ => hp i)
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp i)).mp he i (Finset.mem_univ i)
  apply ha
  ext i
  exact hz i


/-- Exact physical test realization and one fixed Euclidean observation margin.
There is no assertion of uniform support or recovery cost over changing bases. -/
def ProfileAdaptedBasisTests {n : ℕ} (basis : Fin n → List JetDatum)
    (hv : ∀ i, ∀ j ∈ basis i, ValidJet j) : Prop :=
  ∃ tests : Fin (n + 1) → 𝓢(ℝ, ℝ), ∃ c : ℝ, 0 < c ∧
    (∀ j, profilePositiveOffLatticeTest (tests j)) ∧
    (∀ j i, (zeroJetRealSpan (basis i)).integral (tests j) = profileSimplexDirection n j i) ∧
    (∀ a : EuclideanSpace ℝ (Fin n), ∃ j,
      (zeroJetRealSpan (realBasisCombinationData basis (fun i => a i))).integral (tests j) ≤ -c * ‖a‖) ∧
    (∀ a : EuclideanSpace ℝ (Fin n), ∀ a0 epsilon : ℝ, 0 < a0 → a0 ≤ ‖a‖ →
      ∀ P : Fin (n + 1) → ℝ, (∀ j, 0 ≤ P j) →
      (∀ j, |P j - (zeroJetRealSpan (realBasisCombinationData basis (fun i => a i))).integral
        (tests j)| ≤ epsilon) → c * a0 ≤ epsilon)

theorem profile_actual_basis_adapted_tests {n : ℕ} (basis : Fin n → List JetDatum)
    (hv : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (hind : LinearIndependent ℝ (fun i => (zeroJetRealSpan (basis i)).distributionOfLinearGrowth
      (zeroJetRealSpan_growth _ (hv i)))) : ProfileAdaptedBasisTests basis hv := by
  have ht (j : Fin (n + 1)) := profile_actual_basis_positive_test_realization basis hv hind
    (profileSimplexDirection n j)
  choose tests hp hobs using ht
  let L : Fin (n + 1) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun j => innerSL ℝ (profileSimplexDirection n j)
  obtain ⟨c, hc, hmargin⟩ := profile_finite_linear_negative_margin (Nat.zero_lt_succ n) L
    (fun a ha => profileSimplex_negative a ha)
  have hcomb (a : EuclideanSpace ℝ (Fin n)) (j : Fin (n + 1)) :
      (zeroJetRealSpan (realBasisCombinationData basis (fun i => a i))).integral (tests j) = L j a := by
    rw [profile_combination_real_pairing basis hv a (tests j)]
    have ho : profileBasisObservation basis hv (tests j) = profileSimplexDirection n j := by
      ext i
      rw [profileBasisObservation_apply]
      exact hobs j i
    rw [ho]
    rfl
  refine ⟨tests, c, hc, hp, hobs, ?_, ?_⟩
  · intro a
    obtain ⟨j, hj⟩ := hmargin a
    exact ⟨j, by rw [hcomb]; exact hj⟩
  · intro a a0 epsilon ha0 ha P hP herr
    obtain ⟨j, hj⟩ := hmargin a
    have he := (le_abs_self (P j - (zeroJetRealSpan
      (realBasisCombinationData basis (fun i => a i))).integral (tests j))).trans (herr j)
    rw [hcomb] at he
    have hm := mul_le_mul_of_nonneg_left ha hc.le
    linarith [hP j]

/-- Actual canonical Re/Im zero-measure independence is proved upstream,
including every actual multiplicity at order zero. No simple-zero premise. -/
theorem profile_canonical_three_adapted_tests {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) (hk : (OPICAFollowup.spectralKappa rho).im ≠ 0) :
    ProfileAdaptedBasisTests (OPICAFollowup.OffcriticalRealBasis.canonicalBasis rho)
      (OPICAFollowup.OffcriticalRealBasis.canonicalBasis_valid hz h0 h1) :=
  profile_actual_basis_adapted_tests _ _
    (OPICAFollowup.OffcriticalRealBasis.canonicalBasis_independent hz h0 h1 hk)

theorem profileWitness_kappa_im (w : ProfileWitness) :
    (OPICAFollowup.spectralKappa w.rho).im = -2 * profileDelta w * profileGamma w := by
  unfold OPICAFollowup.spectralKappa profileDelta profileGamma
  simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

theorem profileWitness_kappa_im_ne_zero (w : ProfileWitness) :
    (OPICAFollowup.spectralKappa w.rho).im ≠ 0 := by
  rw [profileWitness_kappa_im]
  exact ne_of_lt (by have hd := profileDelta_pos w; have hg := profileGamma_pos w; nlinarith)

theorem profileWitness_three_tests (w : ProfileWitness) :
    ProfileAdaptedBasisTests (OPICAFollowup.OffcriticalRealBasis.canonicalBasis w.rho)
      (OPICAFollowup.OffcriticalRealBasis.canonicalBasis_valid w.isZero
        (by linarith [w.right]) w.strip) :=
  profile_canonical_three_adapted_tests w.isZero (by linarith [w.right]) w.strip
    (profileWitness_kappa_im_ne_zero w)


theorem profile_real_zeroth_pairing {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) (c : ℂ) (phi : 𝓢(ℝ, ℝ)) :
    (zeroJetRealSpan [(c, rho, 0)]).integral phi =
      (c * (OPICAFollowup.zeroMeasure rho).integral (profileComplexTest phi)).re := by
  have hv := OPICAFollowup.OffcriticalRealBasis.validZeroth hz h0 h1 c
  have hi := actualZeroJetSum_integral [(c, rho, 0)] (valid_singleton _ hv) (profileComplexTest phi)
  have hr := congrArg Complex.re hi
  change ((actualZeroJetSum [(c, rho, 0)]).integral (fun x : ℝ => (phi x : ℂ))).re = _ at hr
  rw [profile_integral_re_real_test] at hr
  change (actualZeroJetSum [(c, rho, 0)]).rePart.integral phi = _
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    OPICAFollowup.normalizedZeroMeasureJet_zero] using hr

theorem profile_canonical_basis_physical_pairings {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) (phi : 𝓢(ℝ, ℝ)) :
    (zeroJetRealSpan (OPICAFollowup.OffcriticalRealBasis.canonicalBasis rho 0)).integral phi =
      (OPICAFollowup.zeroMeasure rho).rePart.integral phi ∧
    (zeroJetRealSpan (OPICAFollowup.OffcriticalRealBasis.canonicalBasis rho 1)).integral phi =
      (OPICAFollowup.zeroMeasure rho).imPart.integral phi := by
  constructor
  · change (zeroJetRealSpan [(1, rho, 0)]).integral phi = _
    rw [profile_real_zeroth_pairing hz h0 h1, one_mul]
    exact profile_integral_re_real_test _ phi
  · change (zeroJetRealSpan [(-Complex.I, rho, 0)]).integral phi = _
    rw [profile_real_zeroth_pairing hz h0 h1]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      neg_zero, zero_mul, neg_mul, one_mul, zero_sub, neg_neg]
    exact profile_integral_im_real_test _ phi

theorem profile_scaled_real_pairing (nu : OPICAFollowup.LocallyFiniteComplexMeasure)
    (hg : nu.HasLinearGrowth) (c : ℂ) (phi : 𝓢(ℝ, ℝ)) :
    (nu.scale c).rePart.integral phi =
      c.re * nu.rePart.integral phi - c.im * nu.imPart.integral phi := by
  have hi := congrArg Complex.re (complex_integral_scale nu hg c (profileComplexTest phi))
  change ((nu.scale c).integral (fun x : ℝ => (phi x : ℂ))).re =
    (c * nu.integral (fun x : ℝ => (phi x : ℂ))).re at hi
  rw [profile_integral_re_real_test, Complex.mul_re,
    profile_integral_re_real_test, profile_integral_im_real_test] at hi
  exact hi

def profilePhaseCoordinates (c : ℂ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![c.re, -c.im]

theorem profilePhaseCoordinates_norm (c : ℂ) : ‖profilePhaseCoordinates c‖ = ‖c‖ := by
  have he : ‖profilePhaseCoordinates c‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Complex.sq_norm, Complex.normSq_apply]
    simp [profilePhaseCoordinates, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, pow_two]
  nlinarith [norm_nonneg (profilePhaseCoordinates c), norm_nonneg c]

theorem profile_canonical_combination_phase_pairing {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) (c : ℂ) (phi : 𝓢(ℝ, ℝ)) :
    (zeroJetRealSpan (realBasisCombinationData
      (OPICAFollowup.OffcriticalRealBasis.canonicalBasis rho)
      (fun i => profilePhaseCoordinates c i))).integral phi =
        ((OPICAFollowup.zeroMeasure rho).scale c).rePart.integral phi := by
  rw [profile_combination_real_pairing _ (OPICAFollowup.OffcriticalRealBasis.canonicalBasis_valid hz h0 h1),
    PiLp.inner_apply, Fin.sum_univ_two]
  rw [profileBasisObservation_apply, profileBasisObservation_apply]
  obtain ⟨hr, hi⟩ := profile_canonical_basis_physical_pairings hz h0 h1 phi
  rw [hr, hi, profile_scaled_real_pairing _ (OPICAFollowup.zeroMeasure_hasLinearGrowth h0 h1)]
  simp only [RCLike.inner_apply, conj_trivial, profilePhaseCoordinates, WithLp.ofLp_toLp,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem profile_canonical_three_physical_tests {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) (hk : (OPICAFollowup.spectralKappa rho).im ≠ 0) :
    ∃ tests : Fin 3 → 𝓢(ℝ, ℝ), ∃ margin : ℝ, 0 < margin ∧
      (∀ j, profilePositiveOffLatticeTest (tests j)) ∧
      (∀ c : ℂ, ∃ j, ((OPICAFollowup.zeroMeasure rho).scale c).rePart.integral (tests j) ≤ -margin * ‖c‖) ∧
      (∀ c : ℂ, ∀ a0 epsilon : ℝ, 0 < a0 → a0 ≤ ‖c‖ → ∀ P : Fin 3 → ℝ,
        (∀ j, 0 ≤ P j) →
        (∀ j, |P j - ((OPICAFollowup.zeroMeasure rho).scale c).rePart.integral (tests j)| ≤ epsilon) →
        margin * a0 ≤ epsilon) := by
  obtain ⟨tests, margin, hm, hp, hcov, hmargin, herror⟩ := profile_canonical_three_adapted_tests hz h0 h1 hk
  refine ⟨tests, margin, hm, hp, ?_, ?_⟩
  · intro c
    obtain ⟨j, hj⟩ := hmargin (profilePhaseCoordinates c)
    rw [profile_canonical_combination_phase_pairing hz h0 h1, profilePhaseCoordinates_norm] at hj
    exact ⟨j, hj⟩
  · intro c a0 epsilon ha0 hc P hP herr
    apply herror (profilePhaseCoordinates c) a0 epsilon ha0 (by rwa [profilePhaseCoordinates_norm]) P hP
    intro j
    simpa only [profile_canonical_combination_phase_pairing hz h0 h1] using herr j



def ProfileExplicitFourControls (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) : Prop :=
    0 < profileQuarterEta w ∧ 0 < profileQuarterRadius w ∧
    (∀ j : Fin 4, profileQuarterX w j ∈ Ioo (1 : ℝ) 2 ∧
      profileDensity w (profileQuarterX w j) =
        profileQuarterDirection j * profileZ w * (profileQuarterP w j : ℂ) ∧
      HasCompactSupport (profileQuarterTest w hh j) ∧
      (∀ x : ℝ, 0 ≤ profileQuarterTest w hh j x) ∧
      (∫ x : ℝ, profileQuarterTest w hh j x) = 1 ∧
      tsupport (profileQuarterTest w hh j) ⊆ Ioo (1 : ℝ) 2) ∧
    (∀ c : ℂ, ∃ j : Fin 4, profilePhasePairing w c (profileQuarterTest w hh j) ≤
      -profileQuarterEta w * ‖c‖ / 2) ∧
    (∀ c : ℂ, ∀ a0 epsilon : ℝ, 0 < a0 → a0 ≤ ‖c‖ → ∀ P : Fin 4 → ℝ,
      (∀ j, 0 ≤ P j) →
      (∀ j, |P j - profilePhasePairing w c (profileQuarterTest w hh j)| ≤ epsilon) →
      profileQuarterEta w * a0 / 2 ≤ epsilon)

def ProfileCanonicalThreePhysicalTests (rho : ℂ) : Prop :=
    ∃ tests : Fin 3 → 𝓢(ℝ, ℝ), ∃ margin : ℝ, 0 < margin ∧
      (∀ j, profilePositiveOffLatticeTest (tests j)) ∧
      (∀ c : ℂ, ∃ j, ((OPICAFollowup.zeroMeasure rho).scale c).rePart.integral (tests j) ≤ -margin * ‖c‖) ∧
      (∀ c : ℂ, ∀ a0 epsilon : ℝ, 0 < a0 → a0 ≤ ‖c‖ → ∀ P : Fin 3 → ℝ,
        (∀ j, 0 ≤ P j) →
        (∀ j, |P j - ((OPICAFollowup.zeroMeasure rho).scale c).rePart.integral (tests j)| ≤ epsilon) →
        margin * a0 ≤ epsilon)

/-- Complete finite actual-profile positive-test observability. The test
realization, phase margins, and error thresholds construct no positive
arithmetic observations and assert no uniform recovery cost. -/
theorem phase_complete_positive_test_observability :
    (∀ n : ℕ, 1 ≤ n → ∀ basis : Fin n → List JetDatum,
      ∀ hv : ∀ i, ∀ j ∈ basis i, ValidJet j,
      LinearIndependent ℝ (fun i => (zeroJetRealSpan (basis i)).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (hv i))) → ProfileAdaptedBasisTests basis hv) ∧
    (∀ rho : ℂ, riemannZeta rho = 0 → 0 < rho.re → rho.re < 1 →
      (OPICAFollowup.spectralKappa rho).im ≠ 0 → ProfileCanonicalThreePhysicalTests rho) ∧
    (∀ w : ProfileWitness, ∀ hh : 2 * Real.pi / Real.log 2 < profileGamma w,
      ProfileExplicitFourControls w hh) ∧
    (∀ m n : ℕ, 1 ≤ n → m ≤ n → ∀ F : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ),
      ∃ a : Fin n → ℝ, a ≠ 0 ∧ ∀ i : Fin m, 0 ≤ F a i) := by
  exact ⟨fun _ _ basis hv hind => profile_actual_basis_adapted_tests basis hv hind,
    fun _ hz h0 h1 hk => profile_canonical_three_physical_tests hz h0 h1 hk,
    profile_four_positive_test_observability,
    fun _ _ hn hm F => profile_at_most_n_linear_tests_cannot_exclude hn hm F⟩

end Zeta23.OPICARound2
