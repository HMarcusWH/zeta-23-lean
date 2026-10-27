import Zeta23.OPICARound2.TruncationControls
import Zeta23.OPICAFollowup.ConfluentProfiles
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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


/-! ## Finite native quadratic obstruction (S09)
The all-order analytic, source, real-block and correction-domain proofs below
are specialized to the actual normalized co-Poisson zero profiles.
-/

/-! Generic analytic/bootstrap helpers only. Actual source-profile premises
are proved and instantiated separately; this is not an S09 completion claim. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators FourierTransform SchwartzMap ContDiff

namespace Zeta23.OPICARound2.QuadraticProfileBootstrap

/-- Literal Schwartz-pairing self-duality determines an ordinary continuous L1 function. -/
theorem ordinary_fourier_eq_of_pairing {q : ℝ → ℂ} (hq : Integrable q)
    (hc : Continuous q)
    (hsd : ∀ φ : 𝓢(ℝ,ℂ), (∫ x, q x*(𝓕 φ : 𝓢(ℝ,ℂ)) x)=∫ x, q x*φ x) :
    𝓕 q=q := by
  have hFc : Continuous (𝓕 q) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hq
  have key : ∀ φ : 𝓢(ℝ,ℂ), (∫ x, (𝓕 q x-q x)*φ x)=0 := by
    intro φ
    have hm := OPICAFollowup.integral_fourier_mul_eq_of_integrable hq φ.integrable
    have hp := hsd φ
    have hFφ : Integrable (fun x => 𝓕 q x*φ x) := by
      have hb : ∀ x, ‖𝓕 q x‖≤∫ y, ‖q y‖ := fun x => by
        rw [Real.fourier_real_eq]
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        simp_rw [Circle.norm_smul]
      exact φ.integrable.bdd_mul hFc.aestronglyMeasurable (Eventually.of_forall hb)
    have hqφ := OPICAFollowup.square_integrable_mul_schwartz hq φ
    rw [show (fun x => (𝓕 q x-q x)*φ x) =
      (fun x => 𝓕 q x*φ x-q x*φ x) by funext x; ring,
      integral_sub hFφ hqφ, hm]
    rw [←hp]
    simp only [SchwartzMap.fourier_coe,sub_self]
  have hae : ∀ᵐ x, 𝓕 q x-q x=0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (hFc.sub hc).locallyIntegrable
      (fun g hg hgs => ?_)
    have hgc : HasCompactSupport (fun x => (g x:ℂ)) := hgs.comp_left Complex.ofReal_zero
    have hgd : ContDiff ℝ ∞ (fun x => (g x:ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have h := key (hgc.toSchwartzMap hgd)
    calc
      (∫ x, g x • (𝓕 q x-q x)) = ∫ x, (𝓕 q x-q x)*(hgc.toSchwartzMap hgd) x := by
        congr 1
        funext x
        rw [Complex.real_smul,mul_comm]
        rfl
      _ = 0 := h
  have he : (fun x => 𝓕 q x-q x) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq volume (hFc.sub hc) continuous_const).mp hae
  funext x
  exact sub_eq_zero.mp (congrFun he x)

theorem ordinary_selfdual_contDiff {q : ℝ → ℂ} (hq : Integrable q) (hc : Continuous q)
    (hsd : ∀ φ : 𝓢(ℝ,ℂ), (∫ x, q x*(𝓕 φ : 𝓢(ℝ,ℂ)) x)=∫ x, q x*φ x)
    (M : ℕ) (hm : ∀ k : ℕ, k≤M → Integrable (fun x : ℝ => ‖x‖^k*‖q x‖)) :
    ContDiff ℝ M q := by
  rw [←ordinary_fourier_eq_of_pairing hq hc hsd]
  apply Real.contDiff_fourier
  intro k hk
  exact hm k (by exact_mod_cast hk)

/-- Actual closed one-sided equality transfers every finite jet at an endpoint. -/
theorem right_cell_jet_eq {q g : ℝ → ℂ} (m : ℕ) {a ε : ℝ} (hε : 0<ε)
    (hq : ContDiffAt ℝ m q a) (hg : ContDiffAt ℝ m g a)
    (he : EqOn g q (Icc a (a+ε))) : iteratedDeriv m g a=iteratedDeriv m q a := by
  have ha : a∈Icc a (a+ε) := ⟨le_rfl,by linarith⟩
  have h := iteratedDerivWithin_congr (n := m) he ha
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith)) hg ha,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith)) hq ha] at h
  exact h

theorem left_cell_jet_eq {q g : ℝ → ℂ} (m : ℕ) {a ε : ℝ} (hε : 0<ε)
    (hq : ContDiffAt ℝ m q a) (hg : ContDiffAt ℝ m g a)
    (he : EqOn g q (Icc (a-ε) a)) : iteratedDeriv m g a=iteratedDeriv m q a := by
  have ha : a∈Icc (a-ε) a := ⟨by linarith,le_rfl⟩
  have h := iteratedDerivWithin_congr (n := m) he ha
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith)) hg ha,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith)) hq ha] at h
  exact h

theorem scalar_cell_jet_match {q gp gm : ℝ → ℂ} (m : ℕ) {a ε : ℝ} (hε : 0<ε)
    (hq : ContDiffAt ℝ m q a) (hgp : ContDiffAt ℝ m gp a) (hgm : ContDiffAt ℝ m gm a)
    (hp : EqOn gp q (Icc a (a+ε))) (hm : EqOn gm q (Icc (a-ε) a)) :
    iteratedDeriv m gp a-iteratedDeriv m gm a=0 := by
  rw [right_cell_jet_eq m hε hq hgp hp,left_cell_jet_eq m hε hq hgm hm,sub_self]



def QuadraticKillsBelow {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (R : ℕ → Fin d → ℂ) (j : ℕ) : Prop := ∀ r : ℕ, r<j → A.mulVec (R r)=0

def quadraticJumpScale (j n : ℕ) : ℂ :=
  2*(-1:ℂ)^(j+1)/((n+1:ℕ):ℂ)^(2*j+2)

theorem quadraticJumpScale_ne_zero (j n : ℕ) : quadraticJumpScale j n≠0 := by
  unfold quadraticJumpScale
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  · apply pow_ne_zero
    exact_mod_cast Nat.succ_ne_zero n

/-- A bilinear functional vanishing on a true spanning sample set vanishes identically. -/
theorem vector_eq_zero_of_sample_span {d : ℕ} (H : ℝ → Fin d → ℂ)
    (hspan : Submodule.span ℂ (Set.range (fun n : ℕ => H ((n+1:ℕ):ℝ)))=⊤)
    (v : Fin d → ℂ) (hv : ∀ n : ℕ, dotProduct (H ((n+1:ℕ):ℝ)) v=0) : v=0 := by
  let L : (Fin d → ℂ) →ₗ[ℂ] ℂ := (dotProductBilin ℂ ℂ).flip v
  have hk : Submodule.span ℂ (Set.range (fun n : ℕ => H ((n+1:ℕ):ℝ)))≤LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact hv n
  have hall (x : Fin d → ℂ) : L x=0 := by
    apply hk
    rw [hspan]
    trivial
  ext i
  have h := hall (Pi.single i 1)
  change dotProduct (Pi.single i 1) v=0 at h
  simpa only [single_one_dotProduct,Pi.zero_apply] using h

theorem matrix_eq_zero_of_row_span {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (R : ℕ → Fin d → ℂ)
    (hspan : Submodule.span ℂ (Set.range (fun r : Fin d => R r.val))=⊤)
    (hR : ∀ r : Fin d, A.mulVec (R r.val)=0) : A=0 := by
  let L := A.mulVecLin
  have hk : Submodule.span ℂ (Set.range (fun r : Fin d => R r.val))≤LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r,rfl⟩
    exact hR r
  have hall (x : Fin d → ℂ) : A.mulVec x=0 := by
    apply hk
    rw [hspan]
    trivial
  ext i j
  have h := congrFun (hall (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.zero_apply,Matrix.zero_apply] using h

/-- The generic Fourier/bootstrap argument. Every analytic cell identity,
weighted moment and span premise is an explicit independent source obligation.
No positivity assumption on A occurs. -/
theorem quadratic_fourier_bootstrap {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (H : ℝ → Fin d → ℂ)
    (R : ℕ → Fin d → ℂ) (q : ℝ → ℂ) (gp gm : ℕ → ℝ → ℂ)
    (hq : Integrable q) (hc : Continuous q)
    (hsd : ∀ φ : 𝓢(ℝ,ℂ), (∫ x, q x*(𝓕 φ : 𝓢(ℝ,ℂ)) x)=∫ x, q x*φ x)
    (hHspan : Submodule.span ℂ (Set.range (fun n : ℕ => H ((n+1:ℕ):ℝ)))=⊤)
    (hRspan : Submodule.span ℂ (Set.range (fun r : Fin d => R r.val))=⊤)
    (hMom : ∀ j : ℕ, j<d → QuadraticKillsBelow A R j →
      ∀ k : ℕ, k≤4*j+2 → Integrable (fun x : ℝ => ‖x‖^k*‖q x‖))
    (hCell : ∀ n : ℕ, ∃ ε : ℝ, 0<ε ∧
      ContDiffAt ℝ ∞ (gp n) ((n+1:ℕ):ℝ) ∧
      ContDiffAt ℝ ∞ (gm n) ((n+1:ℕ):ℝ) ∧
      EqOn (gp n) q (Icc ((n+1:ℕ):ℝ) (((n+1:ℕ):ℝ)+ε)) ∧
      EqOn (gm n) q (Icc (((n+1:ℕ):ℝ)-ε) ((n+1:ℕ):ℝ)))
    (hJump : ∀ j : ℕ, j<d → QuadraticKillsBelow A R j → ∀ n : ℕ,
      iteratedDeriv (2*j+1) (gp n) ((n+1:ℕ):ℝ)-
        iteratedDeriv (2*j+1) (gm n) ((n+1:ℕ):ℝ) =
      quadraticJumpScale j n * dotProduct (H ((n+1:ℕ):ℝ)) (A.mulVec (R j))) : A=0 := by
  have hstep (j : ℕ) (hj : j<d) (hlow : QuadraticKillsBelow A R j) : A.mulVec (R j)=0 := by
    have hreg := ordinary_selfdual_contDiff hq hc hsd (4*j+2) (hMom j hj hlow)
    apply vector_eq_zero_of_sample_span H hHspan
    intro n
    rcases hCell n with ⟨ε,hε,hgp,hgm,hp,hm⟩
    have hqAt : ContDiffAt ℝ (2*j+1) q ((n+1:ℕ):ℝ) :=
      (hreg.of_le (by exact_mod_cast (show 2*j+1≤4*j+2 by omega))).contDiffAt
    have hz := scalar_cell_jet_match (2*j+1) hε hqAt (hgp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _))
      (hgm.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)) hp hm
    have hJ := hJump j hj hlow n
    rw [hz] at hJ
    exact (mul_eq_zero.mp hJ.symm).resolve_left (quadraticJumpScale_ne_zero j n)
  have hstage : ∀ j : ℕ, j≤d → QuadraticKillsBelow A R j := by
    intro j
    induction j with
    | zero => intro _ r hr; omega
    | succ j ih =>
      intro hj
      have hjd : j<d := by omega
      have hlow := ih (by omega)
      have hkill := hstep j hjd hlow
      intro r hr
      by_cases he : r=j
      · simpa only [he] using hkill
      · exact hlow r (by omega)
  exact matrix_eq_zero_of_row_span A R hRspan (fun r => hstage d le_rfl r.val r.isLt)

end Zeta23.OPICARound2.QuadraticProfileBootstrap

noncomputable section
open Finset Matrix
open scoped BigOperators
namespace Zeta23.OPICARound2.QuadraticProfileBootstrap

theorem symmetric_bilinear_swap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.transpose=A) (u v : Fin d → ℂ) :
    dotProduct u (A.mulVec v)=dotProduct v (A.mulVec u) := by
  have h := Matrix.dotProduct_transpose_mulVec A u v
  rwa [hA] at h

theorem bilinear_eq_of_killed_jump {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.transpose=A) (u v w : Fin d → ℂ) (hk : A.mulVec (u-v)=0) :
    dotProduct u (A.mulVec w)=dotProduct v (A.mulVec w) := by
  have he : A.mulVec u=A.mulVec v := by
    apply sub_eq_zero.mp
    simpa only [Matrix.mulVec_sub] using hk
  rw [symmetric_bilinear_swap A hA u w,he,symmetric_bilinear_swap A hA w v]

/-- Pure finite Leibniz cancellation. Symmetry and killed lower jumps suffice;
there is no positivity assumption on the matrix. -/
theorem symmetric_leibniz_jump_cancel {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.transpose=A) (JP JM : ℕ → Fin d → ℂ) (H : Fin d → ℂ)
    (r : ℕ) (hr : 1≤r) (hP0 : JP 0=H) (hM0 : JM 0=H)
    (hKill : ∀ s : ℕ, 0<s → s<r → A.mulVec (JP s-JM s)=0) :
    (∑ k ∈ range (r+1), (r.choose k:ℂ)*
      (dotProduct (JP k) (A.mulVec (JP (r-k)))-dotProduct (JM k) (A.mulVec (JM (r-k))))) =
      2*dotProduct H (A.mulVec (JP r-JM r)) := by
  let F : ℕ → ℂ := fun k => (r.choose k:ℂ)*
    (dotProduct (JP k) (A.mulVec (JP (r-k)))-dotProduct (JM k) (A.mulVec (JM (r-k))))
  have hinterior (k : ℕ) (hk0 : 0<k) (hkr : k<r) : F k=0 := by
    have hkn := hKill k hk0 hkr
    have hkm := hKill (r-k) (by omega) (by omega)
    have he : A.mulVec (JP (r-k))=A.mulVec (JM (r-k)) := by
      apply sub_eq_zero.mp
      simpa only [Matrix.mulVec_sub] using hkm
    have hl := bilinear_eq_of_killed_jump A hA (JP k) (JM k) (JM (r-k)) hkn
    simp only [F,he,hl,sub_self,mul_zero]
  have hsum : (∑ k ∈ range r, F k)=F 0 := by
    apply Finset.sum_eq_single 0
    · intro k hk hk0
      exact hinterior k (by omega) (Finset.mem_range.mp hk)
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  have hright : F 0=dotProduct H (A.mulVec (JP r-JM r)) := by
    simp only [F,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero,hP0,hM0,
      Matrix.mulVec_sub,dotProduct_sub]
  have hleft : F r=dotProduct H (A.mulVec (JP r-JM r)) := by
    simp only [F,Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,hP0,hM0,
      Matrix.mulVec_sub,dotProduct_sub]
    rw [symmetric_bilinear_swap A hA (JP r) H,symmetric_bilinear_swap A hA (JM r) H]
  change (∑ k ∈ range (r+1), F k)=_
  rw [Finset.sum_range_succ,hsum,hright,hleft]
  ring

end Zeta23.OPICARound2.QuadraticProfileBootstrap

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Zeta23.OPICARound2.QuadraticProfileBootstrap

theorem weighted_rpow_tail_kernel {a : ℝ} (ha : 1≤a) (p k : ℕ) (hpk : k+2≤p) :
    a^k*a^(-(p:ℝ)) ≤ (a^2)⁻¹ := by
  have hap : 0<a := by linarith
  rw [←Real.rpow_natCast a k,←Real.rpow_add hap]
  have he : (k:ℝ)+(-(p:ℝ))≤-2 := by
    have hle : (k:ℝ)+2≤(p:ℝ) := by exact_mod_cast hpk
    linarith
  have h := Real.rpow_le_rpow_of_exponent_le ha he
  simpa only [Real.rpow_neg hap.le,Real.rpow_two] using h

/-- A real polynomial tail rate yields every weighted L1 moment below the
sharp integrability threshold; compact behavior is handled by continuity. -/
theorem continuous_weighted_moment_integrable {q : ℝ → ℂ} (hc : Continuous q)
    (C : ℝ) (hC : 0≤C) (p k : ℕ) (hpk : k+2≤p)
    (htail : ∀ x : ℝ, 1≤|x| → ‖q x‖≤C*|x|^(-(p:ℝ))) :
    Integrable (fun x : ℝ => ‖x‖^k*‖q x‖) := by
  have hfc : Continuous (fun x : ℝ => ‖x‖^k*‖q x‖) := (continuous_norm.pow k).mul hc.norm
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).exists_bound_of_continuousOn hfc.continuousOn
  have hmax : 0≤max B C := hC.trans (le_max_right B C)
  apply (integrable_inv_one_add_sq.const_mul (2*max B C)).mono' hfc.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hd : 0<1+x^2 := by positivity
    by_cases hx : |x|≤1
    · have hmem : x∈Icc (-1:ℝ) 1 := abs_le.mp hx
      have hb := hB x hmem
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hb
      have hx2 : x^2≤1 := by nlinarith [sq_abs x,abs_nonneg x]
      have hratio : max B C≤2*max B C*(1+x^2)⁻¹ := by
        change max B C≤(2*max B C)/(1+x^2)
        apply (le_div_iff₀ hd).2
        have h := mul_le_mul_of_nonneg_left (show 1+x^2≤2 by linarith) hmax
        nlinarith
      exact (hb.trans (le_max_left B C)).trans hratio
    · have hx1 : 1≤|x| := (lt_of_not_ge hx).le
      have hxp : 0 < |x| := by linarith
      have hker := weighted_rpow_tail_kernel hx1 p k hpk
      have hq := mul_le_mul_of_nonneg_left (htail x hx1) (show 0≤‖x‖^k by positivity)
      have htailw : ‖x‖^k*‖q x‖≤C*(x^2)⁻¹ := by
        calc
          _ ≤ ‖x‖^k*(C*|x|^(-(p:ℝ))) := hq
          _ = C*(|x|^k*|x|^(-(p:ℝ))) := by rw [Real.norm_eq_abs]; ring
          _ ≤ C*(|x|^2)⁻¹ := mul_le_mul_of_nonneg_left hker hC
          _ = _ := by rw [sq_abs]
      have hx2 : 1≤x^2 := by nlinarith [sq_abs x,abs_nonneg x]
      have hinv : (x^2)⁻¹≤2*(1+x^2)⁻¹ := by
        have hdiv : 1/(x^2)≤2/(1+x^2) := by
          apply (div_le_div_iff₀ (by linarith) hd).2
          nlinarith
        simpa only [one_div,div_eq_mul_inv,one_mul] using hdiv
      calc
        _ ≤ C*(x^2)⁻¹ := htailw
        _ ≤ C*(2*(1+x^2)⁻¹) := mul_le_mul_of_nonneg_left hinv hC
        _ ≤ (max B C)*(2*(1+x^2)⁻¹) := mul_le_mul_of_nonneg_right (le_max_right B C) (by positivity)
        _ = _ := by ring

theorem quadratic_tail_weighted_moments {q : ℝ → ℂ} (hc : Continuous q)
    (j : ℕ) (hTail : ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, 1≤|x| →
      ‖q x‖≤C*|x|^(-(4*(j:ℝ)+4))) :
    ∀ k : ℕ, k≤4*j+2 → Integrable (fun x : ℝ => ‖x‖^k*‖q x‖) := by
  rcases hTail with ⟨C,hC,htail⟩
  intro k hk
  apply continuous_weighted_moment_integrable hc C hC (4*j+4) k (by omega)
  intro x hx
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using htail x hx

end Zeta23.OPICARound2.QuadraticProfileBootstrap

/-! Generic order-zero lattice Fourier rigidity, extracted from the checked
physical-square argument without its special density or origin witness. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ContDiff
namespace Zeta23.OPICARound2.QuadraticProfileBootstrap
open Zeta23.OPICAFollowup

theorem continuous_cocompact_zero_of_lattice_fourier_key (d : ℝ → ℂ)
    (hdc : Continuous d) (hdt : Tendsto d (cocompact ℝ) (𝓝 0))
    (S : 𝓢(ℝ,ℂ) → ℂ)
    (hSzero : ∀ χ : 𝓢(ℝ,ℂ), (∀ n : ℤ, χ n=0) → S χ=0)
    (hScongr : ∀ χ ψ : 𝓢(ℝ,ℂ), (∀ n : ℤ, χ n=ψ n) → S χ=S ψ)
    (key : ∀ φ : 𝓢(ℝ,ℂ), S (𝓕 φ)=S φ-∫ x, d x*φ x) : d=0 := by
  -- d is bounded
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖d x‖ ≤ M := by
    obtain ⟨K, hK, hKc⟩ : ∃ K : Set ℝ, IsCompact K ∧ ∀ x ∉ K, ‖d x‖ < 1 := by
      have := hdt (Metric.ball_mem_nhds 0 one_pos)
      rw [Filter.mem_map, Filter.mem_cocompact] at this
      obtain ⟨K, hK, hKs⟩ := this
      exact ⟨K, hK, fun x hx => by simpa using hKs hx⟩
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hdc.continuousOn
    exact ⟨max B 1, fun x => by
      by_cases hx : x ∈ K
      · exact (hB x hx).trans (le_max_left _ _)
      · exact (hKc x hx).le.trans (le_max_right _ _)⟩
  set U : Set ℝ := (Set.range (fun n : ℤ => (n : ℝ)))ᶜ with hU
  have hUo : IsOpen U := by
    rw [hU, isOpen_compl_iff]
    exact (Int.isClosedEmbedding_coe_real.isClosed_range)
  set D : ℝ → ℂ := fun x => d (x + 1) - d x with hD
  have hDc : Continuous D := (hdc.comp (continuous_id.add continuous_const)).sub hdc
  have hint0 : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ → Integrable (fun x => d x * φ x) := by
    intro φ hφ hcs
    exact (hφ.integrable_of_hasCompactSupport hcs).bdd_mul hdc.aestronglyMeasurable
      (Eventually.of_forall hM)
  have hDzero : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x • D x = 0 := by
    intro g hg hgc hgU
    set φ : ℝ → ℂ := fun x => (g x : ℂ) with hφ
    have hφs : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp hg
    have hφc : HasCompactSupport φ := hgc.comp_left Complex.ofReal_zero
    set ψ : ℝ → ℂ := fun x => φ (x - 1) with hψ
    have hψs : ContDiff ℝ ∞ ψ := hφs.comp (contDiff_id.sub contDiff_const)
    have hψc : HasCompactSupport ψ := hφc.comp_homeomorph (Homeomorph.subRight (1 : ℝ))
    have hφZ : ∀ n : ℤ, φ n = 0 := fun n => by
      have : (n : ℝ) ∉ tsupport g := fun hn => hgU hn ⟨n, rfl⟩
      simp [φ, image_eq_zero_of_notMem_tsupport this]
    have hψZ : ∀ n : ℤ, ψ n = 0 := fun n => by
      simp only [ψ, show (n : ℝ) - 1 = ((n - 1 : ℤ) : ℝ) by push_cast; ring, hφZ]
    set Φ : 𝓢(ℝ, ℂ) := hφc.toSchwartzMap hφs
    set Ψ : 𝓢(ℝ, ℂ) := hψc.toSchwartzMap hψs
    have hkΦ := key Φ
    have hkΨ := key Ψ
    have hl0 : ∀ χ : 𝓢(ℝ, ℂ), (∀ n : ℤ, χ n = 0) → S χ = 0 := hSzero
    rw [hl0 Φ hφZ] at hkΦ
    rw [hl0 Ψ hψZ] at hkΨ
    have hsame : S (𝓕 Ψ) = S (𝓕 Φ) := by
      apply hScongr
      intro n
      simp only [SchwartzMap.fourier_coe]
      exact fourier_shift_int φ n
    have hI : (∫ x, d x * ψ x) = ∫ x, d (x + 1) * φ x := by
      rw [← integral_add_right_eq_self (fun x => d x * ψ x) (1 : ℝ)]
      simp only [ψ, add_sub_cancel_right]
    have heq : (∫ x, d (x + 1) * φ x) = ∫ x, d x * φ x := by
      have e1 : S (𝓕 Ψ) = -∫ x, d x * Ψ x := by rw [hkΨ]; ring
      have e2 : S (𝓕 Φ) = -∫ x, d x * Φ x := by rw [hkΦ]; ring
      have : (∫ x, d x * Ψ x) = ∫ x, d x * Φ x := by rw [← neg_inj, ← e1, ← e2, hsame]
      rw [← hI]; exact this
    have hi1 : Integrable (fun x => d (x + 1) * φ x) :=
      (hφs.continuous.integrable_of_hasCompactSupport hφc).bdd_mul
        (hdc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Eventually.of_forall fun x => hM _)
    have hi2 := hint0 φ hφs.continuous hφc
    calc ∫ x, g x • D x = ∫ x, d (x + 1) * φ x - d x * φ x := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [hD, φ, Complex.real_smul]; ring
      _ = 0 := by rw [integral_sub hi1 hi2, heq, sub_self]
  have hae := hUo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hDc.locallyIntegrable.locallyIntegrableOn U) hDzero
  have hnull : (volume : Measure ℝ) (Set.range (fun n : ℤ => (n : ℝ))) = 0 :=
    (Set.countable_range _).measure_zero _
  have hae' : D =ᵐ[volume] 0 := by
    filter_upwards [hae, measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxU
    exact hx hxU
  have hDall : ∀ x, D x = 0 := fun x => congrFun ((hDc.ae_eq_iff_eq volume continuous_const).mp hae') x
  have hper (x : ℝ) (n : ℕ) : d (x+(n:ℝ))=d x := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hDall (x+(n:ℝ))
      simp only [hD,sub_eq_zero] at h
      have ht : x+((n+1:ℕ):ℝ)=(x+(n:ℝ))+1 := by push_cast; ring
      rw [ht,h,ih]
  funext x
  have ht : Tendsto (fun n : ℕ => x+(n:ℝ)) atTop atTop := by
    simpa only [add_comm] using tendsto_natCast_atTop_atTop.atTop_add
      (tendsto_const_nhds (x := x))
  have hlim : Tendsto (fun n : ℕ => d (x+(n:ℝ))) atTop (𝓝 0) :=
    hdt.comp (ht.mono_right atTop_le_cocompact)
  have hconst : Tendsto (fun n : ℕ => d (x+(n:ℝ))) atTop (𝓝 (d x)) :=
    tendsto_const_nhds.congr fun n => (hper x n).symm
  exact tendsto_nhds_unique hconst hlim

/-- A genuine order-zero lattice repair cannot change a continuous C0 L1
function's ordinary Fourier self-duality. -/
theorem ordinary_fourier_eq_of_lattice_repair {q : ℝ → ℂ} (hq : Integrable q)
    (hc : Continuous q) (hvan : Tendsto q (cocompact ℝ) (𝓝 0))
    (S : 𝓢(ℝ,ℂ) → ℂ)
    (hSzero : ∀ χ : 𝓢(ℝ,ℂ), (∀ n : ℤ, χ n=0) → S χ=0)
    (hScongr : ∀ χ ψ : 𝓢(ℝ,ℂ), (∀ n : ℤ, χ n=ψ n) → S χ=S ψ)
    (hRepair : ∀ φ : 𝓢(ℝ,ℂ),
      (∫ x, q x*(𝓕 φ : 𝓢(ℝ,ℂ)) x)+S (𝓕 φ)=(∫ x, q x*φ x)+S φ) : 𝓕 q=q := by
  have hFc : Continuous (𝓕 q) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hq
  let d : ℝ → ℂ := fun x => 𝓕 q x-q x
  have hdc : Continuous d := hFc.sub hc
  have hdt : Tendsto d (cocompact ℝ) (𝓝 0) := by
    simpa only [d,sub_zero] using (Real.zero_at_infty_fourier q).sub hvan
  have key : ∀ φ : 𝓢(ℝ,ℂ), S (𝓕 φ)=S φ-∫ x, d x*φ x := by
    intro φ
    have hFφ : Integrable (fun x => 𝓕 q x*φ x) := by
      have hb : ∀ x, ‖𝓕 q x‖≤∫ y, ‖q y‖ := fun x => by
        rw [Real.fourier_real_eq]
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        simp_rw [Circle.norm_smul]
      exact φ.integrable.bdd_mul hFc.aestronglyMeasurable (Eventually.of_forall hb)
    have hqφ := OPICAFollowup.square_integrable_mul_schwartz hq φ
    have hfub := OPICAFollowup.integral_fourier_mul_eq_of_integrable hq φ.integrable
    have hqF : (∫ x, q x*(𝓕 φ : 𝓢(ℝ,ℂ)) x)=∫ x, 𝓕 q x*φ x := by
      simpa only [SchwartzMap.fourier_coe] using hfub.symm
    have hD : (∫ x, d x*φ x)=(∫ x, 𝓕 q x*φ x)-∫ x, q x*φ x := by
      dsimp only [d]
      simp_rw [sub_mul]
      exact integral_sub hFφ hqφ
    have hh := hRepair φ
    rw [hqF] at hh
    rw [hD]
    linear_combination hh
  have he := continuous_cocompact_zero_of_lattice_fourier_key d hdc hdt S hSzero hScongr key
  funext x
  have h := congrFun he x
  change 𝓕 q x-q x=0 at h
  exact sub_eq_zero.mp h

theorem pairing_selfdual_of_lattice_repair {q : ℝ → ℂ} (hq : Integrable q)
    (hc : Continuous q) (hvan : Tendsto q (cocompact ℝ) (𝓝 0))
    (S : 𝓢(ℝ,ℂ) → ℂ)
    (hSzero : ∀ χ : 𝓢(ℝ,ℂ), (∀ n : ℤ, χ n=0) → S χ=0)
    (hScongr : ∀ χ ψ : 𝓢(ℝ,ℂ), (∀ n : ℤ, χ n=ψ n) → S χ=S ψ)
    (hRepair : ∀ φ : 𝓢(ℝ,ℂ),
      (∫ x, q x*(𝓕 φ : 𝓢(ℝ,ℂ)) x)+S (𝓕 φ)=(∫ x, q x*φ x)+S φ) :
    ∀ φ : 𝓢(ℝ,ℂ), (∫ x, q x*(𝓕 φ : 𝓢(ℝ,ℂ)) x)=∫ x, q x*φ x := by
  have he := ordinary_fourier_eq_of_lattice_repair hq hc hvan S hSzero hScongr hRepair
  intro φ
  have h := OPICAFollowup.integral_fourier_mul_eq_of_integrable hq φ.integrable
  rw [he] at h
  simpa only [SchwartzMap.fourier_coe] using h.symm

end Zeta23.OPICARound2.QuadraticProfileBootstrap
namespace Zeta23.OPICARound2.QuadraticProfileRealification
abbrev MixedIndex (r c : ℕ) := Fin r ⊕ (Fin c × Fin 2)

def realify {r c : ℕ} (v : MixedIndex r c → ℂ) : MixedIndex r c → ℂ
  | .inl i => v (.inl i)
  | .inr (i,k) => if k = 0 then (v (.inr (i,0)) + v (.inr (i,1))) / 2
      else (v (.inr (i,0)) - v (.inr (i,1))) / (2 * Complex.I)

def unrealify {r c : ℕ} (v : MixedIndex r c → ℂ) : MixedIndex r c → ℂ
  | .inl i => v (.inl i)
  | .inr (i,k) => if k = 0 then v (.inr (i,0)) + Complex.I * v (.inr (i,1))
      else v (.inr (i,0)) - Complex.I * v (.inr (i,1))

theorem realify_unrealify {r c : ℕ} (v : MixedIndex r c → ℂ) :
    realify (unrealify v) = v := by
  funext i
  rcases i with i | ⟨i,k⟩
  · rfl
  · fin_cases k <;> simp [realify, unrealify] <;> field_simp <;> ring

theorem unrealify_realify {r c : ℕ} (v : MixedIndex r c → ℂ) :
    unrealify (realify v) = v := by
  funext i
  rcases i with i | ⟨i,k⟩
  · rfl
  · fin_cases k <;> simp [realify, unrealify] <;> field_simp <;> ring

def realifyLinear {r c : ℕ} : (MixedIndex r c → ℂ) →ₗ[ℂ] (MixedIndex r c → ℂ) where
  toFun := realify
  map_add' v w := by
    funext i
    rcases i with i | ⟨i,k⟩
    · rfl
    · fin_cases k <;> simp [realify] <;> ring
  map_smul' a v := by
    funext i
    rcases i with i | ⟨i,k⟩
    · rfl
    · fin_cases k <;> simp [realify] <;> ring

def unrealifyLinear {r c : ℕ} : (MixedIndex r c → ℂ) →ₗ[ℂ] (MixedIndex r c → ℂ) where
  toFun := unrealify
  map_add' v w := by
    funext i
    rcases i with i | ⟨i,k⟩
    · rfl
    · fin_cases k <;> simp [unrealify] <;> ring
  map_smul' a v := by
    funext i
    rcases i with i | ⟨i,k⟩
    · rfl
    · fin_cases k <;> simp [unrealify] <;> ring

def realificationEquiv {r c : ℕ} : (MixedIndex r c → ℂ) ≃ₗ[ℂ] (MixedIndex r c → ℂ) where
  toFun := realify
  invFun := unrealify
  left_inv := unrealify_realify
  right_inv := realify_unrealify
  map_add' := realifyLinear.map_add
  map_smul' := realifyLinear.map_smul

def realificationMatrix {r c : ℕ} : Matrix (MixedIndex r c) (MixedIndex r c) ℂ :=
  LinearMap.toMatrix' realifyLinear

def inverseRealificationMatrix {r c : ℕ} : Matrix (MixedIndex r c) (MixedIndex r c) ℂ :=
  LinearMap.toMatrix' unrealifyLinear

theorem realificationMatrix_mulVec {r c : ℕ} (v : MixedIndex r c → ℂ) :
    realificationMatrix.mulVec v = realify v := LinearMap.toMatrix'_mulVec _ _

theorem inverseRealificationMatrix_mulVec {r c : ℕ} (v : MixedIndex r c → ℂ) :
    inverseRealificationMatrix.mulVec v = unrealify v := LinearMap.toMatrix'_mulVec _ _

theorem realificationMatrix_mul_inverse {r c : ℕ} :
    (realificationMatrix : Matrix (MixedIndex r c) _ ℂ) * inverseRealificationMatrix = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec, realificationMatrix_mulVec, inverseRealificationMatrix_mulVec]
  simpa using realify_unrealify v

theorem inverseRealificationMatrix_mul {r c : ℕ} :
    (inverseRealificationMatrix : Matrix (MixedIndex r c) _ ℂ) * realificationMatrix = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec, inverseRealificationMatrix_mulVec, realificationMatrix_mulVec]
  simpa using unrealify_realify v

def expandedVector {r c : ℕ} (u : Fin r → ℝ) (v : Fin c → ℂ) : MixedIndex r c → ℂ
  | .inl i => (u i : ℂ)
  | .inr (i,k) => if k = 0 then v i else star (v i)

def realVector {r c : ℕ} (u : Fin r → ℝ) (v : Fin c → ℂ) : MixedIndex r c → ℝ
  | .inl i => u i
  | .inr (i,k) => if k = 0 then (v i).re else (v i).im

theorem realify_expandedVector {r c : ℕ} (u : Fin r → ℝ) (v : Fin c → ℂ) :
    realify (expandedVector u v) = fun i => ((realVector u v i : ℝ) : ℂ) := by
  funext i
  rcases i with i | ⟨i,k⟩
  · rfl
  · fin_cases k <;> apply Complex.ext <;> simp [realify, expandedVector, realVector,
      Complex.div_re, Complex.div_im] <;> ring

def transportedMatrix {r c : ℕ} (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) :
    Matrix (MixedIndex r c) (MixedIndex r c) ℂ :=
  realificationMatrix.transpose * A.map Complex.ofReal * realificationMatrix

theorem transportedMatrix_symmetric {r c : ℕ}
    (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) (hA : A.IsSymm) :
    (transportedMatrix A).IsSymm := by
  unfold transportedMatrix Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    (hA.map Complex.ofReal).eq, Matrix.mul_assoc]

theorem transportedMatrix_eq_zero_iff {r c : ℕ}
    (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) :
    transportedMatrix A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have he := congrArg (fun B => inverseRealificationMatrix.transpose * B *
      inverseRealificationMatrix) h
    have hcancel : inverseRealificationMatrix.transpose * transportedMatrix A *
        inverseRealificationMatrix = A.map Complex.ofReal := by
      unfold transportedMatrix
      calc
        _ = (realificationMatrix * inverseRealificationMatrix).transpose *
            A.map Complex.ofReal * (realificationMatrix * inverseRealificationMatrix) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
        _ = A.map Complex.ofReal := by rw [realificationMatrix_mul_inverse]; simp
    rw [hcancel] at he
    ext i j
    have hij := congrArg (fun B => B i j) he
    simpa using congrArg Complex.re hij
  · intro h
    subst A
    simp [transportedMatrix]

theorem transported_quadratic {r c : ℕ}
    (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) (v : MixedIndex r c → ℂ) :
    dotProduct v ((transportedMatrix A).mulVec v) =
      dotProduct (realify v) ((A.map Complex.ofReal).mulVec (realify v)) := by
  unfold transportedMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, realificationMatrix_mulVec]
  rw [dotProduct_comm]

theorem transported_real_quadratic {r c : ℕ}
    (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ)
    (u : Fin r → ℝ) (v : Fin c → ℂ) :
    dotProduct (expandedVector u v) ((transportedMatrix A).mulVec (expandedVector u v)) =
      ((dotProduct (realVector u v) (A.mulVec (realVector u v)) : ℝ) : ℂ) := by
  rw [transported_quadratic, realify_expandedVector]
  symm
  exact (RingHom.map_dotProduct Complex.ofRealHom _ _).trans (by
    congr 1
    funext i
    exact RingHom.map_mulVec Complex.ofRealHom A (realVector u v) i)

def realBlockOperator {r c : ℕ} (α : Fin r → ℝ) (ξ : Fin c → ℂ)
    (v : MixedIndex r c → ℝ) : MixedIndex r c → ℝ
  | .inl i => α i * v (.inl i)
  | .inr (i,k) => if k = 0 then (ξ i).re * v (.inr (i,0)) - (ξ i).im * v (.inr (i,1))
      else (ξ i).im * v (.inr (i,0)) + (ξ i).re * v (.inr (i,1))

def cyclicVector {r c : ℕ} : MixedIndex r c → ℝ
  | .inl _ => 1
  | .inr (_,k) => if k = 0 then 1 else 0

theorem realBlockOperator_realVector {r c : ℕ}
    (α : Fin r → ℝ) (ξ : Fin c → ℂ) (u : Fin r → ℝ) (v : Fin c → ℂ) :
    realBlockOperator α ξ (realVector u v) =
      realVector (fun i => α i * u i) (fun i => ξ i * v i) := by
  funext i
  rcases i with i | ⟨i,k⟩
  · rfl
  · fin_cases k <;> simp [realBlockOperator, realVector, Complex.mul_re, Complex.mul_im] <;> ring

theorem realBlockOperator_iterate {r c : ℕ}
    (α : Fin r → ℝ) (ξ : Fin c → ℂ) (n : ℕ) :
    (realBlockOperator α ξ)^[n] cyclicVector =
      realVector (fun i => α i ^ n) (fun i => ξ i ^ n) := by
  induction n with
  | zero => funext i; rcases i with i | ⟨i,k⟩
            · simp [cyclicVector, realVector]
            · fin_cases k <;> simp [cyclicVector, realVector]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, realBlockOperator_realVector]
    simp only [pow_succ']

theorem realify_spectral_powers {r c : ℕ}
    (α : Fin r → ℝ) (ξ : Fin c → ℂ) (n : ℕ) :
    realify (fun i => (expandedVector α ξ i)^n) =
      fun i => (((realBlockOperator α ξ)^[n] cyclicVector i : ℝ) : ℂ) := by
  rw [realBlockOperator_iterate]
  have h : (fun i => (expandedVector α ξ i)^n) =
      expandedVector (fun i => α i^n) (fun i => ξ i^n) := by
    funext i
    rcases i with i | ⟨i,k⟩
    · simp [expandedVector]
    · fin_cases k <;> simp [expandedVector]
  rw [h, realify_expandedVector]

theorem real_span_top_of_complex_cast_span {ι ν : Type*} (v : ν → ι → ℝ)
    (h : Submodule.span ℂ (Set.range (fun j i => ((v j i : ℝ) : ℂ))) = ⊤) :
    Submodule.span ℝ (Set.range v) = ⊤ := by
  let S := Submodule.span ℝ (Set.range v)
  have hparts : ∀ z ∈ Submodule.span ℂ (Set.range (fun j i => ((v j i : ℝ) : ℂ))),
      (fun i => (z i).re) ∈ S ∧ (fun i => (z i).im) ∈ S := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨j,rfl⟩
      constructor
      · simpa using (Submodule.subset_span (Set.mem_range_self j) : v j ∈ S)
      · convert (S.zero_mem : (0 : ι → ℝ) ∈ S) using 1
        funext i
        simp
    | zero =>
      constructor <;> convert (S.zero_mem : (0 : ι → ℝ) ∈ S) using 1 <;> funext i <;> simp
    | add z w hz hw ihz ihw =>
      constructor
      · convert S.add_mem ihz.1 ihw.1 using 1
        funext i
        simp
      · convert S.add_mem ihz.2 ihw.2 using 1
        funext i
        simp
    | smul a z hz ih =>
      constructor
      · convert S.sub_mem (S.smul_mem a.re ih.1) (S.smul_mem a.im ih.2) using 1
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Pi.sub_apply]
      · convert S.add_mem (S.smul_mem a.re ih.2) (S.smul_mem a.im ih.1) using 1
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im, Pi.add_apply]
  apply top_unique
  intro x hx
  have hxC : (fun i => ((x i : ℝ) : ℂ)) ∈
      Submodule.span ℂ (Set.range (fun j i => ((v j i : ℝ) : ℂ))) := by rw [h]; trivial
  simpa only [Complex.ofReal_re] using (hparts _ hxC).1

theorem realify_span_top {r c : ℕ} {ν : Type*} (v : ν → MixedIndex r c → ℂ)
    (h : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range (fun j => realify (v j))) = ⊤ := by
  have he : Set.range (fun j => realify (v j)) = realify '' Set.range v := by
    ext x
    simp only [Set.mem_range, Set.mem_image]
    aesop
  rw [he]
  change Submodule.span ℂ (realifyLinear '' Set.range v) = ⊤
  rw [← Submodule.map_span, h]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (show Function.Surjective realifyLinear from
    realificationEquiv.surjective)

theorem real_block_cyclic_of_spectral_span {r c d : ℕ}
    (α : Fin r → ℝ) (ξ : Fin c → ℂ)
    (h : Submodule.span ℂ (Set.range (fun n : Fin d =>
      fun i => (expandedVector α ξ i)^(n.val+1))) = ⊤) :
    Submodule.span ℝ (Set.range (fun n : Fin d =>
      (realBlockOperator α ξ)^[n.val+1] cyclicVector)) = ⊤ := by
  apply real_span_top_of_complex_cast_span
  have ht := realify_span_top _ h
  have he : (fun n : Fin d => realify (fun i => (expandedVector α ξ i)^(n.val+1))) =
      (fun n : Fin d => fun i =>
        (((realBlockOperator α ξ)^[n.val+1] cyclicVector i : ℝ) : ℂ)) := by
    funext n
    exact realify_spectral_powers α ξ (n.val+1)
  rw [he] at ht
  exact ht

def realBlockLinear {r c : ℕ} (α : Fin r → ℝ) (ξ : Fin c → ℂ) :
    (MixedIndex r c → ℝ) →ₗ[ℝ] (MixedIndex r c → ℝ) where
  toFun := realBlockOperator α ξ
  map_add' v w := by
    funext i
    rcases i with i | ⟨i,k⟩
    · simp [realBlockOperator, mul_add]
    · fin_cases k <;> simp [realBlockOperator] <;> ring
  map_smul' a v := by
    funext i
    rcases i with i | ⟨i,k⟩
    · simp [realBlockOperator]; ring
    · fin_cases k <;> simp [realBlockOperator] <;> ring

def realBlockMatrix {r c : ℕ} (α : Fin r → ℝ) (ξ : Fin c → ℂ) :
    Matrix (MixedIndex r c) (MixedIndex r c) ℝ :=
  LinearMap.toMatrix' (realBlockLinear α ξ)

theorem realBlockMatrix_mulVec {r c : ℕ} (α : Fin r → ℝ) (ξ : Fin c → ℂ)
    (v : MixedIndex r c → ℝ) :
    (realBlockMatrix α ξ).mulVec v = realBlockOperator α ξ v :=
  LinearMap.toMatrix'_mulVec _ _

theorem realBlockMatrix_power_cyclic {r c : ℕ} (α : Fin r → ℝ) (ξ : Fin c → ℂ) (n : ℕ) :
    ((realBlockMatrix α ξ)^n).mulVec cyclicVector =
      (realBlockOperator α ξ)^[n] cyclicVector := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, realBlockMatrix_mulVec,
      Function.iterate_succ_apply']

theorem real_block_matrix_cyclic_of_spectral_span {r c d : ℕ}
    (α : Fin r → ℝ) (ξ : Fin c → ℂ)
    (h : Submodule.span ℂ (Set.range (fun n : Fin d =>
      fun i => (expandedVector α ξ i)^(n.val+1))) = ⊤) :
    Submodule.span ℝ (Set.range (fun n : Fin d =>
      ((realBlockMatrix α ξ)^(n.val+1)).mulVec cyclicVector)) = ⊤ := by
  simpa only [realBlockMatrix_power_cyclic] using
    real_block_cyclic_of_spectral_span α ξ h


end Zeta23.OPICARound2.QuadraticProfileRealification
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter Polynomial
open scoped Topology FourierTransform SchwartzMap ContDiff BigOperators
namespace Zeta23.OPICARound2
open OPICAFollowup NativeBernoulli
def profileFactorPolynomial : ℕ → ℂ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => C (2 * ((n + 1 : ℕ) : ℂ)) * profileFactorPolynomial (n + 1) -
      (C ((n : ℂ) * ((n + 1 : ℕ) : ℂ)) + X) * profileFactorPolynomial n

theorem profileEMRising_difference_recurrence (rho : ℂ) (n : ℕ) :
    profileEMRising rho (n + 2) - profileEMRising (1 - rho) (n + 2) =
      2 * ((n + 1 : ℕ) : ℂ) *
        (profileEMRising rho (n + 1) - profileEMRising (1 - rho) (n + 1)) -
      ((n : ℂ) * ((n + 1 : ℕ) : ℂ) + rho * (1 - rho)) *
        (profileEMRising rho n - profileEMRising (1 - rho) n) := by
  simp only [profileEMRising, Nat.cast_add, Nat.cast_one]
  ring

theorem profileEMRising_difference (rho : ℂ) (n : ℕ) :
    profileEMRising rho n - profileEMRising (1 - rho) n =
      (2 * rho - 1) * (profileFactorPolynomial n).eval (rho * (1 - rho)) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [profileEMRising, profileFactorPolynomial]
  | one => simp [profileEMRising, profileFactorPolynomial]; ring
  | more n hn hn1 =>
    rw [profileEMRising_difference_recurrence, hn, hn1, profileFactorPolynomial]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X]
    ring

theorem profileFactorPolynomial_coeff_recurrence (n m : ℕ) :
    (profileFactorPolynomial (n + 2)).coeff (m + 1) =
      (2 * ((n + 1 : ℕ) : ℂ)) * (profileFactorPolynomial (n + 1)).coeff (m + 1) -
      ((n : ℂ) * ((n + 1 : ℕ) : ℂ) * (profileFactorPolynomial n).coeff (m + 1) +
        (profileFactorPolynomial n).coeff m) := by
  rw [profileFactorPolynomial, add_mul]
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul]

theorem profileFactorPolynomial_degree_pair (r : ℕ) :
    (profileFactorPolynomial (2 * r + 1)).natDegree ≤ r ∧
    (profileFactorPolynomial (2 * r + 1)).coeff r = (-1 : ℂ) ^ r ∧
    (profileFactorPolynomial (2 * r + 2)).natDegree ≤ r := by
  induction r with
  | zero => simp [profileFactorPolynomial]
  | succ r ih =>
    obtain ⟨hodd, hcoeff, heven⟩ := ih
    have hvanOdd := natDegree_le_iff_coeff_eq_zero.mp hodd
    have hvanEven := natDegree_le_iff_coeff_eq_zero.mp heven
    have hoddNext : (profileFactorPolynomial (2 * (r + 1) + 1)).natDegree ≤ r + 1 := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro m hm
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      have h1 : r < m + 1 := by omega
      have h0 : r < m := by omega
      rw [show 2 * (r + 1) + 1 = 2 * r + 1 + 2 by omega,
        profileFactorPolynomial_coeff_recurrence]
      rw [show 2 * r + 1 + 1 = 2 * r + 2 by omega, hvanEven _ h1, hvanOdd _ h1, hvanOdd _ h0]
      ring
    have hcoeffNext : (profileFactorPolynomial (2 * (r + 1) + 1)).coeff (r + 1) = (-1 : ℂ) ^ (r + 1) := by
      rw [show 2 * (r + 1) + 1 = 2 * r + 1 + 2 by omega,
        profileFactorPolynomial_coeff_recurrence]
      rw [show 2 * r + 1 + 1 = 2 * r + 2 by omega,
        hvanEven _ (by omega), hvanOdd _ (by omega), hcoeff, pow_succ]
      ring
    refine ⟨hoddNext, hcoeffNext, ?_⟩
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    have h1 : r + 1 < m + 1 := by omega
    have h0 : r < m := by omega
    rw [show 2 * (r + 1) + 2 = (2 * (r + 1) + 1) + 1 by omega]
    rw [show (2 * (r + 1) + 1) + 1 = (2 * r + 2) + 2 by omega,
      profileFactorPolynomial_coeff_recurrence]
    rw [show 2 * r + 2 + 1 = 2 * (r + 1) + 1 by omega,
      natDegree_le_iff_coeff_eq_zero.mp hoddNext _ h1,
      hvanEven _ (by omega), hvanEven _ h0]
    ring

theorem profileFactorPolynomial_odd_leading (r : ℕ) :
    (profileFactorPolynomial (2 * r + 1)).natDegree = r ∧
      (profileFactorPolynomial (2 * r + 1)).leadingCoeff = (-1 : ℂ) ^ r := by
  obtain ⟨hdeg, hc, heven⟩ := profileFactorPolynomial_degree_pair r
  have hn : (profileFactorPolynomial (2 * r + 1)).coeff r ≠ 0 := by rw [hc]; exact pow_ne_zero _ (by norm_num)
  have hd : (profileFactorPolynomial (2 * r + 1)).natDegree = r :=
    le_antisymm hdeg (le_natDegree_of_ne_zero hn)
  exact ⟨hd, by rw [Polynomial.leadingCoeff, hd, hc]⟩

def profileZeroEMTerms (rho : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, (spectralKappa rho *
    (profileFactorPolynomial n).eval (spectralKappa rho) / ((n + 1).factorial : ℂ)) *
      (profilePeriodicBernoulli (n + 1) x : ℂ) * (x : ℂ) ^ (-(n : ℂ) - 1)

def profileZeroEMRawRemainder (rho : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-rho) * profileEMCoefficient (1 - rho) N * profileBernoulliTailIntegral (1 - rho) N x -
    (x : ℂ) ^ (rho - 1) * profileEMCoefficient rho N * profileBernoulliTailIntegral rho N x

def profileZeroEMRemainder (rho : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  -profileZeroEMRawRemainder rho N x / normalizationBrho rho

theorem profileEMTerms_source_transport (rho : ℂ) (N : ℕ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-rho) * profileEMTerms (1 - rho) N x -
      (x : ℂ) ^ (rho - 1) * profileEMTerms rho N x =
    ∑ n ∈ Finset.range N, ((profileEMRising (1 - rho) n - profileEMRising rho n) /
      ((n + 1).factorial : ℂ)) * (profilePeriodicBernoulli (n + 1) x : ℂ) *
        (x : ℂ) ^ (-(n : ℂ) - 1) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  unfold profileEMTerms
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hA : (x : ℂ) ^ (-rho) * (x : ℂ) ^ (-(1 - rho) - (n : ℂ)) =
      (x : ℂ) ^ (-(n : ℂ) - 1) := by
    rw [← Complex.cpow_add _ _ hxC]
    congr 1
    ring
  have hB : (x : ℂ) ^ (rho - 1) * (x : ℂ) ^ (-rho - (n : ℂ)) =
      (x : ℂ) ^ (-(n : ℂ) - 1) := by
    rw [← Complex.cpow_add _ _ hxC]
    congr 1
    ring
  calc
    _ = (profileEMRising (1 - rho) n / ((n + 1).factorial : ℂ)) *
        (profilePeriodicBernoulli (n + 1) x : ℂ) *
          ((x : ℂ) ^ (-rho) * (x : ℂ) ^ (-(1 - rho) - (n : ℂ))) -
        (profileEMRising rho n / ((n + 1).factorial : ℂ)) *
          (profilePeriodicBernoulli (n + 1) x : ℂ) *
            ((x : ℂ) ^ (rho - 1) * (x : ℂ) ^ (-rho - (n : ℂ))) := by ring
    _ = _ := by rw [hA, hB]; ring

theorem profileZeroEMTerms_source_factor {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1)
    (hh : rho ≠ 1 / 2) (N : ℕ) {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) ^ (-rho) * profileEMTerms (1 - rho) N x -
      (x : ℂ) ^ (rho - 1) * profileEMTerms rho N x) / normalizationBrho rho =
        profileZeroEMTerms rho N x := by
  rw [profileEMTerms_source_transport rho N hx, Finset.sum_div]
  unfold profileZeroEMTerms
  apply Finset.sum_congr rfl
  intro n hn
  have hd := profileEMRising_difference rho n
  have hk := kappa_div_brho h0 h1 hh
  have hn : profileEMRising (1 - rho) n - profileEMRising rho n =
      -(2 * rho - 1) * (profileFactorPolynomial n).eval (spectralKappa rho) := by
    rw [spectralKappa]
    linear_combination -hd
  rw [hn]
  calc
    _ = -((2 * rho - 1) / normalizationBrho rho) *
        (profileFactorPolynomial n).eval (spectralKappa rho) / ((n + 1).factorial : ℂ) *
          (profilePeriodicBernoulli (n + 1) x : ℂ) * (x : ℂ) ^ (-(n : ℂ) - 1) := by ring
    _ = _ := by rw [hk]; ring

theorem profile_finiteSumSrho_all_order {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) {x : ℝ} (hx : 1 ≤ x)
    (N : ℕ) (hN : 1 ≤ N) :
    finiteSumSrho rho x = normalizationBrho rho -
      ((x : ℂ) ^ (-rho) * profileEMTerms (1 - rho) N x -
        (x : ℂ) ^ (rho - 1) * profileEMTerms rho N x) +
      profileZeroEMRawRemainder rho N x := by
  have hx0 : 0 < x := one_pos.trans_le hx
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  obtain ⟨hr0, hr1⟩ := strip_ne h0 h1
  have hz' : riemannZeta (1 - rho) = 0 := by
    have hn : ∀ n : ℕ, rho ≠ -n := fun n h => by
      have he := congrArg Complex.re h
      simp at he
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [riemannZeta_one_sub hn hr1, hz, mul_zero]
  have hmainA : (x : ℂ) ^ (-rho) * ((x : ℂ) ^ (1 - (1 - rho)) / (1 - (1 - rho))) = 1 / rho := by
    rw [← mul_div_assoc, ← Complex.cpow_add _ _ hxC]
    rw [show -rho + (1 - (1 - rho)) = 0 by ring, Complex.cpow_zero,
      show 1 - (1 - rho) = rho by ring]
  have hmainB : (x : ℂ) ^ (rho - 1) * ((x : ℂ) ^ (1 - rho) / (1 - rho)) = 1 / (1 - rho) := by
    rw [← mul_div_assoc, ← Complex.cpow_add _ _ hxC]
    rw [show rho - 1 + (1 - rho) = 0 by ring, Complex.cpow_zero]
  rw [finiteSumSrho_eq_rightPowerSum,
    profile_rightPowerSum_all_order (by simp; linarith) (by intro h; apply hr0; linear_combination -h) hx N hN,
    profile_rightPowerSum_all_order h0 hr1 hx N hN, hz, hz', brho_eq h0 h1]
  unfold profileZeroEMRawRemainder
  linear_combination hmainA - hmainB

theorem profile_zeroProfile_all_order {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) {x : ℝ} (hx : 1 ≤ |x|)
    (N : ℕ) (hN : 1 ≤ N) :
    zeroProfile rho x = profileZeroEMTerms rho N |x| + profileZeroEMRemainder rho N |x| := by
  obtain ⟨hr0, hr1⟩ := strip_ne h0 h1
  have hh := zero_ne_half hz
  have hb := normalizationBrho_ne_zero hr0 hr1 hh
  have hp := profile_finiteSumSrho_all_order hz h0 h1 hx N hN
  rw [zeroProfile, hp]
  rw [← profileZeroEMTerms_source_factor h0 h1 hh N (one_pos.trans_le hx)]
  unfold profileZeroEMRemainder
  field_simp [hb]
  ring


theorem profileZeroEMRemainder_norm_bound {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖profileZeroEMRemainder rho N x‖ ≤ C * x ^ (-(N : ℝ)) := by
  have hs : 0 < (1 - rho).re := by simp; linarith
  obtain ⟨CA, hCA, hbA⟩ := profile_periodic_bernoulli_tail_norm hN hs
  obtain ⟨CB, hCB, hbB⟩ := profile_periodic_bernoulli_tail_norm hN h0
  let K : ℝ := ‖profileEMCoefficient (1 - rho) N‖ * CA + ‖profileEMCoefficient rho N‖ * CB
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K / ‖normalizationBrho rho‖, div_nonneg hK (norm_nonneg _), fun x hx => ?_⟩
  have hA : ‖(x : ℂ) ^ (-rho) * profileEMCoefficient (1 - rho) N *
      profileBernoulliTailIntegral (1 - rho) N x‖ ≤
      (‖profileEMCoefficient (1 - rho) N‖ * CA) * x ^ (-(N : ℝ)) := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.neg_re]
    calc
      _ ≤ x ^ (-rho.re) * ‖profileEMCoefficient (1 - rho) N‖ *
          (CA * x ^ (-(1 - rho).re - (N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (hbA x hx) (by positivity)
      _ = (‖profileEMCoefficient (1 - rho) N‖ * CA) *
          (x ^ (-rho.re) * x ^ (-(1 - rho).re - (N : ℝ) + 1)) := by ring
      _ = _ := by rw [← Real.rpow_add hx]; congr 2; simp only [Complex.sub_re, Complex.one_re]; ring
  have hB : ‖(x : ℂ) ^ (rho - 1) * profileEMCoefficient rho N *
      profileBernoulliTailIntegral rho N x‖ ≤
      (‖profileEMCoefficient rho N‖ * CB) * x ^ (-(N : ℝ)) := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.sub_re, Complex.one_re]
    calc
      _ ≤ x ^ (rho.re - 1) * ‖profileEMCoefficient rho N‖ *
          (CB * x ^ (-rho.re - (N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (hbB x hx) (by positivity)
      _ = (‖profileEMCoefficient rho N‖ * CB) *
          (x ^ (rho.re - 1) * x ^ (-rho.re - (N : ℝ) + 1)) := by ring
      _ = _ := by rw [← Real.rpow_add hx]; congr 2; ring
  have hraw : ‖profileZeroEMRawRemainder rho N x‖ ≤ K * x ^ (-(N : ℝ)) := by
    exact (norm_sub_le _ _).trans ((add_le_add hA hB).trans_eq (by dsimp [K]; ring))
  unfold profileZeroEMRemainder
  rw [norm_div, norm_neg]
  exact (div_le_div_of_nonneg_right hraw (norm_nonneg _)).trans_eq (by ring)

theorem profile_zeroProfile_all_order_asymptotic {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖zeroProfile rho x - profileZeroEMTerms rho N |x|‖ ≤ C * |x| ^ (-(N : ℝ) - 1) := by
  obtain ⟨CR, hCR, hbR⟩ := profileZeroEMRemainder_norm_bound h0 h1 (N + 1) (by omega)
  obtain ⟨B, hB, hbB⟩ := profilePeriodicBernoulli_bound (N + 1)
  let C0 : ℝ := ‖spectralKappa rho * (profileFactorPolynomial N).eval (spectralKappa rho) /
    ((N + 1).factorial : ℂ)‖ * B
  refine ⟨C0 + CR, by dsimp [C0]; positivity, fun x hx => ?_⟩
  have hx0 : 0 < |x| := one_pos.trans_le hx
  rw [profile_zeroProfile_all_order hz h0 h1 hx (N + 1) (by omega)]
  have hterms : profileZeroEMTerms rho (N + 1) |x| = profileZeroEMTerms rho N |x| +
      (spectralKappa rho * (profileFactorPolynomial N).eval (spectralKappa rho) /
        ((N + 1).factorial : ℂ)) * (profilePeriodicBernoulli (N + 1) |x| : ℂ) *
          ((|x| : ℝ) : ℂ) ^ (-(N : ℂ) - 1) := by
    exact Finset.sum_range_succ _ _
  rw [hterms, add_assoc, add_sub_cancel_left]
  have ht : ‖(spectralKappa rho * (profileFactorPolynomial N).eval (spectralKappa rho) /
        ((N + 1).factorial : ℂ)) * (profilePeriodicBernoulli (N + 1) |x| : ℂ) *
          ((|x| : ℝ) : ℂ) ^ (-(N : ℂ) - 1)‖ ≤ C0 * |x| ^ (-(N : ℝ) - 1) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbB |x|) (norm_nonneg _))
      (Real.rpow_nonneg hx0.le _)
  have hr := hbR |x| hx0
  push_cast at hr
  have hr' : ‖profileZeroEMRemainder rho (N + 1) |x|‖ ≤ CR * |x| ^ (-(N : ℝ) - 1) := by
    convert hr using 1 <;> ring
  exact (norm_add_le _ _).trans ((add_le_add ht hr').trans_eq (by ring))


def profileOddPolynomialSequence : Polynomial.Sequence ℂ where
  elems' r := profileFactorPolynomial (2 * r + 1)
  degree_eq' r := by
    obtain ⟨hd, hc⟩ := profileFactorPolynomial_odd_leading r
    have hp : profileFactorPolynomial (2 * r + 1) ≠ 0 := by
      intro hz
      rw [hz, leadingCoeff_zero] at hc
      exact (pow_ne_zero r (by norm_num : (-1 : ℂ) ≠ 0)) hc.symm
    rw [degree_eq_natDegree hp, hd]

def profileWeightedPolynomialEvaluation {d : ℕ} (kappa : Fin d → ℂ) :
    ℂ[X] →ₗ[ℂ] (Fin d → ℂ) where
  toFun p i := kappa i * p.eval (kappa i)
  map_add' p q := by ext i; simp [mul_add]
  map_smul' c p := by ext i; simp [smul_eq_mul]; ring

theorem profile_spectral_polynomial_vectors_span {d : ℕ} (kappa : Fin d → ℂ)
    (hne : ∀ i, kappa i ≠ 0) (hinj : Function.Injective kappa) :
    Submodule.span ℂ (Set.range (fun r : ℕ => fun i : Fin d =>
      kappa i * (profileFactorPolynomial (2 * r + 1)).eval (kappa i))) = ⊤ := by
  let V : Submodule ℂ (Fin d → ℂ) := Submodule.span ℂ (Set.range (fun r : ℕ => fun i : Fin d =>
    kappa i * (profileFactorPolynomial (2 * r + 1)).eval (kappa i)))
  let E := profileWeightedPolynomialEvaluation kappa
  have hcoeff (r : ℕ) : IsUnit (profileOddPolynomialSequence r).leadingCoeff := by
    apply isUnit_iff_ne_zero.mpr
    change (profileFactorPolynomial (2 * r + 1)).leadingCoeff ≠ 0
    rw [(profileFactorPolynomial_odd_leading r).2]
    exact pow_ne_zero r (by norm_num)
  have hle : Submodule.span ℂ (Set.range profileOddPolynomialSequence) ≤ V.comap E := by
    apply Submodule.span_le.mpr
    rintro p ⟨r, rfl⟩
    exact Submodule.subset_span ⟨r, rfl⟩
  rw [profileOddPolynomialSequence.span hcoeff] at hle
  have hany (p : ℂ[X]) : E p ∈ V := hle (show p ∈ (⊤ : Submodule ℂ ℂ[X]) from trivial)
  have hs (i : Fin d) : Pi.single i (1 : ℂ) ∈ V := by
    have hp := hany (C ((kappa i)⁻¹) * Lagrange.basis Finset.univ kappa i)
    convert hp using 1
    ext j
    dsimp [E, profileWeightedPolynomialEvaluation]
    by_cases hij : i = j
    · subst j
      rw [eval_mul, eval_C, Lagrange.eval_basis_self hinj.injOn (Finset.mem_univ i), mul_one]
      simp [hne i]
    · rw [eval_mul, eval_C, Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]
      simp [Pi.single_apply, hij, Ne.symm hij]
  change V = ⊤
  apply top_unique
  intro v hv
  have hd : v = ∑ i : Fin d, v i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  rw [hd]
  exact V.sum_mem (fun i _ => V.smul_mem (v i) (hs i))


def profileSampleSpan {d : ℕ} (H : ℕ → Fin d → ℂ) : Submodule ℂ (Fin d → ℂ) :=
  Submodule.span ℂ (Set.range (fun n : ℕ => H (n + 1)))

/-- Actual all-order coefficient estimates recover coefficients inside the
closed finite-dimensional span of the actual positive-integer samples. -/
theorem profile_sample_span_contains_coefficients {d : ℕ} (H : ℕ → Fin d → ℂ)
    (a : ℕ → Fin d → ℂ)
    (happrox : ∀ N : ℕ, 1 ≤ N → ∀ i : Fin d, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 1 ≤ n →
        ‖H n i - ∑ k ∈ Finset.range N, (((n : ℂ) ^ (k + 1))⁻¹ * a k i)‖ ≤
          C / (n : ℝ) ^ (N + 1)) :
    ∀ k : ℕ, a k ∈ profileSampleSpan H := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    let R : ℕ → Fin d → ℂ := fun n => (((n + 1 : ℕ) : ℂ) ^ (k + 1)) •
      (H (n + 1) - ∑ j ∈ Finset.range k, ((((n + 1 : ℕ) : ℂ) ^ (j + 1))⁻¹) • a j)
    have hmem (n : ℕ) : R n ∈ profileSampleSpan H := by
      apply Submodule.smul_mem
      apply Submodule.sub_mem
      · exact Submodule.subset_span ⟨n, rfl⟩
      · apply Submodule.sum_mem
        intro j hj
        exact Submodule.smul_mem _ _ (ih j (Finset.mem_range.mp hj))
    have hlim : Tendsto R atTop (𝓝 (a k)) := by
      apply tendsto_pi_nhds.mpr
      intro i
      obtain ⟨C, hC, hb⟩ := happrox (k + 1) (by omega) i
      have hbound (n : ℕ) : ‖R n i - a k i‖ ≤ C / ((n : ℝ) + 1) := by
        have hy : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
        have hyR : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
        have hp : (((n + 1 : ℕ) : ℂ) ^ (k + 1)) ≠ 0 := pow_ne_zero _ hy
        have he : R n i - a k i = (((n + 1 : ℕ) : ℂ) ^ (k + 1)) *
            (H (n + 1) i - ∑ j ∈ Finset.range (k + 1),
              ((((n + 1 : ℕ) : ℂ) ^ (j + 1))⁻¹ * a j i)) := by
          dsimp only [R]
          simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, Finset.sum_range_succ]
          have hc : (((n + 1 : ℕ) : ℂ) ^ (k + 1)) *
              ((((n + 1 : ℕ) : ℂ) ^ (k + 1))⁻¹ * a k i) = a k i := by
            rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
          linear_combination hc
        rw [he, norm_mul, norm_pow]
        have hn : ‖(((n + 1 : ℕ) : ℂ))‖ = (((n + 1 : ℕ) : ℝ)) := Complex.norm_natCast (n + 1)
        rw [hn]
        calc
          _ ≤ (((n + 1 : ℕ) : ℝ) ^ (k + 1)) *
              (C / (((n + 1 : ℕ) : ℝ) ^ (k + 1 + 1))) :=
            mul_le_mul_of_nonneg_left (hb (n + 1) (by omega)) (by positivity)
          _ = C / ((n : ℝ) + 1) := by
            simp only [pow_succ]
            push_cast
            field_simp <;> ring
      have hz : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa only [mul_zero, ← div_eq_mul_inv, one_div] using
          tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
      have hn := squeeze_zero (fun n => norm_nonneg _) hbound hz
      exact tendsto_iff_norm_sub_tendsto_zero.mpr hn
    exact (profileSampleSpan H).closed_of_finiteDimensional.mem_of_tendsto hlim (Eventually.of_forall hmem)

theorem profilePeriodicBernoulli_nat (N n : ℕ) :
    profilePeriodicBernoulli N (n : ℝ) = (_root_.bernoulli N : ℝ) := by
  change bernoulliFun N (Int.fract (n : ℝ)) = _
  rw [Int.fract_natCast, bernoulliFun_eval_zero]

def profileZeroEMIntegerCoefficient (rho : ℂ) (k : ℕ) : ℂ :=
  spectralKappa rho * (profileFactorPolynomial k).eval (spectralKappa rho) /
    ((k + 1).factorial : ℂ) * (_root_.bernoulli (k + 1) : ℂ)

theorem profileZeroEMTerms_nat (rho : ℂ) (N n : ℕ) :
    profileZeroEMTerms rho N (n : ℝ) =
      ∑ k ∈ Finset.range N, ((n : ℂ) ^ (k + 1))⁻¹ * profileZeroEMIntegerCoefficient rho k := by
  unfold profileZeroEMTerms
  apply Finset.sum_congr rfl
  intro k hk
  rw [profilePeriodicBernoulli_nat]
  have hp : (-(k : ℂ) - 1) = -((k + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hp, Complex.cpow_neg, Complex.cpow_natCast]
  unfold profileZeroEMIntegerCoefficient
  push_cast
  ring

theorem profile_zero_samples_coefficient_estimate {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖zeroProfile rho (n : ℝ) - ∑ k ∈ Finset.range N,
        ((n : ℂ) ^ (k + 1))⁻¹ * profileZeroEMIntegerCoefficient rho k‖ ≤ C / (n : ℝ) ^ (N + 1) := by
  obtain ⟨C, hC, hb⟩ := profile_zeroProfile_all_order_asymptotic hz h0 h1 N hN
  refine ⟨C, hC, fun n hn => ?_⟩
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := one_pos.trans_le hnr
  have hh := hb (n : ℝ) (by rwa [abs_of_pos hnp])
  rw [abs_of_pos hnp, profileZeroEMTerms_nat] at hh
  convert hh using 1
  rw [show -(N : ℝ) - 1 = -((N + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg hnp.le, Real.rpow_natCast]
  ring

theorem profile_zero_integer_samples_span {d : ℕ} (rho : Fin d → ℂ)
    (hz : ∀ i, riemannZeta (rho i) = 0) (h0 : ∀ i, 0 < (rho i).re)
    (h1 : ∀ i, (rho i).re < 1)
    (hinj : Function.Injective (fun i => spectralKappa (rho i))) :
    profileSampleSpan (fun n i => zeroProfile (rho i) (n : ℝ)) = ⊤ := by
  let H : ℕ → Fin d → ℂ := fun n i => zeroProfile (rho i) (n : ℝ)
  let kappa : Fin d → ℂ := fun i => spectralKappa (rho i)
  let V := profileSampleSpan H
  have hcoeff (k : ℕ) : (fun i => profileZeroEMIntegerCoefficient (rho i) k) ∈ V := by
    exact profile_sample_span_contains_coefficients H (fun k i => profileZeroEMIntegerCoefficient (rho i) k)
      (fun N hN i => profile_zero_samples_coefficient_estimate (hz i) (h0 i) (h1 i) N hN) k
  have hrows (r : ℕ) : (fun i => kappa i * (profileFactorPolynomial (2 * r + 1)).eval (kappa i)) ∈ V := by
    let alpha : ℂ := (_root_.bernoulli (2 * r + 2) : ℂ) / ((2 * r + 2).factorial : ℂ)
    have ha : alpha ≠ 0 := by
      apply div_ne_zero
      · have hb := profile_even_bernoulli_ne_zero (r + 1) (by omega)
        have he : 2 * (r + 1) = 2 * r + 2 := by omega
        rw [he] at hb
        exact_mod_cast hb
      · exact_mod_cast Nat.factorial_ne_zero (2 * r + 2)
    have hm := V.smul_mem (alpha⁻¹) (hcoeff (2 * r + 1))
    convert hm using 1
    ext i
    change _ = alpha⁻¹ * profileZeroEMIntegerCoefficient (rho i) (2 * r + 1)
    have he : profileZeroEMIntegerCoefficient (rho i) (2 * r + 1) =
        alpha * (kappa i * (profileFactorPolynomial (2 * r + 1)).eval (kappa i)) := by
      dsimp [profileZeroEMIntegerCoefficient, alpha, kappa]
      rw [show 2 * r + 1 + 1 = 2 * r + 2 by omega]
      ring
    rw [he, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have hspan := profile_spectral_polynomial_vectors_span kappa
    (fun i => by
      obtain ⟨hr0, hr1⟩ := strip_ne (h0 i) (h1 i)
      exact mul_ne_zero hr0 (sub_ne_zero.mpr hr1.symm)) hinj
  have hle : Submodule.span ℂ (Set.range (fun r : ℕ => fun i =>
      kappa i * (profileFactorPolynomial (2 * r + 1)).eval (kappa i))) ≤ V := by
    apply Submodule.span_le.mpr
    rintro p ⟨r, rfl⟩
    exact hrows r
  rw [hspan] at hle
  exact top_unique hle



def profileComplexQuadratic {d : ℕ} (rho : Fin d → ℂ) (A : Matrix (Fin d) (Fin d) ℂ) (x : ℝ) : ℂ :=
  dotProduct (fun i => zeroProfile (rho i) x) (A.mulVec (fun i => zeroProfile (rho i) x))

def profilePowerRow {d : ℕ} (kappa : Fin d → ℂ) (r : ℕ) : Fin d → ℂ :=
  fun i => kappa i ^ (r + 1)

theorem profile_polynomial_vector_annihilation {d j : ℕ}
    (kappa : Fin d → ℂ) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ r : ℕ, r < j → A.mulVec (profilePowerRow kappa r) = 0)
    (p : ℂ[X]) (hp : p.natDegree < j) :
    A.mulVec (fun i => kappa i * p.eval (kappa i)) = 0 := by
  let F : ℂ[X] →ₗ[ℂ] (Fin d → ℂ) := A.mulVecLin.comp (profileWeightedPolynomialEvaluation kappa)
  have hpow (r : ℕ) : F (X ^ r) = A.mulVec (profilePowerRow kappa r) := by
    change A.mulVec _ = _
    congr 1
    ext i
    simp [profileWeightedPolynomialEvaluation, profilePowerRow, pow_succ, mul_comm]
  change F p = 0
  rw [p.as_sum_range_C_mul_X_pow' hp, map_sum]
  apply Finset.sum_eq_zero
  intro r hr
  rw [← Polynomial.smul_eq_C_mul, map_smul, hpow, hA r (Finset.mem_range.mp hr), smul_zero]

theorem profileFactorPolynomial_small_degree {m j : ℕ} (hm : m ≠ 0) (hb : m ≤ 2 * j) :
    (profileFactorPolynomial m).natDegree < j := by
  rcases Nat.even_or_odd m with he | ho
  · rcases he with ⟨r, hr⟩
    have heq : m = 2 * (r - 1) + 2 := by omega
    rw [heq]
    exact (profileFactorPolynomial_degree_pair (r - 1)).2.2.trans_lt (by omega)
  · rcases ho with ⟨r, hr⟩
    have heq : m = 2 * r + 1 := by omega
    rw [heq]
    exact (profileFactorPolynomial_degree_pair r).1.trans_lt (by omega)

theorem profile_small_coefficient_vector_annihilation {d j : ℕ}
    (kappa : Fin d → ℂ) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ r : ℕ, r < j → A.mulVec (profilePowerRow kappa r) = 0)
    {m : ℕ} (hm : m ≤ 2 * j) :
    A.mulVec (fun i => kappa i * (profileFactorPolynomial m).eval (kappa i)) = 0 := by
  by_cases hz : m = 0
  · subst m
    simp only [profileFactorPolynomial, eval_zero, mul_zero]
    exact Matrix.mulVec_zero A
  · exact profile_polynomial_vector_annihilation kappa A hA _ (profileFactorPolynomial_small_degree hz hm)

theorem profileZeroEMTerms_vector_annihilation {d j : ℕ} (rho : Fin d → ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ r : ℕ, r < j → A.mulVec (profilePowerRow (fun i => spectralKappa (rho i)) r) = 0)
    (x : ℝ) : A.mulVec (fun i => profileZeroEMTerms (rho i) (2 * j + 1) x) = 0 := by
  have he : (fun i => profileZeroEMTerms (rho i) (2 * j + 1) x) =
      ∑ m ∈ Finset.range (2 * j + 1),
        (((profilePeriodicBernoulli (m + 1) x : ℂ) * (x : ℂ) ^ (-(m : ℂ) - 1)) /
          ((m + 1).factorial : ℂ)) •
            (fun i => spectralKappa (rho i) * (profileFactorPolynomial m).eval (spectralKappa (rho i))) := by
    ext i
    simp only [profileZeroEMTerms, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [he, Matrix.mulVec_sum]
  apply Finset.sum_eq_zero
  intro m hm
  rw [Matrix.mulVec_smul, profile_small_coefficient_vector_annihilation
    (fun i => spectralKappa (rho i)) A hA (by have h := Finset.mem_range.mp hm; omega), smul_zero]

theorem profile_symmetric_quadratic_remove_annihilated {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsSymm) (u v : Fin d → ℂ) (hv : A.mulVec v = 0) :
    dotProduct u (A.mulVec u) = dotProduct (u - v) (A.mulVec (u - v)) := by
  have ht : dotProduct v (A.mulVec u) = 0 := by
    rw [← Matrix.dotProduct_transpose_mulVec A u v, hA, hv]
    simp
  rw [Matrix.mulVec_sub, hv, sub_zero, sub_dotProduct, ht, sub_zero]



theorem profile_power_rows_span {d : ℕ} (kappa : Fin d → ℂ)
    (hne : ∀ i, kappa i ≠ 0) (hinj : Function.Injective kappa) :
    Submodule.span ℂ (Set.range (fun r : Fin d => profilePowerRow kappa r.val)) = ⊤ := by
  let M : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal kappa * Matrix.vandermonde kappa
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hne i)
      (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsurj := Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  have hm (i r : Fin d) : M i r = profilePowerRow kappa r.val i := by
    simp [M, Matrix.diagonal_mul, Matrix.vandermonde_apply, profilePowerRow, pow_succ, mul_comm]
  apply top_unique
  intro v hv
  obtain ⟨a, ha⟩ := hsurj v
  have he : M.mulVec a = ∑ r : Fin d, a r • profilePowerRow kappa r.val := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hm]
    ring
  rw [← ha, he]
  apply Submodule.sum_mem
  intro r hr
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)


theorem profile_quadratic_bound_from_coordinates {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (C : Fin d → ℝ)
    (hC : ∀ i, 0 ≤ C i) (X : ℝ) (hX : 0 ≤ X) (hv : ∀ i, ‖v i‖ ≤ C i * X) :
    ‖dotProduct v (A.mulVec v)‖ ≤
      (∑ i : Fin d, ∑ j : Fin d, ‖A i j‖ * C i * C j) * X ^ 2 := by
  have he : dotProduct v (A.mulVec v) = ∑ i : Fin d, ∑ j : Fin d, v i * A i j * v j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  calc
    _ ≤ ∑ i : Fin d, ‖∑ j : Fin d, v i * A i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, ‖v i * A i j * v j‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ = ∑ i : Fin d, ∑ j : Fin d, ‖v i‖ * ‖A i j‖ * ‖v j‖ := by simp only [norm_mul]
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, (C i * X) * ‖A i j‖ * (C j * X) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _))
        (hv j) (norm_nonneg _) (mul_nonneg (mul_nonneg (hC i) hX) (norm_nonneg _))
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem profileComplexQuadratic_continuous {d : ℕ} (rho : Fin d → ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) : Continuous (profileComplexQuadratic rho A) := by
  unfold profileComplexQuadratic Matrix.mulVec dotProduct
  exact continuous_finset_sum _ (fun i _ => (continuous_zeroProfile (rho i)).mul
    (continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_zeroProfile (rho j)))))

theorem profileComplexQuadratic_improved_tail {d : ℕ} (rho : Fin d → ℂ)
    (hz : ∀ i, riemannZeta (rho i) = 0) (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (A : Matrix (Fin d) (Fin d) ℂ) (hSym : A.IsSymm) (j : ℕ)
    (hA : ∀ r : ℕ, r < j → A.mulVec (profilePowerRow (fun i => spectralKappa (rho i)) r) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖profileComplexQuadratic rho A x‖ ≤ C * |x| ^ (-((4 * j + 4 : ℕ) : ℝ)) := by
  have hcoeff (i : Fin d) := profile_zeroProfile_all_order_asymptotic (hz i) (h0 i) (h1 i)
    (2 * j + 1) (by omega)
  choose C hC hb using hcoeff
  refine ⟨∑ i : Fin d, ∑ k : Fin d, ‖A i k‖ * C i * C k,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ =>
      mul_nonneg (mul_nonneg (norm_nonneg _) (hC i)) (hC k))), fun x hx => ?_⟩
  let R : Fin d → ℂ := fun i => zeroProfile (rho i) x - profileZeroEMTerms (rho i) (2 * j + 1) |x|
  have hq : profileComplexQuadratic rho A x = dotProduct R (A.mulVec R) :=
    profile_symmetric_quadratic_remove_annihilated A hSym _ _
      (profileZeroEMTerms_vector_annihilation rho A hA |x|)
  rw [hq]
  have hx0 : 0 < |x| := one_pos.trans_le hx
  have hbound := profile_quadratic_bound_from_coordinates A R C hC
    (|x| ^ (-((2 * j + 1 : ℕ) : ℝ) - 1)) (Real.rpow_nonneg hx0.le _) (fun i => hb i x hx)
  have he : (|x| ^ (-((2 * j + 1 : ℕ) : ℝ) - 1)) ^ 2 =
      |x| ^ (-((4 * j + 4 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  rwa [he] at hbound



def profilePowerOrder (s : ℂ) (r : ℕ) (x : ℝ) : ℂ :=
  (-1 : ℂ) ^ r * profileEMRising (-s) r * (x : ℂ) ^ (s - (r : ℂ))

theorem profile_hasDerivAt_real_cpow (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x := by
  by_cases hs : s = 0
  · subst s
    simpa using (hasDerivAt_const x (1 : ℂ))
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hs

theorem profile_contDiffAt_real_cpow (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ (fun t : ℝ => (t : ℂ) ^ s) x := by
  have hl : ContDiffAt ℝ ∞ (fun t : ℝ => Complex.log (t : ℂ)) x :=
    ((Complex.contDiffAt_log (Complex.ofReal_mem_slitPlane.mpr hx)).restrict_scalars ℝ).comp x
      Complex.ofRealCLM.contDiff.contDiffAt
  have he : ContDiffAt ℝ ∞ (fun t : ℝ => Complex.exp (Complex.log (t : ℂ) * s)) x :=
    ((Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).contDiffAt).comp x (hl.mul contDiffAt_const)
  apply he.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
  exact Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') s

theorem profilePowerOrder_hasDerivAt (s : ℂ) (r : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (profilePowerOrder s r) (profilePowerOrder s (r + 1) x) x := by
  have he := (profile_hasDerivAt_real_cpow (s - (r : ℂ)) hx).const_mul
    ((-1 : ℂ) ^ r * profileEMRising (-s) r)
  apply he.congr_deriv
  simp only [profilePowerOrder, profileEMRising, pow_succ, Nat.cast_add, Nat.cast_one]
  rw [show s - (r : ℂ) - 1 = s - ((r : ℂ) + 1) by ring]
  ring

theorem profilePowerOrder_iteratedDeriv (s : ℂ) (r : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv r (fun t : ℝ => (t : ℂ) ^ s) x = profilePowerOrder s r x := by
  induction r generalizing x with
  | zero => simp [profilePowerOrder, profileEMRising]
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have hh : iteratedDeriv r (fun t : ℝ => (t : ℂ) ^ s) =ᶠ[𝓝 x] profilePowerOrder s r := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
      exact ih ht
    rw [hh.deriv_eq]
    exact (profilePowerOrder_hasDerivAt s r hx).deriv

def profileAnalyticCell (rho : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  1 - srhoCell rho n x / normalizationBrho rho

def profileAnalyticCellJet (rho : ℂ) (n r : ℕ) (x : ℝ) : ℂ :=
  if r = 0 then profileAnalyticCell rho n x else
    -(profilePowerOrder (-rho) r x * cellSumA rho n -
      profilePowerOrder (rho - 1) r x * cellSumB rho n) / normalizationBrho rho

theorem profileAnalyticCell_contDiffAt (rho : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ (profileAnalyticCell rho n) x := by
  unfold profileAnalyticCell srhoCell
  exact contDiffAt_const.sub ((((profile_contDiffAt_real_cpow (-rho) hx).mul contDiffAt_const).sub
    ((profile_contDiffAt_real_cpow (rho - 1) hx).mul contDiffAt_const)).div_const _)

theorem profileAnalyticCellJet_hasDerivAt (rho : ℂ) (n r : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (profileAnalyticCellJet rho n r) (profileAnalyticCellJet rho n (r + 1) x) x := by
  by_cases hr : r = 0
  · subst r
    have h := ((profile_hasDerivAt_real_cpow (-rho) hx).mul_const (cellSumA rho n)).sub
      ((profile_hasDerivAt_real_cpow (rho - 1) hx).mul_const (cellSumB rho n))
    convert! (h.div_const (normalizationBrho rho)).const_sub 1 using 1 <;>
      simp +unfoldPartialApp [profileAnalyticCellJet, profileAnalyticCell, srhoCell,
        profilePowerOrder, profileEMRising] <;> ring
  · have h := ((profilePowerOrder_hasDerivAt (-rho) r hx).mul_const (cellSumA rho n)).sub
      ((profilePowerOrder_hasDerivAt (rho - 1) r hx).mul_const (cellSumB rho n))
    simpa +unfoldPartialApp [profileAnalyticCellJet, hr, Nat.succ_ne_zero] using!
      (h.neg.div_const (normalizationBrho rho))

theorem profileAnalyticCellJet_iteratedDeriv (rho : ℂ) (n r : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv r (profileAnalyticCell rho n) x = profileAnalyticCellJet rho n r x := by
  induction r generalizing x with
  | zero => simp [profileAnalyticCellJet]
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv r (profileAnalyticCell rho n) =ᶠ[𝓝 x] profileAnalyticCellJet rho n r := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
      exact ih ht
    rw [he.deriv_eq]
    exact (profileAnalyticCellJet_hasDerivAt rho n r hx).deriv

theorem profileAnalyticCell_eq_source (rho : ℂ) {n : ℕ} {x : ℝ}
    (hn : 0 < x) (hx : x ∈ Ico (n : ℝ) (n + 1)) :
    profileAnalyticCell rho n x = zeroProfile rho x := by
  rw [zeroProfile, abs_of_pos hn, finiteSumSrho_eq_cell rho hx]
  rfl


theorem profileAnalyticCellJet_jump {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1)
    (hh : rho ≠ 1 / 2) (n r : ℕ) :
    profileAnalyticCellJet rho (n + 1) r ((n + 1 : ℕ) : ℝ) -
      profileAnalyticCellJet rho n r ((n + 1 : ℕ) : ℝ) =
        (-1 : ℂ) ^ r * spectralKappa rho * (profileFactorPolynomial r).eval (spectralKappa rho) *
          ((n + 1 : ℕ) : ℂ) ^ (-(r : ℂ) - 1) := by
  by_cases hr : r = 0
  · subst r
    have he := srhoCell_succ_eq rho n
    simp only [Nat.cast_add, Nat.cast_one] at he
    simp [profileAnalyticCellJet, profileAnalyticCell, he, profileFactorPolynomial]

  · let m : ℕ := n + 1
    have hm : (m : ℂ) ≠ 0 := by dsimp [m]; exact_mod_cast (Nat.succ_ne_zero n)
    have hA : cellSumA rho (n + 1) = cellSumA rho n + (m : ℂ) ^ (rho - 1) := by
      unfold cellSumA
      rw [Finset.sum_Icc_succ_top (by omega)]
    have hB : cellSumB rho (n + 1) = cellSumB rho n + (m : ℂ) ^ (-rho) := by
      unfold cellSumB
      rw [Finset.sum_Icc_succ_top (by omega)]
    have hPA : profilePowerOrder (-rho) r (m : ℝ) * (m : ℂ) ^ (rho - 1) =
        (-1 : ℂ) ^ r * profileEMRising rho r * (m : ℂ) ^ (-(r : ℂ) - 1) := by
      unfold profilePowerOrder
      rw [neg_neg]
      simp only [Complex.ofReal_natCast]
      calc
        _ = (-1 : ℂ) ^ r * profileEMRising rho r *
            ((m : ℂ) ^ (-rho - (r : ℂ)) * (m : ℂ) ^ (rho - 1)) := by ring
        _ = _ := by rw [← Complex.cpow_add _ _ hm]; congr 2; ring
    have hPB : profilePowerOrder (rho - 1) r (m : ℝ) * (m : ℂ) ^ (-rho) =
        (-1 : ℂ) ^ r * profileEMRising (1 - rho) r * (m : ℂ) ^ (-(r : ℂ) - 1) := by
      unfold profilePowerOrder
      rw [show -(rho - 1) = 1 - rho by ring]
      simp only [Complex.ofReal_natCast]
      calc
        _ = (-1 : ℂ) ^ r * profileEMRising (1 - rho) r *
            ((m : ℂ) ^ (rho - 1 - (r : ℂ)) * (m : ℂ) ^ (-rho)) := by ring
        _ = _ := by rw [← Complex.cpow_add _ _ hm]; congr 2; ring
    simp only [profileAnalyticCellJet, if_neg hr]
    change -(profilePowerOrder (-rho) r (m : ℝ) * cellSumA rho (n + 1) -
        profilePowerOrder (rho - 1) r (m : ℝ) * cellSumB rho (n + 1)) / normalizationBrho rho -
      -(profilePowerOrder (-rho) r (m : ℝ) * cellSumA rho n -
        profilePowerOrder (rho - 1) r (m : ℝ) * cellSumB rho n) / normalizationBrho rho = _
    rw [hA, hB]
    have hd := profileEMRising_difference rho r
    have hk := kappa_div_brho h0 h1 hh
    calc
      _ = -(profilePowerOrder (-rho) r (m : ℝ) * (m : ℂ) ^ (rho - 1) -
          profilePowerOrder (rho - 1) r (m : ℝ) * (m : ℂ) ^ (-rho)) / normalizationBrho rho := by ring
      _ = -((-1 : ℂ) ^ r * (profileEMRising rho r - profileEMRising (1 - rho) r) *
          (m : ℂ) ^ (-(r : ℂ) - 1)) / normalizationBrho rho := by rw [hPA, hPB]; ring
      _ = (-1 : ℂ) ^ r * (-((2 * rho - 1) / normalizationBrho rho)) *
          (profileFactorPolynomial r).eval (spectralKappa rho) * (m : ℂ) ^ (-(r : ℂ) - 1) := by
        rw [hd]
        unfold spectralKappa
        ring
      _ = _ := by rw [hk]; ring



def profileQuadraticCell {d : ℕ} (rho : Fin d → ℂ) (A : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ i : Fin d, ∑ k : Fin d, A i k * profileAnalyticCell (rho i) n x * profileAnalyticCell (rho k) n x

def profileQuadraticCellJet {d : ℕ} (rho : Fin d → ℂ) (A : Matrix (Fin d) (Fin d) ℂ)
    (n r : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (r + 1), (r.choose k : ℂ) *
    dotProduct (fun i => profileAnalyticCellJet (rho i) n k x)
      (A.mulVec (fun i => profileAnalyticCellJet (rho i) n (r - k) x))

theorem profileQuadraticCell_contDiffAt {d : ℕ} (rho : Fin d → ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ (profileQuadraticCell rho A n) x := by
  unfold profileQuadraticCell
  apply ContDiffAt.sum
  intro i hi
  apply ContDiffAt.sum
  intro k hk
  exact (contDiffAt_const.mul (profileAnalyticCell_contDiffAt (rho i) n hx)).mul
    (profileAnalyticCell_contDiffAt (rho k) n hx)

theorem profileQuadraticCell_iteratedDeriv {d : ℕ} (rho : Fin d → ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (n r : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv r (profileQuadraticCell rho A n) x = profileQuadraticCellJet rho A n r x := by
  have hci (i : Fin d) : ContDiffAt ℝ (r : ℕ∞ω) (profileAnalyticCell (rho i) n) x :=
    (profileAnalyticCell_contDiffAt (rho i) n hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)
  have hd (i j : Fin d) :
      iteratedDeriv r (fun t : ℝ => A i j * profileAnalyticCell (rho i) n t *
        profileAnalyticCell (rho j) n t) x =
      ∑ k ∈ Finset.range (r + 1), (r.choose k : ℂ) * A i j *
        profileAnalyticCellJet (rho i) n k x * profileAnalyticCellJet (rho j) n (r - k) x := by
    have hf : ContDiffAt ℝ (r : ℕ∞ω) (fun t : ℝ => A i j * profileAnalyticCell (rho i) n t) x :=
      contDiffAt_const.mul (hci i)
    have hh := iteratedDeriv_mul hf (hci j)
    have hh' : iteratedDeriv r (fun t : ℝ => A i j * profileAnalyticCell (rho i) n t *
        profileAnalyticCell (rho j) n t) x =
        ∑ k ∈ Finset.range (r + 1), (r.choose k : ℂ) *
          iteratedDeriv k (fun t : ℝ => A i j * profileAnalyticCell (rho i) n t) x *
            iteratedDeriv (r - k) (profileAnalyticCell (rho j) n) x := by
      simpa only [Pi.mul_apply] using! hh
    rw [hh']
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDeriv_const_mul_field, profileAnalyticCellJet_iteratedDeriv _ _ _ hx,
      profileAnalyticCellJet_iteratedDeriv _ _ _ hx]
    ring
  have hsij (i j : Fin d) : ContDiffAt ℝ (r : ℕ∞ω)
      (fun t : ℝ => A i j * profileAnalyticCell (rho i) n t * profileAnalyticCell (rho j) n t) x :=
    (contDiffAt_const.mul (hci i)).mul (hci j)
  change iteratedDeriv r (fun t : ℝ => ∑ i : Fin d, ∑ j : Fin d,
    A i j * profileAnalyticCell (rho i) n t * profileAnalyticCell (rho j) n t) x = _
  rw [iteratedDeriv_fun_sum (fun i _ => ContDiffAt.sum (fun j _ => hsij i j))]
  simp_rw [iteratedDeriv_fun_sum (fun j _ => hsij _ j), hd]
  calc
    _ = ∑ i : Fin d, ∑ k ∈ Finset.range (r + 1), ∑ j : Fin d,
        (r.choose k : ℂ) * A i j * profileAnalyticCellJet (rho i) n k x *
          profileAnalyticCellJet (rho j) n (r - k) x := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (r + 1), ∑ i : Fin d, ∑ j : Fin d,
        (r.choose k : ℂ) * A i j * profileAnalyticCellJet (rho i) n k x *
          profileAnalyticCellJet (rho j) n (r - k) x := Finset.sum_comm
    _ = _ := by
      unfold profileQuadraticCellJet Matrix.mulVec dotProduct
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem profileQuadraticCell_eq_source {d : ℕ} (rho : Fin d → ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) {n : ℕ} {x : ℝ} (hpos : 0 < x)
    (hx : x ∈ Ico (n : ℝ) (n + 1)) : profileQuadraticCell rho A n x = profileComplexQuadratic rho A x := by
  unfold profileQuadraticCell profileComplexQuadratic Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [profileAnalyticCell_eq_source _ hpos hx, profileAnalyticCell_eq_source _ hpos hx]
  ring

theorem profileAnalyticCell_endpoint_eq (rho : ℂ) (n : ℕ) :
    profileAnalyticCell rho (n + 1) ((n + 1 : ℕ) : ℝ) = profileAnalyticCell rho n ((n + 1 : ℕ) : ℝ) := by
  unfold profileAnalyticCell
  rw [srhoCell_succ_eq]

theorem profileQuadraticCell_endpoint_eq {d : ℕ} (rho : Fin d → ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    profileQuadraticCell rho A (n + 1) ((n + 1 : ℕ) : ℝ) =
      profileQuadraticCell rho A n ((n + 1 : ℕ) : ℝ) := by
  unfold profileQuadraticCell
  simp only [profileAnalyticCell_endpoint_eq]

theorem profileQuadraticCell_right_eq {d : ℕ} (rho : Fin d → ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    EqOn (profileQuadraticCell rho A (n + 1)) (profileComplexQuadratic rho A)
      (Icc (((n + 1 : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ) + 1 / 2)) := by
  intro x hx
  have hpos : 0 < x := by
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    exact hn.trans_le hx.1
  apply profileQuadraticCell_eq_source rho A hpos
  constructor
  · exact hx.1
  · push_cast at *
    linarith [hx.2]

theorem profileQuadraticCell_left_eq {d : ℕ} (rho : Fin d → ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    EqOn (profileQuadraticCell rho A n) (profileComplexQuadratic rho A)
      (Icc ((((n + 1 : ℕ) : ℝ)) - 1 / 2) (((n + 1 : ℕ) : ℝ))) := by
  intro x hx
  by_cases he : x = ((n + 1 : ℕ) : ℝ)
  · subst x
    rw [← profileQuadraticCell_endpoint_eq]
    exact profileQuadraticCell_right_eq rho A n ⟨le_rfl, by linarith⟩
  · apply profileQuadraticCell_eq_source rho A (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; push_cast at *; linarith [hx.1])
    constructor
    · push_cast at *
      linarith [hx.1]
    · have hlt := lt_of_le_of_ne hx.2 he
      simpa only [Nat.cast_add, Nat.cast_one] using hlt



theorem profile_top_coefficient_vector_mod_lower {d j : ℕ}
    (kappa : Fin d → ℂ) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ r : ℕ, r < j → A.mulVec (profilePowerRow kappa r) = 0)
    (p : ℂ[X]) (hp : p.natDegree ≤ j) :
    A.mulVec (fun i => kappa i * p.eval (kappa i)) =
      p.coeff j • A.mulVec (profilePowerRow kappa j) := by
  let F : ℂ[X] →ₗ[ℂ] (Fin d → ℂ) := A.mulVecLin.comp (profileWeightedPolynomialEvaluation kappa)
  have hpow (r : ℕ) : F (X ^ r) = A.mulVec (profilePowerRow kappa r) := by
    change A.mulVec _ = _
    congr 1
    ext i
    simp [profileWeightedPolynomialEvaluation, profilePowerRow, pow_succ, mul_comm]
  change F p = _
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (show p.natDegree < j + 1 by omega)]
  rw [map_sum, Finset.sum_range_succ]
  have hl : (∑ r ∈ Finset.range j, F (C (p.coeff r) * X ^ r)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [← Polynomial.smul_eq_C_mul, map_smul, hpow, hA r (Finset.mem_range.mp hr), smul_zero]
  rw [hl, zero_add, ← Polynomial.smul_eq_C_mul, map_smul, hpow]

theorem profile_odd_coefficient_vector_mod_lower {d j : ℕ}
    (kappa : Fin d → ℂ) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ r : ℕ, r < j → A.mulVec (profilePowerRow kappa r) = 0) :
    A.mulVec (fun i => kappa i * (profileFactorPolynomial (2*j+1)).eval (kappa i)) =
      (-1 : ℂ)^j • A.mulVec (profilePowerRow kappa j) := by
  rw [profile_top_coefficient_vector_mod_lower kappa A hA _
    (profileFactorPolynomial_degree_pair j).1, (profileFactorPolynomial_degree_pair j).2.1]

theorem profile_cell_jump_vector {d : ℕ} (rho : Fin d → ℂ)
    (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (hh : ∀ i, rho i ≠ 1/2) (n r : ℕ) :
    (fun i => profileAnalyticCellJet (rho i) (n+1) r ((n+1:ℕ):ℝ)) -
      (fun i => profileAnalyticCellJet (rho i) n r ((n+1:ℕ):ℝ)) =
    ((-1:ℂ)^r * ((n+1:ℕ):ℂ)^(-(r:ℂ)-1)) •
      (fun i => spectralKappa (rho i) * (profileFactorPolynomial r).eval (spectralKappa (rho i))) := by
  ext i
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    using profileAnalyticCellJet_jump (h0 i) (h1 i) (hh i) n r

theorem profile_lower_cell_jumps_killed {d j : ℕ} (rho : Fin d → ℂ)
    (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (hh : ∀ i, rho i ≠ 1/2) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ r : ℕ, r < j → A.mulVec (profilePowerRow (fun i => spectralKappa (rho i)) r) = 0)
    (n s : ℕ) (hs : s < 2*j+1) :
    A.mulVec ((fun i => profileAnalyticCellJet (rho i) (n+1) s ((n+1:ℕ):ℝ)) -
      (fun i => profileAnalyticCellJet (rho i) n s ((n+1:ℕ):ℝ))) = 0 := by
  rw [profile_cell_jump_vector rho h0 h1 hh, Matrix.mulVec_smul,
    profile_small_coefficient_vector_annihilation _ A hA (by omega), smul_zero]

theorem profile_odd_cell_jump_after_projection {d j : ℕ} (rho : Fin d → ℂ)
    (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (hh : ∀ i, rho i ≠ 1/2) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ r : ℕ, r < j → A.mulVec (profilePowerRow (fun i => spectralKappa (rho i)) r) = 0)
    (n : ℕ) :
    A.mulVec ((fun i => profileAnalyticCellJet (rho i) (n+1) (2*j+1) ((n+1:ℕ):ℝ)) -
      (fun i => profileAnalyticCellJet (rho i) n (2*j+1) ((n+1:ℕ):ℝ))) =
      ((-1:ℂ)^(j+1) / ((n+1:ℕ):ℂ)^(2*j+2)) •
        A.mulVec (profilePowerRow (fun i => spectralKappa (rho i)) j) := by
  rw [profile_cell_jump_vector rho h0 h1 hh, Matrix.mulVec_smul,
    profile_odd_coefficient_vector_mod_lower _ A hA, smul_smul]
  congr 1
  have he : (-((2*j+1:ℕ):ℂ)-1) = -((2*j+2:ℕ):ℂ) := by push_cast; ring
  rw [he, Complex.cpow_neg, Complex.cpow_natCast]
  have hp : (-1:ℂ)^(2*j+1) * (-1:ℂ)^j = (-1:ℂ)^(j+1) := by
    rw [pow_add, pow_mul]
    norm_num
    simp [pow_succ]
  rw [mul_right_comm, hp, div_eq_mul_inv]

theorem profile_actual_quadratic_odd_jump {d j : ℕ} (rho : Fin d → ℂ)
    (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (hh : ∀ i, rho i ≠ 1/2) (A : Matrix (Fin d) (Fin d) ℂ) (hSym : A.IsSymm)
    (hA : ∀ r : ℕ, r < j → A.mulVec (profilePowerRow (fun i => spectralKappa (rho i)) r) = 0)
    (n : ℕ) :
    iteratedDeriv (2*j+1) (profileQuadraticCell rho A (n+1)) ((n+1:ℕ):ℝ) -
      iteratedDeriv (2*j+1) (profileQuadraticCell rho A n) ((n+1:ℕ):ℝ) =
    QuadraticProfileBootstrap.quadraticJumpScale j n *
      dotProduct (fun i => zeroProfile (rho i) ((n+1:ℕ):ℝ))
        (A.mulVec (profilePowerRow (fun i => spectralKappa (rho i)) j)) := by
  have hn : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
  rw [profileQuadraticCell_iteratedDeriv _ _ _ _ hn, profileQuadraticCell_iteratedDeriv _ _ _ _ hn]
  let JP : ℕ → Fin d → ℂ := fun r i => profileAnalyticCellJet (rho i) (n+1) r ((n+1:ℕ):ℝ)
  let JM : ℕ → Fin d → ℂ := fun r i => profileAnalyticCellJet (rho i) n r ((n+1:ℕ):ℝ)
  let H : Fin d → ℂ := fun i => zeroProfile (rho i) ((n+1:ℕ):ℝ)
  have hp0 : JP 0 = H := by
    ext i
    change profileAnalyticCell (rho i) (n+1) ((n+1:ℕ):ℝ) = _
    apply profileAnalyticCell_eq_source _ hn
    constructor <;> push_cast <;> linarith
  have hm0 : JM 0 = H := by
    ext i
    change profileAnalyticCell (rho i) n ((n+1:ℕ):ℝ) = _
    rw [← profileAnalyticCell_endpoint_eq]
    exact congrFun hp0 i
  have hk : ∀ s : ℕ, 0<s → s<2*j+1 → A.mulVec (JP s-JM s)=0 := by
    intro s _ hs
    exact profile_lower_cell_jumps_killed rho h0 h1 hh A hA n s hs
  have hc := QuadraticProfileBootstrap.symmetric_leibniz_jump_cancel A hSym JP JM H
    (2*j+1) (by omega) hp0 hm0 hk
  change (∑ k ∈ Finset.range (2*j+1+1), _) - (∑ k ∈ Finset.range (2*j+1+1), _) = _
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ k ∈ Finset.range (2*j+1+1), ((2*j+1).choose k:ℂ) *
        (dotProduct (JP k) (A.mulVec (JP (2*j+1-k))) - dotProduct (JM k) (A.mulVec (JM (2*j+1-k)))) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [JP, JM]
      ring
    _ = 2*dotProduct H (A.mulVec (JP (2*j+1)-JM (2*j+1))) := hc
    _ = _ := by
      have he := profile_odd_cell_jump_after_projection rho h0 h1 hh A hA n
      change A.mulVec (JP (2*j+1)-JM (2*j+1)) = _ at he
      rw [he, dotProduct_smul]
      unfold QuadraticProfileBootstrap.quadraticJumpScale
      simp only [smul_eq_mul]
      ring



theorem profileComplexQuadratic_weighted_moments {d : ℕ} (rho : Fin d → ℂ)
    (hz : ∀ i, riemannZeta (rho i) = 0) (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (A : Matrix (Fin d) (Fin d) ℂ) (hSym : A.IsSymm) (j : ℕ)
    (hA : ∀ r : ℕ, r < j → A.mulVec (profilePowerRow (fun i => spectralKappa (rho i)) r) = 0) :
    ∀ k : ℕ, k ≤ 4*j+2 → Integrable (fun x : ℝ => ‖x‖^k * ‖profileComplexQuadratic rho A x‖) := by
  apply QuadraticProfileBootstrap.quadratic_tail_weighted_moments
    (profileComplexQuadratic_continuous rho A) j
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    profileComplexQuadratic_improved_tail rho hz h0 h1 A hSym j hA

theorem profileComplexQuadratic_integrable {d : ℕ} (rho : Fin d → ℂ)
    (hz : ∀ i, riemannZeta (rho i) = 0) (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (A : Matrix (Fin d) (Fin d) ℂ) (hSym : A.IsSymm) :
    Integrable (profileComplexQuadratic rho A) := by
  have hm := profileComplexQuadratic_weighted_moments rho hz h0 h1 A hSym 0
    (by intro r hr; omega) 0 (by omega)
  apply (integrable_norm_iff (profileComplexQuadratic_continuous rho A).aestronglyMeasurable).mp
  simpa only [pow_zero, one_mul] using hm

/-- Source-faithful complex strengthening of the finite quadratic obstruction:
the matrix is symmetric, with no positivity premise. Every source asymptotic,
sample-span, moment and integer-cell jump obligation is discharged above. -/
theorem profile_complex_symmetric_selfdual_rigidity {d : ℕ} (rho : Fin d → ℂ)
    (hz : ∀ i, riemannZeta (rho i) = 0) (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (hinj : Function.Injective (fun i => spectralKappa (rho i)))
    (A : Matrix (Fin d) (Fin d) ℂ) (hSym : A.IsSymm)
    (hsd : ∀ φ : 𝓢(ℝ,ℂ),
      (∫ x, profileComplexQuadratic rho A x * (𝓕 φ : 𝓢(ℝ,ℂ)) x) =
        ∫ x, profileComplexQuadratic rho A x * φ x) : A = 0 := by
  let H : ℝ → Fin d → ℂ := fun x i => zeroProfile (rho i) x
  let R : ℕ → Fin d → ℂ := profilePowerRow (fun i => spectralKappa (rho i))
  have hκ : ∀ i, spectralKappa (rho i) ≠ 0 := by
    intro i
    obtain ⟨hr0, hr1⟩ := strip_ne (h0 i) (h1 i)
    exact mul_ne_zero hr0 (sub_ne_zero.mpr hr1.symm)
  refine QuadraticProfileBootstrap.quadratic_fourier_bootstrap A H R
    (profileComplexQuadratic rho A) (fun n => profileQuadraticCell rho A (n+1))
    (fun n => profileQuadraticCell rho A n)
    (profileComplexQuadratic_integrable rho hz h0 h1 A hSym)
    (profileComplexQuadratic_continuous rho A) hsd ?_ ?_ ?_ ?_ ?_
  · exact profile_zero_integer_samples_span rho hz h0 h1 hinj
  · exact profile_power_rows_span _ hκ hinj
  · intro j hj hlow
    exact profileComplexQuadratic_weighted_moments rho hz h0 h1 A hSym j hlow
  · intro n
    refine ⟨1/2, by norm_num, ?_, ?_, profileQuadraticCell_right_eq rho A n,
      profileQuadraticCell_left_eq rho A n⟩
    · exact profileQuadraticCell_contDiffAt rho A (n+1) (by positivity)
    · exact profileQuadraticCell_contDiffAt rho A n (by positivity)
  · intro j hj hlow n
    exact profile_actual_quadratic_odd_jump rho h0 h1 (fun i => zero_ne_half (hz i)) A hSym hlow n




theorem profile_spectral_conj (rho : ℂ) :
    spectralKappa (starRingEnd ℂ rho) = starRingEnd ℂ (spectralKappa rho) := by
  simp only [spectralKappa, map_mul, map_sub, map_one]

theorem profile_spectral_eq_iff_reflection (rho sigma : ℂ) :
    spectralKappa rho = spectralKappa sigma ↔ rho = sigma ∨ rho = 1-sigma := by
  constructor
  · intro h
    have hf : (rho-sigma)*(rho+sigma-1)=0 := by
      unfold spectralKappa at h
      linear_combination -h
    rcases mul_eq_zero.mp hf with he | he
    · exact Or.inl (sub_eq_zero.mp he)
    · exact Or.inr (by linear_combination he)
  · rintro (rfl | rfl)
    · rfl
    · exact spectralKappa_one_sub sigma

theorem profile_source_eq_of_spectral_eq {rho sigma : ℂ}
    (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) (hrh : rho ≠ 1/2)
    (hs0 : sigma ≠ 0) (hs1 : sigma ≠ 1) (hsh : sigma ≠ 1/2)
    (he : spectralKappa rho = spectralKappa sigma) : zeroProfile rho = zeroProfile sigma := by
  funext x
  rw [zeroProfile_eq_one_sub_family hr0 hr1 hrh, zeroProfile_eq_one_sub_family hs0 hs1 hsh, he]

theorem profile_source_conj {rho : ℂ} (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) (hrh : rho ≠ 1/2) (x : ℝ) :
    zeroProfile (starRingEnd ℂ rho) x = starRingEnd ℂ (zeroProfile rho x) := by
  have hc0 : starRingEnd ℂ rho ≠ 0 := (_root_.map_ne_zero _).mpr hr0
  have hc1 : starRingEnd ℂ rho ≠ 1 := by
    intro he
    apply hr1
    have hc := congrArg (starRingEnd ℂ) he
    simpa using hc
  have hch : starRingEnd ℂ rho ≠ 1/2 := by
    intro he
    apply hrh
    have hc := congrArg (starRingEnd ℂ) he
    simp only [map_div₀, map_one, map_ofNat] at hc
    simpa using hc
  rw [zeroProfile_eq_one_sub_family hc0 hc1 hch, zeroProfile_eq_one_sub_family hr0 hr1 hrh,
    profile_spectral_conj, zeroFamilyDensity_conj, map_sub, map_one]

theorem profile_source_real_of_real_spectral {rho : ℂ}
    (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) (hrh : rho ≠ 1/2)
    (hk : (spectralKappa rho).im = 0) (x : ℝ) :
    ((zeroProfile rho x).re : ℂ) = zeroProfile rho x := by
  apply Complex.conj_eq_iff_re.mp
  rw [zeroProfile_eq_one_sub_family hr0 hr1 hrh, map_sub, map_one,
    ← zeroFamilyDensity_conj, Complex.conj_eq_iff_im.mpr hk]

theorem profile_source_cocompact_zero {rho : ℂ}
    (hz : riemannZeta rho = 0) (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    Tendsto (zeroProfile rho) (cocompact ℝ) (𝓝 0) := by
  rw [← fourier_zeroProfile hz h0 h1]
  exact Real.zero_at_infty_fourier _

theorem profileComplexQuadratic_cocompact_zero {d : ℕ} (rho : Fin d → ℂ)
    (hz : ∀ i, riemannZeta (rho i) = 0) (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    Tendsto (profileComplexQuadratic rho A) (cocompact ℝ) (𝓝 0) := by
  have ht (i : Fin d) := profile_source_cocompact_zero (hz i) (h0 i) (h1 i)
  unfold profileComplexQuadratic Matrix.mulVec dotProduct
  have hinner (i : Fin d) : Tendsto (fun x : ℝ => ∑ j : Fin d, A i j * zeroProfile (rho j) x)
      (cocompact ℝ) (𝓝 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun j _ => tendsto_const_nhds.mul (ht j))
  simpa only [mul_zero, Finset.sum_const_zero] using
    tendsto_finset_sum Finset.univ (fun i _ => (ht i).mul (hinner i))




/-- Full locally finite complex-measure correction domain. The correction
has a genuine order-zero tempered extension of its compact-test pairing;
no total-variation growth exponent is prescribed. Selfdual comb terms may
remain when the quadratic density is zero. -/
theorem profile_complex_quadratic_lattice_repair_rigidity {d : ℕ} (rho : Fin d → ℂ)
    (hz : ∀ i, riemannZeta (rho i) = 0) (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (hinj : Function.Injective (fun i => spectralKappa (rho i)))
    (A : Matrix (Fin d) (Fin d) ℂ) (hSym : A.IsSymm)
    (sigma : LocallyFiniteComplexMeasure) (T : TemperedDistribution ℝ ℂ)
    (hsigma : sigma.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ = 0)
    (hT : TemperedLatticeBridge.ExtendsCompactPairing sigma T)
    (hRepair : ∀ φ : 𝓢(ℝ,ℂ),
      (∫ x, profileComplexQuadratic rho A x * (𝓕 φ : 𝓢(ℝ,ℂ)) x) + T (𝓕 φ) =
        (∫ x, profileComplexQuadratic rho A x * φ x) + T φ) : A = 0 := by
  apply profile_complex_symmetric_selfdual_rigidity rho hz h0 h1 hinj A hSym
  exact QuadraticProfileBootstrap.pairing_selfdual_of_lattice_repair
    (profileComplexQuadratic_integrable rho hz h0 h1 A hSym)
    (profileComplexQuadratic_continuous rho A)
    (profileComplexQuadratic_cocompact_zero rho hz h0 h1 A) T
    (TemperedLatticeBridge.extension_annihilates_lattice_zero sigma T hsigma hT)
    (TemperedLatticeBridge.extension_congr_on_lattice sigma T hsigma hT) hRepair




def profileComplexQuadraticOnIndex {ι : Type*} [Fintype ι]
    (rho : ι → ℂ) (A : Matrix ι ι ℂ) (x : ℝ) : ℂ :=
  dotProduct (fun i => zeroProfile (rho i) x) (A.mulVec (fun i => zeroProfile (rho i) x))

theorem profileComplexQuadratic_reindex {ι : Type*} [Fintype ι]
    (rho : ι → ℂ) (A : Matrix ι ι ℂ) (e : Fin (Fintype.card ι) ≃ ι) (x : ℝ) :
    profileComplexQuadratic (fun i => rho (e i)) (fun i j => A (e i) (e j)) x =
      profileComplexQuadraticOnIndex rho A x := by
  unfold profileComplexQuadratic profileComplexQuadraticOnIndex Matrix.mulVec dotProduct
  change (∑ i : Fin (Fintype.card ι), zeroProfile (rho (e i)) x *
    ∑ j : Fin (Fintype.card ι), A (e i) (e j) * zeroProfile (rho (e j)) x) =
    ∑ i : ι, zeroProfile (rho i) x * ∑ j : ι, A i j * zeroProfile (rho j) x
  calc
    _ = ∑ i : Fin (Fintype.card ι), zeroProfile (rho (e i)) x *
        ∑ j : ι, A (e i) j * zeroProfile (rho j) x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun z : ℂ => zeroProfile (rho (e i)) x * z)
        (e.sum_comp (fun j => A (e i) j * zeroProfile (rho j) x))
    _ = _ := e.sum_comp (fun i : ι => zeroProfile (rho i) x *
      ∑ j : ι, A i j * zeroProfile (rho j) x)

theorem profile_complex_symmetric_selfdual_rigidity_on_index {ι : Type*} [Fintype ι]
    (rho : ι → ℂ) (hz : ∀ i, riemannZeta (rho i) = 0)
    (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (hinj : Function.Injective (fun i => spectralKappa (rho i)))
    (A : Matrix ι ι ℂ) (hSym : A.IsSymm)
    (hsd : ∀ φ : 𝓢(ℝ,ℂ),
      (∫ x, profileComplexQuadraticOnIndex rho A x * (𝓕 φ : 𝓢(ℝ,ℂ)) x) =
        ∫ x, profileComplexQuadraticOnIndex rho A x * φ x) : A = 0 := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let AF : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ := fun i j => A (e i) (e j)
  have hAF : AF.IsSymm := by
    ext i j
    exact congrFun (congrFun hSym (e i)) (e j)
  have heq : profileComplexQuadratic (fun i => rho (e i)) AF = profileComplexQuadraticOnIndex rho A := by
    funext x
    exact profileComplexQuadratic_reindex rho A e x
  have hf := profile_complex_symmetric_selfdual_rigidity (fun i => rho (e i))
    (fun i => hz (e i)) (fun i => h0 (e i)) (fun i => h1 (e i))
    (hinj.comp e.injective) AF hAF (by simpa only [heq] using hsd)
  ext i j
  have hh := congrFun (congrFun hf (e.symm i)) (e.symm j)
  simpa only [AF, e.apply_symm_apply, Matrix.zero_apply] using hh




theorem profile_source_tail_order_two {rho : ℂ}
    (hz : riemannZeta rho = 0) (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| → ‖zeroProfile rho x‖ ≤ C * |x|^(-2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := zeroProfile_norm_le hz h0 h1
  refine ⟨C,hC,fun x hx => (hb x).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  have hx0 : 0 < x^2 := by nlinarith [sq_abs x]
  rw [Real.rpow_neg (abs_nonneg x), Real.rpow_two, sq_abs]
  exact (inv_le_inv₀ (by positivity) hx0).mpr (by linarith)

/-- The actual inherited source model, including its gap normalization,
integrability, Fourier normalization and decay, before taking quadratic forms. -/
theorem profile_actual_source_properties {rho : ℂ}
    (hz : riemannZeta rho = 0) (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    rho ≠ 0 ∧ rho ≠ 1 ∧ rho ≠ 1/2 ∧ normalizationBrho rho ≠ 0 ∧ spectralKappa rho ≠ 0 ∧
    Continuous (zeroProfile rho) ∧ Integrable (zeroProfile rho) ∧
    𝓕 (zeroProfile rho) = zeroProfile rho ∧
    (∀ x : ℝ, |x| ≤ 1 → zeroProfile rho x = 1) ∧
    Tendsto (zeroProfile rho) (cocompact ℝ) (𝓝 0) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| → ‖zeroProfile rho x‖ ≤ C * |x|^(-2:ℝ) := by
  obtain ⟨hr0,hr1⟩ := strip_ne h0 h1
  have hh := zero_ne_half hz
  exact ⟨hr0,hr1,hh,normalizationBrho_ne_zero hr0 hr1 hh,
    mul_ne_zero hr0 (sub_ne_zero.mpr hr1.symm),continuous_zeroProfile rho,
    integrable_zeroProfile hz h0 h1,fourier_zeroProfile hz h0 h1,
    fun _ hx => zeroProfile_eq_one rho hx,profile_source_cocompact_zero hz h0 h1,
    profile_source_tail_order_two hz h0 h1⟩

theorem profile_complex_quadratic_selfdual_and_lattice_repair_rigidity {d : ℕ} (rho : Fin d → ℂ)
    (hz : ∀ i, riemannZeta (rho i) = 0) (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (hinj : Function.Injective (fun i => spectralKappa (rho i)))
    (A : Matrix (Fin d) (Fin d) ℂ) (hSym : A.IsSymm)
    (sigma : LocallyFiniteComplexMeasure) (T S : TemperedDistribution ℝ ℂ)
    (hsigma : sigma.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ = 0)
    (hT : TemperedLatticeBridge.ExtendsCompactPairing sigma T) (hS : 𝓕 S = S)
    (hRepair : ∀ φ : 𝓢(ℝ,ℂ),
      (∫ x, profileComplexQuadratic rho A x * (𝓕 φ : 𝓢(ℝ,ℂ)) x) + S (𝓕 φ) + T (𝓕 φ) =
        (∫ x, profileComplexQuadratic rho A x * φ x) + S φ + T φ) : A = 0 := by
  apply profile_complex_quadratic_lattice_repair_rigidity rho hz h0 h1 hinj A hSym sigma T hsigma hT
  intro φ
  have hs : S (𝓕 φ) = S φ := by
    simpa only [TemperedDistribution.fourier_apply] using congrArg (fun D : TemperedDistribution ℝ ℂ => D φ) hS
  have hh := hRepair φ
  rw [hs] at hh
  linear_combination hh




theorem profile_span_top_of_reindex {ι ν : Type*} [Fintype ι]
    (e : Fin (Fintype.card ι) ≃ ι) (v : ν → ι → ℂ)
    (h : Submodule.span ℂ (Set.range (fun n i => v n (e i))) = ⊤) :
    Submodule.span ℂ (Set.range v) = ⊤ := by
  let E : (Fin (Fintype.card ι) → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ e.symm
  have he : Set.range v = E '' Set.range (fun n i => v n (e i)) := by
    ext x
    constructor
    · rintro ⟨n,rfl⟩
      refine ⟨(fun i => v n (e i)),⟨n,rfl⟩,?_⟩
      ext i
      simp [E, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft]
    · rintro ⟨w,⟨n,rfl⟩,rfl⟩
      refine ⟨n,?_⟩
      ext i
      simp [E, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft]
  rw [he]
  change Submodule.span ℂ (E.toLinearMap '' Set.range (fun n i => v n (e i))) = ⊤
  rw [← Submodule.map_span, h]
  simpa only [Submodule.map_top] using (LinearMap.range_eq_top.mpr E.surjective)

theorem profile_power_rows_span_on_index {ι : Type*} [Fintype ι]
    (kappa : ι → ℂ) (hne : ∀ i, kappa i ≠ 0) (hinj : Function.Injective kappa) :
    Submodule.span ℂ (Set.range (fun r : Fin (Fintype.card ι) =>
      fun i => kappa i ^ (r.val+1))) = ⊤ := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  apply profile_span_top_of_reindex e
  exact profile_power_rows_span (fun i => kappa (e i)) (fun i => hne (e i)) (hinj.comp e.injective)




theorem profileComplexQuadraticOnIndex_integrable {ι : Type*} [Fintype ι]
    (rho : ι → ℂ) (hz : ∀ i, riemannZeta (rho i) = 0)
    (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (A : Matrix ι ι ℂ) (hSym : A.IsSymm) : Integrable (profileComplexQuadraticOnIndex rho A) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hs : Matrix.IsSymm (fun i j => A (e i) (e j) : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) := by
    ext i j
    exact congrFun (congrFun hSym (e i)) (e j)
  have he : profileComplexQuadratic (fun i => rho (e i)) (fun i j => A (e i) (e j)) =
      profileComplexQuadraticOnIndex rho A := funext (profileComplexQuadratic_reindex rho A e)
  rw [← he]
  exact profileComplexQuadratic_integrable _ (fun i => hz (e i)) (fun i => h0 (e i)) (fun i => h1 (e i)) _ hs

theorem profileComplexQuadraticOnIndex_continuous {ι : Type*} [Fintype ι]
    (rho : ι → ℂ) (A : Matrix ι ι ℂ) : Continuous (profileComplexQuadraticOnIndex rho A) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have he : profileComplexQuadratic (fun i => rho (e i)) (fun i j => A (e i) (e j)) =
      profileComplexQuadraticOnIndex rho A := funext (profileComplexQuadratic_reindex rho A e)
  rw [← he]
  exact profileComplexQuadratic_continuous _ _

theorem profileComplexQuadraticOnIndex_cocompact_zero {ι : Type*} [Fintype ι]
    (rho : ι → ℂ) (hz : ∀ i, riemannZeta (rho i) = 0)
    (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1) (A : Matrix ι ι ℂ) :
    Tendsto (profileComplexQuadraticOnIndex rho A) (cocompact ℝ) (𝓝 0) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have he : profileComplexQuadratic (fun i => rho (e i)) (fun i j => A (e i) (e j)) =
      profileComplexQuadraticOnIndex rho A := funext (profileComplexQuadratic_reindex rho A e)
  rw [← he]
  exact profileComplexQuadratic_cocompact_zero _ (fun i => hz (e i)) (fun i => h0 (e i)) (fun i => h1 (e i)) _



open QuadraticProfileRealification

def profileExpandedNodes {r c : ℕ} (rhoReal : Fin r → ℂ) (rhoComplex : Fin c → ℂ) : MixedIndex r c → ℂ
  | .inl i => rhoReal i
  | .inr (i,k) => if k = 0 then rhoComplex i else starRingEnd ℂ (rhoComplex i)

/-- Reflection has already been quotiented by requiring distinct actual κ
coordinates; a nonreal conjugate pair has exactly one real/imaginary block. -/
structure ProfileBlockFamily (r c : ℕ) where
  rhoReal : Fin r → ℂ
  rhoComplex : Fin c → ℂ
  realZero : ∀ i, riemannZeta (rhoReal i) = 0
  complexZero : ∀ i, riemannZeta (rhoComplex i) = 0
  realRight : ∀ i, 0 < (rhoReal i).re
  realLeft : ∀ i, (rhoReal i).re < 1
  complexRight : ∀ i, 0 < (rhoComplex i).re
  complexLeft : ∀ i, (rhoComplex i).re < 1
  realSpectral : ∀ i, (spectralKappa (rhoReal i)).im = 0
  nonrealSpectral : ∀ i, (spectralKappa (rhoComplex i)).im ≠ 0
  distinctSpectral : Function.Injective (fun i => spectralKappa (profileExpandedNodes rhoReal rhoComplex i))

def profileBlockH {r c : ℕ} (F : ProfileBlockFamily r c) (x : ℝ) : MixedIndex r c → ℝ :=
  realVector (fun i => (zeroProfile (F.rhoReal i) x).re) (fun i => zeroProfile (F.rhoComplex i) x)

def profileBlockK {r c : ℕ} (F : ProfileBlockFamily r c) : (MixedIndex r c → ℝ) → (MixedIndex r c → ℝ) :=
  realBlockOperator (fun i => (spectralKappa (F.rhoReal i)).re) (fun i => spectralKappa (F.rhoComplex i))

def profileRealQuadratic {r c : ℕ} (F : ProfileBlockFamily r c)
    (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) (x : ℝ) : ℝ :=
  dotProduct (profileBlockH F x) (A.mulVec (profileBlockH F x))

theorem profileExpandedNodes_zero {r c : ℕ} (F : ProfileBlockFamily r c) :
    ∀ i, riemannZeta (profileExpandedNodes F.rhoReal F.rhoComplex i) = 0 := by
  intro i
  rcases i with i | ⟨i,k⟩
  · exact F.realZero i
  · fin_cases k <;> simp [profileExpandedNodes, _root_.riemannZeta_conj, F.complexZero]

theorem profileExpandedNodes_right {r c : ℕ} (F : ProfileBlockFamily r c) :
    ∀ i, 0 < (profileExpandedNodes F.rhoReal F.rhoComplex i).re := by
  intro i
  rcases i with i | ⟨i,k⟩
  · exact F.realRight i
  · fin_cases k <;> simpa [profileExpandedNodes] using F.complexRight i

theorem profileExpandedNodes_left {r c : ℕ} (F : ProfileBlockFamily r c) :
    ∀ i, (profileExpandedNodes F.rhoReal F.rhoComplex i).re < 1 := by
  intro i
  rcases i with i | ⟨i,k⟩
  · exact F.realLeft i
  · fin_cases k <;> simpa [profileExpandedNodes] using F.complexLeft i

theorem profileExpandedNodes_profile {r c : ℕ} (F : ProfileBlockFamily r c) (x : ℝ) :
    (fun i => zeroProfile (profileExpandedNodes F.rhoReal F.rhoComplex i) x) =
      expandedVector (fun i => (zeroProfile (F.rhoReal i) x).re) (fun i => zeroProfile (F.rhoComplex i) x) := by
  funext i
  rcases i with i | ⟨i,k⟩
  · obtain ⟨hr0,hr1⟩ := strip_ne (F.realRight i) (F.realLeft i)
    exact (profile_source_real_of_real_spectral hr0 hr1 (zero_ne_half (F.realZero i)) (F.realSpectral i) x).symm
  · fin_cases k
    · rfl
    · obtain ⟨hr0,hr1⟩ := strip_ne (F.complexRight i) (F.complexLeft i)
      exact profile_source_conj hr0 hr1 (zero_ne_half (F.complexZero i)) x

theorem profileExpandedNodes_spectral {r c : ℕ} (F : ProfileBlockFamily r c) :
    (fun i => spectralKappa (profileExpandedNodes F.rhoReal F.rhoComplex i)) =
      expandedVector (fun i => (spectralKappa (F.rhoReal i)).re) (fun i => spectralKappa (F.rhoComplex i)) := by
  funext i
  rcases i with i | ⟨i,k⟩
  · exact (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr (F.realSpectral i))).symm
  · fin_cases k
    · rfl
    · exact profile_spectral_conj _

theorem profileBlockQuadratic_transport {r c : ℕ} (F : ProfileBlockFamily r c)
    (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) (x : ℝ) :
    profileComplexQuadraticOnIndex (profileExpandedNodes F.rhoReal F.rhoComplex) (transportedMatrix A) x =
      ((profileRealQuadratic F A x : ℝ) : ℂ) := by
  unfold profileComplexQuadraticOnIndex
  rw [profileExpandedNodes_profile]
  exact transported_real_quadratic A _ _

theorem profile_real_block_symmetric_selfdual_rigidity {r c : ℕ} (F : ProfileBlockFamily r c)
    (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) (hSym : A.IsSymm)
    (hsd : ∀ φ : 𝓢(ℝ,ℂ),
      (∫ x, (profileRealQuadratic F A x : ℂ) * (𝓕 φ : 𝓢(ℝ,ℂ)) x) =
        ∫ x, (profileRealQuadratic F A x : ℂ) * φ x) : A = 0 := by
  apply (transportedMatrix_eq_zero_iff A).mp
  apply profile_complex_symmetric_selfdual_rigidity_on_index _ (profileExpandedNodes_zero F)
    (profileExpandedNodes_right F) (profileExpandedNodes_left F) F.distinctSpectral _
    (transportedMatrix_symmetric A hSym)
  intro φ
  simpa only [profileBlockQuadratic_transport] using hsd φ

theorem profileRealQuadratic_integrable {r c : ℕ} (F : ProfileBlockFamily r c)
    (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) (hSym : A.IsSymm) :
    Integrable (profileRealQuadratic F A) := by
  have h := profileComplexQuadraticOnIndex_integrable _ (profileExpandedNodes_zero F)
    (profileExpandedNodes_right F) (profileExpandedNodes_left F) (transportedMatrix A)
    (transportedMatrix_symmetric A hSym)
  have he : profileComplexQuadraticOnIndex (profileExpandedNodes F.rhoReal F.rhoComplex) (transportedMatrix A) =
      fun x => (profileRealQuadratic F A x : ℂ) := funext (profileBlockQuadratic_transport F A)
  rw [he] at h
  simpa using h.re

theorem profileBlockK_cyclic {r c : ℕ} (F : ProfileBlockFamily r c) :
    Submodule.span ℝ (Set.range (fun n : Fin (Fintype.card (MixedIndex r c)) =>
      (profileBlockK F)^[n.val+1] cyclicVector)) = ⊤ := by
  apply real_block_cyclic_of_spectral_span
  rw [← profileExpandedNodes_spectral F]
  apply profile_power_rows_span_on_index _ _ F.distinctSpectral
  intro i
  obtain ⟨hr0,hr1⟩ := strip_ne (profileExpandedNodes_right F i) (profileExpandedNodes_left F i)
  exact mul_ne_zero hr0 (sub_ne_zero.mpr hr1.symm)




theorem profile_finite_source_combination_selfdual {ι : Type*} [Fintype ι]
    (rho : ι → ℂ) (hz : ∀ i, riemannZeta (rho i) = 0)
    (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1) (a : ι → ℂ) :
    𝓕 (fun x : ℝ => ∑ i, a i * zeroProfile (rho i) x) =
      fun x : ℝ => ∑ i, a i * zeroProfile (rho i) x := by
  have hi : Integrable (fun x : ℝ => ∑ i, a i * zeroProfile (rho i) x) :=
    integrable_finset_sum _ (fun i _ => (integrable_zeroProfile (hz i) (h0 i) (h1 i)).const_mul (a i))
  have hc : Continuous (fun x : ℝ => ∑ i, a i * zeroProfile (rho i) x) := by
    exact continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_zeroProfile (rho i)))
  apply QuadraticProfileBootstrap.ordinary_fourier_eq_of_pairing hi hc
  intro φ
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ =>
      ((square_integrable_mul_schwartz (integrable_zeroProfile (hz i) (h0 i) (h1 i)) (𝓕 φ)).const_mul (a i)).congr
        (Eventually.of_forall fun x => by ring)),
    integral_finset_sum _ (fun i _ =>
      ((square_integrable_mul_schwartz (integrable_zeroProfile (hz i) (h0 i) (h1 i)) φ).const_mul (a i)).congr
        (Eventually.of_forall fun x => by ring))]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul, zeroProfile_pairing_fourier (hz i) (h0 i) (h1 i)]

theorem profileBlockH_as_source_combination {r c : ℕ} (F : ProfileBlockFamily r c) (i : MixedIndex r c) :
    (fun x : ℝ => (profileBlockH F x i : ℂ)) = fun x : ℝ =>
      ∑ j : MixedIndex r c, realificationMatrix i j *
        zeroProfile (profileExpandedNodes F.rhoReal F.rhoComplex j) x := by
  funext x
  have he := realificationMatrix_mulVec (fun j => zeroProfile (profileExpandedNodes F.rhoReal F.rhoComplex j) x)
  have hv := congrArg realify (profileExpandedNodes_profile F x)
  rw [realify_expandedVector] at hv
  rw [hv] at he
  exact (congrFun he i).symm

theorem profileBlockH_fourier {r c : ℕ} (F : ProfileBlockFamily r c) (i : MixedIndex r c) :
    𝓕 (fun x : ℝ => (profileBlockH F x i : ℂ)) = fun x : ℝ => (profileBlockH F x i : ℂ) := by
  rw [profileBlockH_as_source_combination]
  exact profile_finite_source_combination_selfdual _ (profileExpandedNodes_zero F)
    (profileExpandedNodes_right F) (profileExpandedNodes_left F) _

theorem profileBlockH_gap {r c : ℕ} (F : ProfileBlockFamily r c) {x : ℝ} (hx : |x| ≤ 1) :
    profileBlockH F x = cyclicVector := by
  funext i
  rcases i with i | ⟨i,k⟩
  · simp [profileBlockH, realVector, cyclicVector, zeroProfile_eq_one _ hx]
  · fin_cases k <;> simp [profileBlockH, realVector, cyclicVector, zeroProfile_eq_one _ hx]

theorem profileBlockH_tail {r c : ℕ} (F : ProfileBlockFamily r c) :
    ∃ C : MixedIndex r c → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ x : ℝ, 1 ≤ |x| →
      ∀ i, ‖profileBlockH F x i‖ ≤ C i * |x|^(-2:ℝ) := by
  have hb (i : MixedIndex r c) := profile_source_tail_order_two (profileExpandedNodes_zero F i)
    (profileExpandedNodes_right F i) (profileExpandedNodes_left F i)
  choose C hC hbound using hb
  refine ⟨fun i => ∑ j : MixedIndex r c, ‖realificationMatrix i j‖ * C j,
    fun i => Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hC j)), ?_⟩
  intro x hx i
  have he := congrFun (profileBlockH_as_source_combination F i) x
  rw [← Complex.norm_real, he]
  calc
    _ ≤ ∑ j : MixedIndex r c, ‖realificationMatrix i j *
        zeroProfile (profileExpandedNodes F.rhoReal F.rhoComplex j) x‖ := norm_sum_le _ _
    _ ≤ ∑ j : MixedIndex r c, ‖realificationMatrix i j‖ * (C j * |x|^(-2:ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound j x hx) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j hj; ring

def profileBlockKMatrix {r c : ℕ} (F : ProfileBlockFamily r c) : Matrix (MixedIndex r c) (MixedIndex r c) ℝ :=
  realBlockMatrix (fun i => (spectralKappa (F.rhoReal i)).re) (fun i => spectralKappa (F.rhoComplex i))

theorem profileBlockKMatrix_mulVec {r c : ℕ} (F : ProfileBlockFamily r c) (v : MixedIndex r c → ℝ) :
    (profileBlockKMatrix F).mulVec v = profileBlockK F v := realBlockMatrix_mulVec _ _ _

theorem profileBlockKMatrix_cyclic {r c : ℕ} (F : ProfileBlockFamily r c) :
    Submodule.span ℝ (Set.range (fun n : Fin (Fintype.card (MixedIndex r c)) =>
      ((profileBlockKMatrix F)^(n.val+1)).mulVec cyclicVector)) = ⊤ := by
  simpa only [profileBlockKMatrix, profileBlockK, realBlockMatrix_power_cyclic] using profileBlockK_cyclic F

theorem profileBlockK_represents_spectral {r c : ℕ} (F : ProfileBlockFamily r c)
    (u : Fin r → ℝ) (v : Fin c → ℂ) :
    (profileBlockKMatrix F).mulVec (realVector u v) =
      realVector (fun i => (spectralKappa (F.rhoReal i)).re * u i)
        (fun i => spectralKappa (F.rhoComplex i) * v i) := by
  rw [profileBlockKMatrix_mulVec]
  exact realBlockOperator_realVector _ _ _ _




theorem profile_real_block_lattice_repair_rigidity {r c : ℕ} (F : ProfileBlockFamily r c)
    (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) (hSym : A.IsSymm)
    (sigma : LocallyFiniteComplexMeasure) (T S : TemperedDistribution ℝ ℂ)
    (hsigma : sigma.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ = 0)
    (hT : TemperedLatticeBridge.ExtendsCompactPairing sigma T) (hS : 𝓕 S = S)
    (hRepair : ∀ φ : 𝓢(ℝ,ℂ),
      (∫ x, (profileRealQuadratic F A x : ℂ) * (𝓕 φ : 𝓢(ℝ,ℂ)) x) + S (𝓕 φ) + T (𝓕 φ) =
        (∫ x, (profileRealQuadratic F A x : ℂ) * φ x) + S φ + T φ) : A = 0 := by
  have he : profileComplexQuadraticOnIndex (profileExpandedNodes F.rhoReal F.rhoComplex) (transportedMatrix A) =
      fun x => (profileRealQuadratic F A x : ℂ) := funext (profileBlockQuadratic_transport F A)
  have hi := profileComplexQuadraticOnIndex_integrable _ (profileExpandedNodes_zero F)
    (profileExpandedNodes_right F) (profileExpandedNodes_left F) (transportedMatrix A)
    (transportedMatrix_symmetric A hSym)
  have hc := profileComplexQuadraticOnIndex_continuous
    (profileExpandedNodes F.rhoReal F.rhoComplex) (transportedMatrix A)
  have hv := profileComplexQuadraticOnIndex_cocompact_zero _ (profileExpandedNodes_zero F)
    (profileExpandedNodes_right F) (profileExpandedNodes_left F) (transportedMatrix A)
  rw [he] at hi hc hv
  apply profile_real_block_symmetric_selfdual_rigidity F A hSym
  apply QuadraticProfileBootstrap.pairing_selfdual_of_lattice_repair hi hc hv T
    (TemperedLatticeBridge.extension_annihilates_lattice_zero sigma T hsigma hT)
    (TemperedLatticeBridge.extension_congr_on_lattice sigma T hsigma hT)
  intro φ
  have hs : S (𝓕 φ) = S φ := by
    simpa only [TemperedDistribution.fourier_apply] using congrArg (fun D : TemperedDistribution ℝ ℂ => D φ) hS
  have hh := hRepair φ
  rw [hs] at hh
  linear_combination hh

/-- Native source clauses for the specified finite reflection-deduplicated
real blocks. The normalization is exp(-2π i x ξ). -/
structure ProfileQuadraticSourceContract {r c : ℕ} (F : ProfileBlockFamily r c) : Prop where
  nonexceptional : ∀ i, let rho := profileExpandedNodes F.rhoReal F.rhoComplex i
    rho ≠ 0 ∧ rho ≠ 1 ∧ rho ≠ 1/2 ∧ normalizationBrho rho ≠ 0 ∧ spectralKappa rho ≠ 0
  gap : ∀ x : ℝ, |x| ≤ 1 → profileBlockH F x = cyclicVector
  tail : ∃ C : MixedIndex r c → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ x : ℝ, 1 ≤ |x| →
    ∀ i, ‖profileBlockH F x i‖ ≤ C i * |x|^(-2:ℝ)
  selfdual : ∀ i : MixedIndex r c, 𝓕 (fun x : ℝ => (profileBlockH F x i : ℂ)) =
    fun x : ℝ => (profileBlockH F x i : ℂ)
  spectralMultiplication : ∀ (u : Fin r → ℝ) (v : Fin c → ℂ),
    (profileBlockKMatrix F).mulVec (realVector u v) =
      realVector (fun i => (spectralKappa (F.rhoReal i)).re * u i)
        (fun i => spectralKappa (F.rhoComplex i) * v i)
  cyclic : Submodule.span ℝ (Set.range (fun n : Fin (Fintype.card (MixedIndex r c)) =>
    ((profileBlockKMatrix F)^(n.val+1)).mulVec cyclicVector)) = ⊤

theorem profile_quadratic_source_contract {r c : ℕ} (F : ProfileBlockFamily r c) :
    ProfileQuadraticSourceContract F := by
  refine ⟨?_,fun _ hx => profileBlockH_gap F hx,profileBlockH_tail F,profileBlockH_fourier F,
    profileBlockK_represents_spectral F,profileBlockKMatrix_cyclic F⟩
  intro i
  obtain ⟨hr0,hr1⟩ := strip_ne (profileExpandedNodes_right F i) (profileExpandedNodes_left F i)
  have hh := zero_ne_half (profileExpandedNodes_zero F i)
  exact ⟨hr0,hr1,hh,normalizationBrho_ne_zero hr0 hr1 hh,mul_ne_zero hr0 (sub_ne_zero.mpr hr1.symm)⟩

/-- Complete finite quadratic profile obstruction. There is no PSD premise,
no pointwise positivity premise, no repeated-node jet coordinate, and no
infinite or higher-degree family. Order-zero lattice repairs may retain
selfdual comb terms; the conclusion concerns the native quadratic matrix. -/
theorem finite_quadratic_profile_selfdual_obstruction {r c : ℕ} (F : ProfileBlockFamily r c) :
    ProfileQuadraticSourceContract F ∧
    (∀ A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ, A.IsSymm →
      Integrable (profileRealQuadratic F A) ∧
      ((∀ φ : 𝓢(ℝ,ℂ),
        (∫ x, (profileRealQuadratic F A x : ℂ) * (𝓕 φ : 𝓢(ℝ,ℂ)) x) =
          ∫ x, (profileRealQuadratic F A x : ℂ) * φ x) → A = 0)) ∧
    (∀ (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ), A.IsSymm →
      ∀ (sigma : LocallyFiniteComplexMeasure) (T S : TemperedDistribution ℝ ℂ),
      sigma.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ = 0 →
      TemperedLatticeBridge.ExtendsCompactPairing sigma T → 𝓕 S = S →
      (∀ φ : 𝓢(ℝ,ℂ),
        (∫ x, (profileRealQuadratic F A x : ℂ) * (𝓕 φ : 𝓢(ℝ,ℂ)) x) + S (𝓕 φ) + T (𝓕 φ) =
          (∫ x, (profileRealQuadratic F A x : ℂ) * φ x) + S φ + T φ) → A = 0) := by
  exact ⟨profile_quadratic_source_contract F,
    fun A hA => ⟨profileRealQuadratic_integrable F A hA,profile_real_block_symmetric_selfdual_rigidity F A hA⟩,
    fun A hA sigma T S hsigma hT hS hRepair =>
      profile_real_block_lattice_repair_rigidity F A hA sigma T S hsigma hT hS hRepair⟩

theorem profile_zero_quadratic_allows_selfdual_correction {r c : ℕ} (F : ProfileBlockFamily r c)
    (S : TemperedDistribution ℝ ℂ) (hS : 𝓕 S = S) (φ : 𝓢(ℝ,ℂ)) :
    (∫ x, (profileRealQuadratic F 0 x : ℂ) * (𝓕 φ : 𝓢(ℝ,ℂ)) x) + S (𝓕 φ) =
      (∫ x, (profileRealQuadratic F 0 x : ℂ) * φ x) + S φ := by
  have hs : S (𝓕 φ) = S φ := by
    simpa only [TemperedDistribution.fourier_apply] using congrArg (fun D : TemperedDistribution ℝ ℂ => D φ) hS
  simp only [profileRealQuadratic, Matrix.zero_mulVec, dotProduct_zero, Complex.ofReal_zero,
    zero_mul, integral_zero, zero_add, hs]



end Zeta23.OPICARound2
