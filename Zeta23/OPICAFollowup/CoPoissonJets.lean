import Zeta23.OPICAFollowup.ZeroProfiles
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
Multiplicity-sensitive zero-jet measures (R2-H1). For an actual zero ρ of ζ with 0 < Re ρ < 1 and
multiplicity m = `zeroJetOrder` ρ (the analytic order of ζ at ρ), put κ₀ = ρ(1 - ρ) and let
ρ(κ) = `zeroLocalInverse` ρ κ be the local holomorphic inverse of κ = ρ(1 - ρ) through ρ
(possible because 1 - 2ρ ≠ 0).

- **The κ-family.** On every cell the zero-measure density is the entire κ-family
  g_κ(y) = κ Σ_(1 ≤ k ≤ |y|) (e^(-u_k/2)/k) Sh(1/4 - κ, u_k), with u_k = log(|y|/k) and
  Sh(w, u) = Σ_n wⁿ u^(2n+1)/(2n+1)!. The power series removes the square-root branch. For every
  strip parameter ρ ≠ 1/2 it equals S_ρ(|y|)/b_ρ (`coPoissonComplexDensity_eq_family`).
- **Parameter limits.** The actual construction (CP1.7)/b_ρ is evaluated at an arbitrary parameter
  (`zeroFamilyFunctional`). Along ρ(κ) it is the density pairing plus the boundary term
  (ζ(ρ)/b_ρ) ∫ |x|^(ρ-1) φ, minus the punctured lattice. The parameter κ-derivatives pass under every
  integral (holomorphic parametric integrals with locally uniform bounds). The boundary term
  vanishes through order m - 1, because ζ ∘ ρ(·) has order exactly m at κ₀. Hence for k < m the
  normalized jets (1/k!) ∂_κ^k of the construction are the measures
  ν_k = (1/k!) ∂_κ^k g_κ(|x|) dx - [k = 0] Σ_(n≠0) δ_n (`normalizedZeroMeasureJet`) (H1.1).
- **Tails.** The finite-sum Euler-Maclaurin expansion splits g_κ into 1, the two power terms,
  -κ B₂({x})/(2x²) and an O(x⁻³) remainder, locally uniformly in κ. The power terms carry ζ(ρ) and
  ζ(1 - ρ), so they vanish to order m. Cauchy estimates then give the jet tails
  [k = 0] - ([k = 0] κ₀ + [k = 1]) B₂/(2x²) + O(x⁻³), and so linear variation growth.
- **Self-duality.** The construction is Fourier self-dual at every parameter, so all jets are.
- **Forced chain.** The forced Euler identity of Stage 11 holds at every strip parameter. It is
  reproduced below under `CoPoissonJets`, because this module imports only ZeroProfiles. Its
  κ-jets give the differentiated forced chain (H1.2) for h_k = [k = 0] - (1/k!) ∂_κ^k g_κ:
  (L - κ₀) h₀ = κ₀ G, (L - κ₀) h₁ = h₀ + G and (L - κ₀) h_k = h_(k-1), with
  G = Σ_(n ≥ 1) δ_n - dx and ⟨L h, ψ⟩ = -∫ h (x² ψ')'.
- **Reflection and conjugation.** 1 - ρ has the same multiplicity, the same node κ₀ and the same
  jets, so it is not a separate node. conj ρ has the same multiplicity and conjugate jets.

Only k < m is claimed. Beyond the multiplicity the boundary term enters at order m and the gap is
lost.
-/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology SchwartzMap FourierTransform

namespace Zeta23.OPICAFollowup

section Kernel

/-- The entire kernel Sh(w, u) = Σ_n wⁿ u^(2n+1)/(2n+1)!, so that τ Sh(τ², u) = sinh(τu). -/
def shKernel (w : ℂ) (u : ℝ) : ℂ := ∑' n : ℕ, w ^ n * (u : ℂ) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ)

lemma summable_shKernel (w : ℂ) (u : ℝ) :
    Summable (fun n : ℕ => w ^ n * (u : ℂ) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ)) := by
  refine Summable.of_norm_bounded ((Real.summable_pow_div_factorial (‖w‖ * u ^ 2)).mul_left |u|)
    fun n => ?_
  rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
  have hf : (n.factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have e : |u| ^ (2 * n + 1) = |u| * (u ^ 2) ^ n := by
    rw [pow_succ, pow_mul, sq_abs]; ring
  rw [e, mul_pow, div_le_iff₀ (by exact_mod_cast Nat.factorial_pos _)]
  calc ‖w‖ ^ n * (|u| * (u ^ 2) ^ n) = |u| * (‖w‖ ^ n * (u ^ 2) ^ n) / n.factorial * n.factorial := by
        field_simp
    _ ≤ |u| * (‖w‖ ^ n * (u ^ 2) ^ n) / n.factorial * ((2 * n + 1).factorial : ℝ) := by gcongr
    _ = _ := by ring

/-- τ Sh(τ², u) = sinh(τu). -/
lemma mul_shKernel (τ : ℂ) (u : ℝ) : τ * shKernel (τ ^ 2) u = Complex.sinh (τ * u) := by
  rw [shKernel, ← tsum_mul_left, ← (Complex.hasSum_sinh (τ * u)).tsum_eq]
  refine tsum_congr fun n => ?_
  rw [mul_pow, ← pow_mul, pow_succ τ (2 * n)]
  ring

lemma shKernel_zero (u : ℝ) : shKernel 0 u = u := by
  rw [shKernel, tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  norm_num

/-- For w ≠ 0 and any square root s of w, Sh(w, u) = sinh(su)/s. -/
lemma shKernel_eq_sinh {w s : ℂ} (hs : s ^ 2 = w) (hs0 : s ≠ 0) (u : ℝ) :
    shKernel w u = Complex.sinh (s * u) / s := by
  rw [← mul_shKernel s u, hs]; field_simp

lemma continuous_shKernel (w : ℂ) : Continuous (shKernel w) := by
  by_cases hw : w = 0
  · subst hw
    have : shKernel 0 = fun u : ℝ => (u : ℂ) := funext shKernel_zero
    rw [this]
    exact Complex.continuous_ofReal
  · set s : ℂ := w ^ ((2 : ℕ)⁻¹ : ℂ)
    have hs : s ^ 2 = w := Complex.cpow_nat_inv_pow w two_ne_zero
    have hs0 : s ≠ 0 := by rintro h; rw [h] at hs; exact hw (by rw [← hs]; ring)
    have he : shKernel w = fun u : ℝ => Complex.sinh (s * u) / s := funext (shKernel_eq_sinh hs hs0)
    rw [he]
    exact (Complex.continuous_sinh.comp (continuous_const.mul Complex.continuous_ofReal)).div_const _

/-- The kernel is entire in w. -/
lemma differentiable_shKernel (u : ℝ) : Differentiable ℂ (fun w => shKernel w u) := by
  intro w
  set R : ℝ := ‖w‖ + 1
  have hU : DifferentiableOn ℂ (fun w => shKernel w u) (Metric.ball 0 R) := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ => R ^ n * |u| ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) ?_ (fun n => ?_)
      Metric.isOpen_ball (fun n v hv => ?_)
    · have h := (Real.summable_pow_div_factorial (R * u ^ 2)).mul_left |u|
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
      have hf : (n.factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
      have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      have e : |u| ^ (2 * n + 1) = |u| * (u ^ 2) ^ n := by rw [pow_succ, pow_mul, sq_abs]; ring
      rw [e, mul_pow]
      have hR : 0 ≤ R := by positivity
      calc R ^ n * (|u| * (u ^ 2) ^ n) / ((2 * n + 1).factorial : ℝ)
          ≤ R ^ n * (|u| * (u ^ 2) ^ n) / (n.factorial : ℝ) := by gcongr
        _ = |u| * (R ^ n * (u ^ 2) ^ n / n.factorial) := by ring
    · exact ((differentiable_id.pow n).mul_const _).div_const _ |>.differentiableOn
    · rw [mem_ball_zero_iff] at hv
      rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_natCast]
      gcongr
  exact hU.differentiableAt (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by
    show ‖w‖ < ‖w‖ + 1; linarith)))

lemma real_cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith [Real.exp_le_exp.mpr (by linarith : -x ≤ x)]
  · rw [abs_of_nonpos hx]; linarith [Real.exp_le_exp.mpr (by linarith : x ≤ -x)]

/-- The crude growth bound ‖Sh(w, u)‖ ≤ |u| exp(√‖w‖ |u|). -/
lemma norm_shKernel_le (w : ℂ) (u : ℝ) :
    ‖shKernel w u‖ ≤ |u| * Real.exp (Real.sqrt ‖w‖ * |u|) := by
  set a := Real.sqrt ‖w‖ * |u|
  have hS := summable_shKernel w u
  have hterm : ∀ n : ℕ, ‖w ^ n * (u : ℂ) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ)‖ ≤
      |u| * (a ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
    intro n
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast]
    have hf : ((2 * n).factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
    have hpos : (0 : ℝ) < (2 * n).factorial := by exact_mod_cast Nat.factorial_pos _
    have ha : a ^ (2 * n) = ‖w‖ ^ n * |u| ^ (2 * n) := by
      rw [mul_pow, pow_mul, Real.sq_sqrt (norm_nonneg w)]
    rw [ha, pow_succ]
    calc ‖w‖ ^ n * (|u| ^ (2 * n) * |u|) / ((2 * n + 1).factorial : ℝ)
        ≤ ‖w‖ ^ n * (|u| ^ (2 * n) * |u|) / ((2 * n).factorial : ℝ) := by gcongr
      _ = |u| * (‖w‖ ^ n * |u| ^ (2 * n) / ((2 * n).factorial : ℝ)) := by ring
  have hcosh := (Real.hasSum_cosh a).mul_left |u|
  calc ‖shKernel w u‖ ≤ ∑' n : ℕ, ‖w ^ n * (u : ℂ) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ)‖ :=
        norm_tsum_le_tsum_norm hS.norm
    _ ≤ |u| * Real.cosh a := hasSum_le hterm hS.norm.hasSum hcosh
    _ ≤ |u| * Real.exp |a| := by gcongr; exact real_cosh_le_exp_abs a
    _ = |u| * Real.exp a := by rw [abs_of_nonneg (show 0 ≤ a by positivity)]


end Kernel

section Family

variable {ρ : ℂ}

lemma ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (s : ℂ) : (x : ℂ) ^ s = Complex.exp (Real.log x * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]

/-- One term of the finite sums: y^(-ρ) k^(ρ-1) - y^(ρ-1) k^(-ρ) = -(2/k) e^(-u/2) sinh((ρ - 1/2) u)
with u = log(y/k). -/
lemma cpow_term_eq_sinh (ρ : ℂ) {y k : ℝ} (hy : 0 < y) (hk : 0 < k) :
    (y : ℂ) ^ (-ρ) * (k : ℂ) ^ (ρ - 1) - (y : ℂ) ^ (ρ - 1) * (k : ℂ) ^ (-ρ) =
      -(2 / (k : ℂ)) * (Real.exp (-Real.log (y / k) / 2) : ℂ) *
        Complex.sinh ((ρ - 1 / 2) * (Real.log (y / k) : ℂ)) := by
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  rw [ofReal_cpow_eq_exp hy, ofReal_cpow_eq_exp hk, ofReal_cpow_eq_exp hy, ofReal_cpow_eq_exp hk,
    Real.log_div hy.ne' hk.ne', Complex.sinh, Complex.ofReal_exp]
  have hk' : (k : ℂ) = Complex.exp (Real.log k) := by
    rw [← Complex.ofReal_exp, Real.exp_log hk]
  rw [hk']
  push_cast
  rw [← Complex.exp_add, ← Complex.exp_add]
  field_simp
  simp only [sub_mul, mul_sub, ← Complex.exp_add, neg_sub]
  congr 1 <;> congr 1 <;> ring


/-- The κ-family density: g_κ(y) = κ Σ_{1 ≤ k ≤ |y|} (e^(-u_k/2)/k) Sh(1/4 - κ, u_k), u_k = log(|y|/k).
It is entire in κ for every y, has no square-root branch, and is invariant under ρ ↦ 1 - ρ. -/
def zeroFamilyDensity (κ : ℂ) (y : ℝ) : ℂ :=
  κ * ∑ k ∈ Finset.Icc 1 ⌊|y|⌋₊, ((Real.exp (-Real.log (|y| / k) / 2) / k : ℝ) : ℂ) *
    shKernel (1 / 4 - κ) (Real.log (|y| / k))

/-- For every strip parameter ρ ≠ 1/2 the zero-measure density is the κ-family at κ = ρ(1 - ρ). -/
theorem coPoissonComplexDensity_eq_family (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (hh : ρ ≠ 1 / 2) (y : ℝ) :
    coPoissonComplexDensity ρ y = zeroFamilyDensity (spectralKappa ρ) y := by
  have hτ : ρ - 1 / 2 ≠ 0 := sub_ne_zero.mpr hh
  have h1' : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hb : coPoissonOriginNormalizer ρ = -2 * (ρ - 1 / 2) / spectralKappa ρ := by
    rw [coPoissonOriginNormalizer, spectralKappa]; field_simp; ring
  have hsq : (1 : ℂ) / 4 - spectralKappa ρ = (ρ - 1 / 2) ^ 2 := by rw [spectralKappa]; ring
  rcases lt_or_ge |y| 1 with hy | hy
  · rw [coPoissonComplexDensity_small ρ hy, zeroFamilyDensity, Nat.floor_eq_zero.mpr hy]
    simp
  have hy0 : 0 < |y| := by linarith
  rw [coPoissonComplexDensity, coPoissonPowerSums, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    zeroFamilyDensity, hsq, Finset.mul_sum, hb, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (0 : ℝ) < k := by
    have := (Finset.mem_Icc.mp hk).1; exact_mod_cast this
  have hterm := cpow_term_eq_sinh ρ hy0 hk0
  rw [Complex.ofReal_natCast] at hterm
  rw [hterm, ← mul_shKernel (ρ - 1 / 2) (Real.log (|y| / k))]
  have hκ : spectralKappa ρ ≠ 0 := mul_ne_zero h0 h1'
  have hkn : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  push_cast
  generalize shKernel ((ρ - 1 / 2) ^ 2) (Real.log (|y| / k)) = X
  generalize ((Real.exp (-Real.log (|y| / k) / 2) : ℝ) : ℂ) = E
  generalize ρ - 1 / 2 = τ at hτ ⊢
  generalize spectralKappa ρ = κ at hκ ⊢
  field_simp

lemma zeroFamilyDensity_small (κ : ℂ) {y : ℝ} (hy : |y| < 1) : zeroFamilyDensity κ y = 0 := by
  rw [zeroFamilyDensity, Nat.floor_eq_zero.mpr hy]; simp

lemma zeroFamilyDensity_neg (κ : ℂ) (y : ℝ) : zeroFamilyDensity κ (-y) = zeroFamilyDensity κ y := by
  simp [zeroFamilyDensity]

lemma measurable_zeroFamilyDensity (κ : ℂ) : Measurable (zeroFamilyDensity κ) := by
  have hF : Measurable (fun p : ℝ × ℕ => κ * ∑ k ∈ Finset.Icc 1 p.2,
      ((Real.exp (-Real.log (|p.1| / k) / 2) / k : ℝ) : ℂ) *
        shKernel (1 / 4 - κ) (Real.log (|p.1| / k))) := by
    refine measurable_from_prod_countable_left (fun n => ?_)
    dsimp only
    refine measurable_const.mul (Finset.measurable_sum _ (fun k _ => ?_))
    have hl : Measurable (fun y : ℝ => Real.log (|y| / k)) :=
      Real.measurable_log.comp (continuous_abs.measurable.div_const _)
    exact (Complex.measurable_ofReal.comp ((Real.measurable_exp.comp (hl.neg.div_const _)).div_const _)).mul
      ((continuous_shKernel _).measurable.comp hl)
  have hg : Measurable (fun y : ℝ => (y, ⌊|y|⌋₊)) :=
    measurable_id.prodMk (Nat.measurable_floor.comp continuous_abs.measurable)
  have h := hF.comp hg
  unfold zeroFamilyDensity
  exact h

lemma differentiable_zeroFamilyDensity (y : ℝ) : Differentiable ℂ (fun κ => zeroFamilyDensity κ y) := by
  unfold zeroFamilyDensity
  refine differentiable_id.mul (Differentiable.fun_sum fun k _ => (differentiable_const _).mul ?_)
  exact (differentiable_shKernel _).comp ((differentiable_const _).sub differentiable_id)

/-- Polynomial growth, uniform on bounded parameter sets: ‖g_κ(y)‖ ≤ ‖κ‖ (1 + |y|)^(2 + ⌈√‖1/4 - κ‖⌉). -/
lemma norm_zeroFamilyDensity_le (κ : ℂ) (y : ℝ) :
    ‖zeroFamilyDensity κ y‖ ≤ ‖κ‖ * (1 + |y|) ^ (2 + ⌈Real.sqrt ‖1 / 4 - κ‖⌉₊) := by
  set s := Real.sqrt ‖1 / 4 - κ‖
  rcases lt_or_ge |y| 1 with hy | hy
  · rw [zeroFamilyDensity_small κ hy, norm_zero]; positivity
  have hy0 : 0 < |y| := by linarith
  have hterm : ∀ k ∈ Finset.Icc 1 ⌊|y|⌋₊, ‖((Real.exp (-Real.log (|y| / k) / 2) / k : ℝ) : ℂ) *
      shKernel (1 / 4 - κ) (Real.log (|y| / k))‖ ≤ |y| * |y| ^ s := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hky : (k : ℝ) ≤ |y| := (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2).trans (Nat.floor_le hy0.le)
    have hk0 : (0 : ℝ) < k := by linarith
    have hu0 : 0 ≤ Real.log (|y| / k) := Real.log_nonneg (by rw [le_div_iff₀ hk0]; linarith)
    have hu1 : Real.log (|y| / k) ≤ Real.log |y| :=
      Real.log_le_log (div_pos hy0 hk0) (div_le_self hy0.le hk1)
    have hly : Real.log |y| ≤ |y| := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hc : |Real.exp (-Real.log (|y| / k) / 2) / k| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one hk0]
      calc Real.exp (-Real.log (|y| / k) / 2) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
        _ ≤ k := hk1
    have hS := norm_shKernel_le (1 / 4 - κ) (Real.log (|y| / k))
    rw [abs_of_nonneg hu0] at hS
    have hE : Real.exp (s * Real.log (|y| / k)) ≤ |y| ^ s := by
      rw [Real.rpow_def_of_pos hy0, mul_comm (Real.log |y|)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu1 (Real.sqrt_nonneg _))
    calc |Real.exp (-Real.log (|y| / k) / 2) / k| * ‖shKernel (1 / 4 - κ) (Real.log (|y| / k))‖
        ≤ 1 * (Real.log (|y| / k) * Real.exp (s * Real.log (|y| / k))) :=
          mul_le_mul hc hS (norm_nonneg _) zero_le_one
      _ ≤ |y| * |y| ^ s := by
          rw [one_mul]
          exact mul_le_mul (hu1.trans hly) hE (Real.exp_pos _).le hy0.le
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hsum
  have hfl : (⌊|y|⌋₊ : ℝ) ≤ |y| := Nat.floor_le hy0.le
  have h1y : (1 : ℝ) ≤ 1 + |y| := by linarith
  have hpow : |y| * (|y| * |y| ^ s) ≤ (1 + |y|) ^ (2 + ⌈s⌉₊) := by
    have e : |y| * (|y| * |y| ^ s) = |y| ^ ((2 : ℝ) + s) := by
      rw [Real.rpow_add hy0, Real.rpow_two]; ring
    rw [e]
    calc |y| ^ ((2 : ℝ) + s) ≤ (1 + |y|) ^ ((2 : ℝ) + s) :=
          Real.rpow_le_rpow hy0.le (by linarith) (by positivity)
      _ ≤ (1 + |y|) ^ ((2 + ⌈s⌉₊ : ℕ) : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le h1y ?_
          push_cast; linarith [Nat.le_ceil s]
      _ = (1 + |y|) ^ (2 + ⌈s⌉₊) := Real.rpow_natCast _ _
  rw [zeroFamilyDensity, norm_mul]
  refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (norm_nonneg _)
  calc (⌊|y|⌋₊ : ℝ) * (|y| * |y| ^ s) ≤ |y| * (|y| * |y| ^ s) :=
        mul_le_mul_of_nonneg_right hfl (by positivity)
    _ ≤ _ := hpow

/-- The uniform version on ‖κ‖ ≤ R. -/
lemma norm_zeroFamilyDensity_le_of_norm_le {κ : ℂ} {R : ℝ} (hκ : ‖κ‖ ≤ R) (y : ℝ) :
    ‖zeroFamilyDensity κ y‖ ≤ R * (1 + |y|) ^ (3 + ⌈R⌉₊) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hκ
  have hs : Real.sqrt ‖1 / 4 - κ‖ ≤ 1 + R := by
    rw [Real.sqrt_le_left (by positivity)]
    have : ‖1 / 4 - κ‖ ≤ 1 / 4 + R := (norm_sub_le _ _).trans (by norm_num; linarith)
    nlinarith
  have hc : 2 + ⌈Real.sqrt ‖1 / 4 - κ‖⌉₊ ≤ 3 + ⌈R⌉₊ := by
    have := Nat.ceil_le_ceil hs
    have h2 : ⌈1 + R⌉₊ ≤ 1 + ⌈R⌉₊ := by
      rw [Nat.ceil_le]; push_cast; linarith [Nat.le_ceil R]
    omega
  refine (norm_zeroFamilyDensity_le κ y).trans ?_
  exact mul_le_mul hκ (pow_le_pow_right₀ (by linarith [abs_nonneg y]) hc) (by positivity) hR


end Family

section Parametric

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Cauchy's estimate on the unit circle around z for an entire function. -/
lemma norm_iteratedDeriv_le_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) (z : ℂ) {C : ℝ}
    (hC : ∀ w : ℂ, ‖w‖ ≤ ‖z‖ + 1 → ‖f w‖ ≤ C) : ‖iteratedDeriv n f z‖ ≤ n.factorial * C := by
  have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n one_pos hf.diffContOnCl
    (c := z) (C := C) (fun w hw => hC w (by
      rw [mem_sphere_iff_norm] at hw
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ = ‖z‖ + 1 := by rw [hw]))
  simpa using h

lemma differentiable_iteratedDeriv_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n f) :=
  (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)

/-- The derivative in the parameter of a measurable entire family is measurable. -/
lemma measurable_deriv_param' {F : ℂ → α → ℂ} {z : ℂ} (hd : ∀ x, DifferentiableAt ℂ (fun w => F w x) z)
    (hm : ∀ z, Measurable (F z)) : Measurable (fun x => deriv (fun w => F w x) z) := by
  have ht : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      simp only [Complex.ofReal_zero] at h
      refine h.congr fun n => ?_
      simp
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, one_div, inv_eq_zero]
      exact_mod_cast Nat.succ_ne_zero n
  have hlim : ∀ x, Tendsto (fun n : ℕ => ((1 : ℂ) / ((n : ℂ) + 1))⁻¹ •
      (F (z + 1 / ((n : ℂ) + 1)) x - F z x)) atTop (𝓝 (deriv (fun w => F w x) z)) := fun x =>
    (hasDerivAt_iff_tendsto_slope_zero.mp (hd x).hasDerivAt).comp ht
  exact measurable_of_tendsto_metrizable (f := fun (n : ℕ) (x : α) => ((1 : ℂ) / ((n : ℂ) + 1))⁻¹ •
      (F (z + 1 / ((n : ℂ) + 1)) x - F z x))
    (fun n => by
      have h := ((hm (z + 1 / ((n : ℂ) + 1))).sub (hm z)).const_smul ((1 : ℂ) / ((n : ℂ) + 1))⁻¹
      exact h) (tendsto_pi_nhds.mpr hlim)

lemma measurable_deriv_param {F : ℂ → α → ℂ} (hd : ∀ x, Differentiable ℂ (fun z => F z x))
    (hm : ∀ z, Measurable (F z)) (z : ℂ) : Measurable (fun x => deriv (fun w => F w x) z) :=
  measurable_deriv_param' (fun x => hd x z) hm

lemma measurable_iteratedDeriv_param {F : ℂ → α → ℂ} (hd : ∀ x, Differentiable ℂ (fun z => F z x))
    (hm : ∀ z, Measurable (F z)) (n : ℕ) (z : ℂ) :
    Measurable (fun x => iteratedDeriv n (fun w => F w x) z) := by
  induction n generalizing z with
  | zero => simpa using hm z
  | succ n ih =>
    simp only [iteratedDeriv_succ]
    exact measurable_deriv_param (F := fun w x => iteratedDeriv n (fun w => F w x) w)
      (fun x => differentiable_iteratedDeriv_of_entire (hd x) n) ih z

/-- Parametric integrals of entire families with locally uniform integrable bounds: the derivative
is the integral of the derivative. -/
lemma hasDerivAt_integral_entire {F : ℂ → α → ℂ} (hd : ∀ x, Differentiable ℂ (fun z => F z x))
    (hm : ∀ z, Measurable (F z))
    (hb : ∀ R : ℝ, ∃ B : α → ℝ, Integrable B μ ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ x, ‖F z x‖ ≤ B x) (z : ℂ) :
    HasDerivAt (fun w => ∫ x, F w x ∂μ) (∫ x, deriv (fun w => F w x) z ∂μ) z := by
  obtain ⟨B, hBi, hB⟩ := hb (‖z‖ + 2)
  have hF'b : ∀ x, ∀ w ∈ Metric.ball z 1, ‖deriv (fun w => F w x) w‖ ≤ B x := by
    intro x w hw
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + 1 := by linarith
    have h := norm_iteratedDeriv_le_of_entire (hd x) 1 w (C := B x) (fun v hv => hB v (by linarith) x)
    simpa using h
  have hint : Integrable (F z) μ :=
    hBi.mono' (hm z).aestronglyMeasurable (Eventually.of_forall fun x => hB z (by linarith [norm_nonneg z]) x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z one_pos)
    (Eventually.of_forall fun w => (hm w).aestronglyMeasurable) hint
    (measurable_deriv_param hd hm z).aestronglyMeasurable (Eventually.of_forall hF'b) hBi
    (Eventually.of_forall fun x w _ => ((hd x) w).hasDerivAt)).2

/-- All parameter derivatives commute with the integral. -/
theorem iteratedDeriv_integral_entire {F : ℂ → α → ℂ} (hd : ∀ x, Differentiable ℂ (fun z => F z x))
    (hm : ∀ z, Measurable (F z))
    (hb : ∀ R : ℝ, ∃ B : α → ℝ, Integrable B μ ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ x, ‖F z x‖ ≤ B x) (n : ℕ) :
    iteratedDeriv n (fun w => ∫ x, F w x ∂μ) = fun z => ∫ x, iteratedDeriv n (fun w => F w x) z ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdn : ∀ x, Differentiable ℂ (fun z => iteratedDeriv n (fun w => F w x) z) := fun x =>
      differentiable_iteratedDeriv_of_entire (hd x) n
    have hmn : ∀ z, Measurable (fun x => iteratedDeriv n (fun w => F w x) z) :=
      measurable_iteratedDeriv_param hd hm n
    have hbn : ∀ R : ℝ, ∃ B : α → ℝ, Integrable B μ ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ x,
        ‖iteratedDeriv n (fun w => F w x) z‖ ≤ B x := by
      intro R
      obtain ⟨B, hBi, hB⟩ := hb (R + 1)
      refine ⟨fun x => n.factorial * B x, hBi.const_mul _, fun z hz x => ?_⟩
      exact norm_iteratedDeriv_le_of_entire (hd x) n z (fun w hw => hB w (by linarith) x)
    funext z
    rw [iteratedDeriv_succ, ih]
    have h := hasDerivAt_integral_entire (μ := μ) hdn hmn hbn z
    rw [h.deriv]
    congr 1
    funext x
    rw [iteratedDeriv_succ]

lemma integrable_of_entire_bound {F : ℂ → α → ℂ} (hm : ∀ z, Measurable (F z))
    (hb : ∀ R : ℝ, ∃ B : α → ℝ, Integrable B μ ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ x, ‖F z x‖ ≤ B x) (z : ℂ) :
    Integrable (F z) μ := by
  obtain ⟨B, hBi, hB⟩ := hb ‖z‖
  exact hBi.mono' (hm z).aestronglyMeasurable (Eventually.of_forall fun x => hB z le_rfl x)

lemma differentiable_integral_entire {F : ℂ → α → ℂ} (hd : ∀ x, Differentiable ℂ (fun z => F z x))
    (hm : ∀ z, Measurable (F z))
    (hb : ∀ R : ℝ, ∃ B : α → ℝ, Integrable B μ ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ x, ‖F z x‖ ≤ B x) :
    Differentiable ℂ (fun w => ∫ x, F w x ∂μ) := fun z =>
  (hasDerivAt_integral_entire hd hm hb z).differentiableAt

/-- Local version: holomorphy on a closed disc with one integrable bound. -/
lemma hasDerivAt_integral_of_closedBall {F : ℂ → α → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ∀ x, DifferentiableOn ℂ (fun w => F w x) (Metric.closedBall z r))
    (hm : ∀ w, Measurable (F w)) {B : α → ℝ} (hBi : Integrable B μ)
    (hB : ∀ w ∈ Metric.closedBall z r, ∀ x, ‖F w x‖ ≤ B x) :
    HasDerivAt (fun w => ∫ x, F w x ∂μ) (∫ x, deriv (fun w => F w x) z ∂μ) z := by
  have hr2 : 0 < r / 2 := by linarith
  have hdat : ∀ x, ∀ w ∈ Metric.ball z r, DifferentiableAt ℂ (fun w => F w x) w := fun x w hw =>
    (hd x).differentiableAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hw)
      Metric.ball_subset_closedBall)
  have hF'b : ∀ x, ∀ w ∈ Metric.ball z (r / 2), ‖deriv (fun w => F w x) w‖ ≤ B x / (r / 2) := by
    intro x w hw
    have hsub : Metric.closedBall w (r / 2) ⊆ Metric.closedBall z r := by
      intro v hv
      rw [Metric.mem_closedBall] at hv ⊢
      rw [Metric.mem_ball] at hw
      linarith [dist_triangle v w z]
    have hdc : DiffContOnCl ℂ (fun w => F w x) (Metric.ball w (r / 2)) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball w hr2.ne']
      exact (hd x).mono hsub
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr2 hdc (fun v hv =>
      hB v (hsub (Metric.sphere_subset_closedBall hv)) x)
  have hint : Integrable (F z) μ :=
    hBi.mono' (hm z).aestronglyMeasurable (Eventually.of_forall fun x =>
      hB z (Metric.mem_closedBall_self hr.le) x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z hr2)
    (Eventually.of_forall fun w => (hm w).aestronglyMeasurable) hint
    (measurable_deriv_param' (fun x => hdat x z (Metric.mem_ball_self hr)) hm).aestronglyMeasurable
    (Eventually.of_forall hF'b) (hBi.div_const _)
    (Eventually.of_forall fun x w hw => (hdat x w (Metric.ball_subset_ball (by linarith) hw)).hasDerivAt)).2

end Parametric

section LocalInverse

/-- The radicand 1 + (κ₀ - κ)/(ρ₀ - 1/2)² of the local inverse branch. -/
def localRadicand (ρ₀ κ : ℂ) : ℂ := 1 + (spectralKappa ρ₀ - κ) / (ρ₀ - 1 / 2) ^ 2

/-- The local holomorphic inverse ρ(κ) of κ = ρ(1 - ρ) through ρ₀ ≠ 1/2:
ρ(κ) = 1/2 + (ρ₀ - 1/2) w^(1/2), w = 1 + (κ₀ - κ)/(ρ₀ - 1/2)², principal branch. -/
def zeroLocalInverse (ρ₀ κ : ℂ) : ℂ := 1 / 2 + (ρ₀ - 1 / 2) * localRadicand ρ₀ κ ^ ((2 : ℕ)⁻¹ : ℂ)

lemma localRadicand_center (ρ₀ : ℂ) : localRadicand ρ₀ (spectralKappa ρ₀) = 1 := by
  simp [localRadicand]

lemma zeroLocalInverse_center (ρ₀ : ℂ) : zeroLocalInverse ρ₀ (spectralKappa ρ₀) = ρ₀ := by
  simp [zeroLocalInverse, localRadicand_center]

lemma spectralKappa_eq_quarter_sub (ρ : ℂ) : spectralKappa ρ = 1 / 4 - (ρ - 1 / 2) ^ 2 := by
  unfold spectralKappa; ring

/-- ρ(κ)(1 - ρ(κ)) = κ for every κ. -/
lemma spectralKappa_zeroLocalInverse {ρ₀ : ℂ} (hh : ρ₀ ≠ 1 / 2) (κ : ℂ) :
    spectralKappa (zeroLocalInverse ρ₀ κ) = κ := by
  have hτ : (ρ₀ - 1 / 2) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hh)
  have hw : (localRadicand ρ₀ κ ^ ((2 : ℕ)⁻¹ : ℂ)) ^ 2 = localRadicand ρ₀ κ :=
    Complex.cpow_nat_inv_pow _ two_ne_zero
  rw [spectralKappa_eq_quarter_sub, zeroLocalInverse, add_sub_cancel_left, mul_pow, hw,
    localRadicand, mul_add, mul_div_cancel₀ _ hτ, spectralKappa_eq_quarter_sub]
  ring

lemma localRadicand_mem_slitPlane {ρ₀ κ : ℂ} (hh : ρ₀ ≠ 1 / 2)
    (hκ : ‖κ - spectralKappa ρ₀‖ < ‖ρ₀ - 1 / 2‖ ^ 2) : localRadicand ρ₀ κ ∈ Complex.slitPlane := by
  have hτ : 0 < ‖ρ₀ - 1 / 2‖ ^ 2 := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hh); positivity
  have hlt : ‖(spectralKappa ρ₀ - κ) / (ρ₀ - 1 / 2) ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, div_lt_one hτ, norm_sub_rev]; exact hκ
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  have hre := Complex.abs_re_le_norm ((spectralKappa ρ₀ - κ) / (ρ₀ - 1 / 2) ^ 2)
  rw [localRadicand, Complex.add_re, Complex.one_re]
  linarith [neg_abs_le ((spectralKappa ρ₀ - κ) / (ρ₀ - 1 / 2) ^ 2).re]

/-- The radius ‖ρ₀ - 1/2‖² of the disc on which the branch is holomorphic. -/
def localInverseRadius (ρ₀ : ℂ) : ℝ := ‖ρ₀ - 1 / 2‖ ^ 2

lemma hasDerivAt_zeroLocalInverse {ρ₀ κ : ℂ} (hh : ρ₀ ≠ 1 / 2)
    (hκ : ‖κ - spectralKappa ρ₀‖ < localInverseRadius ρ₀) :
    HasDerivAt (zeroLocalInverse ρ₀)
      ((ρ₀ - 1 / 2) * (((2 : ℕ)⁻¹ : ℂ) * localRadicand ρ₀ κ ^ (((2 : ℕ)⁻¹ : ℂ) - 1) *
        (-1 / (ρ₀ - 1 / 2) ^ 2))) κ := by
  have hw : HasDerivAt (localRadicand ρ₀) (-1 / (ρ₀ - 1 / 2) ^ 2) κ := by
    have h := (((hasDerivAt_id κ).const_sub (spectralKappa ρ₀)).div_const ((ρ₀ - 1 / 2) ^ 2)).const_add 1
    exact h
  have hc := (Complex.hasStrictDerivAt_cpow_const (c := ((2 : ℕ)⁻¹ : ℂ))
    (localRadicand_mem_slitPlane hh hκ)).hasDerivAt.comp κ hw
  exact (hc.const_mul (ρ₀ - 1 / 2)).const_add (1 / 2)

lemma differentiableOn_zeroLocalInverse {ρ₀ : ℂ} (hh : ρ₀ ≠ 1 / 2) :
    DifferentiableOn ℂ (zeroLocalInverse ρ₀) (Metric.ball (spectralKappa ρ₀) (localInverseRadius ρ₀)) :=
  fun κ hκ => (hasDerivAt_zeroLocalInverse hh (by rwa [Metric.mem_ball, dist_eq_norm] at hκ)).differentiableAt
    |>.differentiableWithinAt

lemma localInverseRadius_pos {ρ₀ : ℂ} (hh : ρ₀ ≠ 1 / 2) : 0 < localInverseRadius ρ₀ := by
  have := norm_pos_iff.mpr (sub_ne_zero.mpr hh); unfold localInverseRadius; positivity

lemma analyticAt_zeroLocalInverse {ρ₀ : ℂ} (hh : ρ₀ ≠ 1 / 2) :
    AnalyticAt ℂ (zeroLocalInverse ρ₀) (spectralKappa ρ₀) :=
  (differentiableOn_zeroLocalInverse hh).analyticAt
    (Metric.ball_mem_nhds _ (localInverseRadius_pos hh))

/-- The branch derivative at the center: dρ/dκ = -1/(2ρ₀ - 1) ≠ 0. -/
lemma deriv_zeroLocalInverse_center {ρ₀ : ℂ} (hh : ρ₀ ≠ 1 / 2) :
    deriv (zeroLocalInverse ρ₀) (spectralKappa ρ₀) = -1 / (2 * (ρ₀ - 1 / 2)) := by
  have hτ : ρ₀ - 1 / 2 ≠ 0 := sub_ne_zero.mpr hh
  rw [(hasDerivAt_zeroLocalInverse hh (by simpa using localInverseRadius_pos hh)).deriv,
    localRadicand_center, Complex.one_cpow]
  field_simp
  push_cast
  ring

lemma deriv_zeroLocalInverse_center_ne_zero {ρ₀ : ℂ} (hh : ρ₀ ≠ 1 / 2) :
    deriv (zeroLocalInverse ρ₀) (spectralKappa ρ₀) ≠ 0 := by
  rw [deriv_zeroLocalInverse_center hh]
  exact div_ne_zero (by norm_num) (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hh))

lemma zeroLocalInverse_ne_half {ρ₀ κ : ℂ} (hh : ρ₀ ≠ 1 / 2)
    (hκ : ‖κ - spectralKappa ρ₀‖ < localInverseRadius ρ₀) : zeroLocalInverse ρ₀ κ ≠ 1 / 2 := by
  intro h
  have hw0 : localRadicand ρ₀ κ ≠ 0 := Complex.slitPlane_ne_zero (localRadicand_mem_slitPlane hh hκ)
  have : (ρ₀ - 1 / 2) * localRadicand ρ₀ κ ^ ((2 : ℕ)⁻¹ : ℂ) = 0 := by
    rw [zeroLocalInverse] at h; linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hh (sub_eq_zero.mp h1)
  · exact hw0 ((Complex.cpow_eq_zero_iff _ _).mp h1).1

/-- The open parameter domain: the holomorphy disc intersected with the strip condition. -/
def localJetDomain (ρ₀ : ℂ) : Set ℂ :=
  Metric.ball (spectralKappa ρ₀) (localInverseRadius ρ₀) ∩
    {κ | 0 < (zeroLocalInverse ρ₀ κ).re ∧ (zeroLocalInverse ρ₀ κ).re < 1}

lemma isOpen_localJetDomain {ρ₀ : ℂ} (hh : ρ₀ ≠ 1 / 2) : IsOpen (localJetDomain ρ₀) := by
  have hc := (differentiableOn_zeroLocalInverse hh).continuousOn
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  exact hc.isOpen_inter_preimage Metric.isOpen_ball hU

lemma center_mem_localJetDomain {ρ₀ : ℂ} (hh : ρ₀ ≠ 1 / 2) (h0 : 0 < ρ₀.re) (h1 : ρ₀.re < 1) :
    spectralKappa ρ₀ ∈ localJetDomain ρ₀ :=
  ⟨Metric.mem_ball_self (localInverseRadius_pos hh), by rw [Set.mem_ofPred_eq, zeroLocalInverse_center]; exact ⟨h0, h1⟩⟩

end LocalInverse

section Order

/-- The actual zero multiplicity: the analytic order of ζ at ρ. -/
def zeroJetOrder (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

lemma analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := {1}ᶜ)
    (fun _ hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

lemma riemannZeta_analyticOrderAt_ne_top {s : ℂ} (hs : s ≠ 1) : analyticOrderAt riemannZeta s ≠ ⊤ := by
  have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  have h2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [(analyticAt_riemannZeta_of_ne_one (by norm_num)).analyticOrderAt_eq_zero.mpr]
    · exact ENat.zero_ne_top
    · rw [riemannZeta_two]; exact div_ne_zero (pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)) (by norm_num)
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (fun z hz => analyticAt_riemannZeta_of_ne_one hz) hU
    (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num) hs h2

lemma analyticOrderAt_riemannZeta_eq {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s = zeroJetOrder s :=
  (Nat.cast_analyticOrderNatAt (riemannZeta_analyticOrderAt_ne_top hs)).symm

lemma one_le_zeroJetOrder {ρ : ℂ} (hz : riemannZeta ρ = 0) (h1 : ρ ≠ 1) : 1 ≤ zeroJetOrder ρ := by
  have hne : analyticOrderAt riemannZeta ρ ≠ 0 :=
    (analyticAt_riemannZeta_of_ne_one h1).analyticOrderAt_ne_zero.mpr hz
  rw [analyticOrderAt_riemannZeta_eq h1] at hne
  exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)

/-- Vanishing of low derivatives of a product with a factor of order ≥ m. -/
lemma iteratedDeriv_mul_eq_zero_of_lt {f g : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hg : AnalyticAt ℂ g z₀) {m : ℕ} (hm : (m : ℕ∞) ≤ analyticOrderAt f z₀) {k : ℕ} (hk : k < m) :
    iteratedDeriv k (fun z => f z * g z) z₀ = 0 := by
  have hmul : analyticOrderAt (f * g) z₀ = analyticOrderAt f z₀ + analyticOrderAt g z₀ :=
    analyticOrderAt_mul hf hg
  have hle : (m : ℕ∞) ≤ analyticOrderAt (f * g) z₀ := by rw [hmul]; exact hm.trans le_self_add
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.mul hg)).mp hle k hk

/-- ζ ∘ ρ(·) has order m at κ₀. -/
lemma analyticOrderAt_riemannZeta_comp_inverse {ρ₀ : ℂ} (hh : ρ₀ ≠ 1 / 2) (h1 : ρ₀ ≠ 1) :
    analyticOrderAt (fun κ => riemannZeta (zeroLocalInverse ρ₀ κ)) (spectralKappa ρ₀) =
      zeroJetOrder ρ₀ := by
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) (analyticAt_zeroLocalInverse hh)
    (deriv_zeroLocalInverse_center_ne_zero hh)
  rw [zeroLocalInverse_center] at h
  rw [← analyticOrderAt_riemannZeta_eq h1, ← h]
  rfl

/-- The functional-equation factor ζ(1 - s) = E(s) ζ(s). -/
def zetaFunctionalFactor (s : ℂ) : ℂ := 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)

lemma zetaFunctionalFactor_eq {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta (1 - s) = zetaFunctionalFactor s * riemannZeta s := by
  have hs : ∀ n : ℕ, s ≠ -n := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [riemannZeta_one_sub hs h1, zetaFunctionalFactor]

lemma analyticAt_zetaFunctionalFactor {s : ℂ} (h0 : 0 < s.re) : AnalyticAt ℂ zetaFunctionalFactor s := by
  have hs : ∀ n : ℕ, s ≠ -n := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re}) (fun z hz => ?_) (hU.mem_nhds h0)
  have hz : ∀ n : ℕ, z ≠ -n := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), hz.out]
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold zetaFunctionalFactor
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  exact ((((differentiableAt_const _).mul ((differentiableAt_id.neg).const_cpow (Or.inl hpi))).mul
    (Complex.differentiableAt_Gamma _ hz)).mul
    (Complex.differentiable_cos.differentiableAt.comp _ ((differentiableAt_id.const_mul _).div_const _)))

lemma zetaFunctionalFactor_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    zetaFunctionalFactor s ≠ 0 := by
  have hs : ∀ n : ℕ, s ≠ -n := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    rw [Ne, Complex.cos_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hpi' : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hs' : s = 2 * k + 1 := by
      apply mul_left_cancel₀ hpi'
      linear_combination 2 * hk
    have hre : s.re = 2 * k + 1 := by rw [hs']; simp
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk0
      linarith
    · rw [hk0] at hre; norm_num at hre; linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      linarith
  unfold zetaFunctionalFactor
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff_of_exponent_ne_zero
    (neg_ne_zero.mpr (fun h => by simp [h] at h0)) |>.mpr hpi)) (Complex.Gamma_ne_zero hs)) hcos

/-- Reflection preserves the multiplicity: m(1 - ρ) = m(ρ). -/
lemma zeroJetOrder_one_sub {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    zeroJetOrder (1 - ρ) = zeroJetOrder ρ := by
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  have hρ0 : 1 - ρ ≠ 1 := fun h => by
    have : ρ = 0 := by linear_combination -h
    simp [this] at h0
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) (z₀ := ρ)
    (g := fun s => 1 - s) ((analyticAt_const).sub analyticAt_id) (by
      have := ((hasDerivAt_id' ρ).const_sub (1 : ℂ)).deriv; rw [this]; norm_num)
  have heq : (riemannZeta ∘ fun s => 1 - s) =ᶠ[𝓝 ρ] fun s => zetaFunctionalFactor s * riemannZeta s := by
    have hU : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
    filter_upwards [hU.mem_nhds ⟨h0, hρ1⟩] with s hs
    exact zetaFunctionalFactor_eq hs.1 hs.2
  have hmul : analyticOrderAt (fun s => zetaFunctionalFactor s * riemannZeta s) ρ =
      analyticOrderAt zetaFunctionalFactor ρ + analyticOrderAt riemannZeta ρ :=
    analyticOrderAt_mul (analyticAt_zetaFunctionalFactor h0) (analyticAt_riemannZeta_of_ne_one hρ1)
  rw [analyticOrderAt_congr heq, hmul, (analyticAt_zetaFunctionalFactor h0).analyticOrderAt_eq_zero.mpr
    (zetaFunctionalFactor_ne_zero h0 h1), zero_add] at hcomp
  have := hcomp.symm
  rw [analyticOrderAt_riemannZeta_eq hρ1, analyticOrderAt_riemannZeta_eq hρ0] at this
  exact_mod_cast this

end Order

section Conj

lemma shKernel_conj (w : ℂ) (u : ℝ) : shKernel (starRingEnd ℂ w) u = starRingEnd ℂ (shKernel w u) := by
  by_cases hw : w = 0
  · subst hw; simp [shKernel_zero]
  · set s : ℂ := w ^ ((2 : ℕ)⁻¹ : ℂ)
    have hs : s ^ 2 = w := Complex.cpow_nat_inv_pow w two_ne_zero
    have hs0 : s ≠ 0 := by rintro h; rw [h] at hs; exact hw (by rw [← hs]; ring)
    have hcs : (starRingEnd ℂ s) ^ 2 = starRingEnd ℂ w := by rw [← map_pow, hs]
    have hcs0 : starRingEnd ℂ s ≠ 0 := (map_ne_zero _).mpr hs0
    rw [shKernel_eq_sinh hcs hcs0, shKernel_eq_sinh hs hs0, map_div₀, ← Complex.sinh_conj, map_mul,
      Complex.conj_ofReal]

lemma zeroFamilyDensity_conj (κ : ℂ) (y : ℝ) :
    zeroFamilyDensity (starRingEnd ℂ κ) y = starRingEnd ℂ (zeroFamilyDensity κ y) := by
  unfold zeroFamilyDensity
  rw [map_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← shKernel_conj]
  congr 2
  rw [map_sub, map_div₀, map_one, map_ofNat]

/-- Conjugation-symmetric functions have conjugation-symmetric iterated derivatives. -/
lemma iteratedDeriv_conj_symm {f : ℂ → ℂ} (hf : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (n : ℕ) (z : ℂ) : iteratedDeriv n f (starRingEnd ℂ z) = starRingEnd ℂ (iteratedDeriv n f z) := by
  induction n generalizing z with
  | zero => simpa using hf z
  | succ n ih =>
    set g := iteratedDeriv n f
    have hg : g = starRingEnd ℂ ∘ g ∘ starRingEnd ℂ := by
      funext w; simp only [Function.comp_apply, ih, Complex.conj_conj]
    rw [iteratedDeriv_succ]
    change deriv g (starRingEnd ℂ z) = starRingEnd ℂ (deriv g z)
    conv_lhs => rw [hg, deriv_conj_conj]
    simp only [Function.comp_apply, Complex.conj_conj]

/-- Conjugation preserves the multiplicity. -/
lemma zeroJetOrder_conj {ρ : ℂ} (h1 : ρ ≠ 1) : zeroJetOrder (starRingEnd ℂ ρ) = zeroJetOrder ρ := by
  have h1' : starRingEnd ℂ ρ ≠ 1 := fun h => h1 (by rw [← Complex.conj_conj ρ, h, map_one])
  have hρ := analyticOrderAt_riemannZeta_eq h1
  have hc := analyticOrderAt_riemannZeta_eq h1'
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticAt_riemannZeta_of_ne_one h1)] at hρ
  have hz := iteratedDeriv_conj_symm (f := riemannZeta) (fun z => _root_.riemannZeta_conj z)
  have key : analyticOrderAt riemannZeta (starRingEnd ℂ ρ) = zeroJetOrder ρ := by
    rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticAt_riemannZeta_of_ne_one h1')]
    refine ⟨fun k hk => ?_, ?_⟩
    · rw [hz, hρ.1 k hk, map_zero]
    · rw [hz]; exact (map_ne_zero _).mpr hρ.2
  rw [hc] at key
  exact_mod_cast key

end Conj

section Jets

/-- The normalized κ-jet density (1/k!) ∂_κ^k g_κ(y) at κ₀. -/
def zeroJetDensity (κ₀ : ℂ) (k : ℕ) (y : ℝ) : ℂ :=
  iteratedDeriv k (fun κ => zeroFamilyDensity κ y) κ₀ / (k.factorial : ℂ)

lemma zeroJetDensity_zero (κ₀ : ℂ) (y : ℝ) : zeroJetDensity κ₀ 0 y = zeroFamilyDensity κ₀ y := by
  simp [zeroJetDensity]

lemma measurable_zeroJetDensity (κ₀ : ℂ) (k : ℕ) : Measurable (zeroJetDensity κ₀ k) :=
  (measurable_iteratedDeriv_param (F := fun κ y => zeroFamilyDensity κ y)
    differentiable_zeroFamilyDensity measurable_zeroFamilyDensity k κ₀).div_const _

/-- The jet exponent bound: ‖(1/k!) ∂^k g‖ ≤ (‖κ₀‖ + 1)(1 + |y|)^N. -/
def jetGrowthExponent (κ₀ : ℂ) : ℕ := 3 + ⌈‖κ₀‖ + 1⌉₊

lemma norm_zeroJetDensity_le (κ₀ : ℂ) (k : ℕ) (y : ℝ) :
    ‖zeroJetDensity κ₀ k y‖ ≤ (‖κ₀‖ + 1) * (1 + |y|) ^ jetGrowthExponent κ₀ := by
  have h := norm_iteratedDeriv_le_of_entire (differentiable_zeroFamilyDensity y) k κ₀
    (fun w hw => norm_zeroFamilyDensity_le_of_norm_le hw y)
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [zeroJetDensity, norm_div, Complex.norm_natCast, div_le_iff₀ hk]
  unfold jetGrowthExponent
  linarith

lemma zeroJetDensity_small (κ₀ : ℂ) (k : ℕ) {y : ℝ} (hy : |y| < 1) : zeroJetDensity κ₀ k y = 0 := by
  have : (fun κ => zeroFamilyDensity κ y) = fun _ => 0 := funext fun κ => zeroFamilyDensity_small κ hy
  rw [zeroJetDensity, this, iteratedDeriv_fun_const_zero, zero_div]

lemma zeroJetDensity_neg (κ₀ : ℂ) (k : ℕ) (y : ℝ) : zeroJetDensity κ₀ k (-y) = zeroJetDensity κ₀ k y := by
  simp only [zeroJetDensity, zeroFamilyDensity_neg]

lemma zeroJetDensity_conj (κ₀ : ℂ) (k : ℕ) (y : ℝ) :
    zeroJetDensity (starRingEnd ℂ κ₀) k y = starRingEnd ℂ (zeroJetDensity κ₀ k y) := by
  rw [zeroJetDensity, zeroJetDensity, iteratedDeriv_conj_symm (fun z => zeroFamilyDensity_conj z y),
    map_div₀, map_natCast]

lemma locallyIntegrable_zeroJetDensity (κ₀ : ℂ) (k : ℕ) :
    LocallyIntegrable (zeroJetDensity κ₀ k) volume :=
  locallyIntegrable_of_abs_le_bound (measurable_zeroJetDensity κ₀ k) fun R _ =>
    ⟨(‖κ₀‖ + 1) * (1 + R) ^ jetGrowthExponent κ₀, fun x hx =>
      (norm_zeroJetDensity_le κ₀ k x).trans (by gcongr)⟩

/-- Polynomial weights against Schwartz tests are integrable. -/
lemma integrable_one_add_pow_mul_schwartz (N : ℕ) (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => (1 + |x|) ^ N * ‖φ x‖) := by
  have hk (k : ℕ) : Integrable (fun x : ℝ => |x| ^ k * ‖φ x‖) := by
    simpa [Real.norm_eq_abs] using SchwartzMap.integrable_pow_mul volume φ k
  have hs := integrable_finsetSum (Finset.range (N + 1)) (fun m _ => (hk m).const_mul (N.choose m : ℝ))
  refine hs.congr (Eventually.of_forall fun x => ?_)
  show ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * (|x| ^ i * ‖φ x‖) = (1 + |x|) ^ N * ‖φ x‖
  rw [add_comm (1 : ℝ), add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_pow, mul_one]; ring

lemma integrable_zeroJetDensity_mul (κ₀ : ℂ) (k : ℕ) (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => zeroJetDensity κ₀ k x * φ x) := by
  refine ((integrable_one_add_pow_mul_schwartz (jetGrowthExponent κ₀) φ).const_mul (‖κ₀‖ + 1)).mono'
    ((measurable_zeroJetDensity κ₀ k).mul φ.continuous.measurable).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_zeroJetDensity_le κ₀ k x) (norm_nonneg _)

/-- The entire density pairing D(κ) = ∫ g_κ φ and its κ-derivatives. -/
lemma zeroFamilyDensity_pairing_bound (φ : 𝓢(ℝ, ℂ)) (R : ℝ) :
    ∃ B : ℝ → ℝ, Integrable B ∧ ∀ κ : ℂ, ‖κ‖ ≤ R → ∀ x, ‖zeroFamilyDensity κ x * φ x‖ ≤ B x := by
  refine ⟨fun x => |R| * ((1 + |x|) ^ (3 + ⌈|R|⌉₊) * ‖φ x‖),
    (integrable_one_add_pow_mul_schwartz _ φ).const_mul _, fun κ hκ x => ?_⟩
  show _ ≤ |R| * ((1 + |x|) ^ (3 + ⌈|R|⌉₊) * ‖φ x‖)
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_zeroFamilyDensity_le_of_norm_le (hκ.trans (le_abs_self R)) x)
    (norm_nonneg _)

lemma iteratedDeriv_zeroFamilyDensity_pairing (φ : 𝓢(ℝ, ℂ)) (k : ℕ) (κ₀ : ℂ) :
    iteratedDeriv k (fun κ => ∫ x, zeroFamilyDensity κ x * φ x) κ₀ =
      ∫ x, iteratedDeriv k (fun κ => zeroFamilyDensity κ x * φ x) κ₀ :=
  congrFun (iteratedDeriv_integral_entire (F := fun κ x => zeroFamilyDensity κ x * φ x)
    (fun x => (differentiable_zeroFamilyDensity x).mul_const _)
    (fun κ => (measurable_zeroFamilyDensity κ).mul φ.continuous.measurable)
    (zeroFamilyDensity_pairing_bound φ) k) κ₀

lemma differentiable_zeroFamilyDensity_pairing (φ : 𝓢(ℝ, ℂ)) :
    Differentiable ℂ (fun κ => ∫ x, zeroFamilyDensity κ x * φ x) :=
  differentiable_integral_entire (F := fun κ x => zeroFamilyDensity κ x * φ x)
    (fun x => (differentiable_zeroFamilyDensity x).mul_const _)
    (fun κ => (measurable_zeroFamilyDensity κ).mul φ.continuous.measurable)
    (zeroFamilyDensity_pairing_bound φ)

/-- The normalized jets of the density pairing are the pairings of the jet densities. -/
lemma zeroFamilyDensity_pairing_jet (φ : 𝓢(ℝ, ℂ)) (k : ℕ) (κ₀ : ℂ) :
    iteratedDeriv k (fun κ => ∫ x, zeroFamilyDensity κ x * φ x) κ₀ / (k.factorial : ℂ) =
      ∫ x, zeroJetDensity κ₀ k x * φ x := by
  rw [iteratedDeriv_zeroFamilyDensity_pairing, ← integral_div]
  congr 1
  funext x
  have h := iteratedDeriv_mul_const_field (n := k) (fun κ => zeroFamilyDensity κ x) (φ x) (x := κ₀)
  rw [h, zeroJetDensity]
  ring

end Jets

section Mellin

/-- The Mellin pairing H(ρ) = ∫ |x|^(ρ-1) φ(x) dx of the boundary term. -/
def boundaryMellinPairing (φ : 𝓢(ℝ, ℂ)) (ρ : ℂ) : ℂ := ∫ x, ((|x| : ℝ) : ℂ) ^ (ρ - 1) * φ x

lemma norm_abs_cpow_le {w : ℂ} {a : ℝ} (ha : a ≤ w.re) (hw : w.re < 1) (x : ℝ) :
    ‖((|x| : ℝ) : ℂ) ^ (w - 1)‖ ≤ |x| ^ (a - 1) + 1 := by
  have hw1 : w - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; simp [Complex.zero_cpow hw1]; positivity
  have hx0 : 0 < |x| := abs_pos.mpr hx
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re]
  rcases le_total |x| 1 with h1 | h1
  · have := Real.rpow_le_rpow_of_exponent_ge hx0 h1 (show a - 1 ≤ w.re - 1 by linarith)
    linarith
  · have := Real.rpow_le_one_of_one_le_of_nonpos h1 (show w.re - 1 ≤ 0 by linarith)
    have : 0 ≤ |x| ^ (a - 1) := Real.rpow_nonneg hx0.le _
    linarith

lemma differentiableOn_boundaryMellinPairing (φ : 𝓢(ℝ, ℂ)) :
    DifferentiableOn ℂ (boundaryMellinPairing φ) {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1} := by
  intro ρ hρ
  obtain ⟨h0, h1⟩ := hρ
  set r : ℝ := min ρ.re (1 - ρ.re) / 2
  have hr : 0 < r := by
    have : 0 < min ρ.re (1 - ρ.re) := lt_min h0 (by linarith)
    positivity
  have hrle1 : r ≤ ρ.re / 2 := by
    have := min_le_left ρ.re (1 - ρ.re); simp only [r]; linarith
  have hrle2 : r ≤ (1 - ρ.re) / 2 := by
    have := min_le_right ρ.re (1 - ρ.re); simp only [r]; linarith
  have hre : ∀ w ∈ Metric.closedBall ρ r, ρ.re - r ≤ w.re ∧ w.re < 1 ∧ w ≠ 1 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have := (Complex.abs_re_le_norm (w - ρ)).trans hw
    rw [Complex.sub_re, abs_le] at this
    refine ⟨by linarith, by linarith, fun h => ?_⟩
    rw [h, Complex.one_re] at this
    linarith
  have hd : ∀ x : ℝ, DifferentiableOn ℂ (fun w => ((|x| : ℝ) : ℂ) ^ (w - 1) * φ x)
      (Metric.closedBall ρ r) := by
    intro x
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      refine (differentiableOn_const (0 : ℂ)).congr fun w hw => ?_
      have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr (hre w hw).2.2
      simp [Complex.zero_cpow hw1]
    · have hc : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)
      exact (((differentiable_id.sub_const 1).const_cpow (Or.inl hc)).mul_const _).differentiableOn
  have hB : ∀ w ∈ Metric.closedBall ρ r, ∀ x : ℝ,
      ‖((|x| : ℝ) : ℂ) ^ (w - 1) * φ x‖ ≤ |x| ^ (ρ.re - r - 1) * ‖φ x‖ + ‖φ x‖ := by
    intro w hw x
    rw [norm_mul]
    have := norm_abs_cpow_le (hre w hw).1 (hre w hw).2.1 x
    nlinarith [norm_nonneg (φ x)]
  have hBi : Integrable (fun x : ℝ => |x| ^ (ρ.re - r - 1) * ‖φ x‖ + ‖φ x‖) :=
    (integrable_abs_rpow_mul_schwartz (by linarith) (by linarith) φ).add φ.integrable.norm
  exact (hasDerivAt_integral_of_closedBall hr hd
    (fun w => (measurable_abs_cpow (w - 1)).mul φ.continuous.measurable) hBi hB).differentiableAt
    |>.differentiableWithinAt

lemma analyticAt_boundaryMellinPairing (φ : 𝓢(ℝ, ℂ)) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    AnalyticAt ℂ (boundaryMellinPairing φ) ρ :=
  (differentiableOn_boundaryMellinPairing φ).analyticAt
    (((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨h0, h1⟩)

lemma integrable_boundary_mul (φ : 𝓢(ℝ, ℂ)) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    Integrable (fun x : ℝ => ((|x| : ℝ) : ℂ) ^ (ρ - 1) * φ x) := by
  refine ((integrable_abs_rpow_mul_schwartz (r := ρ.re - 1) (by linarith) (by linarith) φ).add
    φ.integrable.norm).mono' ((measurable_abs_cpow (ρ - 1)).mul φ.continuous.measurable).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  show _ ≤ |x| ^ (ρ.re - 1) * ‖φ x‖ + ‖φ x‖
  rw [norm_mul]
  have := norm_abs_cpow_le (le_refl ρ.re) h1 x
  nlinarith [norm_nonneg (φ x)]

end Mellin

section Functional

/-- The actual normalized construction (CP1.7)/b_ρ at an arbitrary parameter, on Schwartz tests:
b_ρ⁻¹ (V_(ρ-1/2) - (1-ρ)⁻¹ (δ₀ + dx) - b_ρ D₀). At an actual zero it is the CP1 zero measure. -/
def zeroFamilyFunctional (ρ : ℂ) (φ : 𝓢(ℝ, ℂ)) : ℂ :=
  (coPoissonFamily (ρ - 1 / 2) φ - 1 / (1 - ρ) * (φ 0 + ∫ x, φ x) -
    normalizationBrho ρ * dilatedCombDistribution 0 φ) / normalizationBrho ρ

lemma zeroFamilyFunctional_eq_zeroMeasure {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) (φ : 𝓢(ℝ, ℂ)) :
    zeroFamilyFunctional ρ φ = (zeroMeasure ρ).integral φ :=
  (zeroMeasure_eq_construction hz h0 h1 hh φ).symm

/-- For every strip parameter ρ ≠ 1/2, zero or not: the density pairing, the boundary term
(ζ(ρ)/b_ρ) ∫ |x|^(ρ-1) φ and the punctured lattice. -/
theorem zeroFamilyFunctional_eq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2)
    (φ : 𝓢(ℝ, ℂ)) :
    zeroFamilyFunctional ρ φ = (∫ x, coPoissonComplexDensity ρ x * φ x) +
      riemannZeta ρ / normalizationBrho ρ * boundaryMellinPairing φ ρ -
        ∑' n : ℤ, if n = 0 then (0 : ℂ) else φ n := by
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
  have hbeq := coPoissonOriginNormalizer_eq_brho hρ0 hρ1
  have hS : Integrable (fun x => finiteSumSrho ρ |x| * φ x) := by
    refine (φ.integrable.norm.const_mul (finiteSumSrhoBound ρ)).mono'
      ((measurable_finiteSumSrho_abs ρ).aestronglyMeasurable.mul
        φ.continuous.aestronglyMeasurable) (Eventually.of_forall (fun x => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (finiteSumSrho_norm_le_bound h0 h1 _) (norm_nonneg _)
  have hP := integrable_boundary_mul φ h0 h1
  have hV := coPoissonFamily_eq_limit h0 h1 φ
  have hR : (∫ x, coPoissonLimitDensity ρ x * φ x) =
      (∫ x, finiteSumSrho ρ |x| * φ x) + riemannZeta ρ * boundaryMellinPairing φ ρ +
        1 / (1 - ρ) * ∫ x, φ x := by
    have e : (fun x => coPoissonLimitDensity ρ x * φ x) = fun x =>
        (finiteSumSrho ρ |x| * φ x + riemannZeta ρ * (((|x| : ℝ) : ℂ) ^ (ρ - 1) * φ x)) +
          1 / (1 - ρ) * φ x := by
      funext x; unfold coPoissonLimitDensity; ring
    have i1 : (∫ x, (finiteSumSrho ρ |x| * φ x + riemannZeta ρ * (((|x| : ℝ) : ℂ) ^ (ρ - 1) * φ x)) +
        1 / (1 - ρ) * φ x) = (∫ x, finiteSumSrho ρ |x| * φ x +
          riemannZeta ρ * (((|x| : ℝ) : ℂ) ^ (ρ - 1) * φ x)) + ∫ x, 1 / (1 - ρ) * φ x :=
      integral_add (hS.add (hP.const_mul _)) (φ.integrable.const_mul _)
    have i2 : (∫ x, finiteSumSrho ρ |x| * φ x + riemannZeta ρ * (((|x| : ℝ) : ℂ) ^ (ρ - 1) * φ x)) =
        (∫ x, finiteSumSrho ρ |x| * φ x) + ∫ x, riemannZeta ρ * (((|x| : ℝ) : ℂ) ^ (ρ - 1) * φ x) :=
      integral_add hS (hP.const_mul _)
    rw [e, i1, i2, integral_const_mul, integral_const_mul, boundaryMellinPairing]
  have hg : (∫ x, coPoissonComplexDensity ρ x * φ x) =
      (∫ x, finiteSumSrho ρ |x| * φ x) / normalizationBrho ρ := by
    rw [← integral_div]
    congr 1
    funext x
    unfold coPoissonComplexDensity
    rw [hbeq]
    ring
  have hD : dilatedCombDistribution 0 φ = φ 0 + ∑' n : ℤ, if n = 0 then (0 : ℂ) else φ n := by
    have hA := coPoissonA_apply 0 φ
    rw [coPoissonA, sub_apply, smul_apply, TemperedDistribution.delta_apply] at hA
    simp only [zero_div, Real.exp_zero, Complex.ofReal_one, one_smul, one_mul] at hA
    rw [← hA]; ring
  have hb' : normalizationBrho ρ = 1 / ρ - 1 / (1 - ρ) := by rw [← hbeq]; rfl
  rw [zeroFamilyFunctional, hV, hR, hg, hD, div_eq_iff hb]
  have key : (∫ x, finiteSumSrho ρ |x| * φ x) / normalizationBrho ρ * normalizationBrho ρ =
      ∫ x, finiteSumSrho ρ |x| * φ x := div_mul_cancel₀ _ hb
  have key2 : riemannZeta ρ / normalizationBrho ρ * boundaryMellinPairing φ ρ * normalizationBrho ρ =
      riemannZeta ρ * boundaryMellinPairing φ ρ := by field_simp
  linear_combination -key - key2 - φ 0 * hb'

/-- Fourier self-duality of the construction at every parameter. -/
theorem zeroFamilyFunctional_fourier (ρ : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    zeroFamilyFunctional ρ (𝓕 φ) = zeroFamilyFunctional ρ φ := by
  unfold zeroFamilyFunctional
  rw [dilatedCombDistribution_zero_fourier, schwartz_integral_fourier, schwartz_fourier_zero]
  have hV : coPoissonFamily (ρ - 1 / 2) (𝓕 φ) = coPoissonFamily (ρ - 1 / 2) φ :=
    congrArg (fun T : TemperedDistribution ℝ ℂ => T φ) (coPoissonFamily_fourier (ρ - 1 / 2))
  rw [hV]
  ring

lemma analyticAt_normalizationBrho {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    AnalyticAt ℂ normalizationBrho ρ := by
  have h1' : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold normalizationBrho
  exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div
    (analyticAt_id.mul (analyticAt_const.sub analyticAt_id)) (mul_ne_zero h0 h1')

/-- R2-H1 parameter limits: the normalized κ-jets of the actual construction along the local inverse,
below the actual multiplicity, are the jet-density pairings minus the lattice at order zero. -/
theorem zeroFamilyFunctional_jet {ρ₀ : ℂ} (h0 : 0 < ρ₀.re) (h1 : ρ₀.re < 1) (hh : ρ₀ ≠ 1 / 2)
    {k : ℕ} (hk : k < zeroJetOrder ρ₀) (φ : 𝓢(ℝ, ℂ)) :
    iteratedDeriv k (fun κ => zeroFamilyFunctional (zeroLocalInverse ρ₀ κ) φ) (spectralKappa ρ₀) /
        (k.factorial : ℂ) =
      (∫ x, zeroJetDensity (spectralKappa ρ₀) k x * φ x) -
        if k = 0 then ∑' n : ℤ, (if n = 0 then (0 : ℂ) else φ n) else 0 := by
  have hρ0 : ρ₀ ≠ 0 := fun h => by simp [h] at h0
  have hρ1 : ρ₀ ≠ 1 := fun h => by simp [h] at h1
  set κ₀ := spectralKappa ρ₀
  set c : ℂ := ∑' n : ℤ, (if n = 0 then (0 : ℂ) else φ n)
  set D : ℂ → ℂ := fun κ => ∫ x, zeroFamilyDensity κ x * φ x
  set Z : ℂ → ℂ := fun κ => riemannZeta (zeroLocalInverse ρ₀ κ)
  set W : ℂ → ℂ := fun κ => boundaryMellinPairing φ (zeroLocalInverse ρ₀ κ) /
    normalizationBrho (zeroLocalInverse ρ₀ κ)
  have hρa := analyticAt_zeroLocalInverse hh
  have hZ : AnalyticAt ℂ Z κ₀ :=
    (analyticAt_riemannZeta_of_ne_one (by rw [zeroLocalInverse_center]; exact hρ1)).comp hρa
  have hH : AnalyticAt ℂ (fun κ => boundaryMellinPairing φ (zeroLocalInverse ρ₀ κ)) κ₀ :=
    (analyticAt_boundaryMellinPairing φ (by rw [zeroLocalInverse_center]; exact h0)
      (by rw [zeroLocalInverse_center]; exact h1)).comp hρa
  have hB : AnalyticAt ℂ (fun κ => normalizationBrho (zeroLocalInverse ρ₀ κ)) κ₀ :=
    (analyticAt_normalizationBrho (by rw [zeroLocalInverse_center]; exact hρ0)
      (by rw [zeroLocalInverse_center]; exact hρ1)).comp hρa
  have hB0 : normalizationBrho (zeroLocalInverse ρ₀ κ₀) ≠ 0 := by
    rw [zeroLocalInverse_center]; exact normalizationBrho_ne_zero hρ0 hρ1 hh
  have hW : AnalyticAt ℂ W κ₀ := hH.div hB hB0
  have heq : (fun κ => zeroFamilyFunctional (zeroLocalInverse ρ₀ κ) φ) =ᶠ[𝓝 κ₀]
      fun κ => D κ + Z κ * W κ - c := by
    filter_upwards [(isOpen_localJetDomain hh).mem_nhds (center_mem_localJetDomain hh h0 h1)]
      with κ hκ
    obtain ⟨hball, hs0, hs1⟩ := hκ
    have hκr : ‖κ - κ₀‖ < localInverseRadius ρ₀ := by rwa [Metric.mem_ball, dist_eq_norm] at hball
    have hne := zeroLocalInverse_ne_half hh hκr
    rw [zeroFamilyFunctional_eq hs0 hs1 hne]
    have hr0 : zeroLocalInverse ρ₀ κ ≠ 0 := fun h => by simp [h] at hs0
    have hr1 : zeroLocalInverse ρ₀ κ ≠ 1 := fun h => by simp [h] at hs1
    have hdens : (fun x => coPoissonComplexDensity (zeroLocalInverse ρ₀ κ) x * φ x) =
        fun x => zeroFamilyDensity κ x * φ x := by
      funext x
      rw [coPoissonComplexDensity_eq_family hr0 hr1 hne, spectralKappa_zeroLocalInverse hh]
    simp only [D, Z, W, c, hdens]
    ring
  have hDc : ContDiffAt ℂ k D κ₀ := ((differentiable_zeroFamilyDensity_pairing φ).contDiff).contDiffAt
  have hZW : ContDiffAt ℂ k (fun κ => Z κ * W κ) κ₀ := (hZ.mul hW).contDiffAt
  rw [heq.iteratedDeriv_eq, iteratedDeriv_fun_sub (hDc.add hZW) contDiffAt_const,
    iteratedDeriv_fun_add hDc hZW]
  have hZo : (zeroJetOrder ρ₀ : ℕ∞) ≤ analyticOrderAt Z κ₀ := by
    rw [show Z = fun κ => riemannZeta (zeroLocalInverse ρ₀ κ) from rfl,
      analyticOrderAt_riemannZeta_comp_inverse hh hρ1]
  rw [iteratedDeriv_mul_eq_zero_of_lt hZ hW hZo hk, add_zero, iteratedDeriv_const, sub_div,
    zeroFamilyDensity_pairing_jet]
  split_ifs with h0k
  · subst h0k; simp
  · simp

end Functional

section Tail

variable {ρ₀ : ℂ}

lemma localJetDomain_mem {κ : ℂ} (hh : ρ₀ ≠ 1 / 2) (hκ : κ ∈ localJetDomain ρ₀) :
    0 < (zeroLocalInverse ρ₀ κ).re ∧ (zeroLocalInverse ρ₀ κ).re < 1 ∧ zeroLocalInverse ρ₀ κ ≠ 1 / 2 ∧
      zeroLocalInverse ρ₀ κ ≠ 0 ∧ zeroLocalInverse ρ₀ κ ≠ 1 ∧
        DifferentiableAt ℂ (zeroLocalInverse ρ₀) κ := by
  obtain ⟨hball, hs0, hs1⟩ := hκ
  have hκr : ‖κ - spectralKappa ρ₀‖ < localInverseRadius ρ₀ := by
    rwa [Metric.mem_ball, dist_eq_norm] at hball
  exact ⟨hs0, hs1, zeroLocalInverse_ne_half hh hκr, fun h => by simp [h] at hs0,
    fun h => by simp [h] at hs1, (hasDerivAt_zeroLocalInverse hh hκr).differentiableAt⟩

/-- The two power terms of the finite-sum expansion along the branch, divided by b_ρ. -/
def jetPowerTerms (ρ₀ : ℂ) (x : ℝ) (κ : ℂ) : ℂ :=
  (riemannZeta (1 - zeroLocalInverse ρ₀ κ) * (x : ℂ) ^ (-zeroLocalInverse ρ₀ κ) -
    riemannZeta (zeroLocalInverse ρ₀ κ) * (x : ℂ) ^ (zeroLocalInverse ρ₀ κ - 1)) /
      normalizationBrho (zeroLocalInverse ρ₀ κ)

/-- The remainder g_κ(x) - 1 - (power terms) + κ B₂({x})/(2x²). -/
def jetTailRemainder (ρ₀ : ℂ) (x : ℝ) (κ : ℂ) : ℂ :=
  zeroFamilyDensity κ x - 1 - jetPowerTerms ρ₀ x κ + κ * ((bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2))

lemma differentiableAt_normalizationBrho {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    DifferentiableAt ℂ normalizationBrho ρ :=
  (analyticAt_normalizationBrho h0 h1).differentiableAt

lemma differentiableOn_jetPowerTerms (hh : ρ₀ ≠ 1 / 2) {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (jetPowerTerms ρ₀ x) (localJetDomain ρ₀) := by
  intro κ hκ
  obtain ⟨-, -, -, hr0, hr1, hd⟩ := localJetDomain_mem hh hκ
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hz1 : DifferentiableAt ℂ (fun κ => riemannZeta (1 - zeroLocalInverse ρ₀ κ)) κ :=
    (differentiableAt_riemannZeta (fun h => hr0 (by linear_combination -h))).comp κ
      ((differentiableAt_const _).sub hd)
  have hz2 : DifferentiableAt ℂ (fun κ => riemannZeta (zeroLocalInverse ρ₀ κ)) κ :=
    (differentiableAt_riemannZeta hr1).comp κ hd
  have hp1 : DifferentiableAt ℂ (fun κ => (x : ℂ) ^ (-zeroLocalInverse ρ₀ κ)) κ :=
    hd.neg.const_cpow (Or.inl hxc)
  have hp2 : DifferentiableAt ℂ (fun κ => (x : ℂ) ^ (zeroLocalInverse ρ₀ κ - 1)) κ :=
    (hd.sub_const 1).const_cpow (Or.inl hxc)
  have hb : DifferentiableAt ℂ (fun κ => normalizationBrho (zeroLocalInverse ρ₀ κ)) κ :=
    (differentiableAt_normalizationBrho hr0 hr1).comp κ hd
  have hb0 : normalizationBrho (zeroLocalInverse ρ₀ κ) ≠ 0 :=
    normalizationBrho_ne_zero hr0 hr1 (localJetDomain_mem hh hκ).2.2.1
  exact (((hz1.mul hp1).sub (hz2.mul hp2)).div hb hb0).differentiableWithinAt

lemma differentiableOn_jetTailRemainder (hh : ρ₀ ≠ 1 / 2) {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (jetTailRemainder ρ₀ x) (localJetDomain ρ₀) := by
  have hg := (differentiable_zeroFamilyDensity x).differentiableOn (s := localJetDomain ρ₀)
  exact ((hg.sub_const 1).sub (differentiableOn_jetPowerTerms hh hx)).add
    (differentiableOn_id.mul_const _)

/-- Along the branch the remainder is the Euler-Maclaurin remainder S-term divided by b_ρ. -/
lemma jetTailRemainder_eq (hh : ρ₀ ≠ 1 / 2) {κ : ℂ} (hκ : κ ∈ localJetDomain ρ₀) {x : ℝ}
    (hx : 1 ≤ x) : jetTailRemainder ρ₀ x κ =
      srhoRemainder (zeroLocalInverse ρ₀ κ) x / normalizationBrho (zeroLocalInverse ρ₀ κ) := by
  obtain ⟨hs0, hs1, hne, hr0, hr1, -⟩ := localJetDomain_mem hh hκ
  set ρ := zeroLocalInverse ρ₀ κ with hρ
  have hb := normalizationBrho_ne_zero hr0 hr1 hne
  have hx0 : 0 ≤ x := by linarith
  have hg : zeroFamilyDensity κ x = finiteSumSrho ρ x / normalizationBrho ρ := by
    rw [← spectralKappa_zeroLocalInverse hh κ, ← coPoissonComplexDensity_eq_family hr0 hr1 hne,
      coPoissonComplexDensity, abs_of_nonneg hx0, coPoissonOriginNormalizer_eq_brho hr0 hr1]
  have hk : (2 * ρ - 1) / normalizationBrho ρ = -κ := by
    rw [kappa_div_brho hs0 hs1 hne, hρ, spectralKappa_zeroLocalInverse hh]
  have hbe := brho_eq hs0 hs1
  rw [jetTailRemainder, jetPowerTerms, ← hρ, hg, finiteSumSrho_expansion hs0 hs1 hx]
  have hx2 : (2 * (x : ℂ) ^ 2) ≠ 0 := by
    have : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    exact mul_ne_zero two_ne_zero (pow_ne_zero 2 this)
  rw [← hbe]
  have e : (2 * ρ - 1) * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2) / normalizationBrho ρ =
      -κ * ((bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2)) := by
    rw [← hk]; field_simp
  field_simp
  field_simp at e
  linear_combination e

lemma continuous_srhoRemainderConst : Continuous srhoRemainderConst := by
  unfold srhoRemainderConst; fun_prop

/-- R2-H1 jet tails: below the multiplicity the normalized jet density is
[k = 0] - ([k = 0] κ₀ + [k = 1]) B₂({|y|})/(2y²) + O(|y|⁻³), uniformly in y. -/
theorem zeroJetDensity_tail (h0 : 0 < ρ₀.re) (h1 : ρ₀.re < 1) (hh : ρ₀ ≠ 1 / 2) {k : ℕ}
    (hk : k < zeroJetOrder ρ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ |y| →
      ‖zeroJetDensity (spectralKappa ρ₀) k y -
        ((if k = 0 then 1 else 0) - ((if k = 0 then spectralKappa ρ₀ else 0) + (if k = 1 then 1 else 0)) *
          ((bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2)))‖ ≤ C * |y| ^ (-3 : ℝ) := by
  have hρ1 : ρ₀ ≠ 1 := fun h => by simp [h] at h1
  set κ₀ := spectralKappa ρ₀
  set U := localJetDomain ρ₀
  have hU := isOpen_localJetDomain hh
  have hκ₀ := center_mem_localJetDomain hh h0 h1
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU κ₀ hκ₀
  set r := ε / 2
  have hr : 0 < r := by positivity
  have hcl : Metric.closedBall κ₀ r ⊆ U := (Metric.closedBall_subset_ball (by simp [r]; linarith)).trans hεU
  -- uniform bound for the remainder constant on the closed disc
  have hcont : ContinuousOn (fun κ => srhoRemainderConst (zeroLocalInverse ρ₀ κ) /
      ‖normalizationBrho (zeroLocalInverse ρ₀ κ)‖) (Metric.closedBall κ₀ r) := by
    intro κ hκ
    obtain ⟨-, -, hne, hr0, hr1, hd⟩ := localJetDomain_mem hh (hcl hκ)
    have hb0 := normalizationBrho_ne_zero hr0 hr1 hne
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuous_srhoRemainderConst.continuousAt.comp hd.continuousAt).div
      ((differentiableAt_normalizationBrho hr0 hr1).continuousAt.comp hd.continuousAt).norm
      (norm_ne_zero_iff.mpr hb0)
  obtain ⟨M, hM⟩ := (isCompact_closedBall κ₀ r).exists_bound_of_continuousOn hcont
  set M' := max M 0
  refine ⟨M' / r ^ k, by positivity, fun y hy => ?_⟩
  set x := |y|
  have hx0 : 0 < x := by linarith
  set c : ℂ := (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2)
  -- the density as a function of κ decomposes exactly
  have hdecomp : (fun κ => zeroFamilyDensity κ y) =
      fun κ => (((fun _ => (1 : ℂ)) κ + jetPowerTerms ρ₀ x κ) - κ * c) + jetTailRemainder ρ₀ x κ := by
    funext κ
    have : zeroFamilyDensity κ y = zeroFamilyDensity κ x := by simp [zeroFamilyDensity, x]
    rw [this, jetTailRemainder]; ring
  have hTa : AnalyticAt ℂ (jetPowerTerms ρ₀ x) κ₀ :=
    (differentiableOn_jetPowerTerms hh hx0).analyticAt (hU.mem_nhds hκ₀)
  have hRa : AnalyticAt ℂ (jetTailRemainder ρ₀ x) κ₀ :=
    (differentiableOn_jetTailRemainder hh hx0).analyticAt (hU.mem_nhds hκ₀)
  -- the power terms vanish to order m at κ₀
  have hT0 : iteratedDeriv k (jetPowerTerms ρ₀ x) κ₀ = 0 := by
    set Z : ℂ → ℂ := fun κ => riemannZeta (zeroLocalInverse ρ₀ κ)
    set Q : ℂ → ℂ := fun κ => (zetaFunctionalFactor (zeroLocalInverse ρ₀ κ) *
      (x : ℂ) ^ (-zeroLocalInverse ρ₀ κ) - (x : ℂ) ^ (zeroLocalInverse ρ₀ κ - 1)) /
        normalizationBrho (zeroLocalInverse ρ₀ κ)
    have heq : jetPowerTerms ρ₀ x =ᶠ[𝓝 κ₀] fun κ => Z κ * Q κ := by
      filter_upwards [hU.mem_nhds hκ₀] with κ hκ
      obtain ⟨hs0, -, -, -, hr1, -⟩ := localJetDomain_mem hh hκ
      simp only [jetPowerTerms, Z, Q, zetaFunctionalFactor_eq hs0 hr1]
      ring
    have hQ : AnalyticAt ℂ Q κ₀ := by
      refine DifferentiableOn.analyticAt (s := U) (fun κ hκ => ?_) (hU.mem_nhds hκ₀)
      obtain ⟨hs0, -, hne, hr0, hr1, hd⟩ := localJetDomain_mem hh hκ
      have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
      have hE : DifferentiableAt ℂ (fun κ => zetaFunctionalFactor (zeroLocalInverse ρ₀ κ)) κ :=
        (analyticAt_zetaFunctionalFactor hs0).differentiableAt.comp κ hd
      exact ((((hE.mul (hd.neg.const_cpow (Or.inl hxc))).sub ((hd.sub_const 1).const_cpow (Or.inl hxc))).div
        ((differentiableAt_normalizationBrho hr0 hr1).comp κ hd)
        (normalizationBrho_ne_zero hr0 hr1 hne))).differentiableWithinAt
    have hZ : AnalyticAt ℂ Z κ₀ :=
      (analyticAt_riemannZeta_of_ne_one (by rw [zeroLocalInverse_center]; exact hρ1)).comp
        (analyticAt_zeroLocalInverse hh)
    have hZo : (zeroJetOrder ρ₀ : ℕ∞) ≤ analyticOrderAt Z κ₀ := by
      rw [show Z = fun κ => riemannZeta (zeroLocalInverse ρ₀ κ) from rfl,
        analyticOrderAt_riemannZeta_comp_inverse hh hρ1]
    rw [heq.iteratedDeriv_eq]
    exact iteratedDeriv_mul_eq_zero_of_lt hZ hQ hZo hk
  -- Cauchy estimate for the remainder
  have hRb : ‖iteratedDeriv k (jetTailRemainder ρ₀ x) κ₀‖ ≤ k.factorial * (M' * x ^ (-3 : ℝ)) / r ^ k := by
    refine norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr ?_ (fun κ hκ => ?_)
    · refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball κ₀ hr.ne']
      exact (differentiableOn_jetTailRemainder hh hx0).mono hcl
    · have hκc := hcl (Metric.sphere_subset_closedBall hκ)
      obtain ⟨hs0, hs1, hne, hr0, hr1, -⟩ := localJetDomain_mem hh hκc
      rw [jetTailRemainder_eq hh hκc hy, norm_div]
      have hb0 := norm_pos_iff.mpr (normalizationBrho_ne_zero hr0 hr1 hne)
      have hR := srhoRemainder_norm_le hs0 hs1 hx0
      have hMκ := (le_abs_self _).trans (hM κ (Metric.sphere_subset_closedBall hκ))
      rw [div_le_iff₀ hb0]
      calc ‖srhoRemainder (zeroLocalInverse ρ₀ κ) x‖
          ≤ srhoRemainderConst (zeroLocalInverse ρ₀ κ) * x ^ (-3 : ℝ) := hR
        _ ≤ (M' * ‖normalizationBrho (zeroLocalInverse ρ₀ κ)‖) * x ^ (-3 : ℝ) := by
            gcongr
            rw [div_le_iff₀ hb0] at hMκ
            exact hMκ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
        _ = _ := by ring
  -- assemble
  have hconst : ContDiffAt ℂ k (fun _ : ℂ => (1 : ℂ)) κ₀ := contDiffAt_const
  have hlin : ContDiffAt ℂ k (fun κ : ℂ => κ * c) κ₀ := (contDiffAt_id.mul contDiffAt_const)
  have hdk : iteratedDeriv k (fun κ => zeroFamilyDensity κ y) κ₀ =
      ((if k = 0 then 1 else 0) + 0 - (if k = 0 then κ₀ else if k = 1 then 1 else 0) * c) +
        iteratedDeriv k (jetTailRemainder ρ₀ x) κ₀ := by
    rw [hdecomp, iteratedDeriv_fun_add ((hconst.add hTa.contDiffAt).sub hlin) hRa.contDiffAt,
      iteratedDeriv_fun_sub (hconst.add hTa.contDiffAt) hlin, iteratedDeriv_fun_add hconst hTa.contDiffAt,
      iteratedDeriv_const, hT0, iteratedDeriv_mul_const_field, iteratedDeriv_fun_id]
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have key : zeroJetDensity κ₀ k y -
      ((if k = 0 then 1 else 0) - ((if k = 0 then κ₀ else 0) + (if k = 1 then 1 else 0)) * c) =
        iteratedDeriv k (jetTailRemainder ρ₀ x) κ₀ / (k.factorial : ℂ) := by
    rw [zeroJetDensity, hdk]
    rcases Nat.lt_trichotomy k 1 with hk1 | hk1 | hk1
    · have : k = 0 := by omega
      subst this; simp
    · subst hk1; simp
    · have h0' : k ≠ 0 := by omega
      have h1' : k ≠ 1 := by omega
      simp only [h0', h1', if_false, zero_add, zero_mul, sub_zero, add_zero]
  rw [key, norm_div, Complex.norm_natCast, div_le_iff₀ hfac]
  calc ‖iteratedDeriv k (jetTailRemainder ρ₀ x) κ₀‖ ≤ k.factorial * (M' * x ^ (-3 : ℝ)) / r ^ k := hRb
    _ = M' / r ^ k * x ^ (-3 : ℝ) * k.factorial := by ring

/-- Below the multiplicity the jet densities are bounded. -/
theorem zeroJetDensity_bounded (h0 : 0 < ρ₀.re) (h1 : ρ₀.re < 1) (hh : ρ₀ ≠ 1 / 2) {k : ℕ}
    (hk : k < zeroJetOrder ρ₀) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖zeroJetDensity (spectralKappa ρ₀) k y‖ ≤ B := by
  obtain ⟨C, hC, hCb⟩ := zeroJetDensity_tail h0 h1 hh hk
  refine ⟨1 + (‖spectralKappa ρ₀‖ + 1) + C, by positivity, fun y => ?_⟩
  rcases lt_or_ge |y| 1 with hy | hy
  · rw [zeroJetDensity_small _ _ hy, norm_zero]; positivity
  have hy0 : 0 < |y| := by linarith
  have hpow : |y| ^ (-3 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by norm_num)
  have hB2 : ‖(bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_abs, Complex.norm_ofNat, div_le_one (by positivity)]
    have := abs_bernoulliTwo_le |y|
    nlinarith
  have hmain : ‖(if k = 0 then (1 : ℂ) else 0) - ((if k = 0 then spectralKappa ρ₀ else 0) +
      (if k = 1 then 1 else 0)) * ((bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2))‖ ≤
        1 + (‖spectralKappa ρ₀‖ + 1) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · split_ifs <;> simp
    · rw [norm_mul]
      have hA : ‖(if k = 0 then spectralKappa ρ₀ else 0) + (if k = 1 then (1 : ℂ) else 0)‖ ≤
          ‖spectralKappa ρ₀‖ + 1 :=
        (norm_add_le _ _).trans (add_le_add (by split_ifs <;> simp) (by split_ifs <;> simp))
      calc _ ≤ ‖(if k = 0 then spectralKappa ρ₀ else 0) + (if k = 1 then (1 : ℂ) else 0)‖ * 1 :=
            mul_le_mul_of_nonneg_left hB2 (norm_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact hA
  have h := hCb y hy
  calc ‖zeroJetDensity (spectralKappa ρ₀) k y‖ ≤ ‖(if k = 0 then (1 : ℂ) else 0) - ((if k = 0 then spectralKappa ρ₀ else 0) +
      (if k = 1 then 1 else 0)) * ((bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2))‖ +
        ‖zeroJetDensity (spectralKappa ρ₀) k y - ((if k = 0 then (1 : ℂ) else 0) - ((if k = 0 then spectralKappa ρ₀ else 0) +
      (if k = 1 then 1 else 0)) * ((bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2)))‖ := norm_le_insert' _ _
    _ ≤ (1 + (‖spectralKappa ρ₀‖ + 1)) + C * 1 := add_le_add hmain (h.trans (mul_le_mul_of_nonneg_left hpow hC))
    _ = _ := by ring

end Tail

section JetMeasure
open scoped ENNReal NNReal

/-- The genuine locally finite complex measure g dx with its canonical Jordan pairs. -/
def jetDensityMeasure (g : ℝ → ℂ) (hgm : Measurable g) (hg : LocallyIntegrable g volume) :
    LocallyFiniteComplexMeasure where
  rePart :=
    { positive := volume.withDensity (fun x => ENNReal.ofReal (g x).re)
      negative := volume.withDensity (fun x => ENNReal.ofReal (-(g x).re))
      positive_locallyFinite := isLocallyFinite_withDensity_ofReal (locallyIntegrable_complex_re hg)
      negative_locallyFinite := isLocallyFinite_withDensity_ofReal (locallyIntegrable_complex_re hg).neg
      mutuallySingular := withDensity_ofReal_mutuallySingular (Complex.measurable_re.comp hgm) }
  imPart :=
    { positive := volume.withDensity (fun x => ENNReal.ofReal (g x).im)
      negative := volume.withDensity (fun x => ENNReal.ofReal (-(g x).im))
      positive_locallyFinite := isLocallyFinite_withDensity_ofReal (locallyIntegrable_complex_im hg)
      negative_locallyFinite := isLocallyFinite_withDensity_ofReal (locallyIntegrable_complex_im hg).neg
      mutuallySingular := withDensity_ofReal_mutuallySingular (Complex.measurable_im.comp hgm) }

variable {g : ℝ → ℂ} {hgm : Measurable g} {hg : LocallyIntegrable g volume}

theorem jetDensityMeasure_integral {f : ℝ → ℂ} (hfm : AEStronglyMeasurable f volume)
    (hgf : Integrable (fun x => g x * f x)) :
    (jetDensityMeasure g hgm hg).integral f = ∫ x, g x * f x := by
  have hb (v : ℝ → ℝ) (hv : Measurable v) (hle : ∀ x, |v x| ≤ ‖g x‖) :
      Integrable (fun x => (v x : ℂ) * f x) := by
    refine hgf.mono ((Complex.measurable_ofReal.comp hv).aestronglyMeasurable.mul hfm)
      (Eventually.of_forall (fun x => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hle x) (norm_nonneg _)
  have hre : Measurable (fun x => (g x).re) := Complex.measurable_re.comp hgm
  have him : Measurable (fun x => (g x).im) := Complex.measurable_im.comp hgm
  have hire := hb _ hre (fun x => Complex.abs_re_le_norm _)
  have hiim := hb _ him (fun x => Complex.abs_im_le_norm _)
  have hre' : Measurable (fun x => -(g x).re) := hre.neg
  have him' : Measurable (fun x => -(g x).im) := him.neg
  have hr1 := integral_withDensity_ofReal hre hfm hire
  have hr2 := integral_withDensity_ofReal hre' hfm (hb _ hre' (fun x => by
    rw [abs_neg]; exact Complex.abs_re_le_norm _))
  have hi1 := integral_withDensity_ofReal him hfm hiim
  have hi2 := integral_withDensity_ofReal him' hfm (hb _ him' (fun x => by
    rw [abs_neg]; exact Complex.abs_im_le_norm _))
  unfold LocallyFiniteComplexMeasure.integral
  change ((∫ x, f x ∂volume.withDensity fun x => ENNReal.ofReal (g x).re) -
      (∫ x, f x ∂volume.withDensity fun x => ENNReal.ofReal (-(g x).re))) +
    I * ((∫ x, f x ∂volume.withDensity fun x => ENNReal.ofReal (g x).im) -
      (∫ x, f x ∂volume.withDensity fun x => ENNReal.ofReal (-(g x).im))) = _
  rw [hr1.2, hr2.2, hi1.2, hi2.2, integral_max_sub_max hre hfm hire, integral_max_sub_max him hfm hiim]
  rw [← integral_const_mul, ← integral_add hire (hiim.const_mul I)]
  congr 1
  funext x
  conv_rhs => rw [← Complex.re_add_im (g x)]
  ring

theorem jetDensityMeasure_gap (h : ∀ x, |x| < 1 → g x = 0) :
    (jetDensityMeasure g hgm hg).variationControl (Ioo (-1) 1) = 0 := by
  have h1 := withDensity_ofReal_gap (u := fun x => (g x).re) (fun x hx => by rw [h x hx, Complex.zero_re])
  have h2 := withDensity_ofReal_gap (u := fun x => -(g x).re)
    (fun x hx => by rw [h x hx, Complex.zero_re, neg_zero])
  have h3 := withDensity_ofReal_gap (u := fun x => (g x).im) (fun x hx => by rw [h x hx, Complex.zero_im])
  have h4 := withDensity_ofReal_gap (u := fun x => -(g x).im)
    (fun x hx => by rw [h x hx, Complex.zero_im, neg_zero])
  change ((jetDensityMeasure g hgm hg).rePart.positive + (jetDensityMeasure g hgm hg).rePart.negative +
    ((jetDensityMeasure g hgm hg).imPart.positive + (jetDensityMeasure g hgm hg).imPart.negative))
      (Ioo (-1) 1) = 0
  simp only [Measure.add_apply, jetDensityMeasure]
  rw [h1, h2, h3, h4]
  simp

theorem jetDensityMeasure_origin (h : ∀ x, |x| < 1 → g x = 0) :
    (jetDensityMeasure g hgm hg).variationControl {0} = 0 :=
  measure_mono_null (fun x hx => by
    simp only [mem_singleton_iff] at hx; subst hx; norm_num) (jetDensityMeasure_gap h)

theorem jetDensityMeasure_even (hev : ∀ x, g (-x) = g x) :
    Measure.map (fun x : ℝ => -x) (jetDensityMeasure g hgm hg).rePart.positive =
        (jetDensityMeasure g hgm hg).rePart.positive ∧
    Measure.map (fun x : ℝ => -x) (jetDensityMeasure g hgm hg).rePart.negative =
        (jetDensityMeasure g hgm hg).rePart.negative ∧
    Measure.map (fun x : ℝ => -x) (jetDensityMeasure g hgm hg).imPart.positive =
        (jetDensityMeasure g hgm hg).imPart.positive ∧
    Measure.map (fun x : ℝ => -x) (jetDensityMeasure g hgm hg).imPart.negative =
        (jetDensityMeasure g hgm hg).imPart.negative := by
  have hre : Measurable (fun x => (g x).re) := Complex.measurable_re.comp hgm
  have him : Measurable (fun x => (g x).im) := Complex.measurable_im.comp hgm
  exact ⟨map_neg_withDensity_even (ENNReal.measurable_ofReal.comp hre) (fun x => by simp only [hev]),
    map_neg_withDensity_even (u := fun x => ENNReal.ofReal (-(g x).re))
      (ENNReal.measurable_ofReal.comp hre.neg) (fun x => by simp only [hev]),
    map_neg_withDensity_even (ENNReal.measurable_ofReal.comp him) (fun x => by simp only [hev]),
    map_neg_withDensity_even (u := fun x => ENNReal.ofReal (-(g x).im))
      (ENNReal.measurable_ofReal.comp him.neg) (fun x => by simp only [hev])⟩

theorem jetDensityMeasure_hasLinearGrowth {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    (jetDensityMeasure g hgm hg).HasLinearGrowth := by
  set c : ℝ≥0 := B.toNNReal with hc
  have hdom (u : ℝ → ℝ) (hu : ∀ x, u x ≤ B) :
      volume.withDensity (fun x => ENNReal.ofReal (u x)) ≤ (c : ℝ≥0∞) • volume := by
    rw [← withDensity_const]
    refine withDensity_mono (Eventually.of_forall (fun x => ?_))
    change ENNReal.ofReal (u x) ≤ ENNReal.ofReal B
    exact ENNReal.ofReal_le_ofReal (hu x)
  have hle : (jetDensityMeasure g hgm hg).variationControl ≤
      (((c : ℝ≥0∞) • volume + (c : ℝ≥0∞) • volume) + ((c : ℝ≥0∞) • volume + (c : ℝ≥0∞) • volume)) := by
    change (jetDensityMeasure g hgm hg).rePart.positive + (jetDensityMeasure g hgm hg).rePart.negative +
      ((jetDensityMeasure g hgm hg).imPart.positive + (jetDensityMeasure g hgm hg).imPart.negative) ≤ _
    refine add_le_add (add_le_add ?_ ?_) (add_le_add ?_ ?_)
    · exact hdom _ (fun x => (Complex.re_le_norm _).trans (hB x))
    · exact hdom _ (fun x => (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (hB x)))
    · exact hdom _ (fun x => (Complex.im_le_norm _).trans (hB x))
    · exact hdom _ (fun x => (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (hB x)))
  have : IsFiniteMeasureOnCompacts ((c : ℝ≥0∞) • (volume : Measure ℝ)) :=
    IsFiniteMeasureOnCompacts.smul _ ENNReal.coe_ne_top
  have hv := linearMassGrowth_smul_volume c
  exact (linearMassGrowth_add (linearMassGrowth_add hv hv) (linearMassGrowth_add hv hv)).mono hle

/-- The normalized κ-jets of the actual zero measures: the CP1 zero measure itself at order zero,
and (1/k!) ∂_κ^k g_κ(|x|) dx at κ = ρ(1 - ρ) for k ≥ 1 (the lattice does not depend on κ). -/
def normalizedZeroMeasureJet (ρ : ℂ) (k : ℕ) : LocallyFiniteComplexMeasure :=
  if k = 0 then zeroMeasure ρ else
    jetDensityMeasure (zeroJetDensity (spectralKappa ρ) k) (measurable_zeroJetDensity _ _)
      (locallyIntegrable_zeroJetDensity _ _)

lemma normalizedZeroMeasureJet_zero (ρ : ℂ) : normalizedZeroMeasureJet ρ 0 = zeroMeasure ρ := by
  simp [normalizedZeroMeasureJet]

lemma normalizedZeroMeasureJet_succ (ρ : ℂ) {k : ℕ} (hk : k ≠ 0) :
    normalizedZeroMeasureJet ρ k = jetDensityMeasure (zeroJetDensity (spectralKappa ρ) k)
      (measurable_zeroJetDensity _ _) (locallyIntegrable_zeroJetDensity _ _) := by
  simp [normalizedZeroMeasureJet, hk]

/-- The pairing of every jet with a Schwartz test, for every strip parameter ρ ≠ 1/2. -/
theorem normalizedZeroMeasureJet_integral {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2)
    (k : ℕ) (φ : 𝓢(ℝ, ℂ)) :
    (normalizedZeroMeasureJet ρ k).integral φ = (∫ x, zeroJetDensity (spectralKappa ρ) k x * φ x) -
      if k = 0 then ∑' n : ℤ, (if n = 0 then (0 : ℂ) else φ n) else 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
    rw [normalizedZeroMeasureJet_zero, zeroMeasure_integral h0 h1, if_pos rfl]
    congr 2
    funext x
    rw [zeroJetDensity_zero, coPoissonComplexDensity_eq_family hρ0 hρ1 hh]
  · rw [normalizedZeroMeasureJet_succ ρ hk, if_neg hk, sub_zero]
    exact jetDensityMeasure_integral φ.continuous.aestronglyMeasurable
      (integrable_zeroJetDensity_mul _ _ φ)

end JetMeasure

/-! ### The forced Euler identity at every strip parameter

CoPoissonJets imports only ZeroProfiles, so the Stage 11 identity (ForcedEuler) is reproduced here
under the `CoPoissonJets` namespace, from the same cell lemmas, for use in the differentiated chain. -/

namespace CoPoissonJets
open scoped ContDiff

section CellEuler

/-- x² S'_cell = -ρ x^(1-ρ) A_n - (ρ-1) x^ρ B_n on (0, ∞). -/
lemma sq_mul_srhoCellDeriv (ρ : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ 2 * srhoCellDeriv ρ n x =
      -ρ * (x : ℂ) ^ (1 - ρ) * cellSumA ρ n - (ρ - 1) * (x : ℂ) ^ ρ * cellSumB ρ n := by
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have e1 : (x : ℂ) ^ 2 * (x : ℂ) ^ (-ρ - 1) = (x : ℂ) ^ (1 - ρ) := by
    rw [show (1 - ρ) = (2 : ℂ) + (-ρ - 1) by ring, Complex.cpow_add _ _ hxne]; norm_cast
  have e2 : (x : ℂ) ^ 2 * (x : ℂ) ^ (ρ - 1 - 1) = (x : ℂ) ^ ρ := by
    rw [show ρ = (2 : ℂ) + (ρ - 1 - 1) by ring, Complex.cpow_add _ _ hxne]
    · norm_cast; ring_nf
  unfold srhoCellDeriv
  linear_combination (-ρ * cellSumA ρ n) * e1 - ((ρ - 1) * cellSumB ρ n) * e2

/-- The Euler equation of every cell branch: (x² S'_cell)' = -κ S_cell on (0, ∞). -/
lemma hasDerivAt_sq_mul_srhoCellDeriv (ρ : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * srhoCellDeriv ρ n y)
      (-spectralKappa ρ * srhoCell ρ n x) x := by
  have h1 := (hasDerivAt_cpow_neg (ρ - 1) hx).const_mul (-ρ * cellSumA ρ n)
  have h2 := (hasDerivAt_cpow_neg (-ρ) hx).const_mul (-(ρ - 1) * cellSumB ρ n)
  have hsum := h1.add h2
  refine (hsum.congr_deriv ?_).congr_of_eventuallyEq ?_
  · unfold srhoCell spectralKappa
    have e1 : -(ρ - 1) - 1 = -ρ := by ring
    have e2 : -(-ρ) - 1 = ρ - 1 := by ring
    rw [e1, e2]; ring
  · filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [sq_mul_srhoCellDeriv ρ n hy]
    simp only [neg_sub, neg_neg, Pi.add_apply]
    ring

end CellEuler

section CellParts

/-- On the closed cell [n, n+1] the profile is the smooth branch (S_ρ is continuous at n+1). -/
lemma zeroProfile_eq_cell_closed (ρ : ℂ) {n : ℕ} {x : ℝ} (hx : x ∈ Icc (n : ℝ) (n + 1)) :
    zeroProfile ρ x = 1 - srhoCell ρ n x / normalizationBrho ρ := by
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg n) hx.1
  rw [zeroProfile, abs_of_nonneg hx0]
  rcases lt_or_eq_of_le hx.2 with h | h
  · rw [finiteSumSrho_eq_cell ρ ⟨hx.1, h⟩]
  · have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [h, ← hc, finiteSumSrho_eq_cell ρ (n := n + 1) ⟨le_rfl, by push_cast; linarith⟩, srhoCell_succ_eq]

lemma srhoCell_zero (ρ : ℂ) (y : ℝ) : srhoCell ρ 0 y = 0 := by
  simp [srhoCell, cellSumA, cellSumB]

/-- Integration by parts on one cell [n, n+1] (n ≥ 1) against a C¹ test function. -/
lemma cell_parts (ρ : ℂ) {n : ℕ} (hn : 1 ≤ n) {φ φ' : ℝ → ℂ}
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ') :
    ∫ x in (n : ℝ)..(n + 1), (x : ℂ) ^ 2 * srhoCellDeriv ρ n x * φ' x =
      ((((n : ℝ) + 1 : ℝ) : ℂ) ^ 2 * srhoCellDeriv ρ n ((n : ℝ) + 1) * φ ((n : ℝ) + 1) -
        ((n : ℝ) : ℂ) ^ 2 * srhoCellDeriv ρ n n * φ n) +
      spectralKappa ρ * ∫ x in (n : ℝ)..(n + 1), srhoCell ρ n x * φ x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ x ∈ uIcc (n : ℝ) (n + 1), 0 < x := by
    intro x hx; rw [uIcc_of_le (by linarith)] at hx; linarith [hx.1]
  have hu : ∀ x ∈ uIcc (n : ℝ) (n + 1), HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * srhoCellDeriv ρ n y)
      (-spectralKappa ρ * srhoCell ρ n x) x := fun x hx => hasDerivAt_sq_mul_srhoCellDeriv ρ n (hpos x hx)
  have hv : ∀ x ∈ uIcc (n : ℝ) (n + 1), HasDerivAt φ (φ' x) x := fun x _ => hφ x
  have hcellc : ContinuousOn (fun x => -spectralKappa ρ * srhoCell ρ n x) (uIcc (n : ℝ) (n + 1)) :=
    fun x hx => ((hasDerivAt_srhoCell ρ n (hpos x hx)).continuousAt.const_mul _).continuousWithinAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hcellc.intervalIntegrable) (hφ'.intervalIntegrable _ _)
  have e1 : (∫ x in (n : ℝ)..(n + 1), (x : ℂ) ^ 2 * srhoCellDeriv ρ n x * φ' x) =
      ∫ x in (n : ℝ)..(n + 1), ((x : ℂ) ^ 2 * srhoCellDeriv ρ n x) * φ' x := rfl
  rw [e1, hparts]
  have e2 : (∫ x in (n : ℝ)..(n + 1), -spectralKappa ρ * srhoCell ρ n x * φ x) =
      -spectralKappa ρ * ∫ x in (n : ℝ)..(n + 1), srhoCell ρ n x * φ x := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  rw [e2]; push_cast; ring

end CellParts

section Derivative

/-- The explicit derivative of the zero profile on (0, ∞): the cell derivative of the cell
containing x (the right derivative at integers). -/
def zeroProfileDeriv (ρ : ℂ) (x : ℝ) : ℂ := -(srhoCellDeriv ρ ⌊x⌋₊ x / normalizationBrho ρ)

lemma measurable_zeroProfileDeriv (ρ : ℂ) : Measurable (zeroProfileDeriv ρ) := by
  have hA : Measurable (fun x : ℝ => cellSumA ρ ⌊x⌋₊) :=
    (measurable_from_nat (f := cellSumA ρ)).comp Nat.measurable_floor
  have hB : Measurable (fun x : ℝ => cellSumB ρ ⌊x⌋₊) :=
    (measurable_from_nat (f := cellSumB ρ)).comp Nat.measurable_floor
  unfold zeroProfileDeriv srhoCellDeriv
  have h1 : Measurable (fun x : ℝ => (x : ℂ) ^ (-ρ - 1)) := Complex.measurable_ofReal.pow_const _
  have h2 : Measurable (fun x : ℝ => (x : ℂ) ^ (ρ - 1 - 1)) := Complex.measurable_ofReal.pow_const _
  exact (((measurable_const.mul h1).mul hA).sub ((measurable_const.mul h2).mul hB)).div_const _ |>.neg

lemma zeroProfileDeriv_eq_cell (ρ : ℂ) {n : ℕ} {x : ℝ} (hx : x ∈ Ico (n : ℝ) (n + 1)) :
    zeroProfileDeriv ρ x = -(srhoCellDeriv ρ n x / normalizationBrho ρ) := by
  rw [zeroProfileDeriv, natFloor_eq_of_mem_cell hx]

lemma deriv_zeroProfile_eq {ρ : ℂ} {x : ℝ} (hx : 0 < x) (hn : x ∉ Set.range (fun n : ℕ => (n : ℝ))) :
    deriv (zeroProfile ρ) x = zeroProfileDeriv ρ x := by
  have hcell := mem_cell_of_not_nat hx hn
  rw [(hasDerivAt_zeroProfile_cell ρ hcell).deriv, zeroProfileDeriv_eq_cell ρ (Ioo_subset_Ico_self hcell)]

lemma hasDerivWithinAt_zeroProfile_Ioi (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (zeroProfile ρ) (zeroProfileDeriv ρ x) (Ioi x) x := by
  by_cases hn : x ∈ Set.range (fun n : ℕ => (n : ℝ))
  · obtain ⟨m, rfl⟩ := hn
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hx
      · exact h
    have h := hasDerivWithinAt_zeroProfile_right ρ hm
    rw [zeroProfileDeriv, Nat.floor_natCast]
    exact h.mono Ioi_subset_Ici_self
  · have hcell := mem_cell_of_not_nat hx hn
    rw [zeroProfileDeriv_eq_cell ρ (Ioo_subset_Ico_self hcell)]
    exact (hasDerivAt_zeroProfile_cell ρ hcell).hasDerivWithinAt

/-- The ordinary part of the forced Euler equation: (x² h')' = κ (1 - h) between integers. -/
lemma hasDerivAt_sq_mul_deriv_zeroProfile (ρ : ℂ) {x : ℝ} (hx : 0 < x)
    (hn : x ∉ Set.range (fun n : ℕ => (n : ℝ))) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * deriv (zeroProfile ρ) y)
      (spectralKappa ρ * (1 - zeroProfile ρ x)) x := by
  have hcell := mem_cell_of_not_nat hx hn
  set n := ⌊x⌋₊
  have h := (hasDerivAt_sq_mul_srhoCellDeriv ρ n hx).div_const (normalizationBrho ρ) |>.neg
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [zeroProfile_eq_cell_closed ρ (Ioo_subset_Icc_self hcell)]; ring
  · filter_upwards [Ioo_mem_nhds hcell.1 hcell.2] with y hy
    rw [(hasDerivAt_zeroProfile_cell ρ hy).deriv]; simp only [Pi.neg_apply]; ring

end Derivative

section Telescoping

lemma intervalIntegral_congr_Ioo {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (h : EqOn f g (Ioo a b)) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

lemma intervalIntegrable_congr_Ioo {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (h : EqOn f g (Ioo a b))
    (hg : IntervalIntegrable g volume a b) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at hg ⊢
  exact hg.congr_fun h.symm measurableSet_Ioo

/-- The smooth branch of h on the closed cell [n, n+1] and its derivative. -/
lemma hasDerivAt_zeroProfile_branch (ρ : ℂ) (n : ℕ) {y : ℝ} (hy : (n : ℝ) ≤ y) :
    HasDerivAt (fun z : ℝ => 1 - srhoCell ρ n z / normalizationBrho ρ)
      (-(srhoCellDeriv ρ n y / normalizationBrho ρ)) y := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [srhoCell_zero, srhoCellDeriv_zero, zero_div, sub_zero, neg_zero]
    exact hasDerivAt_const _ _
  · have hy0 : 0 < y := lt_of_lt_of_le (by exact_mod_cast hn) hy
    exact ((hasDerivAt_srhoCell ρ n hy0).div_const _).const_sub 1

/-- Integration by parts of h against ψ' on one cell [n, n+1]. -/
lemma cell_parts_profile (ρ : ℂ) (n : ℕ) {ψ ψ' : ℝ → ℂ} (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hψ' : Continuous ψ') :
    IntervalIntegrable (fun x => zeroProfileDeriv ρ x * ψ x) volume n (n + 1) ∧
    ∫ x in (n : ℝ)..(n + 1), zeroProfile ρ x * ψ' x =
      zeroProfile ρ ((n : ℝ) + 1) * ψ ((n : ℝ) + 1) - zeroProfile ρ n * ψ n -
        ∫ x in (n : ℝ)..(n + 1), zeroProfileDeriv ρ x * ψ x := by
  have hle : (n : ℝ) ≤ n + 1 := by linarith
  have hmem : ∀ x ∈ uIcc (n : ℝ) (n + 1), x ∈ Icc (n : ℝ) (n + 1) := fun x hx => by
    rwa [uIcc_of_le hle] at hx
  have hu : ∀ x ∈ uIcc (n : ℝ) (n + 1), HasDerivAt (fun z : ℝ => 1 - srhoCell ρ n z / normalizationBrho ρ)
      (-(srhoCellDeriv ρ n x / normalizationBrho ρ)) x :=
    fun x hx => hasDerivAt_zeroProfile_branch ρ n (hmem x hx).1
  have hcont : ContinuousOn (fun x => -(srhoCellDeriv ρ n x / normalizationBrho ρ)) (uIcc (n : ℝ) (n + 1)) := by
    intro x hx
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [srhoCellDeriv_zero, zero_div, neg_zero]; exact continuousWithinAt_const
    · have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hn) (hmem x hx).1
      have h1 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-ρ - 1)) x :=
        Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')
      have h2 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (ρ - 1 - 1)) x :=
        Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')
      unfold srhoCellDeriv
      exact ((((continuousAt_const.mul h1).mul continuousAt_const).sub
        ((continuousAt_const.mul h2).mul continuousAt_const)).div_const _).neg.continuousWithinAt
  have hII : IntervalIntegrable (fun x => -(srhoCellDeriv ρ n x / normalizationBrho ρ)) volume n (n + 1) :=
    hcont.intervalIntegrable
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu (fun x _ => hψ x) hII
    (hψ'.intervalIntegrable _ _)
  have heqIoo : EqOn (fun x => zeroProfileDeriv ρ x * ψ x)
      (fun x => -(srhoCellDeriv ρ n x / normalizationBrho ρ) * ψ x) (Ioo (n : ℝ) (n + 1)) :=
    fun x hx => by simp only [zeroProfileDeriv_eq_cell ρ (Ioo_subset_Ico_self hx)]
  have hcontψ : ContinuousOn ψ (uIcc (n : ℝ) (n + 1)) :=
    fun x _ => (hψ x).continuousAt.continuousWithinAt
  refine ⟨intervalIntegrable_congr_Ioo hle heqIoo ((hcont.mul hcontψ).intervalIntegrable), ?_⟩
  have e1 : (∫ x in (n : ℝ)..(n + 1), zeroProfile ρ x * ψ' x) =
      ∫ x in (n : ℝ)..(n + 1), (1 - srhoCell ρ n x / normalizationBrho ρ) * ψ' x :=
    intervalIntegral.integral_congr fun x hx => by
      simp only [zeroProfile_eq_cell_closed ρ (hmem x hx)]
  rw [e1, hparts, intervalIntegral_congr_Ioo hle heqIoo,
    zeroProfile_eq_cell_closed ρ (n := n) ⟨le_refl _, hle⟩,
    zeroProfile_eq_cell_closed ρ (n := n) ⟨hle, le_refl _⟩]

/-- Telescoped distributional integration by parts of h on [0, N+1]. -/
lemma profile_parts (ρ : ℂ) {ψ ψ' : ℝ → ℂ} (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hψ' : Continuous ψ') (N : ℕ) :
    IntervalIntegrable (fun x => zeroProfileDeriv ρ x * ψ x) volume 0 ((N : ℝ) + 1) ∧
    ∫ x in (0 : ℝ)..((N : ℝ) + 1), zeroProfile ρ x * ψ' x =
      zeroProfile ρ ((N : ℝ) + 1) * ψ ((N : ℝ) + 1) - zeroProfile ρ 0 * ψ 0 -
        ∫ x in (0 : ℝ)..((N : ℝ) + 1), zeroProfileDeriv ρ x * ψ x := by
  induction N with
  | zero => simpa using cell_parts_profile ρ 0 hψ hψ'
  | succ N ih =>
    obtain ⟨hI, hE⟩ := ih
    obtain ⟨hI1, hE1⟩ := cell_parts_profile ρ (N + 1) hψ hψ'
    have hc : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hc] at hI1 hE1
    have hc2 : ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 1 + 1 := by push_cast; ring
    rw [hc2]
    have hcontψ' : ∀ a b : ℝ, IntervalIntegrable ψ' volume a b := fun a b => hψ'.intervalIntegrable a b
    have hhψ : ∀ a b : ℝ, IntervalIntegrable (fun x => zeroProfile ρ x * ψ' x) volume a b :=
      fun a b => ((continuous_zeroProfile ρ).mul hψ').intervalIntegrable a b
    refine ⟨hI.trans hI1, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hhψ _ _) (hhψ _ _),
      ← intervalIntegral.integral_add_adjacent_intervals hI hI1, hE, hE1]
    ring

end Telescoping

section EulerTelescoping

lemma continuousOn_srhoCellDeriv (ρ : ℂ) (n : ℕ) : ContinuousOn (srhoCellDeriv ρ n) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have h1 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-ρ - 1)) x :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')
  have h2 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (ρ - 1 - 1)) x :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')
  unfold srhoCellDeriv
  exact (((continuousAt_const.mul h1).mul continuousAt_const).sub
    ((continuousAt_const.mul h2).mul continuousAt_const)).continuousWithinAt

/-- One cell [n, n+1], n ≥ 1, of ∫ x² h' v'. -/
lemma euler_cell (ρ : ℂ) {n : ℕ} (hn : 1 ≤ n) {v v' : ℝ → ℂ} (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : Continuous v') :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x) volume n (n + 1) ∧
    ∫ x in (n : ℝ)..(n + 1), (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x =
      ((((n : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv ρ n ((n : ℝ) + 1) / normalizationBrho ρ) *
          v ((n : ℝ) + 1) -
        ((n : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv ρ n n / normalizationBrho ρ) * v n) +
      spectralKappa ρ * ∫ x in (n : ℝ)..(n + 1), (zeroProfile ρ x - 1) * v x := by
  have hle : (n : ℝ) ≤ n + 1 := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem : ∀ x ∈ uIcc (n : ℝ) (n + 1), x ∈ Icc (n : ℝ) (n + 1) := fun x hx => by
    rwa [uIcc_of_le hle] at hx
  have heqIoo : EqOn (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x)
      (fun x : ℝ => -(1 / normalizationBrho ρ) * ((x : ℂ) ^ 2 * srhoCellDeriv ρ n x * v' x))
      (Ioo (n : ℝ) (n + 1)) := fun x hx => by
    simp only [zeroProfileDeriv_eq_cell ρ (Ioo_subset_Ico_self hx)]; ring
  have hcont : ContinuousOn (fun x : ℝ => -(1 / normalizationBrho ρ) * ((x : ℂ) ^ 2 * srhoCellDeriv ρ n x * v' x))
      (uIcc (n : ℝ) (n + 1)) := by
    refine continuousOn_const.mul ((((Complex.continuous_ofReal.pow 2).continuousOn).mul ?_).mul
      hv'.continuousOn)
    exact (continuousOn_srhoCellDeriv ρ n).mono fun x hx => lt_of_lt_of_le hn0 (hmem x hx).1
  refine ⟨intervalIntegrable_congr_Ioo hle heqIoo hcont.intervalIntegrable, ?_⟩
  have hparts := cell_parts ρ hn hv hv'
  have e2 : (∫ x in (n : ℝ)..(n + 1), (zeroProfile ρ x - 1) * v x) =
      ∫ x in (n : ℝ)..(n + 1), -(1 / normalizationBrho ρ) * (srhoCell ρ n x * v x) :=
    intervalIntegral.integral_congr fun x hx => by
      simp only [zeroProfile_eq_cell_closed ρ (hmem x hx)]; ring
  rw [intervalIntegral_congr_Ioo hle heqIoo, intervalIntegral.integral_const_mul, hparts, e2,
    intervalIntegral.integral_const_mul]
  ring

/-- Telescoped ∫_0^(N+1) x² h' v' with the integer atoms and the boundary term at N+1. -/
lemma euler_parts {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) {v v' : ℝ → ℂ}
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : Continuous v') (N : ℕ) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x) volume 0 ((N : ℝ) + 1) ∧
    ∫ x in (0 : ℝ)..((N : ℝ) + 1), (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x =
      spectralKappa ρ * ((∫ x in (0 : ℝ)..((N : ℝ) + 1), (zeroProfile ρ x - 1) * v x) +
        ∑ m ∈ Finset.range N, v (m + 1)) +
      (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv ρ N ((N : ℝ) + 1) / normalizationBrho ρ) *
        v ((N : ℝ) + 1) := by
  induction N with
  | zero =>
    have hz : EqOn (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x) (fun _ => (0 : ℂ))
        (Ioo (0 : ℝ) 1) := fun x hx => by
      have hx' : x ∈ Ico ((0 : ℕ) : ℝ) ((0 : ℕ) + 1) := by simpa using Ioo_subset_Ico_self hx
      simp only [zeroProfileDeriv_eq_cell ρ hx', srhoCellDeriv_zero, zero_div, neg_zero, mul_zero,
        zero_mul]
    have hone : (∫ x in (0 : ℝ)..1, (zeroProfile ρ x - 1) * v x) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun x hx => ?_]
      · simp
      · rw [uIcc_of_le zero_le_one] at hx
        simp only [zeroProfile_eq_one ρ (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩), sub_self, zero_mul]
    simp only [CharP.cast_eq_zero, zero_add, Finset.range_zero, Finset.sum_empty, add_zero,
      srhoCellDeriv_zero, zero_div, neg_zero, mul_zero, zero_mul]
    refine ⟨intervalIntegrable_congr_Ioo zero_le_one hz intervalIntegrable_const, ?_⟩
    rw [intervalIntegral_congr_Ioo zero_le_one hz, hone]; simp
  | succ N ih =>
    obtain ⟨hI, hE⟩ := ih
    obtain ⟨hI1, hE1⟩ := euler_cell ρ (n := N + 1) (by omega) hv hv'
    have hc : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hc] at hI1 hE1
    have hc2 : ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 1 + 1 := by push_cast; ring
    rw [hc2]
    have hhv : ∀ a b : ℝ, IntervalIntegrable (fun x => (zeroProfile ρ x - 1) * v x) volume a b :=
      fun a b => (((continuous_zeroProfile ρ).sub continuous_const).mul
        (continuous_iff_continuousAt.mpr fun x => (hv x).continuousAt)).intervalIntegrable a b
    refine ⟨hI.trans hI1, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hI hI1, hE, hE1,
      ← intervalIntegral.integral_add_adjacent_intervals (hhv 0 ((N : ℝ) + 1)) (hhv ((N : ℝ) + 1) ((N : ℝ) + 1 + 1)),
      Finset.sum_range_succ]
    have hj := zeroProfile_deriv_jump h0 h1 hh N
    have hNc : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    have hj' : ((N + 1 : ℕ) : ℂ) ^ 2 * (-(srhoCellDeriv ρ (N + 1) (N + 1 : ℕ) / normalizationBrho ρ) -
        -(srhoCellDeriv ρ N (N + 1 : ℕ) / normalizationBrho ρ)) = -spectralKappa ρ := by
      rw [hj]; field_simp
    have hcast : (((N : ℝ) + 1 : ℝ) : ℂ) = ((N + 1 : ℕ) : ℂ) := by push_cast; ring
    have hcastR : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, hcastR] at *
    simp only [Nat.cast_add, Nat.cast_one] at hj'
    push_cast at *
    linear_combination (-(v ((N : ℝ) + 1))) * hj'

end EulerTelescoping

section Distribution

/-- Smooth compactly supported test functions on the positive axis. -/
def PositiveAxisTest (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi 0

/-- The distribution -(x² h')' on (0, ∞), with h' the distributional derivative of h:
φ ↦ ⟨x² h', φ'⟩ = -∫ h (x² φ')'. -/
def eulerImage (ρ : ℂ) (φ : ℝ → ℂ) : ℂ :=
  -∫ x in Ioi 0, zeroProfile ρ x * deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv φ y) x

lemma PositiveAxisTest.eventually_zero {φ : ℝ → ℂ} (hφ : PositiveAxisTest φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, M < x → φ =ᶠ[𝓝 x] 0 := by
  obtain ⟨M, hM⟩ := hφ.2.1.isCompact.bddAbove
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport fun h =>
    absurd (hM h) (not_le.mpr (lt_of_le_of_lt (le_max_left _ _) hy))

lemma setIntegral_Ioi_eq_intervalIntegral {F : ℝ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ x, c < x → F x = 0) : ∫ x in Ioi 0, F x = ∫ x in (0 : ℝ)..c, F x := by
  rw [intervalIntegral.integral_of_le hc]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    fun x hx => hF x (not_le.mp fun h => hx.2 ⟨hx.1, h⟩)

/-- The forced Euler identity against every positive-axis test function, for b_ρ ≠ 0. -/
theorem forced_euler_identity {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2)
    {φ : ℝ → ℂ} (hφ : PositiveAxisTest φ) :
    eulerImage ρ φ = spectralKappa ρ * ((∫ x in Ioi 0, (zeroProfile ρ x - 1) * φ x) +
        ∑' n : ℕ, φ (n + 1)) ∧
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * deriv (zeroProfile ρ) x * deriv φ x) = eulerImage ρ φ := by
  obtain ⟨M, hM0, hMz⟩ := hφ.eventually_zero
  have h1le : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
    ((hφ.1.differentiable (by simp)).differentiableAt).hasDerivAt
  have hdc : ContDiff ℝ ∞ (deriv φ) := by simpa using hφ.1.iterate_deriv 1
  set ψ : ℝ → ℂ := fun y => (y : ℂ) ^ 2 * deriv φ y with hψdef
  have hψc : ContDiff ℝ ∞ ψ := by
    have : ContDiff ℝ ∞ (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
    exact (this.pow 2).mul hdc
  have hψd : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x =>
    ((hψc.differentiable (by simp)).differentiableAt).hasDerivAt
  have hψ' : Continuous (deriv ψ) := hψc.continuous_deriv (by simp)
  have hφ' : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
  have hφ0 : ∀ x, M < x → φ x = 0 := fun x hx => (hMz x hx).self_of_nhds
  have hdφ0 : ∀ x, M < x → deriv φ x = 0 := fun x hx => by
    rw [(hMz x hx).deriv_eq]; simp
  have hψ0 : ∀ x, M < x → ψ =ᶠ[𝓝 x] 0 := fun x hx => by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [hψdef, hdφ0 y hy]
  have hdψ0 : ∀ x, M < x → deriv ψ x = 0 := fun x hx => by
    rw [(hψ0 x hx).deriv_eq]; simp
  set N := ⌈M⌉₊
  set c : ℝ := (N : ℝ) + 1 with hcdef
  have hc : M < c := lt_of_le_of_lt (Nat.le_ceil M) (lt_add_one _)
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨-, hP⟩ := profile_parts ρ hψd hψ' N
  obtain ⟨-, hE⟩ := euler_parts h0 h1 hh hd hφ' N
  have hA : eulerImage ρ φ = ∫ x in (0 : ℝ)..c, (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * deriv φ x := by
    rw [eulerImage, ← hψdef, setIntegral_Ioi_eq_intervalIntegral hc0
      (fun x hx => by simp only [hdψ0 x (lt_trans hc hx), mul_zero]), hP,
      (hψ0 c hc).self_of_nhds]
    simp only [Pi.zero_apply, mul_zero, hψdef, Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_mul, sub_zero, zero_sub, neg_neg]
    exact intervalIntegral.integral_congr fun x _ => by ring
  refine ⟨?_, ?_⟩
  · rw [hA, hE, hφ0 c hc, mul_zero, add_zero,
      setIntegral_Ioi_eq_intervalIntegral hc0 (fun x hx => by simp only [hφ0 x (lt_trans hc hx),
        mul_zero])]
    congr 2
    refine (tsum_eq_sum (s := Finset.range N) fun n hn => hφ0 _ ?_).symm
    have : (N : ℝ) ≤ n := by exact_mod_cast not_lt.mp (Finset.mem_range.not.mp hn)
    linarith
  · rw [hA, ← setIntegral_Ioi_eq_intervalIntegral hc0 (fun x hx => by
      simp only [hdφ0 x (lt_trans hc hx), mul_zero])]
    have hnull : (volume : Measure ℝ) (Set.range (fun n : ℕ => (n : ℝ))) = 0 :=
      (Set.countable_range _).measure_zero _
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hx0
    rw [deriv_zeroProfile_eq hx0 hx]

end Distribution


end CoPoissonJets

section ForcedChain
open scoped ContDiff

/-- The normalized profile jets h_k = (1/k!) ∂_κ^k (1 - g_κ) = [k = 0] - (1/k!) ∂_κ^k g_κ at κ₀. -/
def zeroJetProfile (κ₀ : ℂ) (k : ℕ) (x : ℝ) : ℂ := (if k = 0 then 1 else 0) - zeroJetDensity κ₀ k x

lemma zeroProfile_eq_one_sub_family {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (hh : ρ ≠ 1 / 2) (x : ℝ) :
    zeroProfile ρ x = 1 - zeroFamilyDensity (spectralKappa ρ) x := by
  rw [zeroProfile, ← coPoissonComplexDensity_eq_family h0 h1 hh, coPoissonComplexDensity,
    coPoissonOriginNormalizer_eq_brho h0 h1]

lemma zeroJetProfile_zero (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (hh : ρ ≠ 1 / 2) (x : ℝ) :
    zeroJetProfile (spectralKappa ρ) 0 x = zeroProfile ρ x := by
  rw [zeroJetProfile, zeroJetDensity_zero, if_pos rfl, zeroProfile_eq_one_sub_family h0 h1 hh]

/-- Leibniz for multiplication by the parameter. -/
lemma iteratedDeriv_id_mul {P : ℂ → ℂ} (hP : Differentiable ℂ P) (k : ℕ) (z : ℂ) :
    iteratedDeriv (k + 1) (fun w => w * P w) z =
      z * iteratedDeriv (k + 1) P z + (k + 1) * iteratedDeriv k P z := by
  have hL := iteratedDeriv_fun_mul (f := fun w : ℂ => w) (g := P) (n := k + 1) (x := z) contDiffAt_id
    (hP.contDiff.contDiffAt)
  rw [hL, Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ i ∈ Finset.range k, ((k + 1).choose (i + 1 + 1) : ℂ) *
      iteratedDeriv (i + 1 + 1) (fun w : ℂ => w) z * iteratedDeriv (k + 1 - (i + 1 + 1)) P z = 0 := by
    intro i _
    rw [iteratedDeriv_fun_id]
    simp
  rw [Finset.sum_eq_zero hz, iteratedDeriv_fun_id, iteratedDeriv_fun_id]
  simp only [zero_add, Nat.choose_zero_right, Nat.choose_one_right, if_true, one_ne_zero, if_false,
    Nat.sub_zero, Nat.add_sub_cancel]
  push_cast
  ring

/-- Bound for the profile family against a continuous compactly supported weight. -/
lemma profile_pairing_bound {w : ℝ → ℂ} (hw : Continuous w) (hws : HasCompactSupport w) (R : ℝ) :
    ∃ B : ℝ → ℝ, Integrable B (volume.restrict (Ioi 0)) ∧ ∀ κ : ℂ, ‖κ‖ ≤ R → ∀ x : ℝ,
      ‖(1 - zeroFamilyDensity κ x) * w x‖ ≤ B x ∧ ‖zeroFamilyDensity κ x * w x‖ ≤ B x := by
  set N := 3 + ⌈|R|⌉₊
  refine ⟨fun x => (1 + |R| * (1 + |x|) ^ N) * ‖w x‖, ?_, fun κ hκ x => ?_⟩
  · have hc : Continuous (fun x : ℝ => (1 + |R| * (1 + |x|) ^ N) * ‖w x‖) := by fun_prop
    have hs : HasCompactSupport (fun x : ℝ => (1 + |R| * (1 + |x|) ^ N) * ‖w x‖) :=
      hws.norm.mul_left
    exact (hc.integrable_of_hasCompactSupport hs).restrict
  · have hg := norm_zeroFamilyDensity_le_of_norm_le (hκ.trans (le_abs_self R)) x
    have hn : 0 ≤ |R| * (1 + |x|) ^ N := by positivity
    constructor
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
      rw [norm_one]; linarith
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hg.trans (by linarith)) (norm_nonneg _)

lemma integral_profile_entire {w : ℝ → ℂ} (hw : Continuous w) (hws : HasCompactSupport w) :
    Differentiable ℂ (fun κ => ∫ x in Ioi 0, (1 - zeroFamilyDensity κ x) * w x) ∧
    Differentiable ℂ (fun κ => ∫ x in Ioi 0, zeroFamilyDensity κ x * w x) ∧
    (∀ (k : ℕ) κ₀, iteratedDeriv k (fun κ => ∫ x in Ioi 0, (1 - zeroFamilyDensity κ x) * w x) κ₀ =
      (k.factorial : ℂ) * ∫ x in Ioi 0, zeroJetProfile κ₀ k x * w x) ∧
    (∀ (k : ℕ) κ₀, iteratedDeriv k (fun κ => ∫ x in Ioi 0, zeroFamilyDensity κ x * w x) κ₀ =
      (k.factorial : ℂ) * ∫ x in Ioi 0, zeroJetDensity κ₀ k x * w x) := by
  have hd1 : ∀ x, Differentiable ℂ (fun κ => (1 - zeroFamilyDensity κ x) * w x) := fun x =>
    ((differentiable_const _).sub (differentiable_zeroFamilyDensity x)).mul_const _
  have hd2 : ∀ x, Differentiable ℂ (fun κ => zeroFamilyDensity κ x * w x) := fun x =>
    (differentiable_zeroFamilyDensity x).mul_const _
  have hm1 : ∀ κ, Measurable (fun x => (1 - zeroFamilyDensity κ x) * w x) := fun κ =>
    (measurable_const.sub (measurable_zeroFamilyDensity κ)).mul hw.measurable
  have hm2 : ∀ κ, Measurable (fun x => zeroFamilyDensity κ x * w x) := fun κ =>
    (measurable_zeroFamilyDensity κ).mul hw.measurable
  have hb1 : ∀ R : ℝ, ∃ B : ℝ → ℝ, Integrable B (volume.restrict (Ioi 0)) ∧ ∀ κ : ℂ, ‖κ‖ ≤ R → ∀ x,
      ‖(1 - zeroFamilyDensity κ x) * w x‖ ≤ B x := fun R => by
    obtain ⟨B, hB, hb⟩ := profile_pairing_bound hw hws R
    exact ⟨B, hB, fun κ hκ x => (hb κ hκ x).1⟩
  have hb2 : ∀ R : ℝ, ∃ B : ℝ → ℝ, Integrable B (volume.restrict (Ioi 0)) ∧ ∀ κ : ℂ, ‖κ‖ ≤ R → ∀ x,
      ‖zeroFamilyDensity κ x * w x‖ ≤ B x := fun R => by
    obtain ⟨B, hB, hb⟩ := profile_pairing_bound hw hws R
    exact ⟨B, hB, fun κ hκ x => (hb κ hκ x).2⟩
  refine ⟨differentiable_integral_entire hd1 hm1 hb1, differentiable_integral_entire hd2 hm2 hb2,
    fun k κ₀ => ?_, fun k κ₀ => ?_⟩
  · rw [congrFun (iteratedDeriv_integral_entire hd1 hm1 hb1 k) κ₀, ← integral_const_mul]
    congr 1
    funext x
    rw [iteratedDeriv_mul_const_field (fun κ => 1 - zeroFamilyDensity κ x),
      iteratedDeriv_fun_sub contDiffAt_const ((differentiable_zeroFamilyDensity x).contDiff.contDiffAt),
      iteratedDeriv_const, zeroJetProfile, zeroJetDensity]
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    rcases eq_or_ne k 0 with hk | hk
    · subst hk; simp
    · simp only [hk, if_false]; field_simp; ring
  · rw [congrFun (iteratedDeriv_integral_entire hd2 hm2 hb2 k) κ₀, ← integral_const_mul]
    congr 1
    funext x
    rw [iteratedDeriv_mul_const_field (fun κ => zeroFamilyDensity κ x), zeroJetDensity]
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp

/-- R2-H1 differentiated forced chain, normalized: for every strip parameter ρ₀ ≠ 1/2, every k and
every positive-axis test ψ, with h_k the normalized profile jets at κ₀ and ψ₂ = (x² ψ')',
-∫ h_k ψ₂ = κ₀ (-∫ g_k ψ + [k = 0] Σ ψ(n)) + [k ≥ 1] (-∫ g_(k-1) ψ + [k = 1] Σ ψ(n)). -/
theorem zeroJetProfile_chain {ρ₀ : ℂ} (h0 : 0 < ρ₀.re) (h1 : ρ₀.re < 1) (hh : ρ₀ ≠ 1 / 2) (k : ℕ)
    {ψ : ℝ → ℂ} (hψ : CoPoissonJets.PositiveAxisTest ψ) :
    -(∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ₀) k x *
        deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv ψ y) x) =
      spectralKappa ρ₀ * (-(∫ x in Ioi 0, zeroJetDensity (spectralKappa ρ₀) k x * ψ x) +
          if k = 0 then ∑' n : ℕ, ψ (n + 1) else 0) +
        if k = 0 then 0 else
          (-(∫ x in Ioi 0, zeroJetDensity (spectralKappa ρ₀) (k - 1) x * ψ x) +
            if k = 1 then ∑' n : ℕ, ψ (n + 1) else 0) := by
  set κ₀ := spectralKappa ρ₀
  set c : ℂ := ∑' n : ℕ, ψ (n + 1)
  have hψc : ContDiff ℝ ∞ ψ := hψ.1
  have hdc : ContDiff ℝ ∞ (deriv ψ) := by simpa using hψc.iterate_deriv 1
  have hqc : ContDiff ℝ ∞ (fun y : ℝ => (y : ℂ) ^ 2 * deriv ψ y) :=
    ((Complex.ofRealCLM.contDiff).pow 2).mul hdc
  set ψ₂ := deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv ψ y)
  have hψ₂c : Continuous ψ₂ := hqc.continuous_deriv (by simp)
  have hψ₂s : HasCompactSupport ψ₂ := (hψ.2.1.deriv.mul_left).deriv
  have hψcont : Continuous ψ := hψc.continuous
  obtain ⟨hE, -, hEk, -⟩ := integral_profile_entire hψ₂c hψ₂s
  obtain ⟨-, hP, -, hPk⟩ := integral_profile_entire hψcont hψ.2.1
  set E : ℂ → ℂ := fun κ => -∫ x in Ioi 0, (1 - zeroFamilyDensity κ x) * ψ₂ x
  set P : ℂ → ℂ := fun κ => -(∫ x in Ioi 0, zeroFamilyDensity κ x * ψ x) + c
  have hPd : Differentiable ℂ P := (hP.neg).add_const c
  -- the identity holds near κ₀
  have heq : E =ᶠ[𝓝 κ₀] fun κ => κ * P κ := by
    filter_upwards [(isOpen_localJetDomain hh).mem_nhds (center_mem_localJetDomain hh h0 h1)] with κ hκ
    obtain ⟨hs0, hs1, hne, hr0, hr1, -⟩ := localJetDomain_mem hh hκ
    have hid := (CoPoissonJets.forced_euler_identity hs0 hs1 hne hψ).1
    rw [spectralKappa_zeroLocalInverse hh] at hid
    have hprof : ∀ x, zeroProfile (zeroLocalInverse ρ₀ κ) x = 1 - zeroFamilyDensity κ x := fun x => by
      rw [zeroProfile_eq_one_sub_family hr0 hr1 hne, spectralKappa_zeroLocalInverse hh]
    simp only [CoPoissonJets.eulerImage, hprof] at hid
    simp only [E, P]
    rw [hid]
    congr 1
    congr 1
    rw [← integral_neg]
    congr 1
    funext x
    ring
  have hk := heq.iteratedDeriv_eq k
  have hEk' : iteratedDeriv k E κ₀ = -((k.factorial : ℂ) * ∫ x in Ioi 0, zeroJetProfile κ₀ k x * ψ₂ x) := by
    simp only [E]
    rw [iteratedDeriv_fun_neg, hEk k κ₀]
  have hPj (j : ℕ) : iteratedDeriv j P κ₀ =
      (j.factorial : ℂ) * (-(∫ x in Ioi 0, zeroJetDensity κ₀ j x * ψ x) + if j = 0 then c else 0) := by
    simp only [P]
    have hA := iteratedDeriv_fun_add (f := fun κ => -∫ x in Ioi 0, zeroFamilyDensity κ x * ψ x)
      (g := fun _ => c) (n := j) (x := κ₀) (hP.neg.contDiff.contDiffAt) contDiffAt_const
    rw [hA, iteratedDeriv_fun_neg, hPk j κ₀, iteratedDeriv_const]
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp
    · simp only [hj, if_false]; ring
  have hf (j : ℕ) : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rcases eq_or_ne k 0 with hk0 | hk0
  · subst hk0
    simp only [iteratedDeriv_zero] at hk
    simp only [E, P] at hk
    rw [if_pos rfl, if_pos rfl, add_zero]
    have e1 : (∫ x in Ioi 0, zeroJetProfile κ₀ 0 x * ψ₂ x) = ∫ x in Ioi 0, (1 - zeroFamilyDensity κ₀ x) * ψ₂ x := by
      congr 1; funext x; rw [zeroJetProfile, zeroJetDensity_zero, if_pos rfl]
    have e2 : (∫ x in Ioi 0, zeroJetDensity κ₀ 0 x * ψ x) = ∫ x in Ioi 0, zeroFamilyDensity κ₀ x * ψ x := by
      congr 1; funext x; rw [zeroJetDensity_zero]
    rw [e1, e2]
    exact hk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    rw [iteratedDeriv_id_mul hPd j κ₀, hEk', hPj, hPj] at hk
    rw [if_neg hk0, if_neg hk0, add_zero, Nat.succ_sub_one]
    have hfs : ((j + 1).factorial : ℂ) = (j + 1) * (j.factorial : ℂ) := by
      push_cast [Nat.factorial_succ]; ring
    rw [hfs] at hk
    have hj1 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    apply mul_left_cancel₀ (mul_ne_zero hj1 (hf j))
    rw [show ((j : ℂ) + 1) * (j.factorial : ℂ) * (-(∫ x in Ioi 0, zeroJetProfile κ₀ (j + 1) x * ψ₂ x)) =
      -(((j : ℂ) + 1) * (j.factorial : ℂ) * ∫ x in Ioi 0, zeroJetProfile κ₀ (j + 1) x * ψ₂ x) by ring, hk]
    by_cases hj0 : j = 0
    · subst hj0; simp
    · have : j + 1 ≠ 1 := by omega
      have h3 : j + 1 ≠ 0 := Nat.succ_ne_zero j
      simp only [this, hj0, h3, if_false, add_zero]
      ring

end ForcedChain

section JetProperties

variable {ρ : ℂ}

/-- Fourier self-duality of every jet below the multiplicity, from the parameter limits. -/
theorem normalizedZeroMeasureJet_fourier (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) {k : ℕ}
    (hk : k < zeroJetOrder ρ) (φ : 𝓢(ℝ, ℂ)) :
    (normalizedZeroMeasureJet ρ k).integral ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =
      (normalizedZeroMeasureJet ρ k).integral φ := by
  rw [normalizedZeroMeasureJet_integral h0 h1 hh, normalizedZeroMeasureJet_integral h0 h1 hh,
    ← zeroFamilyFunctional_jet h0 h1 hh hk, ← zeroFamilyFunctional_jet h0 h1 hh hk]
  simp only [zeroFamilyFunctional_fourier]

theorem normalizedZeroMeasureJet_reflect (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) (k : ℕ)
    (φ : 𝓢(ℝ, ℂ)) :
    (normalizedZeroMeasureJet ρ k).integral (schwartzReflect φ) = (normalizedZeroMeasureJet ρ k).integral φ := by
  rw [normalizedZeroMeasureJet_integral h0 h1 hh, normalizedZeroMeasureJet_integral h0 h1 hh]
  congr 1
  · rw [← integral_neg_eq_self (fun x => zeroJetDensity (spectralKappa ρ) k x * φ x)]
    congr 1
    funext x
    rw [schwartzReflect_apply, zeroJetDensity_neg]
  · split_ifs
    · rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => if n = 0 then (0 : ℂ) else φ n)]
      refine tsum_congr (fun n => ?_)
      simp only [Equiv.neg_apply, neg_eq_zero, schwartzReflect_apply, Int.cast_neg]
    · rfl

theorem normalizedZeroMeasureJet_gap (k : ℕ) :
    (normalizedZeroMeasureJet ρ k).variationControl (Ioo (-1) 1) = 0 ∧
      (normalizedZeroMeasureJet ρ k).variationControl {0} = 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; rw [normalizedZeroMeasureJet_zero]; exact ⟨zeroMeasure_gap ρ, zeroMeasure_origin ρ⟩
  · rw [normalizedZeroMeasureJet_succ ρ hk]
    exact ⟨jetDensityMeasure_gap (fun x hx => zeroJetDensity_small _ _ hx),
      jetDensityMeasure_origin (fun x hx => zeroJetDensity_small _ _ hx)⟩

theorem normalizedZeroMeasureJet_even (k : ℕ) :
    Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).rePart.positive =
        (normalizedZeroMeasureJet ρ k).rePart.positive ∧
    Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).rePart.negative =
        (normalizedZeroMeasureJet ρ k).rePart.negative ∧
    Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).imPart.positive =
        (normalizedZeroMeasureJet ρ k).imPart.positive ∧
    Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).imPart.negative =
        (normalizedZeroMeasureJet ρ k).imPart.negative := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; rw [normalizedZeroMeasureJet_zero]; exact zeroMeasure_even ρ
  · rw [normalizedZeroMeasureJet_succ ρ hk]
    exact jetDensityMeasure_even (fun x => zeroJetDensity_neg _ _ x)

theorem normalizedZeroMeasureJet_hasLinearGrowth (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2)
    {k : ℕ} (hk : k < zeroJetOrder ρ) : (normalizedZeroMeasureJet ρ k).HasLinearGrowth := by
  rcases eq_or_ne k 0 with hk0 | hk0
  · subst hk0; rw [normalizedZeroMeasureJet_zero]; exact zeroMeasure_hasLinearGrowth h0 h1
  · rw [normalizedZeroMeasureJet_succ ρ hk0]
    obtain ⟨B, -, hB⟩ := zeroJetDensity_bounded h0 h1 hh hk
    exact jetDensityMeasure_hasLinearGrowth hB

lemma coPoissonPowerSums_one_sub (ρ : ℂ) (x : ℝ) :
    coPoissonPowerSums (1 - ρ) x = -coPoissonPowerSums ρ x := by
  unfold coPoissonPowerSums
  rw [show -(1 - ρ) = ρ - 1 by ring, show (1 - ρ) - 1 = -ρ by ring]
  ring

lemma coPoissonComplexDensity_one_sub (ρ : ℂ) :
    coPoissonComplexDensity (1 - ρ) = coPoissonComplexDensity ρ := by
  funext x
  unfold coPoissonComplexDensity
  rw [coPoissonPowerSums_one_sub, show coPoissonOriginNormalizer (1 - ρ) = -coPoissonOriginNormalizer ρ by
    unfold coPoissonOriginNormalizer; ring, neg_div_neg_eq]

lemma zeroMeasure_one_sub (ρ : ℂ) : zeroMeasure (1 - ρ) = zeroMeasure ρ := by
  have h := coPoissonComplexDensity_one_sub ρ
  unfold zeroMeasure coPoissonRealDensity
  simp only [h]

lemma spectralKappa_one_sub (ρ : ℂ) : spectralKappa (1 - ρ) = spectralKappa ρ := by
  unfold spectralKappa; ring

lemma spectralKappa_conj (ρ : ℂ) : spectralKappa (starRingEnd ℂ ρ) = starRingEnd ℂ (spectralKappa ρ) := by
  unfold spectralKappa; simp [map_sub, map_mul]

lemma normalizedZeroMeasureJet_one_sub (ρ : ℂ) (k : ℕ) :
    normalizedZeroMeasureJet (1 - ρ) k = normalizedZeroMeasureJet ρ k := by
  unfold normalizedZeroMeasureJet
  rw [zeroMeasure_one_sub]
  simp only [spectralKappa_one_sub]

lemma zeroLocalInverse_one_sub (ρ κ : ℂ) : zeroLocalInverse (1 - ρ) κ = 1 - zeroLocalInverse ρ κ := by
  have hr : localRadicand (1 - ρ) κ = localRadicand ρ κ := by
    unfold localRadicand; rw [spectralKappa_one_sub]; ring_nf
  unfold zeroLocalInverse
  rw [hr]
  ring

theorem normalizedZeroMeasureJet_conj (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) (k : ℕ)
    (φ : 𝓢(ℝ, ℂ)) :
    (normalizedZeroMeasureJet (starRingEnd ℂ ρ) k).integral φ =
      starRingEnd ℂ ((normalizedZeroMeasureJet ρ k).integral (complexSchwartzConj φ)) := by
  have h0' : 0 < (starRingEnd ℂ ρ).re := by rwa [Complex.conj_re]
  have h1' : (starRingEnd ℂ ρ).re < 1 := by rwa [Complex.conj_re]
  have hh' : starRingEnd ℂ ρ ≠ 1 / 2 := fun h => hh (by
    rw [← Complex.conj_conj ρ, h, map_div₀, map_one, map_ofNat])
  rw [normalizedZeroMeasureJet_integral h0' h1' hh', normalizedZeroMeasureJet_integral h0 h1 hh,
    map_sub, ← integral_conj]
  congr 1
  · congr 1
    funext x
    rw [map_mul, complexSchwartzConj_apply, Complex.conj_conj, spectralKappa_conj, zeroJetDensity_conj]
  · split_ifs
    · rw [Complex.conj_tsum]
      refine tsum_congr fun n => ?_
      split_ifs
      · simp
      · rw [complexSchwartzConj_apply, Complex.conj_conj]
    · simp

end JetProperties

section Roots
open scoped ContDiff

lemma integrableOn_zeroJetDensity_mul (κ₀ : ℂ) (k : ℕ) {w : ℝ → ℂ} (hw : Continuous w)
    (hws : HasCompactSupport w) :
    Integrable (fun x => zeroJetDensity κ₀ k x * w x) (volume.restrict (Ioi 0)) := by
  have hc : Continuous (fun x : ℝ => (‖κ₀‖ + 1) * (1 + |x|) ^ jetGrowthExponent κ₀ * ‖w x‖) := by
    fun_prop
  have hs : HasCompactSupport (fun x : ℝ => (‖κ₀‖ + 1) * (1 + |x|) ^ jetGrowthExponent κ₀ * ‖w x‖) :=
    hws.norm.mul_left
  refine ((hc.integrable_of_hasCompactSupport hs).restrict).mono'
    ((measurable_zeroJetDensity κ₀ k).mul hw.measurable).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_zeroJetDensity_le κ₀ k x) (norm_nonneg _)

lemma integral_zeroJetProfile_mul (κ₀ : ℂ) (k : ℕ) {w : ℝ → ℂ} (hw : Continuous w)
    (hws : HasCompactSupport w) :
    (∫ x in Ioi 0, zeroJetProfile κ₀ k x * w x) =
      (if k = 0 then ∫ x in Ioi 0, w x else 0) - ∫ x in Ioi 0, zeroJetDensity κ₀ k x * w x := by
  have hJ := integrableOn_zeroJetDensity_mul κ₀ k hw hws
  have hW : Integrable w (volume.restrict (Ioi 0)) := (hw.integrable_of_hasCompactSupport hws).restrict
  have e : (fun x => zeroJetProfile κ₀ k x * w x) =
      fun x => (if k = 0 then (1 : ℂ) else 0) * w x - zeroJetDensity κ₀ k x * w x := by
    funext x; rw [zeroJetProfile]; ring
  rw [e, integral_sub (hW.const_mul _) hJ, integral_const_mul]
  split_ifs <;> simp

/-- (H1.2) in the paper's form, tested on positive-axis tests, with ⟨G, ψ⟩ = Σ_(n ≥ 1) ψ(n) - ∫ ψ:
(L - κ₀) h₀ = κ₀ G, (L - κ₀) h₁ = h₀ + G and (L - κ₀) h_k = h_(k-1) for k ≥ 2, where
⟨L h, ψ⟩ = -∫ h (x² ψ')'. -/
theorem zeroJetProfile_forced_chain {ρ₀ : ℂ} (h0 : 0 < ρ₀.re) (h1 : ρ₀.re < 1) (hh : ρ₀ ≠ 1 / 2)
    (k : ℕ) {ψ : ℝ → ℂ} (hψ : CoPoissonJets.PositiveAxisTest ψ) :
    -(∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ₀) k x *
        deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv ψ y) x) -
      spectralKappa ρ₀ * (∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ₀) k x * ψ x) =
    if k = 0 then spectralKappa ρ₀ * ((∑' n : ℕ, ψ (n + 1)) - ∫ x in Ioi 0, ψ x)
    else if k = 1 then (∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ₀) 0 x * ψ x) +
      ((∑' n : ℕ, ψ (n + 1)) - ∫ x in Ioi 0, ψ x)
    else ∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ₀) (k - 1) x * ψ x := by
  have hc := zeroJetProfile_chain h0 h1 hh k hψ
  have hψc : Continuous ψ := hψ.1.continuous
  have hψs := hψ.2.1
  rw [hc, integral_zeroJetProfile_mul _ k hψc hψs]
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; simp only [if_true]; ring
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have hs : j.succ ≠ 0 := Nat.succ_ne_zero j
    simp only [hs, if_false, Nat.succ_sub_one, add_zero, zero_sub]
    by_cases hj : j = 0
    · subst hj
      simp only [Nat.succ_eq_add_one, zero_add, if_true, integral_zeroJetProfile_mul _ 0 hψc hψs]
      ring
    · have hj1 : j.succ ≠ 1 := by omega
      simp only [hj1, hj, if_false, integral_zeroJetProfile_mul _ j hψc hψs, add_zero, zero_sub]
      ring

/-- **R2-H1.** Let ρ be an actual zero with 0 < Re ρ < 1, of multiplicity m = `zeroJetOrder` ρ ≥ 1,
κ₀ = ρ(1 - ρ), and ρ(κ) the local holomorphic inverse through ρ (1 - 2ρ ≠ 0). For every derivative
index k < m the normalized κ-jet ν_k = `normalizedZeroMeasureJet` ρ k is a genuine locally finite
complex measure and:
- (parameter limits) on every Schwartz test, ν_k(φ) = (1/k!) ∂_κ^k [b⁻¹(V - (1-ρ)⁻¹(δ₀ + dx) - b D₀)]
  at κ₀ along ρ(κ), the actual normalized construction (CP1.7)/b; explicitly
  ν_k = (1/k!) ∂_κ^k g_κ(|x|) dx - [k = 0] Σ_(n≠0) δ_n (H1.1); ν₀ is the CP1 zero measure;
- the exact open unit gap and zero origin atom; even Jordan parts; linear variation growth;
- the jet densities are [k = 0] - ([k = 0] κ₀ + [k = 1]) B₂({|x|})/(2x²) + O(|x|⁻³);
- Fourier self-duality on Schwartz tests and as tempered distributions, also for the real part;
- the differentiated forced chain (H1.2) for the normalized profile jets h_k;
- reflection: 1 - ρ has the same multiplicity, the same node κ₀ and the same jets (its branch is
  1 - ρ(κ)), so it is not a separate node; conjugation: conj ρ has the same multiplicity and
  ν_k(conj ρ)(φ) = conj(ν_k(ρ)(conj φ)). -/
theorem copoisson_zero_jets_measures (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (k : ℕ) (hk : k < zeroJetOrder ρ) :
    1 ≤ zeroJetOrder ρ ∧ analyticOrderAt riemannZeta ρ = zeroJetOrder ρ ∧
    (zeroLocalInverse ρ (spectralKappa ρ) = ρ ∧ AnalyticAt ℂ (zeroLocalInverse ρ) (spectralKappa ρ) ∧
      deriv (zeroLocalInverse ρ) (spectralKappa ρ) = -1 / (2 * (ρ - 1 / 2)) ∧
      (∀ κ, spectralKappa (zeroLocalInverse ρ κ) = κ) ∧
      analyticOrderAt (fun κ => riemannZeta (zeroLocalInverse ρ κ)) (spectralKappa ρ) = zeroJetOrder ρ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral φ =
      iteratedDeriv k (fun κ => zeroFamilyFunctional (zeroLocalInverse ρ κ) φ) (spectralKappa ρ) /
        (k.factorial : ℂ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral φ =
      (∫ x, zeroJetDensity (spectralKappa ρ) k x * φ x) -
        if k = 0 then ∑' n : ℤ, (if n = 0 then (0 : ℂ) else φ n) else 0) ∧
    (∀ y : ℝ, zeroJetDensity (spectralKappa ρ) k y =
      iteratedDeriv k (fun κ => zeroFamilyDensity κ y) (spectralKappa ρ) / (k.factorial : ℂ)) ∧
    (k = 0 → normalizedZeroMeasureJet ρ k = zeroMeasure ρ) ∧
    (normalizedZeroMeasureJet ρ k).variationControl (Ioo (-1) 1) = 0 ∧
    (normalizedZeroMeasureJet ρ k).variationControl {0} = 0 ∧
    (Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).rePart.positive =
        (normalizedZeroMeasureJet ρ k).rePart.positive ∧
      Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).rePart.negative =
        (normalizedZeroMeasureJet ρ k).rePart.negative ∧
      Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).imPart.positive =
        (normalizedZeroMeasureJet ρ k).imPart.positive ∧
      Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).imPart.negative =
        (normalizedZeroMeasureJet ρ k).imPart.negative) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ |y| →
      ‖zeroJetDensity (spectralKappa ρ) k y -
        ((if k = 0 then 1 else 0) - ((if k = 0 then spectralKappa ρ else 0) + (if k = 1 then 1 else 0)) *
          ((bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2)))‖ ≤ C * |y| ^ (-3 : ℝ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =
      (normalizedZeroMeasureJet ρ k).integral φ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral (schwartzReflect φ) =
      (normalizedZeroMeasureJet ρ k).integral φ) ∧
    (∃ hL : (normalizedZeroMeasureJet ρ k).HasLinearGrowth,
      𝓕 ((normalizedZeroMeasureJet ρ k).distributionOfLinearGrowth hL) =
          (normalizedZeroMeasureJet ρ k).distributionOfLinearGrowth hL ∧
        𝓕 ((normalizedZeroMeasureJet ρ k).rePart.distributionOfLinearGrowth
            ((normalizedZeroMeasureJet ρ k).re_hasLinearGrowth hL)) =
          (normalizedZeroMeasureJet ρ k).rePart.distributionOfLinearGrowth
            ((normalizedZeroMeasureJet ρ k).re_hasLinearGrowth hL)) ∧
    (∀ ψ : ℝ → ℂ, CoPoissonJets.PositiveAxisTest ψ →
      -(∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) k x *
          deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv ψ y) x) -
        spectralKappa ρ * (∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) k x * ψ x) =
      if k = 0 then spectralKappa ρ * ((∑' n : ℕ, ψ (n + 1)) - ∫ x in Ioi 0, ψ x)
      else if k = 1 then (∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) 0 x * ψ x) +
        ((∑' n : ℕ, ψ (n + 1)) - ∫ x in Ioi 0, ψ x)
      else ∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) (k - 1) x * ψ x) ∧
    (zeroJetOrder (1 - ρ) = zeroJetOrder ρ ∧ spectralKappa (1 - ρ) = spectralKappa ρ ∧
      normalizedZeroMeasureJet (1 - ρ) k = normalizedZeroMeasureJet ρ k ∧
      (∀ κ, zeroLocalInverse (1 - ρ) κ = 1 - zeroLocalInverse ρ κ) ∧
      ∀ φ : 𝓢(ℝ, ℂ), iteratedDeriv k (fun κ => zeroFamilyFunctional (1 - zeroLocalInverse ρ κ) φ)
          (spectralKappa ρ) / (k.factorial : ℂ) = (normalizedZeroMeasureJet ρ k).integral φ) ∧
    (zeroJetOrder (starRingEnd ℂ ρ) = zeroJetOrder ρ ∧
      ∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet (starRingEnd ℂ ρ) k).integral φ =
        starRingEnd ℂ ((normalizedZeroMeasureJet ρ k).integral (complexSchwartzConj φ))) := by
  have hh := zero_ne_half hz
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hL := normalizedZeroMeasureJet_hasLinearGrowth h0 h1 hh hk
  have hF := normalizedZeroMeasureJet_fourier h0 h1 hh hk
  have hR := normalizedZeroMeasureJet_reflect h0 h1 hh k
  have hint := normalizedZeroMeasureJet_integral h0 h1 hh k
  obtain ⟨hgap, horig⟩ := normalizedZeroMeasureJet_gap (ρ := ρ) k
  -- reflected zero
  have h0r : 0 < (1 - ρ).re := by simp; linarith
  have h1r : (1 - ρ).re < 1 := by simp; linarith
  have hhr : 1 - ρ ≠ 1 / 2 := fun h => hh (by linear_combination -h)
  have hmr := zeroJetOrder_one_sub h0 h1
  refine ⟨one_le_zeroJetOrder hz hρ1, analyticOrderAt_riemannZeta_eq hρ1,
    ⟨zeroLocalInverse_center ρ, analyticAt_zeroLocalInverse hh, deriv_zeroLocalInverse_center hh,
      spectralKappa_zeroLocalInverse hh, analyticOrderAt_riemannZeta_comp_inverse hh hρ1⟩,
    fun φ => by rw [zeroFamilyFunctional_jet h0 h1 hh hk, hint], hint, fun y => rfl,
    fun hk0 => by subst hk0; exact normalizedZeroMeasureJet_zero ρ, hgap, horig,
    normalizedZeroMeasureJet_even k, zeroJetDensity_tail h0 h1 hh hk, hF, hR,
    ⟨hL, by ext φ; exact hF φ, rePart_fourierSelfdual_of_complex _ hL hF hR⟩,
    fun ψ hψ => zeroJetProfile_forced_chain h0 h1 hh k hψ,
    ⟨hmr, spectralKappa_one_sub ρ, normalizedZeroMeasureJet_one_sub ρ k, zeroLocalInverse_one_sub ρ,
      fun φ => ?_⟩, ⟨zeroJetOrder_conj hρ1, normalizedZeroMeasureJet_conj h0 h1 hh k⟩⟩
  have hkr : k < zeroJetOrder (1 - ρ) := by rw [hmr]; exact hk
  have hj := zeroFamilyFunctional_jet h0r h1r hhr hkr φ
  simp only [zeroLocalInverse_one_sub, spectralKappa_one_sub] at hj
  rw [hj, hint]

end Roots

end Zeta23.OPICAFollowup
