import Zeta23.CCM.OriginalDetectorDividedLobeBounds
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier coefficients of the literal divided original lobe

These are Mathlib's actual `fourierCoeffOn` on `[0,L]`, with its `1/L`
normalization. Repeated integration by parts uses the source-derived
endpoint jets of the literal quotient. No coefficient estimate is supplied.
Summability, reconstruction and truncation tails are separate obligations.
-/

noncomputable section

open Set Metric Complex
open scoped Topology

namespace Zeta23.CCM

/-- The literal interval Fourier coefficient of the divided original lobe. -/
def originalDetectorDividedLobeFourierCoeff (s L c : ℝ) (hL : 0 < L) (n : ℤ) : ℂ :=
  fourierCoeffOn hL (originalDetectorDividedLobe s L c) n

private theorem norm_fourierCoeffOn_le {L C : ℝ} (hL : 0 < L)
    (f : ℝ → ℂ) (n : ℤ) (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖fourierCoeffOn hL f n‖ ≤ C := by
  have : Fact (0 < L - 0) := ⟨by simpa using hL⟩
  rw [fourierCoeffOn_eq_integral]
  rw [norm_smul, Real.norm_eq_abs]
  have hb : ‖∫ x in (0 : ℝ)..L, fourier (-n) (x : AddCircle (L - 0)) • f x‖ ≤
      C * |L - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using hf x
  calc
    _ ≤ |1 / (L - 0)| * (C * |L - 0|) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = C := by rw [sub_zero, abs_div, abs_one, abs_of_pos hL]; field_simp

private theorem dividedLobe_fourierCoeffOn_jet_step
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    {n : ℤ} (hn : n ≠ 0) (m : ℕ) :
    fourierCoeffOn (by linarith : 0 < L)
        (iteratedDeriv m (originalDetectorDividedLobe s L c)) n =
      ((L : ℂ) / (2 * Real.pi * I * n)) *
        fourierCoeffOn (by linarith : 0 < L)
          (iteratedDeriv (m + 1) (originalDetectorDividedLobe s L c)) n := by
  have hf := originalDetectorDividedLobe_contDiff hs hL hleft hright
  have hm : (m : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (m : ℕ∞) < ⊤ from WithTop.coe_lt_top m)
  have hm' : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show ((m + 1 : ℕ) : ℕ∞) ≤ ⊤ from le_top)
  have hderiv : ∀ x : ℝ,
      HasDerivAt (iteratedDeriv m (originalDetectorDividedLobe s L c))
        (iteratedDeriv (m + 1) (originalDetectorDividedLobe s L c) x) x := by
    intro x
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv m hm x).hasDerivAt
  have hb := fourierCoeffOn_of_hasDerivAt (by linarith : 0 < L) hn
    (fun x _ => hderiv x) ((hf.continuous_iteratedDeriv (m + 1) hm').intervalIntegrable 0 L)
  have he := originalDetectorDividedLobe_endpoint_jets hs hleft hright m
  simp only [he.1, he.2, sub_self, mul_zero, zero_sub, Complex.ofReal_zero, sub_zero] at hb
  rw [hb]
  field_simp

/-- Repeated integration by parts for the actual divided lobe. Every
boundary term is eliminated by its already proved endpoint jets. -/
theorem originalDetectorDividedLobeFourierCoeff_eq_iteratedDeriv
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    {n : ℤ} (hn : n ≠ 0) (m : ℕ) :
    originalDetectorDividedLobeFourierCoeff s L c (by linarith) n =
      ((L : ℂ) / (2 * Real.pi * I * n)) ^ m *
        fourierCoeffOn (by linarith : 0 < L)
          (iteratedDeriv m (originalDetectorDividedLobe s L c)) n := by
  induction m with
  | zero => simp [originalDetectorDividedLobeFourierCoeff]
  | succ m ih =>
    rw [ih, dividedLobe_fourierCoeffOn_jet_step hs hL hleft hright hn m, pow_succ]
    ring_nf

private theorem norm_dividedLobe_fourier_factor {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ‖(L : ℂ) / (2 * Real.pi * I * n)‖ = L / (2 * Real.pi * |(n : ℝ)|) := by
  simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast,
    Complex.norm_I, norm_ofNat, abs_of_pos Real.pi_pos, abs_of_pos hL, mul_one]

/-- The source-derived arbitrary-order bound for the literal Fourier
coefficient, with the true interval normalization and frequency scale. -/
theorem originalDetectorDividedLobeFourierCoeff_le_gevrey_order
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    {n : ℤ} (hn : n ≠ 0) (m : ℕ) :
    ‖originalDetectorDividedLobeFourierCoeff s L c (by linarith) n‖ ≤
      (4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)) * L ^ 8 *
        (((12 / (UniversalSinc.gevreyMomentScale s) ^ 2 + 2) * L) /
          (2 * Real.pi * |(n : ℝ)|)) ^ m * (Nat.factorial m : ℝ) ^ 2 := by
  rw [originalDetectorDividedLobeFourierCoeff_eq_iteratedDeriv hs hL hleft hright hn m,
    norm_mul, norm_pow, norm_dividedLobe_fourier_factor (by linarith)]
  have hb := norm_fourierCoeffOn_le (by linarith : 0 < L)
    (iteratedDeriv m (originalDetectorDividedLobe s L c)) n
    (originalDetectorDividedLobe_iteratedDeriv_le_gevrey hs hL hleft hright m)
  refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_
  unfold originalDetectorDividedLobeJetBudget
  rw [mul_div_assoc, mul_pow, div_pow]
  ring_nf

private theorem gevrey_order_two_floor_bound {b t : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) (hbt : b * t ^ 2 ≤ 1 / 4) :
    b ^ Nat.floor t * (Nat.factorial (Nat.floor t) : ℝ) ^ 2 ≤
      4 * Real.exp (-(Real.log 4) * t) := by
  let m := Nat.floor t
  have hm : (m : ℝ) ≤ t := Nat.floor_le ht
  have hmsq : (m : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - (m : ℝ))]
  have hbase : b * (m : ℝ) ^ 2 ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left hmsq hb).trans hbt
  have hfac : (Nat.factorial m : ℝ) ≤ (m : ℝ) ^ m := by
    exact_mod_cast Nat.factorial_le_pow m
  have he : Real.exp (-Real.log 4) = (1 / 4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  calc
    b ^ m * (Nat.factorial m : ℝ) ^ 2 ≤ b ^ m * ((m : ℝ) ^ m) ^ 2 := by
      gcongr
    _ = (b * (m : ℝ) ^ 2) ^ m := by
      simp only [mul_pow, ← pow_mul, Nat.mul_comm]
    _ ≤ (1 / 4 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) hbase m
    _ = Real.exp ((m : ℝ) * (-Real.log 4)) := by rw [← he, Real.exp_nat_mul]
    _ ≤ Real.exp (Real.log 4 - Real.log 4 * t) := by
      apply Real.exp_le_exp.mpr
      have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
      have hfloor : t < (m : ℝ) + 1 := Nat.lt_floor_add_one t
      nlinarith
    _ = 4 * Real.exp (-(Real.log 4) * t) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      congr 1
      ring_nf

/-- The specified derivative order balancing factorial growth against the
actual Fourier frequency. -/
def originalDetectorDividedLobeFourierOrder (s L : ℝ) (n : ℤ) : ℕ :=
  Nat.floor (Real.sqrt ((Real.pi * |(n : ℝ)|) /
    (2 * (12 / (UniversalSinc.gevreyMomentScale s) ^ 2 + 2) * L)))

/-- Optimizing the actual arbitrary-order estimate gives stretched
exponential frequency decay, with constants derived from the source. -/
theorem originalDetectorDividedLobeFourierCoeff_le_stretched_exp
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    {n : ℤ} (hn : n ≠ 0) :
    ‖originalDetectorDividedLobeFourierCoeff s L c (by linarith) n‖ ≤
      4 * (4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)) * L ^ 8 *
        Real.exp (-(Real.log 4) * Real.sqrt ((Real.pi * |(n : ℝ)|) /
          (2 * (12 / (UniversalSinc.gevreyMomentScale s) ^ 2 + 2) * L))) := by
  let H : ℝ := 12 / (UniversalSinc.gevreyMomentScale s) ^ 2 + 2
  let C : ℝ := 4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)
  let b : ℝ := H * L / (2 * Real.pi * |(n : ℝ)|)
  let t : ℝ := Real.sqrt (Real.pi * |(n : ℝ)| / (2 * H * L))
  have hH : 0 < H := by dsimp [H]; positivity
  have hLp : 0 < L := by linarith
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnabs : 0 < |(n : ℝ)| := abs_pos.mpr hnreal
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hbt : b * t ^ 2 ≤ 1 / 4 := by
    dsimp [b, t]
    rw [Real.sq_sqrt (by positivity)]
    have hHne := hH.ne'
    have hLne := hLp.ne'
    have hpi := Real.pi_pos.ne'
    have hna := hnabs.ne'
    field_simp
    norm_num
  have hopt := gevrey_order_two_floor_bound hb ht hbt
  have harb := originalDetectorDividedLobeFourierCoeff_le_gevrey_order
    hs hL hleft hright hn (originalDetectorDividedLobeFourierOrder s L n)
  change ‖originalDetectorDividedLobeFourierCoeff s L c _ n‖ ≤
    4 * C * L ^ 8 * Real.exp (-(Real.log 4) * t)
  change ‖originalDetectorDividedLobeFourierCoeff s L c _ n‖ ≤
    C * L ^ 8 * b ^ Nat.floor t * (Nat.factorial (Nat.floor t) : ℝ) ^ 2 at harb
  calc
    _ ≤ C * L ^ 8 * (b ^ Nat.floor t * (Nat.factorial (Nat.floor t) : ℝ) ^ 2) := by
      simpa only [mul_assoc] using harb
    _ ≤ C * L ^ 8 * (4 * Real.exp (-(Real.log 4) * t)) :=
      mul_le_mul_of_nonneg_left hopt (by dsimp [C]; positivity)
    _ = _ := by ring_nf

/-- Positive decay rate depending only on the original source width. -/
def originalDetectorDividedLobeFourierDecayRate (s : ℝ) : ℝ :=
  Real.log 4 * Real.sqrt (Real.pi /
    (2 * (12 / (UniversalSinc.gevreyMomentScale s) ^ 2 + 2)))

theorem originalDetectorDividedLobeFourierDecayRate_pos (s : ℝ) :
    0 < originalDetectorDividedLobeFourierDecayRate s := by
  unfold originalDetectorDividedLobeFourierDecayRate
  exact mul_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by positivity))

/-- Equivalent decay form making the aperture scaling `sqrt(|n|/L)`
explicit. The prefactor and positive decay constant are source-derived. -/
theorem originalDetectorDividedLobeFourierCoeff_le_exp_sqrt_frequency
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    {n : ℤ} (hn : n ≠ 0) :
    ‖originalDetectorDividedLobeFourierCoeff s L c (by linarith) n‖ ≤
      4 * (4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)) * L ^ 8 *
        Real.exp (-originalDetectorDividedLobeFourierDecayRate s *
          Real.sqrt (|(n : ℝ)| / L)) := by
  have hb := originalDetectorDividedLobeFourierCoeff_le_stretched_exp hs hL hleft hright hn
  let H : ℝ := 12 / (UniversalSinc.gevreyMomentScale s) ^ 2 + 2
  have hH : 0 < H := by dsimp [H]; positivity
  have hLp : 0 < L := by linarith
  have hratio : (Real.pi * |(n : ℝ)|) / (2 * H * L) =
      (Real.pi / (2 * H)) * (|(n : ℝ)| / L) := by ring_nf
  change ‖originalDetectorDividedLobeFourierCoeff s L c _ n‖ ≤
    4 * (4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)) * L ^ 8 *
      Real.exp (-(Real.log 4) * Real.sqrt ((Real.pi * |(n : ℝ)|) / (2 * H * L))) at hb
  rw [hratio, Real.sqrt_mul (by positivity)] at hb
  unfold originalDetectorDividedLobeFourierDecayRate
  convert hb using 1
  congr 2
  dsimp [H]
  ring_nf

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierCoeff_eq_iteratedDeriv
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierCoeff_le_gevrey_order
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierCoeff_le_stretched_exp
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierDecayRate_pos
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierCoeff_le_exp_sqrt_frequency
