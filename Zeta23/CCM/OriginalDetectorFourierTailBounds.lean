import Zeta23.CCM.OriginalDetectorFourierCoefficientBounds
import Zeta23.CCM.OriginalDetectorFourierScalarTailBounds
import Mathlib.Analysis.PSeries

/-!
# Actual Fourier reconstruction and tails of the divided original lobe

The coefficients and periodized jets here are the literal Mathlib Fourier
objects. Summability is derived from source bounds; no reconstruction or
truncation estimate is a producer premise.
-/

noncomputable section

open Set Metric Complex
open scoped Topology

namespace Zeta23.CCM

/-- The true angular Fourier multiplier at the signed integer frequency. -/
def originalDetectorFourierFrequency (L : ℝ) (n : ℤ) : ℂ :=
  2 * Real.pi * I * n / (L : ℂ)

/-- The coefficient prescribed by differentiating the actual Fourier mode. -/
def originalDetectorDividedLobeFourierJetCoeff (s L c : ℝ) (hL : 0 < L)
    (r : ℕ) (n : ℤ) : ℂ :=
  originalDetectorFourierFrequency L n ^ r *
    originalDetectorDividedLobeFourierCoeff s L c hL n

private theorem norm_originalDetectorFourierFrequency {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ‖originalDetectorFourierFrequency L n‖ = 2 * Real.pi * |(n : ℝ)| / L := by
  simp only [originalDetectorFourierFrequency, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_intCast, Complex.norm_I, norm_ofNat,
    abs_of_pos Real.pi_pos, abs_of_pos hL, mul_one]

private theorem jetCoeff_inverse_square_bound
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (r : ℕ) {n : ℤ} (hn : n ≠ 0) :
    ‖originalDetectorDividedLobeFourierJetCoeff s L c (by linarith) r n‖ ≤
      ((4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)) * L ^ 8 *
        (12 / (UniversalSinc.gevreyMomentScale s) ^ 2 + 2) ^ (r + 2) *
        (Nat.factorial (r + 2) : ℝ) ^ 2 * (L / (2 * Real.pi)) ^ 2) *
          (1 / (n : ℝ) ^ 2) := by
  have hLp : 0 < L := by linarith
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnabs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr hnreal
  have hb := originalDetectorDividedLobeFourierCoeff_le_gevrey_order
    hs hL hleft hright hn (r + 2)
  unfold originalDetectorDividedLobeFourierJetCoeff
  rw [norm_mul, norm_pow, norm_originalDetectorFourierFrequency hLp]
  refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_
  simp only [pow_add, mul_pow, div_pow]
  have hpi := Real.pi_pos.ne'
  have hLne := hLp.ne'
  rw [← sq_abs (n : ℝ)]
  field_simp

/-- All signed Fourier jet coefficients are absolutely summable. This
holds for every finite order, and in particular for orders zero through three. -/
theorem originalDetectorDividedLobeFourierJetCoeff_summable
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) (r : ℕ) :
    Summable (originalDetectorDividedLobeFourierJetCoeff s L c (by linarith) r) := by
  let K : ℝ := (4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)) * L ^ 8 *
    (12 / (UniversalSinc.gevreyMomentScale s) ^ 2 + 2) ^ (r + 2) *
    (Nat.factorial (r + 2) : ℝ) ^ 2 * (L / (2 * Real.pi)) ^ 2
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  apply (hp.mul_left K).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  exact jetCoeff_inverse_square_bound hs hL hleft hright r hn

theorem originalDetectorDividedLobeFourierCoeff_summable
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) :
    Summable (originalDetectorDividedLobeFourierCoeff s L c (by linarith)) := by
  exact (originalDetectorDividedLobeFourierJetCoeff_summable hs hL hleft hright 0).congr
    (fun n => by simp only [originalDetectorDividedLobeFourierJetCoeff, pow_zero, one_mul])

/-- Differentiating the actual lobe gives exactly the expected signed
Fourier multiplier, including the zero frequency. -/
theorem originalDetectorDividedLobeFourierJetCoeff_eq
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) (r : ℕ) (n : ℤ) :
    originalDetectorDividedLobeFourierJetCoeff s L c (by linarith) r n =
      fourierCoeffOn (by linarith : 0 < L)
        (iteratedDeriv r (originalDetectorDividedLobe s L c)) n := by
  by_cases hn : n = 0
  · subst n
    cases r with
    | zero => simp [originalDetectorDividedLobeFourierJetCoeff,
        originalDetectorDividedLobeFourierCoeff]
    | succ r =>
      have hf := originalDetectorDividedLobe_contDiff hs hL hleft hright
      have hm : (r : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (show (r : ℕ∞) < ⊤ from WithTop.coe_lt_top r)
      have hm' : ((r + 1 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (show ((r + 1 : ℕ) : ℕ∞) ≤ ⊤ from le_top)
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := L)
        (f' := iteratedDeriv (r + 1) (originalDetectorDividedLobe s L c))
        (fun x _ => by simpa only [iteratedDeriv_succ] using
          (hf.differentiable_iteratedDeriv r hm x).hasDerivAt)
        ((hf.continuous_iteratedDeriv (r + 1) hm').intervalIntegrable 0 L)
      have he := originalDetectorDividedLobe_endpoint_jets hs hleft hright r
      rw [he.1, he.2, sub_self] at hi
      have : Fact (0 < L - 0) := ⟨by linarith⟩
      simp only [originalDetectorDividedLobeFourierJetCoeff,
        originalDetectorFourierFrequency, Int.cast_zero, mul_zero, zero_div,
        zero_pow (Nat.succ_ne_zero _), zero_mul]
      rw [fourierCoeffOn_eq_integral]
      simp only [neg_zero, fourier_zero, one_smul, hi, smul_zero]
  · have he := originalDetectorDividedLobeFourierCoeff_eq_iteratedDeriv
      hs hL hleft hright hn r
    have hncomplex : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hLcomplex : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hpicomplex : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hfactor : originalDetectorFourierFrequency L n *
        ((L : ℂ) / (2 * Real.pi * I * n)) = 1 := by
      unfold originalDetectorFourierFrequency
      field_simp
    unfold originalDetectorDividedLobeFourierJetCoeff
    rw [he, ← mul_assoc, ← mul_pow, hfactor, one_pow, one_mul]

/-- Continuous periodization of each actual jet, with equality of endpoint
values supplied by compact support rather than by a producer assumption. -/
def originalDetectorDividedLobePeriodicJet
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) (r : ℕ) :
    C(AddCircle L, ℂ) := by
  have : Fact (0 < L) := ⟨by linarith⟩
  refine ⟨AddCircle.liftIoc L 0 (iteratedDeriv r (originalDetectorDividedLobe s L c)), ?_⟩
  apply AddCircle.liftIoc_zero_continuous
  · have he := originalDetectorDividedLobe_endpoint_jets hs hleft hright r
    rw [he.1, he.2]
  · have hf := originalDetectorDividedLobe_contDiff hs hL hleft hright
    apply (hf.continuous_iteratedDeriv r _).continuousOn
    exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)

theorem originalDetectorDividedLobePeriodicJet_fourierCoeff
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) (r : ℕ) (n : ℤ) :
    letI : Fact (0 < L) := ⟨by linarith⟩
    fourierCoeff (originalDetectorDividedLobePeriodicJet hs hL hleft hright r) n =
      originalDetectorDividedLobeFourierJetCoeff s L c (by linarith) r n := by
  have : Fact (0 < L) := ⟨by linarith⟩
  rw [originalDetectorDividedLobeFourierJetCoeff_eq hs hL hleft hright]
  simpa only [zero_add, originalDetectorDividedLobePeriodicJet, ContinuousMap.coe_mk] using
    fourierCoeff_liftIoc_eq (T := L)
      (a := (0 : ℝ)) (iteratedDeriv r (originalDetectorDividedLobe s L c)) n

/-- Actual pointwise reconstruction on the entire period circle, for all
jets. This is Mathlib's Fourier reconstruction theorem applied to the
continuous periodization and the proved summability. -/
theorem originalDetectorDividedLobePeriodicJet_hasSum
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) (r : ℕ) (x : AddCircle L) :
    letI : Fact (0 < L) := ⟨by linarith⟩
    HasSum (fun n : ℤ =>
      originalDetectorDividedLobeFourierJetCoeff s L c (by linarith) r n *
        fourier n x)
      (originalDetectorDividedLobePeriodicJet hs hL hleft hright r x) := by
  have : Fact (0 < L) := ⟨by linarith⟩
  have hcoeff : fourierCoeff (originalDetectorDividedLobePeriodicJet hs hL hleft hright r) =
      originalDetectorDividedLobeFourierJetCoeff s L c (by linarith) r := by
    funext n
    exact originalDetectorDividedLobePeriodicJet_fourierCoeff hs hL hleft hright r n
  have hsum := originalDetectorDividedLobeFourierJetCoeff_summable hs hL hleft hright r
  rw [← hcoeff] at hsum
  simpa only [hcoeff, smul_eq_mul] using
    has_pointwise_sum_fourier_series_of_summable hsum x

/-- The actual circle lift agrees with the actual source jet on the
closed period interval, including both endpoints. -/
theorem originalDetectorDividedLobePeriodicJet_eq_on_interval
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (r : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    originalDetectorDividedLobePeriodicJet hs hL hleft hright r (x : AddCircle L) =
      iteratedDeriv r (originalDetectorDividedLobe s L c) x := by
  have : Fact (0 < L) := ⟨by linarith⟩
  change AddCircle.liftIoc L 0 (iteratedDeriv r (originalDetectorDividedLobe s L c))
    (x : AddCircle L) = _
  by_cases hzero : x = 0
  · subst x
    have hp : ((0 : ℝ) : AddCircle L) = (L : AddCircle L) := by
      simpa only [zero_add] using (AddCircle.coe_add_period L (0 : ℝ)).symm
    rw [hp, AddCircle.liftIoc_zero_coe_apply (show L ∈ Ioc 0 L from ⟨by linarith, le_rfl⟩)]
    have he := originalDetectorDividedLobe_endpoint_jets hs hleft hright r
    rw [he.1, he.2]
  · exact AddCircle.liftIoc_zero_coe_apply ⟨lt_of_le_of_ne hx.1 (Ne.symm hzero), hx.2⟩

/-- Genuine source-jet reconstruction throughout `[0,L]`. -/
theorem originalDetectorDividedLobeFourierJet_hasSum_on_interval
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (r : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    letI : Fact (0 < L) := ⟨by linarith⟩
    HasSum (fun n : ℤ =>
      originalDetectorDividedLobeFourierJetCoeff s L c (by linarith) r n *
        fourier n (x : AddCircle L))
      (iteratedDeriv r (originalDetectorDividedLobe s L c) x) := by
  have : Fact (0 < L) := ⟨by linarith⟩
  rw [← originalDetectorDividedLobePeriodicJet_eq_on_interval hs hL hleft hright r hx]
  exact originalDetectorDividedLobePeriodicJet_hasSum hs hL hleft hright r (x : AddCircle L)

/-- The genuine signed-frequency partial sum, with the mandated raw
cutoff reserving exactly four degrees for the sine multiplier. -/
def originalDetectorDividedLobeFourierPartialJet (s L c : ℝ) (hL : 0 < L)
    (r : ℕ) (x : ℝ) : ℂ :=
  letI : Fact (0 < L) := ⟨hL⟩
  ∑ n ∈ Finset.Icc (-(originalDetectorRawCutoff L : ℤ)) (originalDetectorRawCutoff L : ℤ),
    originalDetectorDividedLobeFourierJetCoeff s L c hL r n *
      fourier n (x : AddCircle L)

/-- Actual norm tail of the literal coefficients. Its bound must be proved
from those coefficients; this is a definition rather than an input budget. -/
def originalDetectorDividedLobeFourierJetTail (s L c : ℝ) (hL : 0 < L)
    (r : ℕ) : ℝ :=
  ∑' n : ℤ, if originalDetectorRawCutoff L < n.natAbs then
    ‖originalDetectorDividedLobeFourierJetCoeff s L c hL r n‖ else 0

theorem originalDetectorDividedLobeFourierPartialJet_hasDerivAt
    (s L c : ℝ) (hL : 0 < L) (r : ℕ) (x : ℝ) :
    HasDerivAt (originalDetectorDividedLobeFourierPartialJet s L c hL r)
      (originalDetectorDividedLobeFourierPartialJet s L c hL (r + 1) x) x := by
  have : Fact (0 < L) := ⟨hL⟩
  unfold originalDetectorDividedLobeFourierPartialJet
  apply HasDerivAt.fun_sum
  intro n hn
  convert (hasDerivAt_fourier L n x).const_mul
    (originalDetectorDividedLobeFourierJetCoeff s L c hL r n) using 1 <;>
    first | rfl | (simp only [originalDetectorDividedLobeFourierJetCoeff,
      originalDetectorFourierFrequency, pow_succ]; ring_nf)

/-- The finite weighted sums are the actual iterated derivatives of the
raw partial sum, rather than a formally unrelated family of jet values. -/
theorem originalDetectorDividedLobeFourierPartialJet_iteratedDeriv
    (s L c : ℝ) (hL : 0 < L) (r : ℕ) :
    iteratedDeriv r (originalDetectorDividedLobeFourierPartialJet s L c hL 0) =
      originalDetectorDividedLobeFourierPartialJet s L c hL r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (originalDetectorDividedLobeFourierPartialJet_hasDerivAt s L c hL r x).deriv

/-- The norm tail is absolutely convergent, derived from the actual jet
coefficients for every finite derivative order. -/
theorem originalDetectorDividedLobeFourierJetTail_summable
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) (r : ℕ) :
    Summable (fun n : ℤ => if originalDetectorRawCutoff L < n.natAbs then
      ‖originalDetectorDividedLobeFourierJetCoeff s L c (by linarith) r n‖ else 0) := by
  classical
  have hh := (originalDetectorDividedLobeFourierJetCoeff_summable hs hL hleft hright r).norm
  apply hh.of_norm_bounded
  intro n
  split_ifs
  · simp only [Real.norm_eq_abs, abs_norm, le_refl]
  · simp only [Real.norm_eq_abs, abs_zero]
    exact norm_nonneg _

/-- Uniform pointwise jet error against the literal signed coefficient
tail at the fixed raw cutoff. No tail estimate is supplied by the caller. -/
theorem originalDetectorDividedLobeFourierPartialJet_error_le_tail
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (r : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖iteratedDeriv r (originalDetectorDividedLobe s L c) x -
      originalDetectorDividedLobeFourierPartialJet s L c (by linarith) r x‖ ≤
        originalDetectorDividedLobeFourierJetTail s L c (by linarith) r := by
  classical
  have : Fact (0 < L) := ⟨by linarith⟩
  let F := Finset.Icc (-(originalDetectorRawCutoff L : ℤ)) (originalDetectorRawCutoff L : ℤ)
  let f : ℤ → ℂ := fun n =>
    originalDetectorDividedLobeFourierJetCoeff s L c (by linarith) r n *
      fourier n (x : AddCircle L)
  have hnorm : Summable (fun n => ‖f n‖) := by
    have hh := (originalDetectorDividedLobeFourierJetCoeff_summable hs hL hleft hright r).norm
    apply hh.congr
    intro n
    simp only [f, norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  have hsum : Summable f := hnorm.of_norm
  have hrec := (originalDetectorDividedLobeFourierJet_hasSum_on_interval
    hs hL hleft hright r hx).tsum_eq
  have hsplit := hsum.sum_add_tsum_subtype_compl F
  have heq : iteratedDeriv r (originalDetectorDividedLobe s L c) x -
      originalDetectorDividedLobeFourierPartialJet s L c (by linarith) r x =
        ∑' n : {n : ℤ // n ∉ F}, f n := by
    change iteratedDeriv r (originalDetectorDividedLobe s L c) x - ∑ n ∈ F, f n = _
    rw [← hrec, ← hsplit]
    ring_nf
  rw [heq]
  refine (norm_tsum_le_tsum_norm (hnorm.subtype _)).trans_eq ?_
  refine (tsum_subtype {n : ℤ | n ∉ F} (fun n : ℤ => ‖f n‖)).trans ?_
  unfold originalDetectorDividedLobeFourierJetTail
  apply tsum_congr
  intro n
  have hcrit : n ∉ F ↔ originalDetectorRawCutoff L < n.natAbs := by
    dsimp [F]
    simp only [Finset.mem_Icc]
    omega
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, hcrit, f, norm_mul,
    fourier_apply, Circle.norm_coe, mul_one]

/-- The source-only constant after absorbing the derivative-frequency
weight into half of the already proved coefficient decay. -/
def originalDetectorDividedLobeFourierJetDecayConstant (s : ℝ) (r : ℕ) : ℝ :=
  4 * (4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)) *
    (2 * Real.pi) ^ r * (Nat.factorial (2 * r) : ℝ) *
      (2 / originalDetectorDividedLobeFourierDecayRate s) ^ (2 * r)

theorem originalDetectorDividedLobeFourierJetDecayConstant_nonneg (s : ℝ) (r : ℕ) :
    0 ≤ originalDetectorDividedLobeFourierJetDecayConstant s r := by
  unfold originalDetectorDividedLobeFourierJetDecayConstant
  have hc := originalDetectorDividedLobeFourierDecayRate_pos s
  positivity

/-- Actual weighted coefficients obey a source-derived stretched
exponential envelope. No coefficient or derivative estimate is an input. -/
theorem originalDetectorDividedLobeFourierJetCoeff_le_decay
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (r : ℕ) {n : ℤ} (hn : n ≠ 0) :
    ‖originalDetectorDividedLobeFourierJetCoeff s L c (by linarith) r n‖ ≤
      originalDetectorDividedLobeFourierJetDecayConstant s r * L ^ 8 *
        originalDetectorScalarFourierDecay L
          (originalDetectorDividedLobeFourierDecayRate s / 2) |(n : ℝ)| := by
  let k := originalDetectorDividedLobeFourierDecayRate s
  let D := 4 * (4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2))
  let t := |(n : ℝ)| / L
  have hLp : 0 < L := by linarith
  have hk : 0 < k := originalDetectorDividedLobeFourierDecayRate_pos s
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hb := originalDetectorDividedLobeFourierCoeff_le_exp_sqrt_frequency
    hs hL hleft hright hn
  have hp := originalDetectorScalarWeightedDecay_le hk ht r
  unfold originalDetectorDividedLobeFourierJetCoeff
  rw [norm_mul, norm_pow, norm_originalDetectorFourierFrequency hLp]
  have hfreq : 2 * Real.pi * |(n : ℝ)| / L = (2 * Real.pi) * t := by
    dsimp [t]
    ring_nf
  rw [hfreq, mul_pow]
  change _ ≤ originalDetectorDividedLobeFourierJetDecayConstant s r * L ^ 8 *
    Real.exp (-(k / 2) * Real.sqrt t)
  change ‖originalDetectorDividedLobeFourierCoeff s L c _ n‖ ≤
    D * L ^ 8 * Real.exp (-k * Real.sqrt t) at hb
  calc
    _ ≤ ((2 * Real.pi) ^ r * t ^ r) *
        (D * L ^ 8 * Real.exp (-k * Real.sqrt t)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = D * (2 * Real.pi) ^ r * L ^ 8 *
        (t ^ r * Real.exp (-k * Real.sqrt t)) := by ring_nf
    _ ≤ D * (2 * Real.pi) ^ r * L ^ 8 *
        ((Nat.factorial (2 * r) : ℝ) * (2 / k) ^ (2 * r) *
          Real.exp (-(k / 2) * Real.sqrt t)) :=
      mul_le_mul_of_nonneg_left hp (by dsimp [D]; positivity)
    _ = _ := by unfold originalDetectorDividedLobeFourierJetDecayConstant; dsimp [D, k]; ring_nf

/-- The explicit source-only budget at the literal `ceil(L^4)-4` cutoff. -/
def originalDetectorDividedLobeFourierJetTailBudget (s L : ℝ) (r : ℕ) : ℝ :=
  (320 * originalDetectorDividedLobeFourierJetDecayConstant s r /
    (originalDetectorDividedLobeFourierDecayRate s) ^ 3) * L ^ 8 *
      Real.exp (-(originalDetectorDividedLobeFourierDecayRate s / 4) *
        Real.sqrt ((originalDetectorRawCutoff L : ℝ) / L))

private theorem rawCutoff_sqrt_ge_aperture {L : ℝ} (hL : 2 ≤ L) :
    L ≤ Real.sqrt ((originalDetectorRawCutoff L : ℝ) / L) := by
  have hcube : L ^ 2 ≤ L ^ 3 / 2 := by
    nlinarith [mul_nonneg (sq_nonneg L) (show 0 ≤ L - 2 by linarith)]
  exact Real.le_sqrt_of_sq_le (hcube.trans (originalDetectorRawCutoff_div_lower hL))

/-- The actual signed coefficient tail at the fixed raw cutoff satisfies
the paper's source-derived exponential budget, for every finite jet order. -/
theorem originalDetectorDividedLobeFourierJetTail_le_budget
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) (r : ℕ) :
    originalDetectorDividedLobeFourierJetTail s L c (by linarith) r ≤
      originalDetectorDividedLobeFourierJetTailBudget s L r := by
  let k := originalDetectorDividedLobeFourierDecayRate s
  let B := originalDetectorDividedLobeFourierJetDecayConstant s r
  let N := originalDetectorRawCutoff L
  have hLp : 0 < L := by linarith
  have hk : 0 < k := originalDetectorDividedLobeFourierDecayRate_pos s
  have hB : 0 ≤ B := originalDetectorDividedLobeFourierJetDecayConstant_nonneg s r
  have hscalar := originalDetectorScalarFourierDecay_signed_tail_summable hLp
    (show 0 < k / 2 by positivity) N
  have htail := originalDetectorDividedLobeFourierJetTail_summable hs hL hleft hright r
  have hbound := hscalar.mul_left (B * L ^ 8)
  have hcmp : originalDetectorDividedLobeFourierJetTail s L c (by linarith) r ≤
      (B * L ^ 8) * (∑' n : ℤ, if N < n.natAbs then
        originalDetectorScalarFourierDecay L (k / 2) |(n : ℝ)| else 0) := by
    unfold originalDetectorDividedLobeFourierJetTail
    rw [← tsum_mul_left]
    apply Summable.tsum_le_tsum _ htail hbound
    intro n
    split_ifs with hn
    · have hnne : n ≠ 0 := by
        intro hh
        subst n
        simp only [Int.natAbs_zero] at hn
        omega
      exact originalDetectorDividedLobeFourierJetCoeff_le_decay hs hL hleft hright r hnne
    · simp only [mul_zero, le_refl]
  have hscalarBound := originalDetectorScalarFourierDecay_signed_tsum_tail_le_exp hLp
    (show 0 < k / 2 by positivity) N (rawCutoff_sqrt_ge_aperture hL)
  refine hcmp.trans ((mul_le_mul_of_nonneg_left hscalarBound (by positivity)).trans_eq ?_)
  unfold originalDetectorDividedLobeFourierJetTailBudget
  dsimp [k, B, N]
  ring_nf

/-- The actual finite Fourier truncation has the proved uniform source-jet
error at the mandated cutoff. In particular this supplies all orders `r≤3`. -/
theorem originalDetectorDividedLobeFourierPartialJet_error_le_budget
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (r : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖iteratedDeriv r (originalDetectorDividedLobe s L c) x -
      originalDetectorDividedLobeFourierPartialJet s L c (by linarith) r x‖ ≤
        originalDetectorDividedLobeFourierJetTailBudget s L r :=
  (originalDetectorDividedLobeFourierPartialJet_error_le_tail hs hL hleft hright r hx).trans
    (originalDetectorDividedLobeFourierJetTail_le_budget hs hL hleft hright r)

/-- The budget controls the actual derivatives of the single raw Fourier
partial sum, uniformly on the closed interval. -/
theorem originalDetectorDividedLobeFourierPartialSum_iteratedDeriv_error_le_budget
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (r : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖iteratedDeriv r (originalDetectorDividedLobe s L c) x -
      iteratedDeriv r (originalDetectorDividedLobeFourierPartialJet s L c (by linarith) 0) x‖ ≤
        originalDetectorDividedLobeFourierJetTailBudget s L r := by
  rw [originalDetectorDividedLobeFourierPartialJet_iteratedDeriv]
  exact originalDetectorDividedLobeFourierPartialJet_error_le_budget hs hL hleft hright r hx

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierJetCoeff_summable
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierJetCoeff_eq
#print axioms Zeta23.CCM.originalDetectorDividedLobePeriodicJet_fourierCoeff
#print axioms Zeta23.CCM.originalDetectorDividedLobePeriodicJet_hasSum
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierJet_hasSum_on_interval
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierPartialJet_iteratedDeriv
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierPartialJet_error_le_tail
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierJetCoeff_le_decay
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierJetTail_le_budget
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierPartialJet_error_le_budget
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierPartialSum_iteratedDeriv_error_le_budget
