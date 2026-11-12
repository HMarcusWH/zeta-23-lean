import Zeta23.OPICARound4.ArithmeticFrontier.GrowthClosure
import Zeta23.OPICARound4.ArithmeticFrontier.CofinalSemiboundedClosure
import Zeta23.CCM.NativeDeepThresholdGround
import Zeta23.ExceptionalZero.BoundaryFlatFiniteWeil
import Zeta23.ExceptionalZero.GeneratedFamilyFinalGateEquivalence
import Zeta23.WeilEF.ZeroSummability

/-!
# Floor adapter: a zero-free strip gives a fixed-rate native floor

`GrowthClosure` proves that a fixed-parity lower bound `Q ≥ -C e^{αL}` on the
quartic moment slices at every large aperture excludes every zero with
displacement `|Re ρ - 1/2| > α`. This module proves the converse direction with
explicit constants:

* one-sided transform bounds for a `C²` function supported in `[0, L]`, so that
  the pair `h_f(γ) · conj h_f(conj γ)` costs `exp (|Im γ| L)` and not its square;
* a lower bound for the genuine Weil form `W(f,f)` in terms of the summable
  zero weight `∑ m_ρ / (1 + |γ_ρ|²)` and the budget `‖f‖₁ + ‖f''‖₁`;
* the same bound on every boundary-flat native carrier, with a polynomial
  budget in the aperture and the cutoff;
* `EvenFixedRateMomentSliceBound α` and `OddFixedRateMomentSliceBound α` for
  every `α` above the supremum `a` of the displacements, and the resulting
  equivalence between the two families of statements.

A further section reads the repository's critical-line positivity on the moment
slices and records that the slice contracts (C1), (SB), (PG) and (SE) are each
equivalent to Mathlib's `RiemannHypothesis`.

The final section is a separate finite statement about the least-crossing
selector (contract M61): a cutoff-3 bottom below `-D/2` forces the stored
cutoff to be `3`, with an empty predecessor.

Nothing here bounds the displacement `a`. With no information on the zeros the
only available value is the trivial `a = 1/2`. The theorems are adapters: any
separately proved zero-free half-plane becomes a native floor at the matching
rate. RH and Step 4 remain OPEN.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open CCM ExceptionalZero Complex MeasureTheory Set
open scoped ComplexConjugate

/-! ## One-sided transform bounds on `[0, L]` -/

/-- On the source interval the phase costs at most `exp (max (-Im z) 0 * L)`. -/
theorem norm_cexp_I_mul_le_of_mem_Icc {z : ℂ} {u L : ℝ} (hu : u ∈ Icc (0 : ℝ) L) :
    ‖cexp (I * z * u)‖ ≤ Real.exp (max (-z.im) 0 * L) := by
  rw [norm_cexp_I_mul, Real.exp_le_exp]
  have hu0 : 0 ≤ u := hu.1
  have huL : u ≤ L := hu.2
  rcases le_total 0 (-z.im) with h | h
  · rw [max_eq_left h]
    nlinarith [mul_le_mul_of_nonneg_left huL h]
  · rw [max_eq_right h]
    nlinarith [mul_nonneg (neg_nonneg.mpr h) hu0]

/-- Zeroth-order bound for a function supported in `[0, L]`. -/
theorem norm_paperFT_le_of_support_Icc {f : ℝ → ℂ} {L : ℝ} (hfi : Integrable f)
    (hsupp : ∀ u, f u ≠ 0 → u ∈ Icc (0 : ℝ) L) (z : ℂ) :
    ‖paperFT f z‖ ≤ Real.exp (max (-z.im) 0 * L) * ∫ u, ‖f u‖ := by
  rw [paperFT_def, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hfi.norm.const_mul _) (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  by_cases hu : f u = 0
  · simp [hu]
  · rw [mul_comm]
    gcongr
    exact norm_cexp_I_mul_le_of_mem_Icc (hsupp u hu)

/-- Second-order bound for a `C²` function supported in `[0, L]`. -/
theorem norm_paperFT_mul_sq_le_of_support_Icc {f : ℝ → ℂ} {L : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → u ∈ Icc (0 : ℝ) L) (z : ℂ) :
    ‖paperFT f z‖ * ‖z‖ ^ 2 ≤
      Real.exp (max (-z.im) 0 * L) * ∫ u, ‖deriv (deriv f) u‖ := by
  have hcs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := L))
      (fun u hu => hsupp u hu)
  have hts : tsupport f ⊆ Icc (0 : ℝ) L :=
    closure_minimal (fun u hu => hsupp u hu) isClosed_Icc
  have hsupp2 : ∀ u, deriv (deriv f) u ≠ 0 → u ∈ Icc (0 : ℝ) L := by
    intro u hu
    exact hts (tsupport_deriv_subset (support_deriv_subset (Function.mem_support.mpr hu)))
  have hint : Integrable (deriv (deriv f)) :=
    (hf.deriv'.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcs.deriv.deriv
  have := norm_paperFT_le_of_support_Icc hint hsupp2 z
  rw [paperFT_deriv_deriv hf hcs, norm_mul, norm_neg, norm_pow, mul_comm] at this
  exact this

/-- The `L¹` budget of a test function: `‖f‖₁ + ‖f''‖₁`. -/
def weilL1Budget (f : ℝ → ℂ) : ℝ :=
  (∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖

theorem weilL1Budget_nonneg (f : ℝ → ℂ) : 0 ≤ weilL1Budget f :=
  add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)

/-- Weighted one-sided bound with denominator `1 + |z|²`. -/
theorem norm_paperFT_mul_one_add_normSq_le_of_support_Icc {f : ℝ → ℂ} {L : ℝ}
    (hf : ContDiff ℝ 2 f) (hsupp : ∀ u, f u ≠ 0 → u ∈ Icc (0 : ℝ) L) (z : ℂ) :
    ‖paperFT f z‖ * (1 + Complex.normSq z) ≤
      Real.exp (max (-z.im) 0 * L) * weilL1Budget f := by
  have hcs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := L))
      (fun u hu => hsupp u hu)
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcs
  have h0 := norm_paperFT_le_of_support_Icc hfi hsupp z
  have h2 := norm_paperFT_mul_sq_le_of_support_Icc hf hsupp z
  rw [Complex.normSq_eq_norm_sq]
  unfold weilL1Budget
  calc ‖paperFT f z‖ * (1 + ‖z‖ ^ 2)
      = ‖paperFT f z‖ + ‖paperFT f z‖ * ‖z‖ ^ 2 := by ring
    _ ≤ Real.exp (max (-z.im) 0 * L) * (∫ u, ‖f u‖) +
        Real.exp (max (-z.im) 0 * L) * (∫ u, ‖deriv (deriv f) u‖) := add_le_add h0 h2
    _ = Real.exp (max (-z.im) 0 * L) *
        ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) := by ring

/-- **Pair bound.** For a function supported in `[0, L]` the two transform values
entering one Weil summand cost `exp (|Im z| L)` together. -/
theorem norm_paperFT_pair_le {f : ℝ → ℂ} {L : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → u ∈ Icc (0 : ℝ) L) (z : ℂ) :
    ‖paperFT f z‖ * ‖paperFT f (conj z)‖ * (1 + Complex.normSq z) ≤
      Real.exp (|z.im| * L) * weilL1Budget f ^ 2 := by
  have h1 := norm_paperFT_mul_one_add_normSq_le_of_support_Icc hf hsupp z
  have h2 := norm_paperFT_mul_one_add_normSq_le_of_support_Icc hf hsupp (conj z)
  rw [Complex.normSq_conj, Complex.conj_im, neg_neg] at h2
  have hexp : Real.exp (max (-z.im) 0 * L) * Real.exp (max z.im 0 * L) =
      Real.exp (|z.im| * L) := by
    rw [← Real.exp_add]
    congr 1
    rcases le_total 0 z.im with h | h
    · rw [max_eq_right (by linarith : -z.im ≤ 0), max_eq_left h, abs_of_nonneg h]
      ring
    · rw [max_eq_left (by linarith : 0 ≤ -z.im), max_eq_right h, abs_of_nonpos h]
      ring
  have hn : 1 ≤ 1 + Complex.normSq z := by linarith [Complex.normSq_nonneg z]
  have hB := weilL1Budget_nonneg f
  have hprod := mul_le_mul h1 h2 (by positivity)
    (mul_nonneg (Real.exp_pos _).le hB)
  calc ‖paperFT f z‖ * ‖paperFT f (conj z)‖ * (1 + Complex.normSq z)
      ≤ ‖paperFT f z‖ * ‖paperFT f (conj z)‖ *
          ((1 + Complex.normSq z) * (1 + Complex.normSq z)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = (‖paperFT f z‖ * (1 + Complex.normSq z)) *
          (‖paperFT f (conj z)‖ * (1 + Complex.normSq z)) := by ring
    _ ≤ (Real.exp (max (-z.im) 0 * L) * weilL1Budget f) *
          (Real.exp (max z.im 0 * L) * weilL1Budget f) := hprod
    _ = Real.exp (|z.im| * L) * weilL1Budget f ^ 2 := by rw [← hexp]; ring

/-! ## The zero weight and the Weil floor -/

/-- The convergent zero weight `∑ m_ρ / (1 + |γ_ρ|²)` over the nontrivial zeros. -/
def zetaZeroInvSqWeight : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))

theorem summable_zetaZeroInvSqWeight :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
  Zeta23.WeilEF.zero_sum_inv_sq zetaSeam

theorem zetaZeroInvSqWeight_nonneg : 0 ≤ zetaZeroInvSqWeight :=
  tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))])

/-- **Weil floor from a zero strip.** If every nontrivial zero has displacement at
most `a`, the genuine Weil form of a `C²` function supported in `[0, L]` is
bounded below by minus the zero weight times `exp (a L)` times the squared
budget. No sign information on any summand is used. -/
theorem zeta_W_self_re_ge_neg_of_zeroStrip {a L : ℝ} (hL : 0 ≤ L)
    (hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hsupp : ∀ u, f u ≠ 0 → u ∈ Icc (0 : ℝ) L) :
    -(zetaZeroInvSqWeight * (Real.exp (a * L) * weilL1Budget f ^ 2)) ≤
      Complex.re (zetaZeroConfig.W f f) := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := L))
      (fun u hu => hsupp u hu)
  set c : ℝ := Real.exp (a * L) * weilL1Budget f ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hterm : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand f f ρ‖ ≤
        c * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hpair := norm_paperFT_pair_le hf hsupp (gammaOf (ρ : ℂ))
    have him : |(gammaOf (ρ : ℂ)).im| ≤ a := by
      rw [Zeta23.WeilEF.gammaOf_im, abs_sub_comm]
      exact hstrip ρ ρ.2
    have hexp : Real.exp (|(gammaOf (ρ : ℂ)).im| * L) ≤ Real.exp (a * L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right him hL)
    have hden : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
      linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have hnorm : ‖zetaZeroConfig.Wsummand f f ρ‖ =
        (zetaZeroConfig.mult ρ : ℝ) *
          (‖paperFT f (gammaOf ρ)‖ * ‖paperFT f (conj (gammaOf ρ))‖) := by
      unfold ZeroConfig.Wsummand
      rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
      ring
    rw [hnorm]
    have hbound : ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f (conj (gammaOf ρ))‖ ≤
        c / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
      rw [le_div_iff₀ hden]
      calc ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f (conj (gammaOf ρ))‖ *
            (1 + Complex.normSq (gammaOf (ρ : ℂ)))
          ≤ Real.exp (|(gammaOf (ρ : ℂ)).im| * L) * weilL1Budget f ^ 2 := hpair
        _ ≤ c := by
            rw [hc]
            exact mul_le_mul_of_nonneg_right hexp (sq_nonneg _)
    calc (zetaZeroConfig.mult ρ : ℝ) *
          (‖paperFT f (gammaOf ρ)‖ * ‖paperFT f (conj (gammaOf ρ))‖)
        ≤ (zetaZeroConfig.mult ρ : ℝ) * (c / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
          mul_le_mul_of_nonneg_left hbound hm
      _ = c * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by ring
  have hmaj : HasSum (fun ρ : zetaZeroConfig.carrier =>
      c * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))))
      (c * zetaZeroInvSqWeight) :=
    summable_zetaZeroInvSqWeight.hasSum.mul_left c
  have hnormW : ‖zetaZeroConfig.W f f‖ ≤ c * zetaZeroInvSqWeight := by
    unfold ZeroConfig.W
    exact tsum_of_norm_bounded hmaj hterm
  have hre : -‖zetaZeroConfig.W f f‖ ≤ (zetaZeroConfig.W f f).re := by
    have h1 := Complex.abs_re_le_norm (zetaZeroConfig.W f f)
    have h2 := neg_abs_le (zetaZeroConfig.W f f).re
    linarith
  linarith [mul_comm c zetaZeroInvSqWeight]

/-! ## Budget of a boundary-flat native vector -/

/-- Frequencies of the retained modes are at most `2π N / L`. -/
theorem norm_localizedFrequency_centered_le {L : ℝ} (hL : 0 < L) (N : ℕ)
    (i : Fin (2 * N + 1)) :
    ‖localizedFrequency L (centeredIndex N i)‖ ≤ 2 * Real.pi * N / L := by
  have hbase : (0 : ℝ) < 2 * Real.pi / L := by positivity
  have h : |((centeredIndex N i : ℤ) : ℝ)| ≤ (N : ℝ) := by
    have h1 := i.2
    have habs : |centeredIndex N i| ≤ (N : ℤ) := by
      rw [abs_le]; simp only [centeredIndex]; omega
    rw [← Int.cast_abs]
    exact_mod_cast habs
  unfold localizedFrequency localizedBaseFrequency
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_intCast,
    Real.norm_eq_abs, abs_of_pos hbase]
  calc 2 * Real.pi / L * |((centeredIndex N i : ℤ) : ℝ)| ≤ 2 * Real.pi / L * N :=
        mul_le_mul_of_nonneg_left h hbase.le
    _ = 2 * Real.pi * N / L := by ring

/-- Pointwise bound of the finite Fourier combination by the coefficient `ℓ¹` mass. -/
theorem norm_localizedFiniteFunction_le {L : ℝ} (hL : 0 < L) (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) (x : ℝ) :
    ‖localizedFiniteFunction L N u x‖ ≤ 1 / Real.sqrt L * ∑ i, ‖u i‖ := by
  unfold localizedFiniteFunction
  calc ‖∑ i, u i * localizedMode L (centeredIndex N i) x‖
      ≤ ∑ i, ‖u i * localizedMode L (centeredIndex N i) x‖ := norm_sum_le _ _
    _ = ∑ i, ‖u i‖ * (1 / Real.sqrt L) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_localizedMode_of_pos hL]
    _ = 1 / Real.sqrt L * ∑ i, ‖u i‖ := by rw [← Finset.sum_mul]; ring

/-- Pointwise bound of the second jet. -/
theorem norm_localizedFiniteSecondJet_le {L : ℝ} (hL : 0 < L) (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) (x : ℝ) :
    ‖localizedFiniteSecondJet L N u x‖ ≤
      (2 * Real.pi * N / L) ^ 2 * (1 / Real.sqrt L * ∑ i, ‖u i‖) := by
  have hsqrt : 0 ≤ 1 / Real.sqrt L := by positivity
  unfold localizedFiniteSecondJet
  calc ‖∑ i, u i * localizedFrequency L (centeredIndex N i) ^ 2 *
          localizedMode L (centeredIndex N i) x‖
      ≤ ∑ i, ‖u i * localizedFrequency L (centeredIndex N i) ^ 2 *
          localizedMode L (centeredIndex N i) x‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖u i‖ * ((2 * Real.pi * N / L) ^ 2 * (1 / Real.sqrt L)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_mul, norm_pow, norm_localizedMode_of_pos hL, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (norm_localizedFrequency_centered_le hL N i) 2) hsqrt
    _ = (2 * Real.pi * N / L) ^ 2 * (1 / Real.sqrt L * ∑ i, ‖u i‖) := by
        rw [← Finset.sum_mul]; ring

/-- A function bounded by `M` on `[0, L]` and cut off outside has `L¹` norm at most `M L`. -/
theorem integral_norm_indicator_Icc_le {g : ℝ → ℂ} {L M : ℝ} (hL : 0 ≤ L)
    (hM : ∀ x ∈ Icc (0 : ℝ) L, ‖g x‖ ≤ M) :
    ∫ x, ‖(Icc (0 : ℝ) L).indicator g x‖ ≤ M * L := by
  have hfun : (fun x => ‖(Icc (0 : ℝ) L).indicator g x‖) =
      (Icc (0 : ℝ) L).indicator (fun x => ‖g x‖) := by
    funext x
    exact norm_indicator_eq_indicator_norm g x
  rw [hfun, integral_indicator measurableSet_Icc]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : ℝ) L)
    (f := fun x => ‖g x‖) (C := M) (by simp)
    (fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hM x hx)
  rw [Real.volume_real_Icc_of_le hL, sub_zero] at h
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)

/-- The second derivative of a boundary-flat native vector is the cut-off second jet. -/
theorem deriv_deriv_localizedFiniteVector_of_boundaryFlat (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) {L : ℝ} (hL : 0 < L) (hflat : BoundaryFlatCoefficients N u) :
    deriv (deriv (localizedFiniteVector L N u)) =
      (Icc (0 : ℝ) L).indicator (localizedFiniteSecondJet L N u) := by
  rw [localizedFiniteVector_eq_indicator]
  have hF : ∀ x, HasDerivAt ((Icc (0 : ℝ) L).indicator (localizedFiniteFunction L N u))
      ((Icc (0 : ℝ) L).indicator (localizedFiniteFirstJet L N u) x) x := fun x =>
    hasDerivAt_indicator_Icc_of_endpoint_jets_zero hL (hasDerivAt_localizedFiniteFunction L N u)
      (localizedFiniteFunction_zero_of_boundaryFlat L N u hflat)
      (localizedFiniteFunction_rightEndpoint_zero_of_boundaryFlat hL N u hflat)
      (localizedFiniteFirstJet_zero_of_boundaryFlat L N u hflat)
      (localizedFiniteFirstJet_rightEndpoint_zero_of_boundaryFlat hL N u hflat)
  have hF₁ : ∀ x, HasDerivAt ((Icc (0 : ℝ) L).indicator (localizedFiniteFirstJet L N u))
      ((Icc (0 : ℝ) L).indicator (localizedFiniteSecondJet L N u) x) x := fun x =>
    hasDerivAt_indicator_Icc_of_endpoint_jets_zero hL (hasDerivAt_localizedFiniteFirstJet L N u)
      (localizedFiniteFirstJet_zero_of_boundaryFlat L N u hflat)
      (localizedFiniteFirstJet_rightEndpoint_zero_of_boundaryFlat hL N u hflat)
      (localizedFiniteSecondJet_zero_of_boundaryFlat L N u hflat)
      (localizedFiniteSecondJet_rightEndpoint_zero_of_boundaryFlat hL N u hflat)
  rw [deriv_eq hF, deriv_eq hF₁]

/-- **Budget of a boundary-flat native vector.** -/
theorem weilL1Budget_localizedFiniteVector_le (N : ℕ) (u : Fin (2 * N + 1) → ℂ) {L : ℝ}
    (hL : 0 < L) (hflat : BoundaryFlatCoefficients N u) :
    weilL1Budget (localizedFiniteVector L N u) ≤
      Real.sqrt L * (1 + (2 * Real.pi * N / L) ^ 2) * ∑ i, ‖u i‖ := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsq : 1 / Real.sqrt L * L = Real.sqrt L := by
    rw [one_div, inv_mul_eq_div, div_eq_iff hs.ne']
    exact (Real.mul_self_sqrt hL.le).symm
  have h0 : ∫ x, ‖localizedFiniteVector L N u x‖ ≤ 1 / Real.sqrt L * (∑ i, ‖u i‖) * L := by
    rw [localizedFiniteVector_eq_indicator]
    exact integral_norm_indicator_Icc_le hL.le
      (fun x _ => norm_localizedFiniteFunction_le hL N u x)
  have h2 : ∫ x, ‖(Icc (0 : ℝ) L).indicator (localizedFiniteSecondJet L N u) x‖ ≤
      (2 * Real.pi * N / L) ^ 2 * (1 / Real.sqrt L * ∑ i, ‖u i‖) * L :=
    integral_norm_indicator_Icc_le hL.le
      (fun x _ => norm_localizedFiniteSecondJet_le hL N u x)
  unfold weilL1Budget
  rw [deriv_deriv_localizedFiniteVector_of_boundaryFlat N u hL hflat]
  calc (∫ x, ‖localizedFiniteVector L N u x‖) +
        ∫ x, ‖(Icc (0 : ℝ) L).indicator (localizedFiniteSecondJet L N u) x‖
      ≤ 1 / Real.sqrt L * (∑ i, ‖u i‖) * L +
          (2 * Real.pi * N / L) ^ 2 * (1 / Real.sqrt L * ∑ i, ‖u i‖) * L := add_le_add h0 h2
    _ = (1 / Real.sqrt L * L) * (1 + (2 * Real.pi * N / L) ^ 2) * ∑ i, ‖u i‖ := by ring
    _ = Real.sqrt L * (1 + (2 * Real.pi * N / L) ^ 2) * ∑ i, ‖u i‖ := by rw [hsq]

/-- Cauchy--Schwarz between the coefficient `ℓ¹` mass and the Euclidean norm. -/
theorem sq_sum_norm_equiv_le (N : ℕ) (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    (∑ i, ‖(EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x i‖) ^ 2 ≤
      (2 * (N : ℝ) + 1) * ‖x‖ ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (2 * N + 1))))
    (f := fun i => ‖x i‖)
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simpa [Finset.card_univ, Fintype.card_fin] using h

/-- The polynomial budget of the native carrier at aperture `L` and cutoff `K`. -/
def nativeFloorBudget (L : ℝ) (K : ℕ) : ℝ :=
  L * (1 + (2 * Real.pi * K / L) ^ 2) ^ 2 * (2 * (K : ℝ) + 1)

theorem nativeFloorBudget_nonneg {L : ℝ} (hL : 0 ≤ L) (K : ℕ) : 0 ≤ nativeFloorBudget L K := by
  unfold nativeFloorBudget
  positivity

/-! ## The floor on native carriers and moment slices -/

/-- **Native floor from a zero strip.** On every boundary-flat coefficient vector
the canonical self-energy is at least minus the zero weight times `exp (a L)`
times the polynomial budget times the squared physical norm. -/
theorem canonicalSource_re_inner_ge_neg_of_zeroStrip {a L : ℝ} (hL : 0 < L)
    (hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ a) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    -(zetaZeroInvSqWeight * Real.exp (a * L) * nativeFloorBudget L K) * ‖x‖ ^ 2 ≤
      (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin x) x).re := by
  have hf : ContDiff ℝ 2 (localizedFiniteVector L K ((EuclideanSpace.equiv _ ℂ) x)) :=
    contDiff_localizedFiniteVector_of_boundaryFlat K _ hL hflat
  have hsupp : ∀ t, localizedFiniteVector L K ((EuclideanSpace.equiv _ ℂ) x) t ≠ 0 →
      t ∈ Icc (0 : ℝ) L := fun t ht =>
    localizedFiniteVector_support_subset L K _ (Function.mem_support.mpr ht)
  have hW := zeta_W_self_re_ge_neg_of_zeroStrip hL.le hstrip hf hsupp
  rw [zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm K _ hL hflat] at hW
  have hE : (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin x) x).re =
      Complex.re (quadraticForm (canonicalSourceMatrix L K)
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :=
    (matrixRealEnergy_eq_re_inner_apply_self (canonicalSourceMatrix L K) x).symm
  rw [hE]
  have hB := weilL1Budget_localizedFiniteVector_le K ((EuclideanSpace.equiv _ ℂ) x) hL hflat
  have hB0 := weilL1Budget_nonneg (localizedFiniteVector L K ((EuclideanSpace.equiv _ ℂ) x))
  have hl1 := sq_sum_norm_equiv_le K x
  have hfac : 0 ≤ L * (1 + (2 * Real.pi * K / L) ^ 2) ^ 2 := by positivity
  have hBsq : weilL1Budget (localizedFiniteVector L K ((EuclideanSpace.equiv _ ℂ) x)) ^ 2 ≤
      nativeFloorBudget L K * ‖x‖ ^ 2 := by
    calc weilL1Budget (localizedFiniteVector L K ((EuclideanSpace.equiv _ ℂ) x)) ^ 2
        ≤ (Real.sqrt L * (1 + (2 * Real.pi * K / L) ^ 2) *
            ∑ i, ‖(EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x i‖) ^ 2 :=
          pow_le_pow_left₀ hB0 hB 2
      _ = L * (1 + (2 * Real.pi * K / L) ^ 2) ^ 2 *
            (∑ i, ‖(EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x i‖) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hL.le]
      _ ≤ L * (1 + (2 * Real.pi * K / L) ^ 2) ^ 2 * ((2 * (K : ℝ) + 1) * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hl1 hfac
      _ = nativeFloorBudget L K * ‖x‖ ^ 2 := by unfold nativeFloorBudget; ring
  have hS := zetaZeroInvSqWeight_nonneg
  have hcoef : 0 ≤ zetaZeroInvSqWeight * Real.exp (a * L) :=
    mul_nonneg hS (Real.exp_pos _).le
  have hmain : zetaZeroInvSqWeight * (Real.exp (a * L) *
      weilL1Budget (localizedFiniteVector L K ((EuclideanSpace.equiv _ ℂ) x)) ^ 2) ≤
      zetaZeroInvSqWeight * Real.exp (a * L) * nativeFloorBudget L K * ‖x‖ ^ 2 := by
    calc zetaZeroInvSqWeight * (Real.exp (a * L) *
          weilL1Budget (localizedFiniteVector L K ((EuclideanSpace.equiv _ ℂ) x)) ^ 2)
        = zetaZeroInvSqWeight * Real.exp (a * L) *
          weilL1Budget (localizedFiniteVector L K ((EuclideanSpace.equiv _ ℂ) x)) ^ 2 := by ring
      _ ≤ zetaZeroInvSqWeight * Real.exp (a * L) * (nativeFloorBudget L K * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hBsq hcoef
      _ = zetaZeroInvSqWeight * Real.exp (a * L) * nativeFloorBudget L K * ‖x‖ ^ 2 := by ring
  linarith

/-- The even moment slice inherits the floor (so does the whole even pole-neutral carrier). -/
theorem evenMomentSliceLowerBound_of_zeroStrip {a L : ℝ} (hL : 0 < L)
    (hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ a) (K : ℕ) :
    EvenMomentSliceLowerBound L K
      (zetaZeroInvSqWeight * Real.exp (a * L) * nativeFloorBudget L K) := by
  intro u _
  have hflat : BoundaryFlatCoefficients K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) :=
    (mem_boundaryFlatSubspace_iff K _).mp
      (Submodule.mem_inf.mp ((mem_euclideanEvenBoundaryFlatSubspace_iff K _).mp u.val.property)).1
  have h := canonicalSource_re_inner_ge_neg_of_zeroStrip hL hstrip K
    (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) hflat
  have hn : ‖u‖ = ‖(u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ := rfl
  unfold evenNativeEnergy
  rw [inner_poleNeutralEvenCompressedCanonical_self, hn]
  exact h

/-- The odd moment slice inherits the floor. -/
theorem oddMomentSliceLowerBound_of_zeroStrip {a L : ℝ} (hL : 0 < L)
    (hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ a) (K : ℕ) :
    OddMomentSliceLowerBound L K
      (zetaZeroInvSqWeight * Real.exp (a * L) * nativeFloorBudget L K) := by
  intro v _
  have hflat : BoundaryFlatCoefficients K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
      (v.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) :=
    (mem_boundaryFlatSubspace_iff K _).mp
      (Submodule.mem_inf.mp ((mem_euclideanOddBoundaryFlatSubspace_iff K _).mp v.val.property)).1
  have h := canonicalSource_re_inner_ge_neg_of_zeroStrip hL hstrip K
    (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))) hflat
  have hn : ‖v‖ = ‖(v.val : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ := rfl
  unfold oddNativeEnergy
  rw [inner_poleNeutralOddCompressedCanonical_self, hn]
  exact h

/-! ## The quartic cutoff and the fixed-rate bounds -/

/-- At the literal quartic cutoff the budget is at most `128000 (1 + L)^17`. -/
theorem nativeFloorBudget_quartic_le {L : ℝ} (hL : 1 ≤ L) :
    nativeFloorBudget L (originalDetectorQuarticCutoff L) ≤ 128000 * (1 + L) ^ 17 := by
  have hL0 : 0 < L := by linarith
  have hy : (1 : ℝ) ≤ 1 + L := by linarith
  have hy0 : (0 : ℝ) ≤ 1 + L := by linarith
  have hK0 : (0 : ℝ) ≤ (originalDetectorQuarticCutoff L : ℝ) := Nat.cast_nonneg _
  have hL4 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL
  have hKle : (originalDetectorQuarticCutoff L : ℝ) ≤ 2 * L ^ 4 := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ L ^ 4 by positivity)
    unfold originalDetectorQuarticCutoff
    linarith
  have hLy3 : L ^ 3 ≤ (1 + L) ^ 3 := pow_le_pow_left₀ hL0.le (by linarith) 3
  have hLy4 : L ^ 4 ≤ (1 + L) ^ 4 := pow_le_pow_left₀ hL0.le (by linarith) 4
  have hy4 : (1 : ℝ) ≤ (1 + L) ^ 4 := one_le_pow₀ hy
  have hy6 : (1 : ℝ) ≤ (1 + L) ^ 6 := one_le_pow₀ hy
  have hKL : (originalDetectorQuarticCutoff L : ℝ) / L ≤ 2 * (1 + L) ^ 3 := by
    rw [div_le_iff₀ hL0]
    have h4 : L ^ 4 = L ^ 3 * L := by ring
    nlinarith [mul_le_mul_of_nonneg_right hLy3 hL0.le]
  have hKL0 : 0 ≤ (originalDetectorQuarticCutoff L : ℝ) / L := div_nonneg hK0 hL0.le
  have hpi : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
  have hfreq0 : 0 ≤ 2 * Real.pi * (originalDetectorQuarticCutoff L : ℝ) / L := by positivity
  have hfreq : 2 * Real.pi * (originalDetectorQuarticCutoff L : ℝ) / L ≤ 12.6 * (1 + L) ^ 3 := by
    have hrew : 2 * Real.pi * (originalDetectorQuarticCutoff L : ℝ) / L =
        2 * Real.pi * ((originalDetectorQuarticCutoff L : ℝ) / L) := by ring
    rw [hrew]
    have h3 : (0 : ℝ) ≤ (1 + L) ^ 3 := by positivity
    calc 2 * Real.pi * ((originalDetectorQuarticCutoff L : ℝ) / L)
        ≤ 2 * 3.15 * (2 * (1 + L) ^ 3) :=
          mul_le_mul (by linarith [Real.pi_pos]) hKL hKL0 (by norm_num)
      _ = 12.6 * (1 + L) ^ 3 := by ring
  have hA : 1 + (2 * Real.pi * (originalDetectorQuarticCutoff L : ℝ) / L) ^ 2 ≤
      160 * (1 + L) ^ 6 := by
    have hsq := pow_le_pow_left₀ hfreq0 hfreq 2
    have hexp : (12.6 * (1 + L) ^ 3) ^ 2 = 158.76 * (1 + L) ^ 6 := by ring
    rw [hexp] at hsq
    linarith
  have hA0 : 0 ≤ 1 + (2 * Real.pi * (originalDetectorQuarticCutoff L : ℝ) / L) ^ 2 := by positivity
  have hA2 : (1 + (2 * Real.pi * (originalDetectorQuarticCutoff L : ℝ) / L) ^ 2) ^ 2 ≤
      25600 * (1 + L) ^ 12 := by
    have hsq := pow_le_pow_left₀ hA0 hA 2
    have hexp : (160 * (1 + L) ^ 6) ^ 2 = 25600 * (1 + L) ^ 12 := by ring
    rw [hexp] at hsq
    exact hsq
  have hBk : 2 * (originalDetectorQuarticCutoff L : ℝ) + 1 ≤ 5 * (1 + L) ^ 4 := by linarith
  have hBk0 : 0 ≤ 2 * (originalDetectorQuarticCutoff L : ℝ) + 1 := by positivity
  have hsq0 : 0 ≤ (1 + (2 * Real.pi * (originalDetectorQuarticCutoff L : ℝ) / L) ^ 2) ^ 2 :=
    sq_nonneg _
  unfold nativeFloorBudget
  calc L * (1 + (2 * Real.pi * (originalDetectorQuarticCutoff L : ℝ) / L) ^ 2) ^ 2 *
        (2 * (originalDetectorQuarticCutoff L : ℝ) + 1)
      ≤ (1 + L) * (25600 * (1 + L) ^ 12) * (5 * (1 + L) ^ 4) :=
        mul_le_mul (mul_le_mul (by linarith) hA2 hsq0 hy0) hBk hBk0 (by positivity)
    _ = 128000 * (1 + L) ^ 17 := by ring

/-- **Even fixed rate from a zero strip.** If every zero has displacement at most
`a`, every rate `α > a` is an even fixed-rate bound at the quartic cutoff. -/
theorem evenFixedRateMomentSliceBound_of_zeroStrip {a α : ℝ} (hα : a < α)
    (hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ a) :
    EvenFixedRateMomentSliceBound α := by
  have hε : 0 < α - a := sub_pos.mpr hα
  have hC₀ : 0 < ((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17 :=
    div_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos 17)) (Real.exp_pos _)) (pow_pos hε 17)
  have hS := zetaZeroInvSqWeight_nonneg
  refine ⟨(zetaZeroInvSqWeight + 1) * 128000 *
    (((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17), 1,
    mul_pos (mul_pos (by linarith) (by norm_num)) hC₀, ?_⟩
  intro L hL
  have hL0 : 0 < L := by linarith
  refine (evenMomentSliceLowerBound_of_zeroStrip hL0 hstrip _).mono ?_
  have hbud := nativeFloorBudget_quartic_le hL
  have hdom := one_add_pow_le_mul_exp hε 17 (show -1 ≤ L by linarith)
  have hexp : Real.exp (a * L) * Real.exp ((α - a) * L) = Real.exp (α * L) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : nativeFloorBudget L (originalDetectorQuarticCutoff L) ≤
      128000 * ((((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17) *
        Real.exp ((α - a) * L)) :=
    hbud.trans (mul_le_mul_of_nonneg_left hdom (by norm_num))
  calc zetaZeroInvSqWeight * Real.exp (a * L) *
        nativeFloorBudget L (originalDetectorQuarticCutoff L)
      ≤ (zetaZeroInvSqWeight + 1) * Real.exp (a * L) *
          (128000 * ((((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17) *
            Real.exp ((α - a) * L))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le) h1
          (nativeFloorBudget_nonneg hL0.le _)
          (mul_nonneg (by linarith) (Real.exp_pos _).le)
    _ = (zetaZeroInvSqWeight + 1) * 128000 *
          (((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17) *
          (Real.exp (a * L) * Real.exp ((α - a) * L)) := by ring
    _ = (zetaZeroInvSqWeight + 1) * 128000 *
          (((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17) *
          Real.exp (α * L) := by rw [hexp]

/-- **Odd fixed rate from a zero strip.** -/
theorem oddFixedRateMomentSliceBound_of_zeroStrip {a α : ℝ} (hα : a < α)
    (hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ a) :
    OddFixedRateMomentSliceBound α := by
  have hε : 0 < α - a := sub_pos.mpr hα
  have hC₀ : 0 < ((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17 :=
    div_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos 17)) (Real.exp_pos _)) (pow_pos hε 17)
  have hS := zetaZeroInvSqWeight_nonneg
  refine ⟨(zetaZeroInvSqWeight + 1) * 128000 *
    (((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17), 1,
    mul_pos (mul_pos (by linarith) (by norm_num)) hC₀, ?_⟩
  intro L hL
  have hL0 : 0 < L := by linarith
  refine (oddMomentSliceLowerBound_of_zeroStrip hL0 hstrip _).mono ?_
  have hbud := nativeFloorBudget_quartic_le hL
  have hdom := one_add_pow_le_mul_exp hε 17 (show -1 ≤ L by linarith)
  have hexp : Real.exp (a * L) * Real.exp ((α - a) * L) = Real.exp (α * L) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : nativeFloorBudget L (originalDetectorQuarticCutoff L) ≤
      128000 * ((((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17) *
        Real.exp ((α - a) * L)) :=
    hbud.trans (mul_le_mul_of_nonneg_left hdom (by norm_num))
  calc zetaZeroInvSqWeight * Real.exp (a * L) *
        nativeFloorBudget L (originalDetectorQuarticCutoff L)
      ≤ (zetaZeroInvSqWeight + 1) * Real.exp (a * L) *
          (128000 * ((((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17) *
            Real.exp ((α - a) * L))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le) h1
          (nativeFloorBudget_nonneg hL0.le _)
          (mul_nonneg (by linarith) (Real.exp_pos _).le)
    _ = (zetaZeroInvSqWeight + 1) * 128000 *
          (((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17) *
          (Real.exp (a * L) * Real.exp ((α - a) * L)) := by ring
    _ = (zetaZeroInvSqWeight + 1) * 128000 *
          (((17 : ℕ).factorial : ℝ) * Real.exp (α - a) / (α - a) ^ 17) *
          Real.exp (α * L) := by rw [hexp]

/-! ## The graded equivalence -/

/-- **Graded equivalence, even parity.** For `a ≥ 0`: every zero has displacement
at most `a` if and only if every rate above `a` is an even fixed-rate bound. The
case `a = 0` is RH against the contract (SE) restricted to the even parity. -/
theorem zeroStrip_iff_even_fixed_rates {a : ℝ} (ha : 0 ≤ a) :
    (∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ a) ↔
      ∀ α : ℝ, a < α → EvenFixedRateMomentSliceBound α := by
  constructor
  · intro h α hα
    exact evenFixedRateMomentSliceBound_of_zeroStrip hα h
  · intro h ρ hρ
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact abs_re_sub_half_le_of_even_fixed_rate (by linarith) (h (a + ε) (by linarith)) ⟨ρ, hρ⟩

/-- **Graded equivalence, odd parity.** -/
theorem zeroStrip_iff_odd_fixed_rates {a : ℝ} (ha : 0 ≤ a) :
    (∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ a) ↔
      ∀ α : ℝ, a < α → OddFixedRateMomentSliceBound α := by
  constructor
  · intro h α hα
    exact oddFixedRateMomentSliceBound_of_zeroStrip hα h
  · intro h ρ hρ
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact abs_re_sub_half_le_of_odd_fixed_rate (by linarith) (h (a + ε) (by linarith)) ⟨ρ, hρ⟩

/-- A zero-free half-plane `Re ρ ≤ θ` bounds every displacement by `θ - 1/2`,
because the zeros are symmetric under `ρ ↦ 1 - conj ρ`. -/
theorem abs_re_sub_half_le_of_re_le {θ : ℝ}
    (hθ : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ θ) :
    ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ θ - 1 / 2 := by
  intro ρ hρ
  have h1 := hθ ρ hρ
  have h2 := hθ (reflect ρ) (zetaZeroConfig.reflect_mem ρ hρ)
  have hre : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
  rw [hre] at h2
  rw [abs_le]
  constructor <;> linarith

/-- **Adapter for an external zero-free half-plane.** Any proved bound
`Re ρ ≤ θ` on all nontrivial zeros gives both fixed-rate bounds at every rate
above `θ - 1/2`. The premise is an input; nothing here supplies it. -/
theorem fixedRateMomentSliceBounds_of_re_le {θ α : ℝ}
    (hθ : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ θ) (hα : θ - 1 / 2 < α) :
    EvenFixedRateMomentSliceBound α ∧ OddFixedRateMomentSliceBound α :=
  ⟨evenFixedRateMomentSliceBound_of_zeroStrip hα (abs_re_sub_half_le_of_re_le hθ),
    oddFixedRateMomentSliceBound_of_zeroStrip hα (abs_re_sub_half_le_of_re_le hθ)⟩

/-- **The unconditional trivial rate.** Every rate above `1/2` is a fixed-rate
bound in both parities; this uses only that the zeros lie in the closed strip. -/
theorem fixedRateMomentSliceBounds_of_half_lt {α : ℝ} (hα : 1 / 2 < α) :
    EvenFixedRateMomentSliceBound α ∧ OddFixedRateMomentSliceBound α :=
  fixedRateMomentSliceBounds_of_re_le (θ := 1)
    (fun ρ hρ => (zetaZeroConfig.strip ρ hρ).2) (by linarith)

/-! ## The critical-line case: the slice contracts are equivalent to RH

With every zero on the line the repository already proves that the canonical
form is nonnegative on boundary-flat carriers
(`canonicalSourceQuadraticForm_re_nonnegative_of_criticalLine`). Read on the
moment slices this is the bound with error zero, which is sharper than the
`a = 0` case of the floor above (that estimate discards the sign of the zero
sum). Together with the compiled consumers it makes each slice contract
equivalent to Mathlib's `RiemannHypothesis`. -/

/-- Critical-line zeros give the even slice bound with error zero, at every
aperture and every cutoff. -/
theorem evenMomentSliceLowerBound_zero_of_critical_line
    (hline : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    EvenMomentSliceLowerBound L K 0 := by
  intro u _
  have hflat : BoundaryFlatCoefficients K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) :=
    (mem_boundaryFlatSubspace_iff K _).mp
      (Submodule.mem_inf.mp ((mem_euclideanEvenBoundaryFlatSubspace_iff K _).mp u.val.property)).1
  have h := canonicalSourceQuadraticForm_re_nonnegative_of_criticalLine hline K _ hL hflat
  have hE : (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re =
      Complex.re (quadraticForm (canonicalSourceMatrix L K)
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))) :=
    (matrixRealEnergy_eq_re_inner_apply_self (canonicalSourceMatrix L K) _).symm
  unfold evenNativeEnergy
  rw [inner_poleNeutralEvenCompressedCanonical_self, hE, neg_zero, zero_mul]
  exact h

/-- Critical-line zeros give the odd slice bound with error zero. -/
theorem oddMomentSliceLowerBound_zero_of_critical_line
    (hline : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    OddMomentSliceLowerBound L K 0 := by
  intro v _
  have hflat : BoundaryFlatCoefficients K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
      (v.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) :=
    (mem_boundaryFlatSubspace_iff K _).mp
      (Submodule.mem_inf.mp ((mem_euclideanOddBoundaryFlatSubspace_iff K _).mp v.val.property)).1
  have h := canonicalSourceQuadraticForm_re_nonnegative_of_criticalLine hline K _ hL hflat
  have hE : (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin
        (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
        (v.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re =
      Complex.re (quadraticForm (canonicalSourceMatrix L K)
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))))) :=
    (matrixRealEnergy_eq_re_inner_apply_self (canonicalSourceMatrix L K) _).symm
  unfold oddNativeEnergy
  rw [inner_poleNeutralOddCompressedCanonical_self, hE, neg_zero, zero_mul]
  exact h

/-- **RH gives both slice bounds with error zero.** -/
theorem momentSliceLowerBounds_zero_of_riemannHypothesis (hRH : RiemannHypothesis)
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    EvenMomentSliceLowerBound L K 0 ∧ OddMomentSliceLowerBound L K 0 :=
  ⟨evenMomentSliceLowerBound_zero_of_critical_line
      (fun _ hρ => RH_implies_on_line hRH hρ) hL K,
    oddMomentSliceLowerBound_zero_of_critical_line
      (fun _ hρ => RH_implies_on_line hRH hρ) hL K⟩

/-- **RH gives (C1).** -/
theorem cofinal_moment_slice_bounds_of_riemannHypothesis (hRH : RiemannHypothesis) :
    CofinalMomentSliceVanishingErrorBounds := by
  intro n hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  refine ⟨(n : ℝ) + 2, le_refl _, Or.inl ?_⟩
  refine ((momentSliceLowerBounds_zero_of_riemannHypothesis hRH (by linarith) _).1).mono ?_
  positivity

/-- **RH gives (SB)**, with floor zero. -/
theorem cofinal_moment_slice_semibounded_of_riemannHypothesis (hRH : RiemannHypothesis) :
    CofinalMomentSliceSemibounded := by
  refine ⟨0, le_refl _, fun R => ⟨max R 2 + 1, by linarith, Or.inl ?_⟩⟩
  have h2 : (2 : ℝ) ≤ max R 2 := le_max_right _ _
  exact (momentSliceLowerBounds_zero_of_riemannHypothesis hRH (by linarith) _).1

/-- **RH gives (PG)**, with exponent zero. -/
theorem fixed_parity_polynomial_of_riemannHypothesis (hRH : RiemannHypothesis) :
    FixedParityPolynomialMomentSliceBounds := by
  refine Or.inl ⟨1, 0, 1, one_pos, fun L hL => ?_⟩
  refine ((momentSliceLowerBounds_zero_of_riemannHypothesis hRH (by linarith) _).1).mono ?_
  norm_num

/-- **(C1) is equivalent to RH.** -/
theorem riemannHypothesis_iff_cofinal_moment_slice_bounds :
    RiemannHypothesis ↔ CofinalMomentSliceVanishingErrorBounds :=
  ⟨cofinal_moment_slice_bounds_of_riemannHypothesis, riemannHypothesis_of_cofinal_moment_slice_bounds⟩

/-- **(SB) is equivalent to RH.** -/
theorem riemannHypothesis_iff_cofinal_moment_slice_semibounded :
    RiemannHypothesis ↔ CofinalMomentSliceSemibounded :=
  ⟨cofinal_moment_slice_semibounded_of_riemannHypothesis,
    riemannHypothesis_of_cofinal_moment_slice_semibounded⟩

/-- **(PG) is equivalent to RH.** A sharp interface: proving (PG) is proving RH. -/
theorem riemannHypothesis_iff_fixed_parity_polynomial :
    RiemannHypothesis ↔ FixedParityPolynomialMomentSliceBounds :=
  ⟨fixed_parity_polynomial_of_riemannHypothesis, riemannHypothesis_of_fixed_parity_polynomial⟩

/-- **(SE) is equivalent to RH.** -/
theorem riemannHypothesis_iff_fixed_parity_subexponential :
    RiemannHypothesis ↔ FixedParitySubexponentialMomentSliceBounds :=
  ⟨fun h => fixed_parity_subexponential_of_polynomial (fixed_parity_polynomial_of_riemannHypothesis h),
    riemannHypothesis_of_fixed_parity_subexponential⟩

/-! ## The least-crossing cutoff when the first native space is already deep

`NativeDeepThresholdGroundData` stores the least Fourier cutoff `K ≥ 3` at which
the global pole-neutral bottom falls below `-eta`, with `D/3 < eta < D/2`. That
record allows the cutoff to be `3`, in which case both predecessor spaces at
cutoff `2` have dimension zero.

This section records the exact finite statement behind the round-seven paper
note: if the cutoff-3 bottom is already below `-D/2` (for instance because one
unit vector of either one-dimensional cutoff-3 parity space has energy below
`-D/2`), then every such packet has cutoff exactly `3`, and its predecessor is
empty. Whether a deep cutoff-3 vector exists at a given aperture is an analytic
question that this section does not address.

These statements are independent of the floor above. They live in this module
because the Round4 lane report admits 108 owned modules within its fixed JSON
budget. -/

/-- A packet forces `0 < D`, because `D/3 < eta < D/2`. -/
theorem nativeDeepThresholdGround_depth_pos {L : ℝ} {Kd : ℕ} {D : ℝ} {hL : 0 < L}
    (g : NativeDeepThresholdGroundData L Kd D hL) : 0 < D := by
  have h1 := g.eta_lower
  have h2 := g.eta_upper
  linarith

/-- **Least crossing at the first native cutoff.** If the cutoff-3 global bottom is
below `-D/2`, the stored least-crossing cutoff is `3`. -/
theorem nativeDeepThresholdGround_cutoff_eq_three_of_bottom_three_lt
    {L : ℝ} {Kd : ℕ} {D : ℝ} {hL : 0 < L} (g : NativeDeepThresholdGroundData L Kd D hL)
    (h3 : poleNeutralGlobalRayleighBottom L 3 hL le_rfl < -(D / 2)) :
    g.cutoff = 3 := by
  by_contra hne
  have hlt : 3 < g.cutoff := lt_of_le_of_ne g.cutoff_nonempty (Ne.symm hne)
  have hKd : 3 ≤ Kd := le_trans g.cutoff_nonempty g.cutoff_le_detector
  have hb := g.earlier_bottoms 3 le_rfl hlt
  have hgap := nativeDeepThresholdGap_pos D Kd (nativeDeepThresholdGround_depth_pos g) hKd
  have hη := g.eta_upper
  linarith

/-- In that case both predecessor spaces are zero-dimensional. -/
theorem nativeDeepThresholdGround_predecessor_empty_of_bottom_three_lt
    {L : ℝ} {Kd : ℕ} {D : ℝ} {hL : 0 < L} (g : NativeDeepThresholdGroundData L Kd D hL)
    (h3 : poleNeutralGlobalRayleighBottom L 3 hL le_rfl < -(D / 2)) :
    Module.finrank ℂ (poleNeutralEvenSubspace L 2) = 0 ∧
      Module.finrank ℂ (poleNeutralOddSubspace L 2) = 0 :=
  g.first_predecessor_empty (nativeDeepThresholdGround_cutoff_eq_three_of_bottom_three_lt g h3)

/-- One deep unit vector in the even cutoff-3 space puts the least crossing at `3`. -/
theorem nativeDeepThresholdGround_cutoff_eq_three_of_even_trial
    {L : ℝ} {Kd : ℕ} {D : ℝ} {hL : 0 < L} (g : NativeDeepThresholdGroundData L Kd D hL)
    (u : poleNeutralEvenSubspace L 3) (hu : ‖u‖ = 1)
    (he : evenNativeEnergy L 3 u < -(D / 2)) :
    g.cutoff = 3 := by
  refine nativeDeepThresholdGround_cutoff_eq_three_of_bottom_three_lt g ?_
  have hb := poleNeutralEvenRayleighBottom_mul_norm_sq_le hL 3 le_rfl u
  rw [hu, one_pow, mul_one] at hb
  have hmin : poleNeutralGlobalRayleighBottom L 3 hL le_rfl ≤
      poleNeutralEvenRayleighBottom L 3 hL le_rfl := min_le_left _ _
  unfold evenNativeEnergy at he
  linarith

/-- One deep unit vector in the odd cutoff-3 space puts the least crossing at `3`. -/
theorem nativeDeepThresholdGround_cutoff_eq_three_of_odd_trial
    {L : ℝ} {Kd : ℕ} {D : ℝ} {hL : 0 < L} (g : NativeDeepThresholdGroundData L Kd D hL)
    (v : poleNeutralOddSubspace L 3) (hv : ‖v‖ = 1)
    (he : oddNativeEnergy L 3 v < -(D / 2)) :
    g.cutoff = 3 := by
  refine nativeDeepThresholdGround_cutoff_eq_three_of_bottom_three_lt g ?_
  have hb := poleNeutralOddRayleighBottom_mul_norm_sq_le hL 3 le_rfl v
  rw [hv, one_pow, mul_one] at hb
  have hmin : poleNeutralGlobalRayleighBottom L 3 hL le_rfl ≤
      poleNeutralOddRayleighBottom L 3 hL le_rfl := min_le_right _ _
  unfold oddNativeEnergy at he
  linarith

end Zeta23.OPICARound4.ArithmeticFrontier
