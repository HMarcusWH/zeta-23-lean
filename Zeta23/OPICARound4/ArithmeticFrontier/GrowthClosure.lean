import Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure
import Zeta23.CCM.OriginalDetectorFinitePhaseNativeProducer
import Mathlib.Analysis.Complex.Exponential

/-!
# Coarse-growth consumers: fixed-parity subexponential and polynomial bounds

The existing native producers `exists_originalDetectorFiniteEvenPhase_native_depth`
and `exists_originalDetectorFiniteOddPhase_native_depth` give, under an
off-line zero with displacement `δ = |Re ρ - 1/2|` and any `0 < β < δ`, unit
native phase vectors at arbitrarily late apertures, at the literal quartic
cutoff, with energy at most `-exp (β L)`. This module

* proves that these normalized vectors lie in the exact moment slices of
  `MomentSlices` (the phase moment lemmas plus closure under scaling);
* proves that a fixed-parity lower bound with one rate `α ≥ 0`,
  `Q_p ≥ -C e^{αL}`, at every sufficiently large aperture, excludes every zero
  with displacement greater than `α` (it does not prove RH for `α > 0`);
* proves the consumers (SE) and (PG): a fixed-parity bound with every positive
  exponential rate, or with polynomial growth `C (1 + L)^d`, at every
  sufficiently large aperture implies Mathlib's `RiemannHypothesis`.

The parity is fixed before the rate and the aperture; the bounds are required
at every sufficiently large aperture, not on a cofinal subset. The premises
(SE) and (PG) are OPEN arithmetic suppliers; these theorems are conditional
reductions and close nothing.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open CCM ExceptionalZero OPICARound3 Filter

/-- The normalized native even phase lies in the even quartic moment slice. -/
theorem originalDetectorFiniteEvenPhaseUnit_mem_evenMomentSlice (c : ℝ) {L : ℝ}
    (hL : 2 ≤ L) :
    originalDetectorFiniteEvenPhaseUnit c hL ∈
      evenMomentSlice L (originalDetectorQuarticCutoff L) := by
  have h0 : originalDetectorFiniteEvenPhase c hL ∈
      evenMomentSlice L (originalDetectorQuarticCutoff L) :=
    (mem_evenMomentSlice_iff _ _ _).mpr (originalDetectorFiniteEvenPhase_moment_four c hL)
  unfold originalDetectorFiniteEvenPhaseUnit
  exact Submodule.smul_mem _ _ h0

/-- The normalized native odd phase lies in the odd moment slice. -/
theorem originalDetectorFiniteOddPhaseUnit_mem_oddMomentSlice (c : ℝ) {L : ℝ}
    (hL : 2 ≤ L) :
    originalDetectorFiniteOddPhaseUnit c hL ∈
      oddMomentSlice L (originalDetectorQuarticCutoff L) := by
  have h0 : originalDetectorFiniteOddPhase c hL ∈
      oddMomentSlice L (originalDetectorQuarticCutoff L) :=
    (mem_oddMomentSlice_iff _ _ _).mpr
      ⟨originalDetectorFiniteOddPhase_moment_three c hL,
        originalDetectorFiniteOddPhase_moment_five c hL⟩
  unfold originalDetectorFiniteOddPhaseUnit
  exact Submodule.smul_mem _ _ h0

/-- Exponential-depth unit witnesses in the exact even slice at arbitrarily late
apertures. The aperture is produced by the native producer; it is not chosen. -/
theorem exists_evenMomentSlice_exp_depth (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (R : ℝ) :
    ∃ L : ℝ, max R 4 < L ∧
      ∃ u : poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L),
        u ∈ evenMomentSlice L (originalDetectorQuarticCutoff L) ∧ ‖u‖ = 1 ∧
        evenNativeEnergy L (originalDetectorQuarticCutoff L) u ≤ -Real.exp (β * L) := by
  obtain ⟨d, hunit, hdepth⟩ := exists_originalDetectorFiniteEvenPhase_native_depth ρ hβ hβρ R
  exact ⟨_, d.late, _, originalDetectorFiniteEvenPhaseUnit_mem_evenMomentSlice _ _,
    hunit, hdepth⟩

/-- Exponential-depth unit witnesses in the exact odd slice at arbitrarily late
apertures, constructed independently of the even ones. -/
theorem exists_oddMomentSlice_exp_depth (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (R : ℝ) :
    ∃ L : ℝ, max R 4 < L ∧
      ∃ v : poleNeutralOddSubspace L (originalDetectorQuarticCutoff L),
        v ∈ oddMomentSlice L (originalDetectorQuarticCutoff L) ∧ ‖v‖ = 1 ∧
        oddNativeEnergy L (originalDetectorQuarticCutoff L) v ≤ -Real.exp (β * L) := by
  obtain ⟨d, hunit, hdepth⟩ := exists_originalDetectorFiniteOddPhase_native_depth ρ hβ hβρ R
  exact ⟨_, d.late, _, originalDetectorFiniteOddPhaseUnit_mem_oddMomentSlice _ _,
    hunit, hdepth⟩

/-- A fixed-rate even bound: one rate `α`, one constant, every large aperture. -/
def EvenFixedRateMomentSliceBound (α : ℝ) : Prop :=
  ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L →
    EvenMomentSliceLowerBound L (originalDetectorQuarticCutoff L) (C * Real.exp (α * L))

/-- A fixed-rate odd bound: one rate `α`, one constant, every large aperture. -/
def OddFixedRateMomentSliceBound (α : ℝ) : Prop :=
  ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L →
    OddMomentSliceLowerBound L (originalDetectorQuarticCutoff L) (C * Real.exp (α * L))

/-- **Contract (SE).** One parity fixed before every positive rate, with the
bound at every sufficiently large aperture. This proposition is OPEN. -/
def FixedParitySubexponentialMomentSliceBounds : Prop :=
  (∀ α : ℝ, 0 < α → EvenFixedRateMomentSliceBound α) ∨
    (∀ α : ℝ, 0 < α → OddFixedRateMomentSliceBound α)

/-- **Contract (PG).** One parity, one constant, one natural exponent, and a
polynomial loss at every sufficiently large aperture. This proposition is OPEN. -/
def FixedParityPolynomialMomentSliceBounds : Prop :=
  (∃ (C : ℝ) (d : ℕ) (L₀ : ℝ), 0 < C ∧ ∀ L : ℝ, L₀ ≤ L →
      EvenMomentSliceLowerBound L (originalDetectorQuarticCutoff L) (C * (1 + L) ^ d)) ∨
    (∃ (C : ℝ) (d : ℕ) (L₀ : ℝ), 0 < C ∧ ∀ L : ℝ, L₀ ≤ L →
      OddMomentSliceLowerBound L (originalDetectorQuarticCutoff L) (C * (1 + L) ^ d))

/-- Exponential domination used by both parities: past `log C / (β - α)` the
depth `exp (β L)` exceeds the allowance `C exp (α L)`. -/
theorem mul_exp_lt_exp_of_log_div_lt {C α β L : ℝ} (hC : 0 < C) (hαβ : α < β)
    (hL : Real.log C / (β - α) < L) :
    C * Real.exp (α * L) < Real.exp (β * L) := by
  have hpos : 0 < β - α := sub_pos.mpr hαβ
  have hlog : Real.log C < (β - α) * L := by
    rw [div_lt_iff₀ hpos] at hL
    linarith
  have hexp : C < Real.exp ((β - α) * L) := by
    calc C = Real.exp (Real.log C) := (Real.exp_log hC).symm
      _ < Real.exp ((β - α) * L) := Real.exp_lt_exp.mpr hlog
  have hsplit : Real.exp (β * L) = Real.exp ((β - α) * L) * Real.exp (α * L) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit]
  exact mul_lt_mul_of_pos_right hexp (Real.exp_pos _)

/-- **Fixed-rate exclusion (even).** An even bound with rate `α ≥ 0` at every
large aperture excludes every zero with displacement greater than `α`. -/
theorem abs_re_sub_half_le_of_even_fixed_rate {α : ℝ} (hα : 0 ≤ α)
    (h : EvenFixedRateMomentSliceBound α) (ρ : zetaZeroConfig.carrier) :
    |(ρ : ℂ).re - 1 / 2| ≤ α := by
  by_contra hgt
  replace hgt := not_le.mp hgt
  obtain ⟨C, L₀, hC, hb⟩ := h
  set δ := |(ρ : ℂ).re - 1 / 2| with hδ
  have hαβ : α < (α + δ) / 2 := by linarith
  have hβδ : (α + δ) / 2 < δ := by linarith
  have hβ : 0 < (α + δ) / 2 := by linarith
  obtain ⟨L, hLR, u, hu, hn, he⟩ := exists_evenMomentSlice_exp_depth ρ hβ hβδ
    (max L₀ (Real.log C / ((α + δ) / 2 - α)))
  have hmax : max L₀ (Real.log C / ((α + δ) / 2 - α)) < L :=
    lt_of_le_of_lt (le_max_left _ _) hLR
  have hL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hmax.le
  have hlog : Real.log C / ((α + δ) / 2 - α) < L := lt_of_le_of_lt (le_max_right _ _) hmax
  have hlb := hb L hL₀ u hu
  rw [hn] at hlb
  have hdom := mul_exp_lt_exp_of_log_div_lt hC hαβ hlog
  nlinarith

/-- **Fixed-rate exclusion (odd).** -/
theorem abs_re_sub_half_le_of_odd_fixed_rate {α : ℝ} (hα : 0 ≤ α)
    (h : OddFixedRateMomentSliceBound α) (ρ : zetaZeroConfig.carrier) :
    |(ρ : ℂ).re - 1 / 2| ≤ α := by
  by_contra hgt
  replace hgt := not_le.mp hgt
  obtain ⟨C, L₀, hC, hb⟩ := h
  set δ := |(ρ : ℂ).re - 1 / 2| with hδ
  have hαβ : α < (α + δ) / 2 := by linarith
  have hβδ : (α + δ) / 2 < δ := by linarith
  have hβ : 0 < (α + δ) / 2 := by linarith
  obtain ⟨L, hLR, v, hv, hn, he⟩ := exists_oddMomentSlice_exp_depth ρ hβ hβδ
    (max L₀ (Real.log C / ((α + δ) / 2 - α)))
  have hmax : max L₀ (Real.log C / ((α + δ) / 2 - α)) < L :=
    lt_of_le_of_lt (le_max_left _ _) hLR
  have hL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hmax.le
  have hlog : Real.log C / ((α + δ) / 2 - α) < L := lt_of_le_of_lt (le_max_right _ _) hmax
  have hlb := hb L hL₀ v hv
  rw [hn] at hlb
  have hdom := mul_exp_lt_exp_of_log_div_lt hC hαβ hlog
  nlinarith

/-- (SE) excludes every off-line zero of the actual zero configuration. -/
theorem no_off_line_zero_of_fixed_parity_subexponential
    (h : FixedParitySubexponentialMomentSliceBounds) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 := by
  intro ρ
  have hle : ∀ α : ℝ, 0 < α → |(ρ : ℂ).re - 1 / 2| ≤ α := by
    intro α hα
    rcases h with he | ho
    · exact abs_re_sub_half_le_of_even_fixed_rate hα.le (he α hα) ρ
    · exact abs_re_sub_half_le_of_odd_fixed_rate hα.le (ho α hα) ρ
  have h0 : |(ρ : ℂ).re - 1 / 2| ≤ 0 := by
    by_contra hpos
    replace hpos := not_le.mp hpos
    have := hle (|(ρ : ℂ).re - 1 / 2| / 2) (by linarith)
    linarith
  have := abs_nonpos_iff.mp h0
  linarith

/-- **Conditional reduction (SE) → RH.** The arithmetic premise remains OPEN. -/
theorem riemannHypothesis_of_fixed_parity_subexponential
    (h : FixedParitySubexponentialMomentSliceBounds) : RiemannHypothesis := by
  intro s hz htriv hs1
  have hm : s ∈ zetaZeroConfig.carrier :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  exact no_off_line_zero_of_fixed_parity_subexponential h ⟨s, hm⟩

/-- Polynomial growth is dominated by every positive exponential rate:
`(1 + L)^d ≤ d! e^α α^{-d} e^{αL}` for `L ≥ -1`. -/
theorem one_add_pow_le_mul_exp {α : ℝ} (hα : 0 < α) (d : ℕ) {L : ℝ} (hL : -1 ≤ L) :
    (1 + L) ^ d ≤ (d.factorial * Real.exp α / α ^ d) * Real.exp (α * L) := by
  have hx : 0 ≤ α * (1 + L) := mul_nonneg hα.le (by linarith)
  have hfac := Real.pow_div_factorial_le_exp (α * (1 + L)) hx d
  have hfpos : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hαd : 0 < α ^ d := pow_pos hα d
  have hexp : Real.exp (α * (1 + L)) = Real.exp α * Real.exp (α * L) := by
    rw [← Real.exp_add]
    ring_nf
  rw [mul_pow, hexp, div_le_iff₀ hfpos] at hfac
  rw [div_mul_eq_mul_div, le_div_iff₀ hαd]
  nlinarith [Real.exp_pos α, Real.exp_pos (α * L), pow_nonneg (show (0 : ℝ) ≤ 1 + L by linarith) d]

/-- (PG) implies (SE) by explicit eventual domination; the parity is unchanged. -/
theorem fixed_parity_subexponential_of_polynomial
    (h : FixedParityPolynomialMomentSliceBounds) :
    FixedParitySubexponentialMomentSliceBounds := by
  rcases h with ⟨C, d, L₀, hC, hb⟩ | ⟨C, d, L₀, hC, hb⟩
  · left
    intro α hα
    refine ⟨C * (d.factorial * Real.exp α / α ^ d), max L₀ 0, ?_, ?_⟩
    · have hfpos : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
      positivity
    · intro L hL
      have hL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL
      have hL0 : 0 ≤ L := le_trans (le_max_right _ _) hL
      refine (hb L hL₀).mono ?_
      have hdom := one_add_pow_le_mul_exp hα d (show -1 ≤ L by linarith)
      calc C * (1 + L) ^ d ≤ C * ((d.factorial * Real.exp α / α ^ d) * Real.exp (α * L)) :=
            mul_le_mul_of_nonneg_left hdom hC.le
        _ = C * (d.factorial * Real.exp α / α ^ d) * Real.exp (α * L) := by ring
  · right
    intro α hα
    refine ⟨C * (d.factorial * Real.exp α / α ^ d), max L₀ 0, ?_, ?_⟩
    · have hfpos : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
      positivity
    · intro L hL
      have hL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL
      have hL0 : 0 ≤ L := le_trans (le_max_right _ _) hL
      refine (hb L hL₀).mono ?_
      have hdom := one_add_pow_le_mul_exp hα d (show -1 ≤ L by linarith)
      calc C * (1 + L) ^ d ≤ C * ((d.factorial * Real.exp α / α ^ d) * Real.exp (α * L)) :=
            mul_le_mul_of_nonneg_left hdom hC.le
        _ = C * (d.factorial * Real.exp α / α ^ d) * Real.exp (α * L) := by ring

/-- **Conditional reduction (PG) → RH.** The arithmetic premise remains OPEN. -/
theorem riemannHypothesis_of_fixed_parity_polynomial
    (h : FixedParityPolynomialMomentSliceBounds) : RiemannHypothesis :=
  riemannHypothesis_of_fixed_parity_subexponential (fixed_parity_subexponential_of_polynomial h)

/-- Contrapositive: one actual off-line zero refutes (PG) in both parities. -/
theorem not_fixed_parity_polynomial_of_off_line_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ¬ FixedParityPolynomialMomentSliceBounds :=
  fun h => hoff (no_off_line_zero_of_fixed_parity_subexponential
    (fixed_parity_subexponential_of_polynomial h) ρ)

end Zeta23.OPICARound4.ArithmeticFrontier
