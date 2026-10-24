import Zeta23.OPICAFollowup.MaskedNativeRate

/-! Independent consumers for the complete scheduled mask interfaces.
Constants precede all real horizons and allowed palettes. No Theta equality
is an input, and both retained-minus-full orientations are tested. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace OPICARepairConsumers

example (r d : ℕ) (hr : 2 ≤ r) (hd : r - 1 ≤ d)
    (C η K : ℝ) (hC : 1 < C) (hη : 0 ≤ η) :
    Measurable nativeMovingPrimitiveCutoff ∧
    ∃ a b a' b' T₀ : ℝ, 0 ≤ b ∧ 0 ≤ b' ∧ 1 ≤ T₀ ∧
      (∀ T : ℝ, T₀ ≤ T → ∀ Q : ℕ, Squarefree Q → (Q : ℝ) ≤ T ^ η →
        Real.log (1 + |nativeRawLow d r Q (logSlackY r K T) C T|)
          ≤ a + Real.sqrt T + b * Real.log T ∧
        Real.log (1 + |nativeAbsorbedLow d r Q hd (logSlackY r K T) C T|)
          ≤ a' + Real.sqrt T + b' * Real.log T) ∧
      (∀ (τ : HorizonSchedule) (Q : ℕ → ℕ), (∀ n, Squarefree (Q n)) →
        (∀ᶠ n in atTop, (Q n : ℝ) ≤ τ.time n ^ η) →
        SubexpAlong τ (fun n => nativeRawLow d r (Q n)
          (logSlackY r K (τ.time n)) C (τ.time n)) ∧
        SubexpAlong τ (fun n => nativeAbsorbedLow d r (Q n) hd
          (logSlackY r K (τ.time n)) C (τ.time n)) ∧
        (∀ᶠ n in atTop,
          nativeRawHigh d r (Q n) (logSlackY r K (τ.time n)) C (τ.time n) -
            nativeAbsorbedHigh d r (Q n) hd (logSlackY r K (τ.time n)) C (τ.time n) =
          nativeAbsorbedLow d r (Q n) hd (logSlackY r K (τ.time n)) C (τ.time n) -
            nativeRawLow d r (Q n) (logSlackY r K (τ.time n)) C (τ.time n))) := by
  exact log_slack_both_low_masks_subexp r d hr hd C η K hC hη

example (r d : ℕ) (hr : 2 ≤ r) (hd : r - 1 ≤ d)
    (C η K : ℝ) (hC : 1 < C) (hη : 0 ≤ η)
    (hK : C + (r : ℝ) * η + 2 * r < K)
    (τ : HorizonSchedule) (Q : ℕ → ℕ)
    (hQ : ∀ n, Squarefree (Q n))
    (hbudget : ∀ᶠ n in atTop, (Q n : ℝ) ≤ τ.time n ^ η) :
    Tendsto (fun n =>
      Real.log (1 + max (nativeRawHigh d r (Q n)
        (logSlackY r K (τ.time n)) C (τ.time n)) 0) / (2 * τ.time n) -
      Real.log (1 + ∫ t in Icc (τ.time n - C * Real.log (τ.time n)) (τ.time n),
        (primeFieldFamily d t)^2) / (2 * τ.time n)) atTop (𝓝 0) ∧
    Tendsto (fun n =>
      Real.log (1 + max (nativeAbsorbedHigh d r (Q n) hd
        (logSlackY r K (τ.time n)) C (τ.time n)) 0) / (2 * τ.time n) -
      Real.log (1 + ∫ t in Icc (τ.time n - C * Real.log (τ.time n)) (τ.time n),
        (primeFieldFamily d t)^2) / (2 * τ.time n)) atTop (𝓝 0) := by
  exact log_slack_masked_energy_rate_difference r d hr hd C η K hC hη hK τ Q hQ hbudget

/-- The original Pj specialization, not an order-zero or autocorrelation source. -/
example (τ : HorizonSchedule) :
    Tendsto (fun n => positiveRate τ (fun j => nativeRawHigh 1 2 1
      (logSlackY 2 8 (τ.time j)) 2 (τ.time j)) n -
      Real.log (1 + nativePhysicalWindowEnergy 1 2 (τ.time n))/(2*τ.time n)) atTop (𝓝 0) ∧
    Tendsto (fun n => positiveRate τ (fun j => nativeAbsorbedHigh 1 2 1 (by norm_num)
      (logSlackY 2 8 (τ.time j)) 2 (τ.time j)) n -
      Real.log (1 + nativePhysicalWindowEnergy 1 2 (τ.time n))/(2*τ.time n)) atTop (𝓝 0) := by
  apply log_slack_masked_energy_rate_difference 2 1 (by norm_num) (by norm_num)
    2 0 8 (by norm_num) (by norm_num) (by norm_num) τ (fun _ => 1)
    (fun _ => by simp)
  filter_upwards with n
  simp

/-- Actual L2 realizations remain available on every real initial window,
including reversed or degenerate intervals. No eventual positivity is needed
for constructing the vectors or their exact energy identity. -/
example (d : ℕ) (C T : ℝ) :
    ‖nativePrimeWindowVector d C T‖^2 =
      ∫ t in Icc (T-C*Real.log T) T, (primeFieldFamily d t)^2 := by
  exact nativePrimeWindowVector_norm_sq d C T

example (f : ℝ → ℝ) (hf : Continuous f) (C T : ℝ) :
    MemLp ((Icc (T-C*Real.log T) T).indicator f) 2 (volume : Measure ℝ) := by
  exact nativeWindowFunction_memLp f hf C T

/-- A noninteger cutoff and a nonsquarefree total product remain in the
Dirichlet-convolution coefficient, rather than a pointwise power. -/
example : (((nativeLargeCoefficients 1 (3/2) ^ 2 : ArithmeticFunction ℝ)) 4) = 1 := by
  have h₁ : nativeLargeCoefficients 1 (3/2) 1=0 := by
    norm_num [nativeLargeCoefficients]
  have h₂ : nativeLargeCoefficients 1 (3/2) 2=(-1:ℝ) := by
    norm_num [nativeLargeCoefficients,nativeInverseCoefficients,coprimeCoefficients,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have h₄ : nativeLargeCoefficients 1 (3/2) 4=0 := by
    have hμ : ArithmeticFunction.moebius 4=0 := by
      convert ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two
        (by decide : (2:ℕ)≠0) using 1 <;> norm_num
    norm_num [nativeLargeCoefficients,nativeInverseCoefficients,coprimeCoefficients,hμ]
  have hanti : (4:ℕ).divisorsAntidiagonal={(1,4),(2,2),(4,1)} := by decide
  rw [pow_two,ArithmeticFunction.mul_apply,hanti]
  norm_num [h₁,h₂,h₄]

#print axioms Zeta23.OPICAFollowup.log_slack_both_low_masks_subexp
#print axioms Zeta23.OPICAFollowup.log_slack_masked_energy_rate_difference
#print axioms Zeta23.OPICAFollowup.nativeWindowVector_norm_sq
#print axioms Zeta23.OPICAFollowup.nativeTypeIWindowVector_tendsto_zero
end OPICARepairConsumers
