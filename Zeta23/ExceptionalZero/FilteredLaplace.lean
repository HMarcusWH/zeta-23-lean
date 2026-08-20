import Zeta23.ExceptionalZero.FilteredResolvent
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Set MeasureTheory Filter

/-- The concrete zeta-zero carrier is countable using only the already-proved local finiteness of
zeros in bounded ordinate windows.  No Riemann--von Mangoldt asymptotic or prime-side input is used. -/
theorem zetaZeroCarrier_countable : zetaZeroConfig.carrier.Countable := by
  let S : ℕ → Set ℂ := fun n =>
    zetaZeroConfig.carrier ∩
      {ρ : ℂ | -(n : ℝ) < ρ.im ∧ ρ.im ≤ (n : ℝ)}
  have hS : ∀ n : ℕ, (S n).Finite := by
    intro n
    simpa [S] using zetaZeroConfig.finite_window (-(n : ℝ)) (n : ℝ)
  have hU : (⋃ n : ℕ, S n).Countable :=
    Set.countable_iUnion (fun n => (hS n).countable)
  apply hU.mono
  intro ρ hρ
  obtain ⟨n, hn⟩ := exists_nat_gt |ρ.im|
  have hb : -(n : ℝ) < ρ.im ∧ ρ.im < (n : ℝ) := abs_lt.mp hn
  exact Set.mem_iUnion.mpr ⟨n, hρ, hb.1, hb.2.le⟩

/-- In the safe half-plane `Re z > 1`, every filtered zero mode has strictly negative Laplace
exponent when the center lies on the critical line. -/
theorem filteredLaplaceExponent_re_neg {c z : ℂ} (hc : c.re = 1 / 2)
    (hz : 1 < z.re) (ρ : zetaZeroConfig.carrier) :
    (2 * ((ρ : ℂ) - c) - z).re < 0 := by
  have hρ : (ρ : ℂ).re < 1 := ρ.2.2.2
  simp [Complex.mul_re, hc]
  linarith

/-- A single filtered zero mode has exactly the expected Laplace-resolvent transform in the safe
half-plane.  This theorem is purely termwise; the full-family interchange is proved separately. -/
theorem integral_laplace_filteredZeroTerm
    {φ : ZeroFilter} {c z : ℂ} (hc : c.re = 1 / 2) (hz : 1 < z.re)
    (ρ : zetaZeroConfig.carrier) :
    ∫ a : ℝ in Set.Ioi 0,
      Complex.exp (-z * (a : ℂ)) * filteredZeroTerm φ c ρ a =
      filteredResolventTerm φ c ρ z := by
  let k : ℂ := 2 * ((ρ : ℂ) - c) - z
  have hkneg : k.re < 0 := by
    dsimp [k]
    exact filteredLaplaceExponent_re_neg hc hz ρ
  have heq : ∀ a : ℝ,
      Complex.exp (-z * (a : ℂ)) * filteredZeroTerm φ c ρ a =
        zeroFilterCoeff φ ρ * Complex.exp (k * (a : ℂ)) := by
    intro a
    unfold filteredZeroTerm
    calc
      Complex.exp (-z * (a : ℂ)) *
          (zeroFilterCoeff φ ρ *
            Complex.exp ((2 * ((ρ : ℂ) - c)) * (a : ℂ))) =
          zeroFilterCoeff φ ρ *
            (Complex.exp (-z * (a : ℂ)) *
              Complex.exp ((2 * ((ρ : ℂ) - c)) * (a : ℂ))) := by ring
      _ = zeroFilterCoeff φ ρ *
          Complex.exp ((-z * (a : ℂ)) +
            ((2 * ((ρ : ℂ) - c)) * (a : ℂ))) := by
        rw [Complex.exp_add]
      _ = zeroFilterCoeff φ ρ * Complex.exp (k * (a : ℂ)) := by
        congr 2
        dsimp [k]
        ring
  have heqOn : Set.EqOn
      (fun a : ℝ => Complex.exp (-z * (a : ℂ)) * filteredZeroTerm φ c ρ a)
      (fun a : ℝ => zeroFilterCoeff φ ρ * Complex.exp (k * (a : ℂ)))
      (Set.Ioi 0) := by
    intro a _
    exact heq a
  rw [setIntegral_congr_fun measurableSet_Ioi heqOn]
  rw [integral_const_mul]
  rw [integral_exp_mul_complex_Ioi hkneg 0]
  have hk : k ≠ 0 := by
    intro h
    rw [h] at hkneg
    norm_num at hkneg
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  unfold filteredResolventTerm
  have hden_eq : z - 2 * ((ρ : ℂ) - c) = -k := by
    dsimp [k]
    ring
  rw [hden_eq]
  simp [div_eq_mul_inv]

/-- The safe-half-plane Laplace integrand has a zero-independent exponential envelope.  This is the
claim-bearing domination estimate used to justify exchanging the zero `tsum` with the integral. -/
theorem norm_laplace_filteredZeroTerm_le
    {φ : ZeroFilter} {c z : ℂ} (hc : c.re = 1 / 2) (_hz : 1 < z.re)
    (ρ : zetaZeroConfig.carrier) {a : ℝ} (ha : 0 ≤ a) :
    ‖Complex.exp (-z * (a : ℂ)) * filteredZeroTerm φ c ρ a‖ ≤
      ‖zeroFilterCoeff φ ρ‖ * Real.exp (-(z.re - 1) * a) := by
  have hρ : (ρ : ℂ).re < 1 := ρ.2.2.2
  unfold filteredZeroTerm
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  calc
    Real.exp (-z * (a : ℂ)).re *
        (‖zeroFilterCoeff φ ρ‖ *
          Real.exp (((2 : ℂ) * ((ρ : ℂ) - c)) * (a : ℂ)).re) =
        ‖zeroFilterCoeff φ ρ‖ *
          (Real.exp (-z * (a : ℂ)).re *
            Real.exp (((2 : ℂ) * ((ρ : ℂ) - c)) * (a : ℂ)).re) := by ring
    _ = ‖zeroFilterCoeff φ ρ‖ *
        Real.exp ((-z * (a : ℂ)).re +
          (((2 : ℂ) * ((ρ : ℂ) - c)) * (a : ℂ)).re) := by
      rw [Real.exp_add]
    _ ≤ ‖zeroFilterCoeff φ ρ‖ * Real.exp (-(z.re - 1) * a) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      simp [Complex.mul_re, hc]
      nlinarith

/-- The complete filtered zero family has the filtered resolvent as its Laplace transform throughout
the safe half-plane `Re z > 1`.  The interchange is justified by a countable dominated series with
majorant `‖a_ρ‖ exp(-(Re z - 1)a)`; no analytic continuation is used or claimed here. -/
theorem integral_laplace_filteredZeroFamily
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c z : ℂ} (hc : c.re = 1 / 2) (hz : 1 < z.re) :
    ∫ a : ℝ in Set.Ioi 0,
      Complex.exp (-z * (a : ℂ)) * filteredZeroFamily φ c a =
      filteredResolvent φ c z := by
  letI : Countable zetaZeroConfig.carrier := zetaZeroCarrier_countable.to_subtype
  let F : zetaZeroConfig.carrier → ℝ → ℂ := fun ρ a =>
    Complex.exp (-z * (a : ℂ)) * filteredZeroTerm φ c ρ a
  let bound : zetaZeroConfig.carrier → ℝ → ℝ := fun ρ a =>
    ‖zeroFilterCoeff φ ρ‖ * Real.exp (-(z.re - 1) * a)
  have hcoeff : Summable (fun ρ : zetaZeroConfig.carrier => ‖zeroFilterCoeff φ ρ‖) := by
    simpa [AbsolutelySummableZeroFilter] using hφ
  have hF_meas : ∀ ρ : zetaZeroConfig.carrier,
      AEStronglyMeasurable (F ρ) (volume.restrict (Set.Ioi 0)) := by
    intro ρ
    apply Continuous.aestronglyMeasurable
    dsimp [F, filteredZeroTerm]
    fun_prop
  have hbound : ∀ ρ : zetaZeroConfig.carrier,
      ∀ᵐ a ∂(volume.restrict (Set.Ioi 0)), ‖F ρ a‖ ≤ bound ρ a := by
    intro ρ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact norm_laplace_filteredZeroTerm_le hc hz ρ ha.le
  have hbound_summable :
      ∀ᵐ a ∂(volume.restrict (Set.Ioi 0)), Summable (fun ρ => bound ρ a) := by
    exact Eventually.of_forall fun a => by
      dsimp [bound]
      exact hcoeff.mul_right (Real.exp (-(z.re - 1) * a))
  have hdecay : -(z.re - 1) < 0 := by linarith
  have hbase : IntegrableOn (fun a : ℝ => Real.exp (-(z.re - 1) * a)) (Set.Ioi 0) := by
    simpa using (integrableOn_exp_mul_Ioi (a := -(z.re - 1)) hdecay 0)
  have hsumBoundInt : IntegrableOn
      (fun a : ℝ => (∑' ρ : zetaZeroConfig.carrier, ‖zeroFilterCoeff φ ρ‖) *
        Real.exp (-(z.re - 1) * a)) (Set.Ioi 0) :=
    hbase.const_mul (∑' ρ : zetaZeroConfig.carrier, ‖zeroFilterCoeff φ ρ‖)
  have hbound_tsum : ∀ a : ℝ,
      (∑' ρ : zetaZeroConfig.carrier, bound ρ a) =
        (∑' ρ : zetaZeroConfig.carrier, ‖zeroFilterCoeff φ ρ‖) *
          Real.exp (-(z.re - 1) * a) := by
    intro a
    dsimp [bound]
    exact hcoeff.tsum_mul_right (Real.exp (-(z.re - 1) * a))
  have hbound_integrable : Integrable
      (fun a : ℝ => ∑' ρ : zetaZeroConfig.carrier, bound ρ a)
      (volume.restrict (Set.Ioi 0)) := by
    exact hsumBoundInt.congr (Eventually.of_forall fun a => (hbound_tsum a).symm)
  have hlim : ∀ᵐ a ∂(volume.restrict (Set.Ioi 0)),
      HasSum (fun ρ : zetaZeroConfig.carrier => F ρ a)
        (Complex.exp (-z * (a : ℂ)) * filteredZeroFamily φ c a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have hs := summable_filteredZeroTerm hφ hc ha.le
    have hm := hs.hasSum.mul_left (Complex.exp (-z * (a : ℂ)))
    simpa [F, filteredZeroFamily] using hm
  have hseries := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi 0))
    bound hF_meas hbound hbound_summable hbound_integrable hlim
  have hseries' : HasSum
      (fun ρ : zetaZeroConfig.carrier => filteredResolventTerm φ c ρ z)
      (∫ a : ℝ in Set.Ioi 0,
        Complex.exp (-z * (a : ℂ)) * filteredZeroFamily φ c a) := by
    exact hseries.congr (fun ρ : zetaZeroConfig.carrier => by
      simpa [F] using integral_laplace_filteredZeroTerm (φ := φ) hc hz ρ)
  have hres : HasSum
      (fun ρ : zetaZeroConfig.carrier => filteredResolventTerm φ c ρ z)
      (filteredResolvent φ c z) := by
    have hs := summable_filteredResolventTerm hφ hc hz
    simpa [filteredResolvent] using hs.hasSum
  exact hseries'.unique hres

end Zeta23.ExceptionalZero
