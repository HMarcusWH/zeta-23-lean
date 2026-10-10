import Zeta23.CCM.FiniteDictionary
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate Interval

/-!
# POST284-M04: Fourier convolution representation of the elementary source

For every real source coordinate `ω` (negative values included) and all
lattice indices,

`S_nm(ω) = π⁻¹ ∫_0^{2πω} cos(n t + m (2πω - t)) dt`,

including the diagonal `n = m`.  Consequently, for every complex coefficient
vector `u`, with `C_u(t) = ∑ u_n cos(n t)` and `T_u(t) = ∑ u_n sin(n t)`,

`quadraticForm (sourceMatrix ω N) u
   = π⁻¹ ∫_0^{2πω} [conj(C_u(t)) C_u(a-t) - conj(T_u(t)) T_u(a-t)] dt`,
`a = 2πω`,

in the repository orientation `∑ conj(u_i) S_ij u_j`.  The integral is real
because the source matrix is real symmetric, although the integrand need not
be pointwise real.  No sign is asserted.
-/

/-- Entrywise Fourier convolution representation of the elementary source. -/
theorem sourceEntry_eq_cos_integral (ω : ℝ) (n m : ℤ) :
    sourceEntry ω n m =
      (((1 / Real.pi) * ∫ t in (0 : ℝ)..(2 * Real.pi * ω),
          Real.cos ((n : ℝ) * t + (m : ℝ) * (2 * Real.pi * ω - t)) : ℝ) : ℂ) := by
  set a : ℝ := 2 * Real.pi * ω with ha
  by_cases h : n = m
  · subst h
    have hconst : ∀ t : ℝ, (n : ℝ) * t + (n : ℝ) * (a - t) = 2 * Real.pi * (n : ℝ) * ω := by
      intro t
      rw [ha]
      ring
    simp_rw [hconst]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, sourceEntry_self]
    unfold sourceDiagonal
    congr 1
    rw [ha]
    field_simp
  · have hc : ((n : ℝ) - m) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hF : ∀ t : ℝ,
        HasDerivAt (fun t => Real.sin (((n : ℝ) - m) * t + (m : ℝ) * a) / ((n : ℝ) - m))
          (Real.cos ((n : ℝ) * t + (m : ℝ) * (a - t))) t := by
      intro t
      have h1 := (((hasDerivAt_id t).const_mul ((n : ℝ) - m)).add_const
        ((m : ℝ) * a)).sin.div_const ((n : ℝ) - m)
      convert h1 using 1
      rw [show (n : ℝ) * t + (m : ℝ) * (a - t) = ((n : ℝ) - m) * id t + (m : ℝ) * a by
        simp only [id]; ring]
      field_simp
    have hcont : Continuous fun t : ℝ => Real.cos ((n : ℝ) * t + (m : ℝ) * (a - t)) := by
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
      (hcont.intervalIntegrable _ _)]
    rw [sourceEntry_of_ne _ h]
    unfold sourcePotential
    have hna : ((n : ℝ) - m) * a + (m : ℝ) * a = 2 * Real.pi * (n : ℝ) * ω := by
      rw [ha]; ring
    have hma : ((n : ℝ) - m) * 0 + (m : ℝ) * a = 2 * Real.pi * (m : ℝ) * ω := by
      rw [ha]; ring
    simp only [hna, hma]
    have hcC : (((n - m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr h
    push_cast
    field_simp

/-- Cosine profile `C_u(t) = ∑ u_n cos(n t)`. -/
def sourceCosProfile (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (t : ℝ) : ℂ :=
  ∑ i, u i * (Real.cos ((centeredIndex N i : ℝ) * t) : ℂ)

/-- Sine profile `T_u(t) = ∑ u_n sin(n t)`. -/
def sourceSinProfile (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (t : ℝ) : ℂ :=
  ∑ i, u i * (Real.sin ((centeredIndex N i : ℝ) * t) : ℂ)

/-- Pointwise kernel identity behind the convolution formula. -/
theorem sum_conj_cos_mul_eq_profiles (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (a t : ℝ) :
    ∑ i, ∑ j, conj (u i) *
        (Real.cos ((centeredIndex N i : ℝ) * t +
          (centeredIndex N j : ℝ) * (a - t)) : ℂ) * u j =
      conj (sourceCosProfile N u t) * sourceCosProfile N u (a - t) -
        conj (sourceSinProfile N u t) * sourceSinProfile N u (a - t) := by
  unfold sourceCosProfile sourceSinProfile
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.cos_add]
  push_cast
  ring

/-- **Complex Fourier convolution representation of the elementary source
energy.** -/
theorem quadraticForm_sourceMatrix_eq_convolution (ω : ℝ) (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    quadraticForm (sourceMatrix ω N) u =
      ((1 / Real.pi : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..(2 * Real.pi * ω),
          (conj (sourceCosProfile N u t) * sourceCosProfile N u (2 * Real.pi * ω - t) -
            conj (sourceSinProfile N u t) * sourceSinProfile N u (2 * Real.pi * ω - t)) := by
  set a : ℝ := 2 * Real.pi * ω with ha
  have hentry : ∀ i j : Fin (2 * N + 1),
      sourceMatrix ω N i j =
        ((1 / Real.pi : ℝ) : ℂ) * ∫ t in (0 : ℝ)..a,
          (Real.cos ((centeredIndex N i : ℝ) * t +
            (centeredIndex N j : ℝ) * (a - t)) : ℂ) := by
    intro i j
    rw [sourceMatrix_apply, sourceEntry_eq_cos_integral, ← ha, Complex.ofReal_mul,
      intervalIntegral.integral_ofReal]
  have hcont : ∀ i j : Fin (2 * N + 1), Continuous fun t : ℝ =>
      conj (u i) * (Real.cos ((centeredIndex N i : ℝ) * t +
        (centeredIndex N j : ℝ) * (a - t)) : ℂ) * u j := by
    intro i j
    fun_prop
  have hterm : ∀ i j : Fin (2 * N + 1),
      conj (u i) * sourceMatrix ω N i j * u j =
        ((1 / Real.pi : ℝ) : ℂ) * ∫ t in (0 : ℝ)..a,
          conj (u i) * (Real.cos ((centeredIndex N i : ℝ) * t +
            (centeredIndex N j : ℝ) * (a - t)) : ℂ) * u j := by
    intro i j
    rw [hentry, intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
    ring
  let g : Fin (2 * N + 1) → Fin (2 * N + 1) → ℝ → ℂ := fun i j t =>
    conj (u i) * (Real.cos ((centeredIndex N i : ℝ) * t +
      (centeredIndex N j : ℝ) * (a - t)) : ℂ) * u j
  have hsum : ∀ i, ∑ j, (∫ t in (0 : ℝ)..a, g i j t) =
      ∫ t in (0 : ℝ)..a, ∑ j, g i j t := fun i =>
    (intervalIntegral.integral_finset_sum
      (fun j _ => (hcont i j).intervalIntegrable _ _)).symm
  have hsum2 : ∑ i, (∫ t in (0 : ℝ)..a, ∑ j, g i j t) =
      ∫ t in (0 : ℝ)..a, ∑ i, ∑ j, g i j t :=
    (intervalIntegral.integral_finset_sum
      (fun i _ => (continuous_finset_sum _ (fun j _ => hcont i j)).intervalIntegrable _ _)).symm
  unfold quadraticForm
  calc ∑ i, ∑ j, conj (u i) * sourceMatrix ω N i j * u j
      = ∑ i, ∑ j, ((1 / Real.pi : ℝ) : ℂ) * ∫ t in (0 : ℝ)..a, g i j t := by
        simp only [hterm, g]
    _ = ((1 / Real.pi : ℝ) : ℂ) * ∑ i, ∑ j, ∫ t in (0 : ℝ)..a, g i j t := by
        simp only [Finset.mul_sum]
    _ = ((1 / Real.pi : ℝ) : ℂ) * ∫ t in (0 : ℝ)..a, ∑ i, ∑ j, g i j t := by
        rw [Finset.sum_congr rfl (fun i _ => hsum i), hsum2]
    _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr
        intro t _
        exact sum_conj_cos_mul_eq_profiles N u a t

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceEntry_eq_cos_integral
#print axioms Zeta23.CCM.sum_conj_cos_mul_eq_profiles
#print axioms Zeta23.CCM.quadraticForm_sourceMatrix_eq_convolution
