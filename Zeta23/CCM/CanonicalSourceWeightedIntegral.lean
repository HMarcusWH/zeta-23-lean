import Zeta23.CCM.SourceLatticeCoordinates
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate Interval

/-!
# POST284-M35/M40/M54: integrated elementary source identities

Exact integrals of the elementary source matrix over the source coordinate
`ω ∈ [0, 1]` (follow-up handoff Steps 72, 77, 95):

* `∫₀¹ S_K(ω) dω = P₀`, the projection onto the centred Fourier index `0`;
* for nonzero lattice indices,
  `∫₀¹ (1-ω) S_nm(ω) dω = -(1/(2π²)) (1/(nm) + δ_nm / n²)`;
* for every complex `u` with `u₀ = 0` (no parity, moment, or contact
  hypothesis):
  `∫₀¹ (1-ω) e_u(ω) dω = -(1/(2π²)) (∑_{n≠0} |u_n|²/n² + |∑_{n≠0} u_n/n|²)`,
  a negative-definite averaged form with
  `∫₀¹ (1-ω) Re e_u ≤ -‖u‖²/(2π² K²)`;
* hence `∫₀¹ (1-ω) e_{Dz}(ω) dω = -‖z‖²/(2π²)` when `∑ z = 0`;
* every nonzero `u` with `u₀ = 0` has a source coordinate with
  `Re e_u(ω) < 0` and a zero of `Re e_u` in `(0, 1)` (since `e_u(1) = 2‖u‖²`).

This is averaged elementary-source structure; it is compatible with the
indefinite pointwise source inertia and says nothing about the canonical
operator, contacts, or RH.
-/

/-! ## One-dimensional trigonometric integrals -/

theorem integral_sin_mul_int (k : ℤ) (hk : k ≠ 0) :
    ∫ ω in (0 : ℝ)..1, Real.sin (2 * Real.pi * k * ω) = 0 := by
  have hc : (2 * Real.pi * k : ℝ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    positivity
  have hF : ∀ ω : ℝ, HasDerivAt (fun ω => -Real.cos (2 * Real.pi * k * ω) / (2 * Real.pi * k))
      (Real.sin (2 * Real.pi * k * ω)) ω := by
    intro ω
    have h := ((hasDerivAt_id ω).const_mul (2 * Real.pi * k)).cos.neg.div_const (2 * Real.pi * k)
    convert h using 1
    simp only [id]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ω _ => hF ω)
    ((by fun_prop : Continuous fun ω : ℝ => Real.sin (2 * Real.pi * k * ω)).intervalIntegrable _ _)]
  rw [show 2 * Real.pi * (k : ℝ) * 1 = (k : ℝ) * (2 * Real.pi) by ring, Real.cos_int_mul_two_pi]
  simp

theorem integral_cos_mul_int (k : ℤ) (hk : k ≠ 0) :
    ∫ ω in (0 : ℝ)..1, Real.cos (2 * Real.pi * k * ω) = 0 := by
  have hc : (2 * Real.pi * k : ℝ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    positivity
  have hF : ∀ ω : ℝ, HasDerivAt (fun ω => Real.sin (2 * Real.pi * k * ω) / (2 * Real.pi * k))
      (Real.cos (2 * Real.pi * k * ω)) ω := by
    intro ω
    have h := ((hasDerivAt_id ω).const_mul (2 * Real.pi * k)).sin.div_const (2 * Real.pi * k)
    convert h using 1
    simp only [id]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ω _ => hF ω)
    ((by fun_prop : Continuous fun ω : ℝ => Real.cos (2 * Real.pi * k * ω)).intervalIntegrable _ _)]
  rw [show 2 * Real.pi * (k : ℝ) * 1 = (k : ℝ) * (2 * Real.pi) by ring, Real.sin_int_mul_two_pi]
  simp

/-- `∫₀¹ (1-ω) sin(2πkω) dω = 1/(2πk)` for `k ≠ 0`. -/
theorem integral_one_sub_mul_sin_mul_int (k : ℤ) (hk : k ≠ 0) :
    ∫ ω in (0 : ℝ)..1, (1 - ω) * Real.sin (2 * Real.pi * k * ω) = 1 / (2 * Real.pi * k) := by
  set c : ℝ := 2 * Real.pi * k with hc_def
  have hc : c ≠ 0 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [hc_def]; positivity
  have hF : ∀ ω : ℝ, HasDerivAt
      (fun ω => -(1 - ω) * Real.cos (c * ω) / c - Real.sin (c * ω) / c ^ 2)
      ((1 - ω) * Real.sin (c * ω)) ω := by
    intro ω
    have h1 := (((hasDerivAt_id ω).const_sub 1).neg.mul
      ((hasDerivAt_id ω).const_mul c).cos).div_const c
    have h2 := ((hasDerivAt_id ω).const_mul c).sin.div_const (c ^ 2)
    convert h1.sub h2 using 1
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ω _ => hF ω)
    ((by fun_prop : Continuous fun ω : ℝ => (1 - ω) * Real.sin (c * ω)).intervalIntegrable _ _)]
  rw [hc_def, show 2 * Real.pi * (k : ℝ) * 1 = (k : ℝ) * (2 * Real.pi) by ring,
    Real.sin_int_mul_two_pi, Real.cos_int_mul_two_pi]
  simp
  field_simp

/-- `∫₀¹ (1-ω) · 2ω cos(2πkω) dω = -1/(π² k²)` for `k ≠ 0`. -/
theorem integral_one_sub_mul_two_mul_cos_mul_int (k : ℤ) (hk : k ≠ 0) :
    ∫ ω in (0 : ℝ)..1, (1 - ω) * (2 * ω * Real.cos (2 * Real.pi * k * ω)) =
      -1 / (Real.pi ^ 2 * (k : ℝ) ^ 2) := by
  set c : ℝ := 2 * Real.pi * k with hc_def
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hc : c ≠ 0 := by rw [hc_def]; positivity
  -- antiderivative of (1-ω)·2ω·cos(cω) = (2ω - 2ω²) cos(cω)
  have hF : ∀ ω : ℝ, HasDerivAt
      (fun ω => (2 * ω - 2 * ω ^ 2) * Real.sin (c * ω) / c +
        (2 - 4 * ω) * Real.cos (c * ω) / c ^ 2 + 4 * Real.sin (c * ω) / c ^ 3)
      ((1 - ω) * (2 * ω * Real.cos (c * ω))) ω := by
    intro ω
    have hs := ((hasDerivAt_id ω).const_mul c).sin
    have hco := ((hasDerivAt_id ω).const_mul c).cos
    have hp1 : HasDerivAt (fun ω : ℝ => 2 * ω - 2 * ω ^ 2) (2 - 4 * ω) ω := by
      have := ((hasDerivAt_id ω).const_mul 2).sub ((hasDerivAt_pow 2 ω).const_mul 2)
      convert this using 1
      simp
      ring
    have hp2 : HasDerivAt (fun ω : ℝ => 2 - 4 * ω) (-4) ω := by
      have := ((hasDerivAt_id ω).const_mul 4).const_sub 2
      convert this using 1
      simp
    have h := ((hp1.mul hs).div_const c).add (((hp2.mul hco).div_const (c ^ 2)).add
      (((hs).const_mul 4).div_const (c ^ 3)))
    convert h using 1
    · funext x
      simp only [id]
      ring
    · simp only [id]
      field_simp
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ω _ => hF ω)
    ((by fun_prop : Continuous fun ω : ℝ =>
      (1 - ω) * (2 * ω * Real.cos (c * ω))).intervalIntegrable _ _)]
  rw [hc_def, show 2 * Real.pi * (k : ℝ) * 1 = (k : ℝ) * (2 * Real.pi) by ring,
    Real.sin_int_mul_two_pi, Real.cos_int_mul_two_pi]
  simp
  field_simp
  ring

/-! ## Entry integrals -/

theorem continuous_sourceEntry (n m : ℤ) : Continuous fun ω : ℝ => sourceEntry ω n m := by
  by_cases h : n = m
  · subst h
    simp only [sourceEntry_self, sourceDiagonal]
    fun_prop
  · simp only [sourceEntry_of_ne _ h, sourcePotential]
    fun_prop

/-- Unweighted entry average: `∫₀¹ S_nm = 1` iff `n = m = 0`, else `0`. -/
theorem integral_sourceEntry (n m : ℤ) :
    ∫ ω in (0 : ℝ)..1, sourceEntry ω n m = if n = 0 ∧ m = 0 then 1 else 0 := by
  by_cases h : n = m
  · subst h
    simp only [sourceEntry_self, sourceDiagonal]
    rw [intervalIntegral.integral_ofReal]
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [if_neg (by tauto)]
      have : ∫ ω in (0 : ℝ)..1, 2 * ω * Real.cos (2 * Real.pi * (n : ℝ) * ω) = 0 := by
        have h1 := integral_one_sub_mul_two_mul_cos_mul_int n hn
        -- ∫ 2ω cos = ∫ (1-ω)·2ω cos + ∫ ω·2ω cos, but simpler: direct antiderivative
        have hc : (2 * Real.pi * n : ℝ) ≠ 0 := by
          have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          positivity
        have hF : ∀ ω : ℝ, HasDerivAt
            (fun ω => 2 * ω * Real.sin (2 * Real.pi * n * ω) / (2 * Real.pi * n) +
              2 * Real.cos (2 * Real.pi * n * ω) / (2 * Real.pi * n) ^ 2)
            (2 * ω * Real.cos (2 * Real.pi * n * ω)) ω := by
          intro ω
          have hs := ((hasDerivAt_id ω).const_mul (2 * Real.pi * n)).sin
          have hco := ((hasDerivAt_id ω).const_mul (2 * Real.pi * n)).cos
          have h := ((((hasDerivAt_id ω).const_mul 2).mul hs).div_const (2 * Real.pi * n)).add
            ((hco.const_mul 2).div_const ((2 * Real.pi * n) ^ 2))
          convert h using 1
          · funext x; simp only [id]
          · simp only [id]
            field_simp
            ring
        clear h1
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ω _ => hF ω)
          ((by fun_prop : Continuous fun ω : ℝ =>
            2 * ω * Real.cos (2 * Real.pi * n * ω)).intervalIntegrable _ _)]
        rw [show 2 * Real.pi * (n : ℝ) * 1 = (n : ℝ) * (2 * Real.pi) by ring,
          Real.sin_int_mul_two_pi, Real.cos_int_mul_two_pi]
        simp
      rw [this]
      simp
  · rw [if_neg (by omega)]
    simp only [sourceEntry_of_ne _ h, sourcePotential]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      ((continuous_ofReal.comp (by fun_prop :
        Continuous fun ω : ℝ => Real.sin (2 * Real.pi * n * ω) / Real.pi)).intervalIntegrable _ _)
      ((continuous_ofReal.comp (by fun_prop :
        Continuous fun ω : ℝ => Real.sin (2 * Real.pi * m * ω) / Real.pi)).intervalIntegrable _ _),
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_div, intervalIntegral.integral_div]
    have hz : ∀ k : ℤ, ∫ ω in (0 : ℝ)..1, Real.sin (2 * Real.pi * k * ω) = 0 := by
      intro k
      by_cases hk : k = 0
      · subst hk; simp
      · exact integral_sin_mul_int k hk
    rw [hz n, hz m]
    simp

/-- Weighted entry average on nonzero indices:
`∫₀¹ (1-ω) S_nm = -(1/(2π²)) (1/(nm) + δ_nm/n²)`. -/
theorem integral_one_sub_mul_sourceEntry (n m : ℤ) (hn : n ≠ 0) (hm : m ≠ 0) :
    ∫ ω in (0 : ℝ)..1, ((1 - ω : ℝ) : ℂ) * sourceEntry ω n m =
      -(1 / (2 * (Real.pi : ℂ) ^ 2)) *
        (1 / ((n : ℂ) * m) + if n = m then 1 / (n : ℂ) ^ 2 else 0) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h : n = m
  · subst h
    simp only [sourceEntry_self, sourceDiagonal, if_true]
    rw [show (fun ω : ℝ => ((1 - ω : ℝ) : ℂ) *
        ((2 * ω * Real.cos (2 * Real.pi * (n : ℝ) * ω) : ℝ) : ℂ)) =
        fun ω : ℝ => (((1 - ω) * (2 * ω * Real.cos (2 * Real.pi * (n : ℝ) * ω)) : ℝ) : ℂ) by
      funext ω; push_cast; ring]
    rw [intervalIntegral.integral_ofReal, integral_one_sub_mul_two_mul_cos_mul_int n hn]
    push_cast
    field_simp
    ring
  · rw [if_neg h]
    simp only [sourceEntry_of_ne _ h, sourcePotential]
    have hnm : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr h
    rw [show (fun ω : ℝ => ((1 - ω : ℝ) : ℂ) *
        ((((Real.sin (2 * Real.pi * (n : ℝ) * ω) / Real.pi : ℝ) : ℂ) -
          ((Real.sin (2 * Real.pi * (m : ℝ) * ω) / Real.pi : ℝ) : ℂ)) / (((n - m : ℤ) : ℂ)))) =
        fun ω : ℝ => ((((1 - ω) * Real.sin (2 * Real.pi * (n : ℝ) * ω) -
          (1 - ω) * Real.sin (2 * Real.pi * (m : ℝ) * ω)) / (Real.pi * ((n - m : ℤ) : ℝ)) : ℝ) : ℂ) by
      funext ω; push_cast; field_simp; ring]
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_div,
      intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun ω : ℝ =>
          (1 - ω) * Real.sin (2 * Real.pi * (n : ℝ) * ω)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun ω : ℝ =>
          (1 - ω) * Real.sin (2 * Real.pi * (m : ℝ) * ω)).intervalIntegrable _ _),
      integral_one_sub_mul_sin_mul_int n hn, integral_one_sub_mul_sin_mul_int m hm]
    have hnmC : ((n : ℂ) - m) ≠ 0 := by
      intro h0; apply h; exact_mod_cast sub_eq_zero.mp h0
    push_cast
    field_simp
    ring

/-! ## Integrated quadratic forms -/

/-- Continuity of the complex source energy in the source coordinate. -/
theorem continuous_quadraticForm_sourceMatrix (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    Continuous fun ω : ℝ => quadraticForm (sourceMatrix ω N) u := by
  unfold quadraticForm
  simp only [sourceMatrix_apply]
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro j _
  exact (continuous_const.mul (continuous_sourceEntry _ _)).mul continuous_const

/-- **Unweighted source average (M54):** `∫₀¹ e_u(ω) dω = |u₀|²`. -/
theorem integral_quadraticForm_sourceMatrix (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    ∫ ω in (0 : ℝ)..1, quadraticForm (sourceMatrix ω N) u =
      ∑ i, if centeredIndex N i = 0 then conj (u i) * u i else 0 := by
  unfold quadraticForm
  rw [intervalIntegral.integral_finset_sum (fun i _ =>
    (continuous_finset_sum _ (fun j _ => (continuous_const.mul
      (by simpa using continuous_sourceEntry (centeredIndex N i) (centeredIndex N j))).mul
        continuous_const)).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finset_sum (fun j _ => ((continuous_const.mul
    (by simpa using continuous_sourceEntry (centeredIndex N i) (centeredIndex N j))).mul
      continuous_const).intervalIntegrable _ _)]
  simp only [sourceMatrix_apply]
  have hterm : ∀ j, ∫ ω in (0 : ℝ)..1,
      conj (u i) * sourceEntry ω (centeredIndex N i) (centeredIndex N j) * u j =
        conj (u i) * (if centeredIndex N i = 0 ∧ centeredIndex N j = 0 then 1 else 0) * u j := by
    intro j
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_sourceEntry]
  simp_rw [hterm]
  by_cases hi : centeredIndex N i = 0
  · rw [if_pos hi, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have : centeredIndex N j ≠ 0 := by
        intro hj
        apply hji
        apply centeredIndex_injective N
        rw [hi, hj]
      simp [this]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    simp [hi]

/-- **Weighted source identity (M40, Step 77).**  For every complex `u` with
`u₀ = 0`:
`∫₀¹ (1-ω) e_u = -(1/(2π²)) (∑ |u_n|²/n² + |∑ u_n/n|²)`. -/
theorem integral_one_sub_mul_quadraticForm_sourceMatrix (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hu0 : ∀ i, centeredIndex N i = 0 → u i = 0) :
    ∫ ω in (0 : ℝ)..1, ((1 - ω : ℝ) : ℂ) * quadraticForm (sourceMatrix ω N) u =
      -(1 / (2 * (Real.pi : ℂ) ^ 2)) *
        ((∑ i, conj (u i) * u i / ((centeredIndex N i : ℂ) ^ 2)) +
          conj (∑ i, u i / (centeredIndex N i : ℂ)) * ∑ i, u i / (centeredIndex N i : ℂ)) := by
  unfold quadraticForm
  simp_rw [Finset.mul_sum]
  have hcont : ∀ i j, Continuous fun ω : ℝ =>
      ((1 - ω : ℝ) : ℂ) * (conj (u i) * sourceMatrix ω N i j * u j) := by
    intro i j
    simp only [sourceMatrix_apply]
    exact (continuous_ofReal.comp (by fun_prop)).mul ((continuous_const.mul
      (by simpa using continuous_sourceEntry (centeredIndex N i) (centeredIndex N j))).mul
        continuous_const)
  rw [intervalIntegral.integral_finset_sum (fun i _ =>
    (continuous_finset_sum _ (fun j _ => hcont i j)).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_finset_sum (fun j _ => (hcont _ j).intervalIntegrable _ _)]
  have hterm : ∀ i j, ∫ ω in (0 : ℝ)..1,
      ((1 - ω : ℝ) : ℂ) * (conj (u i) * sourceMatrix ω N i j * u j) =
        -(1 / (2 * (Real.pi : ℂ) ^ 2)) *
          (conj (u i / (centeredIndex N i : ℂ)) * (u j / (centeredIndex N j : ℂ)) +
            if i = j then conj (u i) * u i / ((centeredIndex N i : ℂ) ^ 2) else 0) := by
    intro i j
    by_cases hi : centeredIndex N i = 0
    · have : u i = 0 := hu0 i hi
      simp [this]
    by_cases hj : centeredIndex N j = 0
    · have : u j = 0 := hu0 j hj
      simp [this]
    simp only [sourceMatrix_apply]
    rw [show (fun ω : ℝ => ((1 - ω : ℝ) : ℂ) *
        (conj (u i) * sourceEntry ω (centeredIndex N i) (centeredIndex N j) * u j)) =
        fun ω : ℝ => (conj (u i) * u j) *
          (((1 - ω : ℝ) : ℂ) * sourceEntry ω (centeredIndex N i) (centeredIndex N j)) by
      funext ω; ring]
    rw [intervalIntegral.integral_const_mul, integral_one_sub_mul_sourceEntry _ _ hi hj]
    have hiC : (centeredIndex N i : ℂ) ≠ 0 := by exact_mod_cast hi
    have hjC : (centeredIndex N j : ℂ) ≠ 0 := by exact_mod_cast hj
    have hreal : conj ((centeredIndex N i : ℤ) : ℂ) = (centeredIndex N i : ℂ) := by
      simp
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      rw [map_div₀, hreal]
      field_simp
      ring
    · have hidx : centeredIndex N i ≠ centeredIndex N j :=
        fun h => hij (centeredIndex_injective N h)
      simp only [if_neg hidx, if_neg hij]
      rw [map_div₀, hreal]
      field_simp
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  rw [add_comm]
  congr 1
  · rw [map_sum, Finset.sum_mul_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq]
    simp

/-- Real form of the weighted identity. -/
theorem integral_one_sub_mul_re_quadraticForm_sourceMatrix (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hu0 : ∀ i, centeredIndex N i = 0 → u i = 0) :
    ∫ ω in (0 : ℝ)..1, (1 - ω) * (quadraticForm (sourceMatrix ω N) u).re =
      -(1 / (2 * Real.pi ^ 2)) *
        ((∑ i, Complex.normSq (u i) / ((centeredIndex N i : ℝ) ^ 2)) +
          Complex.normSq (∑ i, u i / (centeredIndex N i : ℂ))) := by
  have h := congrArg Complex.re (integral_one_sub_mul_quadraticForm_sourceMatrix N u hu0)
  have hint : (∫ ω in (0 : ℝ)..1, ((1 - ω : ℝ) : ℂ) * quadraticForm (sourceMatrix ω N) u).re =
      ∫ ω in (0 : ℝ)..1, (1 - ω) * (quadraticForm (sourceMatrix ω N) u).re := by
    rw [← intervalIntegral.integral_re
      ((continuous_ofReal.comp (by fun_prop : Continuous fun ω : ℝ => 1 - ω)).mul
        (continuous_quadraticForm_sourceMatrix N u) |>.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro ω _
    simp
  rw [← hint, h]
  have hpi : (2 * (Real.pi : ℂ) ^ 2) = ((2 * Real.pi ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hpi]
  rw [show (1 : ℂ) / ((2 * Real.pi ^ 2 : ℝ) : ℂ) = ((1 / (2 * Real.pi ^ 2) : ℝ) : ℂ) by
    push_cast; ring]
  rw [show -(((1 / (2 * Real.pi ^ 2) : ℝ) : ℂ)) = ((-(1 / (2 * Real.pi ^ 2)) : ℝ) : ℂ) by
    push_cast; ring]
  rw [Complex.re_ofReal_mul]
  congr 1
  rw [Complex.add_re, Complex.re_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [show conj (u i) * u i / ((centeredIndex N i : ℂ) ^ 2) =
        ((Complex.normSq (u i) / ((centeredIndex N i : ℝ) ^ 2) : ℝ) : ℂ) by
      rw [Complex.normSq_eq_conj_mul_self]; push_cast; ring]
    rw [Complex.ofReal_re]
  · rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- **Zero-sum corollary (M35, Step 72).**  For `∑ z = 0`,
`∫₀¹ (1-ω) Re e_{Dz} = -‖z‖²/(2π²)`, with `(Dz)_n = n z_n`. -/
theorem integral_one_sub_mul_re_energy_indexAction (N : ℕ) (z : Fin (2 * N + 1) → ℂ)
    (hsum : ∑ i, z i = 0) :
    ∫ ω in (0 : ℝ)..1,
        (1 - ω) * (quadraticForm (sourceMatrix ω N) (indexMatrix N *ᵥ z)).re =
      -(1 / (2 * Real.pi ^ 2)) * ∑ i, Complex.normSq (z i) := by
  set u := indexMatrix N *ᵥ z with hu
  have hui : ∀ i, u i = (centeredIndex N i : ℂ) * z i := by
    intro i
    simp [hu, indexMatrix, Matrix.mulVec_diagonal]
  have hu0 : ∀ i, centeredIndex N i = 0 → u i = 0 := by
    intro i hi; rw [hui, hi]; simp
  rw [integral_one_sub_mul_re_quadraticForm_sourceMatrix N u hu0]
  congr 1
  -- center index
  let c : Fin (2 * N + 1) := ⟨N, by omega⟩
  have hc : centeredIndex N c = 0 := by simp [centeredIndex, c]
  have hdiv : ∀ i, u i / (centeredIndex N i : ℂ) = if i = c then 0 else z i := by
    intro i
    by_cases hic : i = c
    · subst hic; rw [hui, hc]; simp
    · have hne : centeredIndex N i ≠ 0 := by
        intro h; apply hic; apply centeredIndex_injective N; rw [h, hc]
      have hneC : (centeredIndex N i : ℂ) ≠ 0 := by exact_mod_cast hne
      rw [if_neg hic, hui]
      field_simp
  have hsq : ∀ i, Complex.normSq (u i) / ((centeredIndex N i : ℝ) ^ 2) =
      if i = c then 0 else Complex.normSq (z i) := by
    intro i
    by_cases hic : i = c
    · subst hic; rw [hui, hc]; simp
    · have hne : centeredIndex N i ≠ 0 := by
        intro h; apply hic; apply centeredIndex_injective N; rw [h, hc]
      have hneR : ((centeredIndex N i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne
      rw [if_neg hic, hui, Complex.normSq_mul, Complex.normSq_intCast]
      field_simp
  simp_rw [hsq, hdiv]
  have hsumc : (∑ i, if i = c then (0 : ℂ) else z i) = -z c := by
    have := Finset.add_sum_erase (Finset.univ) z (Finset.mem_univ c)
    rw [hsum] at this
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c), if_pos rfl, add_zero]
    rw [Finset.sum_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))]
    linear_combination -this
  rw [hsumc, Complex.normSq_neg]
  have hsumr : (∑ i, if i = c then (0 : ℝ) else Complex.normSq (z i)) =
      (∑ i, Complex.normSq (z i)) - Complex.normSq (z c) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c), if_pos rfl, add_zero,
      ← Finset.sum_erase_add _ (fun i => Complex.normSq (z i)) (Finset.mem_univ c)]
    rw [Finset.sum_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))]
    ring
  rw [hsumr]
  ring

/-- **Quantitative averaged negativity (Steps 77/95).**  For `u ≠ 0`,
`u₀ = 0`, `N ≥ 1`: `∫₀¹ (1-ω) Re e_u ≤ -‖u‖²/(2π² N²) < 0`. -/
theorem integral_one_sub_mul_re_quadraticForm_le (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) (hu0 : ∀ i, centeredIndex N i = 0 → u i = 0) :
    ∫ ω in (0 : ℝ)..1, (1 - ω) * (quadraticForm (sourceMatrix ω N) u).re ≤
      -(∑ i, Complex.normSq (u i)) / (2 * Real.pi ^ 2 * (N : ℝ) ^ 2) := by
  rw [integral_one_sub_mul_re_quadraticForm_sourceMatrix N u hu0]
  have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hterm : ∀ i, Complex.normSq (u i) / (N : ℝ) ^ 2 ≤
      Complex.normSq (u i) / ((centeredIndex N i : ℝ) ^ 2) := by
    intro i
    by_cases hi : centeredIndex N i = 0
    · rw [hu0 i hi]; simp
    · have hiR : ((centeredIndex N i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi
      have hle : ((centeredIndex N i : ℤ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
        have h1 := i.2
        have habs : |((centeredIndex N i : ℤ) : ℝ)| ≤ (N : ℝ) := by
          rw [abs_le]
          constructor <;> simp only [centeredIndex] <;> push_cast <;> omega
        calc ((centeredIndex N i : ℤ) : ℝ) ^ 2 = |((centeredIndex N i : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
          _ ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      exact div_le_div_of_nonneg_left (Complex.normSq_nonneg _) (by positivity) hle
  have hsum : (∑ i, Complex.normSq (u i)) / (N : ℝ) ^ 2 ≤
      ∑ i, Complex.normSq (u i) / ((centeredIndex N i : ℝ) ^ 2) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun i _ => hterm i)
  have hns := Complex.normSq_nonneg (∑ i, u i / (centeredIndex N i : ℂ))
  have hpi : 0 < 2 * Real.pi ^ 2 := by positivity
  rw [neg_div, div_mul_eq_div_div, le_neg, ← neg_mul, neg_neg]
  rw [show (∑ i, Complex.normSq (u i)) / (2 * Real.pi ^ 2) / (N : ℝ) ^ 2 =
      (1 / (2 * Real.pi ^ 2)) * ((∑ i, Complex.normSq (u i)) / (N : ℝ) ^ 2) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- **Universal source sign reversal (Steps 77/95).**  Every nonzero `u` with
`u₀ = 0` has a source coordinate with negative energy and a zero of the real
energy in `(0, 1)`. -/
theorem exists_source_zero_of_center_zero (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) (hu : u ≠ 0) (hu0 : ∀ i, centeredIndex N i = 0 → u i = 0) :
    (∃ ω ∈ Set.Ioo (0 : ℝ) 1, (quadraticForm (sourceMatrix ω N) u).re < 0) ∧
      ∃ ω ∈ Set.Ioo (0 : ℝ) 1, (quadraticForm (sourceMatrix ω N) u).re = 0 := by
  have hpos : 0 < ∑ i, Complex.normSq (u i) := by
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h; push_neg at h; exact hu (funext h)
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  have hint := integral_one_sub_mul_re_quadraticForm_le N hN u hu0
  have hneg_int : ∫ ω in (0 : ℝ)..1, (1 - ω) * (quadraticForm (sourceMatrix ω N) u).re < 0 := by
    refine lt_of_le_of_lt hint ?_
    apply div_neg_of_neg_of_pos (neg_lt_zero.mpr hpos)
    positivity
  have hcont : Continuous fun ω : ℝ => (quadraticForm (sourceMatrix ω N) u).re :=
    Complex.continuous_re.comp (continuous_quadraticForm_sourceMatrix N u)
  have hneg : ∃ ω ∈ Set.Ioo (0 : ℝ) 1, (quadraticForm (sourceMatrix ω N) u).re < 0 := by
    by_contra h
    push_neg at h
    have hnn : 0 ≤ ∫ ω in (0 : ℝ)..1, (1 - ω) * (quadraticForm (sourceMatrix ω N) u).re := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict
      · norm_num
      · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
        refine Filter.Eventually.of_forall (fun ω hω => ?_)
        rcases eq_or_lt_of_le hω.1 with h0 | h0
        · subst h0
          simp [sourceMatrix_zero, quadraticForm]
        rcases eq_or_lt_of_le hω.2 with h1 | h1
        · subst h1; simp
        exact mul_nonneg (by linarith) (h ω ⟨h0, h1⟩)
    linarith
  refine ⟨hneg, ?_⟩
  obtain ⟨ω₁, hω₁, hneg₁⟩ := hneg
  have hone : 0 < (quadraticForm (sourceMatrix 1 N) u).re := by
    rw [sourceMatrix_one]
    unfold quadraticForm
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have : (∑ i, ∑ j, conj (u i) * (2 * if i = j then 1 else 0) * u j) =
        ∑ i, 2 * (conj (u i) * u i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp; ring
      · intro j _ hji; simp [Ne.symm hji]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [this, Complex.re_sum]
    have : ∀ i, (2 * (conj (u i) * u i)).re = 2 * Complex.normSq (u i) := by
      intro i; rw [← Complex.normSq_eq_conj_mul_self]; simp
    simp_rw [this, ← Finset.mul_sum]
    positivity
  have hmem : (0 : ℝ) ∈ Set.Ioo ((quadraticForm (sourceMatrix ω₁ N) u).re)
      ((quadraticForm (sourceMatrix 1 N) u).re) := ⟨hneg₁, hone⟩
  obtain ⟨ω₀, hω₀, hzero⟩ := intermediate_value_Ioo hω₁.2.le hcont.continuousOn hmem
  exact ⟨ω₀, ⟨lt_trans hω₁.1 hω₀.1, hω₀.2⟩, hzero⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.integral_sourceEntry
#print axioms Zeta23.CCM.integral_one_sub_mul_sourceEntry
#print axioms Zeta23.CCM.integral_quadraticForm_sourceMatrix
#print axioms Zeta23.CCM.integral_one_sub_mul_quadraticForm_sourceMatrix
#print axioms Zeta23.CCM.integral_one_sub_mul_re_quadraticForm_sourceMatrix
#print axioms Zeta23.CCM.integral_one_sub_mul_re_energy_indexAction
#print axioms Zeta23.CCM.integral_one_sub_mul_re_quadraticForm_le
#print axioms Zeta23.CCM.exists_source_zero_of_center_zero
