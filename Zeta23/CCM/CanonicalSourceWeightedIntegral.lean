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

theorem sin_two_pi_int_mul_one (k : ℤ) : Real.sin (2 * Real.pi * k * 1) = 0 := by
  rw [show 2 * Real.pi * (k : ℝ) * 1 = ((2 * k : ℤ) : ℝ) * Real.pi by push_cast; ring]
  exact Real.sin_int_mul_pi _

theorem cos_two_pi_int_mul_one (k : ℤ) : Real.cos (2 * Real.pi * k * 1) = 1 := by
  rw [show 2 * Real.pi * (k : ℝ) * 1 = (k : ℝ) * (2 * Real.pi) by ring]
  exact Real.cos_int_mul_two_pi _

theorem integral_sin_mul_int (k : ℤ) (hk : k ≠ 0) :
    ∫ ω in (0 : ℝ)..1, Real.sin (2 * Real.pi * k * ω) = 0 := by
  have hc : (2 * Real.pi * k : ℝ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    positivity
  have hF : ∀ ω : ℝ, HasDerivAt (fun ω => -Real.cos (2 * Real.pi * k * ω) / (2 * Real.pi * k))
      (Real.sin (2 * Real.pi * k * ω)) ω := by
    intro ω
    refine ((((hasDerivAt_id ω).const_mul (2 * Real.pi * k)).cos.neg).div_const
      (2 * Real.pi * k)).congr_deriv ?_
    simp only [id, mul_one]
    rw [neg_mul, neg_neg, mul_div_assoc, div_self hc, mul_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ω _ => hF ω)
    ((by fun_prop : Continuous fun ω : ℝ => Real.sin (2 * Real.pi * k * ω)).intervalIntegrable _ _),
    cos_two_pi_int_mul_one, mul_zero, Real.cos_zero, sub_self]

theorem integral_cos_mul_int (k : ℤ) (hk : k ≠ 0) :
    ∫ ω in (0 : ℝ)..1, Real.cos (2 * Real.pi * k * ω) = 0 := by
  have hc : (2 * Real.pi * k : ℝ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    positivity
  have hF : ∀ ω : ℝ, HasDerivAt (fun ω => Real.sin (2 * Real.pi * k * ω) / (2 * Real.pi * k))
      (Real.cos (2 * Real.pi * k * ω)) ω := by
    intro ω
    refine ((((hasDerivAt_id ω).const_mul (2 * Real.pi * k)).sin).div_const
      (2 * Real.pi * k)).congr_deriv ?_
    simp only [id, mul_one]
    rw [mul_div_assoc, div_self hc, mul_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ω _ => hF ω)
    ((by fun_prop : Continuous fun ω : ℝ => Real.cos (2 * Real.pi * k * ω)).intervalIntegrable _ _),
    sin_two_pi_int_mul_one, mul_zero, Real.sin_zero, zero_div, sub_self]

/-- `∫₀¹ (1-ω) sin(2πkω) dω = 1/(2πk)` for `k ≠ 0`. -/
theorem integral_one_sub_mul_sin_mul_int (k : ℤ) (hk : k ≠ 0) :
    ∫ ω in (0 : ℝ)..1, (1 - ω) * Real.sin (2 * Real.pi * k * ω) = 1 / (2 * Real.pi * k) := by
  have hc : (2 * Real.pi * k : ℝ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    positivity
  have hF : ∀ ω : ℝ, HasDerivAt
      (fun ω => -(1 - ω) * Real.cos (2 * Real.pi * k * ω) / (2 * Real.pi * k) -
        Real.sin (2 * Real.pi * k * ω) / (2 * Real.pi * k) ^ 2)
      ((1 - ω) * Real.sin (2 * Real.pi * k * ω)) ω := by
    intro ω
    have h1 := (((hasDerivAt_id ω).const_sub 1).neg.mul
      ((hasDerivAt_id ω).const_mul (2 * Real.pi * k)).cos).div_const (2 * Real.pi * k)
    have h2 := ((hasDerivAt_id ω).const_mul (2 * Real.pi * k)).sin.div_const
      ((2 * Real.pi * k) ^ 2)
    refine (h1.sub h2).congr_deriv ?_
    simp only [id, mul_one, Pi.neg_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ω _ => hF ω)
    ((by fun_prop : Continuous fun ω : ℝ =>
      (1 - ω) * Real.sin (2 * Real.pi * k * ω)).intervalIntegrable _ _)]
  simp only [sin_two_pi_int_mul_one, cos_two_pi_int_mul_one, mul_zero, Real.cos_zero,
    Real.sin_zero]
  field_simp
  ring

/-- `∫₀¹ (1-ω) · 2ω cos(2πkω) dω = -1/(π² k²)` for `k ≠ 0`. -/
theorem integral_one_sub_mul_two_mul_cos_mul_int (k : ℤ) (hk : k ≠ 0) :
    ∫ ω in (0 : ℝ)..1, (1 - ω) * (2 * ω * Real.cos (2 * Real.pi * k * ω)) =
      -1 / (Real.pi ^ 2 * (k : ℝ) ^ 2) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hc : (2 * Real.pi * k : ℝ) ≠ 0 := by positivity
  have hF : ∀ ω : ℝ, HasDerivAt
      (fun ω => (2 * ω - 2 * ω ^ 2) * Real.sin (2 * Real.pi * k * ω) / (2 * Real.pi * k) +
        (2 - 4 * ω) * Real.cos (2 * Real.pi * k * ω) / (2 * Real.pi * k) ^ 2 +
        4 * Real.sin (2 * Real.pi * k * ω) / (2 * Real.pi * k) ^ 3)
      ((1 - ω) * (2 * ω * Real.cos (2 * Real.pi * k * ω))) ω := by
    intro ω
    have hs := ((hasDerivAt_id ω).const_mul (2 * Real.pi * k)).sin
    have hco := ((hasDerivAt_id ω).const_mul (2 * Real.pi * k)).cos
    have hp1 := ((hasDerivAt_id ω).const_mul 2).sub ((hasDerivAt_pow 2 ω).const_mul 2)
    have hp2 := ((hasDerivAt_id ω).const_mul 4).const_sub 2
    have h := (((hp1.mul hs).div_const (2 * Real.pi * k)).add
      ((hp2.mul hco).div_const ((2 * Real.pi * k) ^ 2))).add
      ((hs.const_mul 4).div_const ((2 * Real.pi * k) ^ 3))
    refine h.congr_deriv ?_
    simp only [id, mul_one, Pi.sub_apply, Nat.cast_ofNat, pow_one,
      Nat.add_one_sub_one]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ω _ => hF ω)
    ((by fun_prop : Continuous fun ω : ℝ =>
      (1 - ω) * (2 * ω * Real.cos (2 * Real.pi * k * ω))).intervalIntegrable _ _)]
  simp only [sin_two_pi_int_mul_one, cos_two_pi_int_mul_one, mul_zero, Real.cos_zero,
    Real.sin_zero]
  field_simp
  ring


/-! ## Entry integrals -/

private theorem integral_two_mul_cos_mul_int (k : ℤ) (hk : k ≠ 0) :
    ∫ ω in (0 : ℝ)..1, 2 * ω * Real.cos (2 * Real.pi * k * ω) = 0 := by
  have hc : (2 * Real.pi * k : ℝ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    positivity
  have hF : ∀ ω : ℝ, HasDerivAt
      (fun ω => 2 * ω * Real.sin (2 * Real.pi * k * ω) / (2 * Real.pi * k) +
        2 * Real.cos (2 * Real.pi * k * ω) / (2 * Real.pi * k) ^ 2)
      (2 * ω * Real.cos (2 * Real.pi * k * ω)) ω := by
    intro ω
    have hs := ((hasDerivAt_id ω).const_mul (2 * Real.pi * k)).sin
    have hco := ((hasDerivAt_id ω).const_mul (2 * Real.pi * k)).cos
    have h := ((((hasDerivAt_id ω).const_mul 2).mul hs).div_const (2 * Real.pi * k)).add
      ((hco.const_mul 2).div_const ((2 * Real.pi * k) ^ 2))
    refine h.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ω _ => hF ω)
    ((by fun_prop : Continuous fun ω : ℝ =>
      2 * ω * Real.cos (2 * Real.pi * k * ω)).intervalIntegrable _ _)]
  simp only [sin_two_pi_int_mul_one, cos_two_pi_int_mul_one, mul_zero, Real.cos_zero,
    Real.sin_zero]
  ring

private theorem integral_sin_mul_int' (k : ℤ) :
    ∫ ω in (0 : ℝ)..1, Real.sin (2 * Real.pi * k * ω) = 0 := by
  by_cases hk : k = 0
  · subst hk; simp
  · exact integral_sin_mul_int k hk

private theorem integral_one_sub_mul_sin_mul_int' (k : ℤ) :
    ∫ ω in (0 : ℝ)..1, (1 - ω) * Real.sin (2 * Real.pi * k * ω) =
      if k = 0 then 0 else 1 / (2 * Real.pi * k) := by
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]; exact integral_one_sub_mul_sin_mul_int k hk

/-- Off-diagonal source entries are real-valued divided differences. -/
private theorem sourceEntry_of_ne_eq_ofReal (ω : ℝ) {n m : ℤ} (h : n ≠ m) :
    sourceEntry ω n m =
      (((Real.sin (2 * Real.pi * n * ω) - Real.sin (2 * Real.pi * m * ω)) /
        (Real.pi * ((n - m : ℤ) : ℝ)) : ℝ) : ℂ) := by
  rw [sourceEntry_of_ne _ h]
  simp only [sourcePotential]
  push_cast
  field_simp

/-- Unweighted entry average: `∫₀¹ S_nm = 1` iff `n = m = 0`, else `0`. -/
theorem integral_sourceEntry (n m : ℤ) :
    ∫ ω in (0 : ℝ)..1, sourceEntry ω n m = if n = 0 ∧ m = 0 then 1 else 0 := by
  by_cases h : n = m
  · subst h
    simp only [sourceEntry_self, sourceDiagonal]
    rw [intervalIntegral.integral_ofReal]
    by_cases hn : n = 0
    · subst hn
      simp only [Int.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one, and_self, if_true]
      rw [intervalIntegral.integral_const_mul, integral_id]
      norm_num
    · rw [if_neg (by tauto), integral_two_mul_cos_mul_int n hn, Complex.ofReal_zero]
  · rw [if_neg (by omega)]
    simp only [sourceEntry_of_ne_eq_ofReal _ h]
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_div,
      intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun ω : ℝ =>
          Real.sin (2 * Real.pi * n * ω)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun ω : ℝ =>
          Real.sin (2 * Real.pi * m * ω)).intervalIntegrable _ _),
      integral_sin_mul_int' n, integral_sin_mul_int' m]
    simp

/-- Weighted entry average on nonzero indices:
`∫₀¹ (1-ω) S_nm = -(1/(2π²)) (1/(nm) + δ_nm/n²)`. -/
theorem integral_one_sub_mul_sourceEntry (n m : ℤ) (hn : n ≠ 0) (hm : m ≠ 0) :
    ∫ ω in (0 : ℝ)..1, ((1 - ω : ℝ) : ℂ) * sourceEntry ω n m =
      -(1 / (2 * (Real.pi : ℂ) ^ 2)) *
        (1 / ((n : ℂ) * m) + if n = m then 1 / (n : ℂ) ^ 2 else 0) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h : n = m
  · subst h
    simp only [sourceEntry_self, sourceDiagonal, if_true]
    simp only [← Complex.ofReal_mul]
    rw [intervalIntegral.integral_ofReal, integral_one_sub_mul_two_mul_cos_mul_int n hn]
    push_cast
    field_simp
    ring
  · rw [if_neg h]
    simp only [sourceEntry_of_ne_eq_ofReal _ h, ← Complex.ofReal_mul]
    have hnm : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr h
    have hint : ∫ ω in (0 : ℝ)..1, (1 - ω) *
        ((Real.sin (2 * Real.pi * n * ω) - Real.sin (2 * Real.pi * m * ω)) /
          (Real.pi * ((n - m : ℤ) : ℝ))) =
        ((∫ ω in (0 : ℝ)..1, (1 - ω) * Real.sin (2 * Real.pi * n * ω)) -
          ∫ ω in (0 : ℝ)..1, (1 - ω) * Real.sin (2 * Real.pi * m * ω)) /
            (Real.pi * ((n - m : ℤ) : ℝ)) := by
      rw [← intervalIntegral.integral_sub
          ((by fun_prop : Continuous fun ω : ℝ =>
            (1 - ω) * Real.sin (2 * Real.pi * n * ω)).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun ω : ℝ =>
            (1 - ω) * Real.sin (2 * Real.pi * m * ω)).intervalIntegrable _ _),
        ← intervalIntegral.integral_div]
      congr 1
      funext ω
      ring
    rw [intervalIntegral.integral_ofReal, hint, integral_one_sub_mul_sin_mul_int n hn,
      integral_one_sub_mul_sin_mul_int m hm]
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
  fun_prop

/-- **Unweighted source average (M54):** `∫₀¹ e_u(ω) dω = |u₀|²`. -/
theorem integral_quadraticForm_sourceMatrix (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    ∫ ω in (0 : ℝ)..1, quadraticForm (sourceMatrix ω N) u =
      ∑ i, if centeredIndex N i = 0 then conj (u i) * u i else 0 := by
  unfold quadraticForm
  simp only [sourceMatrix_apply]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (by fun_prop : Continuous fun ω : ℝ =>
    ∑ j, conj (u i) * sourceEntry ω (centeredIndex N i) (centeredIndex N j) * u j
    ).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [intervalIntegral.integral_finsetSum (fun j _ => (by fun_prop : Continuous fun ω : ℝ =>
    conj (u i) * sourceEntry ω (centeredIndex N i) (centeredIndex N j) * u j
    ).intervalIntegrable _ _)]
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
        exact hji (centeredIndex_injective N (hj.trans hi.symm))
      simp [this]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    simp [hi]

/-- Per-entry weighted integral, specialized to coefficient vectors. -/
private theorem integral_one_sub_mul_entry_term (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hu0 : ∀ i, centeredIndex N i = 0 → u i = 0) (i j : Fin (2 * N + 1)) :
    ∫ ω in (0 : ℝ)..1,
        ((1 - ω : ℝ) : ℂ) *
          (conj (u i) * sourceEntry ω (centeredIndex N i) (centeredIndex N j) * u j) =
      -(1 / (2 * (Real.pi : ℂ) ^ 2)) *
        (conj (u i / (centeredIndex N i : ℂ)) * (u j / (centeredIndex N j : ℂ)) +
          if i = j then conj (u i) * u i / ((centeredIndex N i : ℂ) ^ 2) else 0) := by
  by_cases hi : centeredIndex N i = 0
  · have h0 : u i = 0 := hu0 i hi
    simp [h0]
  by_cases hj : centeredIndex N j = 0
  · have h0 : u j = 0 := hu0 j hj
    by_cases hij : i = j
    · subst hij; exact absurd hj hi
    · simp [h0, hij]
  have hfun : (fun ω : ℝ => ((1 - ω : ℝ) : ℂ) *
      (conj (u i) * sourceEntry ω (centeredIndex N i) (centeredIndex N j) * u j)) =
      fun ω : ℝ => (conj (u i) * u j) *
        (((1 - ω : ℝ) : ℂ) * sourceEntry ω (centeredIndex N i) (centeredIndex N j)) := by
    funext ω; ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_one_sub_mul_sourceEntry _ _ hi hj]
  have hiC : ((centeredIndex N i : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hi
  have hjC : ((centeredIndex N j : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hj
  have hreal : conj ((centeredIndex N i : ℤ) : ℂ) = (centeredIndex N i : ℂ) :=
    map_intCast (starRingEnd ℂ) _
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, map_div₀, hreal]
    field_simp
  · have hidx : centeredIndex N i ≠ centeredIndex N j :=
      fun h => hij (centeredIndex_injective N h)
    rw [if_neg hidx, if_neg hij, map_div₀, hreal]
    field_simp
    ring

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
  simp only [sourceMatrix_apply, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (by fun_prop : Continuous fun ω : ℝ =>
    ∑ j, ((1 - ω : ℝ) : ℂ) *
      (conj (u i) * sourceEntry ω (centeredIndex N i) (centeredIndex N j) * u j)
    ).intervalIntegrable _ _)]
  have hrow : ∀ i, ∫ ω in (0 : ℝ)..1, ∑ j, ((1 - ω : ℝ) : ℂ) *
      (conj (u i) * sourceEntry ω (centeredIndex N i) (centeredIndex N j) * u j) =
      ∑ j, -(1 / (2 * (Real.pi : ℂ) ^ 2)) *
        (conj (u i / (centeredIndex N i : ℂ)) * (u j / (centeredIndex N j : ℂ)) +
          if i = j then conj (u i) * u i / ((centeredIndex N i : ℂ) ^ 2) else 0) := by
    intro i
    rw [intervalIntegral.integral_finsetSum (fun j _ => (by fun_prop : Continuous fun ω : ℝ =>
      ((1 - ω : ℝ) : ℂ) *
        (conj (u i) * sourceEntry ω (centeredIndex N i) (centeredIndex N j) * u j)
      ).intervalIntegrable _ _)]
    exact Finset.sum_congr rfl (fun j _ => integral_one_sub_mul_entry_term N u hu0 i j)
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  · rw [map_sum, Finset.sum_mul]

/-- Real form of the weighted identity. -/
theorem integral_one_sub_mul_re_quadraticForm_sourceMatrix (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hu0 : ∀ i, centeredIndex N i = 0 → u i = 0) :
    ∫ ω in (0 : ℝ)..1, (1 - ω) * (quadraticForm (sourceMatrix ω N) u).re =
      -(1 / (2 * Real.pi ^ 2)) *
        ((∑ i, Complex.normSq (u i) / ((centeredIndex N i : ℝ) ^ 2)) +
          Complex.normSq (∑ i, u i / (centeredIndex N i : ℂ))) := by
  have hcont : Continuous fun ω : ℝ =>
      ((1 - ω : ℝ) : ℂ) * quadraticForm (sourceMatrix ω N) u :=
    (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun ω : ℝ => 1 - ω)).mul
      (continuous_quadraticForm_sourceMatrix N u)
  have hre := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (μ := MeasureTheory.volume) (a := 0) (b := 1)
    (hcont.intervalIntegrable 0 1)
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at hre
  rw [hre, integral_one_sub_mul_quadraticForm_sourceMatrix N u hu0]
  have hpi : (1 : ℂ) / (2 * (Real.pi : ℂ) ^ 2) = ((1 / (2 * Real.pi ^ 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hpi, ← Complex.ofReal_neg, Complex.re_ofReal_mul]
  congr 1
  rw [Complex.add_re, Complex.re_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have h : conj (u i) * u i / ((centeredIndex N i : ℂ) ^ 2) =
        ((Complex.normSq (u i) / ((centeredIndex N i : ℝ) ^ 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, Complex.normSq_eq_conj_mul_self]
      push_cast
      ring
    rw [h, Complex.ofReal_re]
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
  let c : Fin (2 * N + 1) := ⟨N, by omega⟩
  have hc : centeredIndex N c = 0 := by simp [centeredIndex, c]
  have hne : ∀ i, i ≠ c → centeredIndex N i ≠ 0 := by
    intro i hic h
    exact hic (centeredIndex_injective N (h.trans hc.symm))
  have hdiv : ∀ i, u i / (centeredIndex N i : ℂ) = if i = c then 0 else z i := by
    intro i
    by_cases hic : i = c
    · rw [if_pos hic, hic, hui, hc]; simp
    · have hneC : ((centeredIndex N i : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hne i hic
      rw [if_neg hic, hui]
      field_simp
  have hsq : ∀ i, Complex.normSq (u i) / ((centeredIndex N i : ℝ) ^ 2) =
      if i = c then 0 else Complex.normSq (z i) := by
    intro i
    by_cases hic : i = c
    · rw [if_pos hic, hic, hui, hc]; simp
    · have hneR : ((centeredIndex N i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne i hic
      rw [if_neg hic, hui, Complex.normSq_mul, Complex.normSq_intCast]
      field_simp
  simp only [hsq, hdiv]
  have hsplit : ∀ f : Fin (2 * N + 1) → ℂ,
      (∑ i, if i = c then (0 : ℂ) else f i) = (∑ i, f i) - f c := by
    intro f
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c),
      ← Finset.sum_erase_add _ f (Finset.mem_univ c), if_pos rfl,
      Finset.sum_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))]
    ring
  have hsplitR : ∀ f : Fin (2 * N + 1) → ℝ,
      (∑ i, if i = c then (0 : ℝ) else f i) = (∑ i, f i) - f c := by
    intro f
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c),
      ← Finset.sum_erase_add _ f (Finset.mem_univ c), if_pos rfl,
      Finset.sum_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))]
    ring
  rw [hsplit z, hsum, zero_sub, Complex.normSq_neg,
    hsplitR (fun i => Complex.normSq (z i))]
  ring

/-- **Quantitative averaged negativity (Steps 77/95).**  For `u₀ = 0`,
`N ≥ 1`: `∫₀¹ (1-ω) Re e_u ≤ -‖u‖²/(2π² N²)`. -/
theorem integral_one_sub_mul_re_quadraticForm_le (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) (hu0 : ∀ i, centeredIndex N i = 0 → u i = 0) :
    ∫ ω in (0 : ℝ)..1, (1 - ω) * (quadraticForm (sourceMatrix ω N) u).re ≤
      -(∑ i, Complex.normSq (u i)) / (2 * Real.pi ^ 2 * (N : ℝ) ^ 2) := by
  rw [integral_one_sub_mul_re_quadraticForm_sourceMatrix N u hu0]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hu : ∀ i, u i = 0 := fun i => hu0 i (by
      have := i.2
      simp only [centeredIndex]
      omega)
    simp [hu]
  have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hterm : ∀ i, Complex.normSq (u i) / (N : ℝ) ^ 2 ≤
      Complex.normSq (u i) / ((centeredIndex N i : ℝ) ^ 2) := by
    intro i
    by_cases hi : centeredIndex N i = 0
    · rw [hu0 i hi]; simp
    · have hiR : ((centeredIndex N i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi
      have hle : ((centeredIndex N i : ℤ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
        have habs : |centeredIndex N i| ≤ (N : ℤ) := by
          have h1 := i.2
          rw [abs_le]
          simp only [centeredIndex]
          omega
        have habsR : |((centeredIndex N i : ℤ) : ℝ)| ≤ (N : ℝ) := by
          rw [← Int.cast_abs]; exact_mod_cast habs
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) habsR 2
      exact div_le_div_of_nonneg_left (Complex.normSq_nonneg _) (by positivity) hle
  have hsum : (∑ i, Complex.normSq (u i)) / (N : ℝ) ^ 2 ≤
      ∑ i, Complex.normSq (u i) / ((centeredIndex N i : ℝ) ^ 2) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun i _ => hterm i)
  have hns := Complex.normSq_nonneg (∑ i, u i / (centeredIndex N i : ℂ))
  have hpi : 0 < 2 * Real.pi ^ 2 := by positivity
  have hrw : -(∑ i, Complex.normSq (u i)) / (2 * Real.pi ^ 2 * (N : ℝ) ^ 2) =
      -(1 / (2 * Real.pi ^ 2)) * ((∑ i, Complex.normSq (u i)) / (N : ℝ) ^ 2) := by
    field_simp
  rw [hrw]
  have hc : 0 ≤ 1 / (2 * Real.pi ^ 2) := by positivity
  nlinarith

/-- **Universal source sign reversal (Steps 77/95).**  Every nonzero `u` with
`u₀ = 0` has a source coordinate with negative energy and a zero of the real
energy in `(0, 1)`. -/
theorem exists_source_zero_of_center_zero (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) (hu : u ≠ 0) (hu0 : ∀ i, centeredIndex N i = 0 → u i = 0) :
    (∃ ω ∈ Set.Ioo (0 : ℝ) 1, (quadraticForm (sourceMatrix ω N) u).re < 0) ∧
      ∃ ω ∈ Set.Ioo (0 : ℝ) 1, (quadraticForm (sourceMatrix ω N) u).re = 0 := by
  have hpos : 0 < ∑ i, Complex.normSq (u i) := by
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h; push Not at h; exact hu (funext h)
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  have hN : 1 ≤ N := by
    by_contra hN
    obtain rfl : N = 0 := by omega
    apply hu
    funext i
    exact hu0 i (by have := i.2; simp only [centeredIndex]; omega)
  have hint := integral_one_sub_mul_re_quadraticForm_le N u hu0
  have hneg_int :
      ∫ ω in (0 : ℝ)..1, (1 - ω) * (quadraticForm (sourceMatrix ω N) u).re < 0 := by
    refine lt_of_le_of_lt hint ?_
    apply div_neg_of_neg_of_pos (neg_lt_zero.mpr hpos)
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  have hcont : Continuous fun ω : ℝ => (quadraticForm (sourceMatrix ω N) u).re :=
    Complex.continuous_re.comp (continuous_quadraticForm_sourceMatrix N u)
  have hneg : ∃ ω ∈ Set.Ioo (0 : ℝ) 1, (quadraticForm (sourceMatrix ω N) u).re < 0 := by
    by_contra h
    push Not at h
    have hnn :
        0 ≤ ∫ ω in (0 : ℝ)..1, (1 - ω) * (quadraticForm (sourceMatrix ω N) u).re := by
      have hcl : ∀ ω ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (quadraticForm (sourceMatrix ω N) u).re := by
        have hclosed : IsClosed {ω : ℝ | 0 ≤ (quadraticForm (sourceMatrix ω N) u).re} :=
          isClosed_le continuous_const hcont
        have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {ω | 0 ≤ (quadraticForm (sourceMatrix ω N) u).re} :=
          fun ω hω => h ω hω
        have := closure_mono hsub
        rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), hclosed.closure_eq] at this
        exact fun ω hω => this hω
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro ω hω
      exact mul_nonneg (by linarith [hω.2]) (hcl ω hω)
    linarith
  refine ⟨hneg, ?_⟩
  obtain ⟨ω₁, hω₁, hneg₁⟩ := hneg
  have hone : 0 < (quadraticForm (sourceMatrix 1 N) u).re := by
    rw [sourceMatrix_one]
    unfold quadraticForm
    have hdiag : ∀ i, (∑ j, conj (u i) *
        ((2 : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)) i j * u j) =
        2 * (conj (u i) * u i) := by
      intro i
      rw [Finset.sum_eq_single i]
      · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
        ring
      · intro j _ hji
        simp [Matrix.one_apply_ne (Ne.symm hji)]
      · intro h; exact absurd (Finset.mem_univ i) h
    simp only [hdiag, Complex.re_sum]
    have hre : ∀ i, (2 * (conj (u i) * u i)).re = 2 * Complex.normSq (u i) := by
      intro i
      rw [← Complex.normSq_eq_conj_mul_self]
      simp
    simp only [hre, ← Finset.mul_sum]
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
