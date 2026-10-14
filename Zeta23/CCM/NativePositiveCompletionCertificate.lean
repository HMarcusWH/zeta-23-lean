import Zeta23.CCM.NativePositiveCompletionHead
import Zeta23.CCM.NativePositiveCompletionTail
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# Kernel-checked rational mass certificate for the unchanged native completion

The finite reciprocal-square-root bounds below are checked by exact rational
squaring. They enter the actual cell-integral and countable-tail theorems.
No Python boolean, decimal comparison, modified kernel or global interchange
with the divergent integer measure is an input to this certificate.
-/

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

open Set MeasureTheory Finset

namespace Zeta23.CCM

private def nativeMassHeadLower : Fin 128 → ℝ :=
  ![1000000 / 1000000, 707106 / 1000000, 577350 / 1000000, 500000 / 1000000, 447213 / 1000000, 408248 / 1000000, 377964 / 1000000, 353553 / 1000000,
    333333 / 1000000, 316227 / 1000000, 301511 / 1000000, 288675 / 1000000, 277350 / 1000000, 267261 / 1000000, 258198 / 1000000, 250000 / 1000000,
    242535 / 1000000, 235702 / 1000000, 229415 / 1000000, 223606 / 1000000, 218217 / 1000000, 213200 / 1000000, 208514 / 1000000, 204124 / 1000000,
    200000 / 1000000, 196116 / 1000000, 192450 / 1000000, 188982 / 1000000, 185695 / 1000000, 182574 / 1000000, 179605 / 1000000, 176776 / 1000000,
    174077 / 1000000, 171498 / 1000000, 169030 / 1000000, 166666 / 1000000, 164398 / 1000000, 162221 / 1000000, 160128 / 1000000, 158113 / 1000000,
    156173 / 1000000, 154303 / 1000000, 152498 / 1000000, 150755 / 1000000, 149071 / 1000000, 147441 / 1000000, 145864 / 1000000, 144337 / 1000000,
    142857 / 1000000, 141421 / 1000000, 140028 / 1000000, 138675 / 1000000, 137360 / 1000000, 136082 / 1000000, 134839 / 1000000, 133630 / 1000000,
    132453 / 1000000, 131306 / 1000000, 130188 / 1000000, 129099 / 1000000, 128036 / 1000000, 127000 / 1000000, 125988 / 1000000, 125000 / 1000000,
    124034 / 1000000, 123091 / 1000000, 122169 / 1000000, 121267 / 1000000, 120385 / 1000000, 119522 / 1000000, 118678 / 1000000, 117851 / 1000000,
    117041 / 1000000, 116247 / 1000000, 115470 / 1000000, 114707 / 1000000, 113960 / 1000000, 113227 / 1000000, 112508 / 1000000, 111803 / 1000000,
    111111 / 1000000, 110431 / 1000000, 109764 / 1000000, 109108 / 1000000, 108465 / 1000000, 107832 / 1000000, 107211 / 1000000, 106600 / 1000000,
    105999 / 1000000, 105409 / 1000000, 104828 / 1000000, 104257 / 1000000, 103695 / 1000000, 103142 / 1000000, 102597 / 1000000, 102062 / 1000000,
    101534 / 1000000, 101015 / 1000000, 100503 / 1000000, 100000 / 1000000, 99503 / 1000000, 99014 / 1000000, 98532 / 1000000, 98058 / 1000000,
    97590 / 1000000, 97128 / 1000000, 96673 / 1000000, 96225 / 1000000, 95782 / 1000000, 95346 / 1000000, 94915 / 1000000, 94491 / 1000000,
    94072 / 1000000, 93658 / 1000000, 93250 / 1000000, 92847 / 1000000, 92450 / 1000000, 92057 / 1000000, 91669 / 1000000, 91287 / 1000000,
    90909 / 1000000, 90535 / 1000000, 90166 / 1000000, 89802 / 1000000, 89442 / 1000000, 89087 / 1000000, 88735 / 1000000, 88388 / 1000000]

private theorem nativeMassHeadLower_nonneg (i : Fin 128) :
    0 ≤ nativeMassHeadLower i := by
  fin_cases i <;> norm_num [nativeMassHeadLower]

private theorem nativeMassHeadLower_square (i : Fin 128) :
    ((i.val : ℝ) + 1) * (nativeMassHeadLower i) ^ 2 ≤ 1 := by
  fin_cases i <;> norm_num [nativeMassHeadLower]

private theorem reciprocal_sqrt_lower {x l : ℝ} (hx : 0 < x)
    (hl : 0 ≤ l) (hsq : x * l ^ 2 ≤ 1) :
    l ≤ 1 / Real.sqrt x := by
  have hr := Real.sqrt_pos.mpr hx
  apply (le_div_iff₀ hr).mpr
  have hp : 0 ≤ l * Real.sqrt x := mul_nonneg hl hr.le
  have heq : (l * Real.sqrt x) ^ 2 = x * l ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx.le]
    ring
  nlinarith

private theorem reciprocal_sqrt_upper {x h : ℝ} (hx : 0 < x)
    (hh : 0 ≤ h) (hsq : 1 ≤ x * h ^ 2) :
    1 / Real.sqrt x ≤ h := by
  have hr := Real.sqrt_pos.mpr hx
  apply (div_le_iff₀ hr).mpr
  have hp : 0 ≤ h * Real.sqrt x := mul_nonneg hh hr.le
  have heq : (h * Real.sqrt x) ^ 2 = x * h ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx.le]
    ring
  nlinarith

private theorem rpow_negative_half_eq_reciprocal_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx,
    ← Real.sqrt_eq_rpow, one_div]

private theorem nativeMassHeadLower_sum :
    (∑ i : Fin 128, nativeMassHeadLower i) = (21211169 / 1000000 : ℝ) := by
  norm_num [nativeMassHeadLower, Fin.sum_univ_succ]

private theorem nativeMass_actual_head_reciprocal_lower :
    (21211169 / 1000000 : ℝ) ≤
      ∑ k ∈ range 128, ((k : ℝ) + 1) ^ (-1 / 2 : ℝ) := by
  rw [← nativeMassHeadLower_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum
  intro i hi
  rw [rpow_negative_half_eq_reciprocal_sqrt (by positivity)]
  exact reciprocal_sqrt_lower (by positivity) (nativeMassHeadLower_nonneg i)
    (nativeMassHeadLower_square i)

private theorem nativeMass_endpoint_reciprocal_upper :
    (129 : ℝ) ^ (-1 / 2 : ℝ) ≤ (88046 / 1000000 : ℝ) := by
  rw [rpow_negative_half_eq_reciprocal_sqrt (by norm_num)]
  exact reciprocal_sqrt_upper (by norm_num) (by norm_num) (by norm_num)

private theorem nativeMass_endpoint_three_halves :
    (129 : ℝ) ^ (-3 / 2 : ℝ) = (129 : ℝ) ^ (-1 / 2 : ℝ) / 129 := by
  apply (eq_div_iff (by norm_num : (129 : ℝ) ≠ 0)).mpr
  calc
    _ = (129 : ℝ) ^ (-3 / 2 : ℝ) * (129 : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    _ = (129 : ℝ) ^ ((-3 / 2 : ℝ) + 1) :=
      (Real.rpow_add (by norm_num) _ _).symm
    _ = _ := by norm_num

/-- Actual mass, after logarithmic substitution, finite exact head and
countable-tail comparison, is below the required rational target. -/
theorem nativePositiveCompletion_mass_lt_605_div_621 :
    (∫ t : ℝ in Ioi 0, nativePositiveCompletion t) < (605 / 621 : ℝ) := by
  rw [nativePositiveCompletion_mass_eq_logIntegral]
  have htail := nativePositiveCompletionLogDensity_tail_integral_le
    (N := 129) (by norm_num)
  norm_num only [Nat.cast_ofNat] at htail
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (a := (1 : ℝ)) (b := (129 : ℝ))
    nativePositiveCompletionLogDensity_integrableOn
    (nativePositiveCompletionLogDensity_integrableOn.mono_set
      (fun u hu => lt_trans (by norm_num : (1 : ℝ) < 129) hu))
  have hhead := nativePositiveCompletionLogDensity_head_integral 128
  norm_num only [Nat.cast_ofNat] at hhead
  rw [hhead] at hsplit
  rw [nativeMass_endpoint_three_halves] at htail
  have hlo := nativeMass_actual_head_reciprocal_lower
  have hhi := nativeMass_endpoint_reciprocal_upper
  linarith

/-- Causality upgrades the existing half-line integrability to the full line. -/
theorem nativePositiveCompletion_integrable : Integrable nativePositiveCompletion := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, nativePositiveCompletion_integrableOn⟩
  exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Iio 0)).congr_fun
    (fun t ht => (nativePositiveCompletion_eq_zero_of_neg ht).symm) measurableSet_Iio

/-- The complete actual L1 mass obeys the same bound, since the kernel is
nonnegative and vanishes at all negative times. -/
theorem nativePositiveCompletion_integral_norm_lt_605_div_621 :
    (∫ t : ℝ, ‖nativePositiveCompletion t‖) < (605 / 621 : ℝ) := by
  have hnorm : (fun t : ℝ => ‖nativePositiveCompletion t‖) = nativePositiveCompletion := by
    funext t
    exact Real.norm_of_nonneg (nativePositiveCompletion_nonneg t)
  rw [hnorm]
  have hmass : (∫ t : ℝ, nativePositiveCompletion t) =
      ∫ t : ℝ in Ioi 0, nativePositiveCompletion t := by
    rw [← integral_Ici_eq_integral_Ioi]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact nativePositiveCompletion_eq_zero_of_neg (lt_of_not_ge ht)
  rw [hmass]
  exact nativePositiveCompletion_mass_lt_605_div_621

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePositiveCompletion_mass_lt_605_div_621
#print axioms Zeta23.CCM.nativePositiveCompletion_integrable
#print axioms Zeta23.CCM.nativePositiveCompletion_integral_norm_lt_605_div_621
