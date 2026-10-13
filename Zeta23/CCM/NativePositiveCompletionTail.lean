import Zeta23.CCM.NativePositiveCompletionMass
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Countable cell assembly and tail bound for the actual native completion

The cells include their left endpoint and exclude their right endpoint.
Their union is exactly the positive half-line above the integer cutoff.
Null singleton endpoints connect the already proved open-cell caps to this
partition. This does not use a global interchange with the divergent integer
measure and does not yet export the final 605/621 mass theorem.
-/

noncomputable section

open Set MeasureTheory

namespace Zeta23.CCM

private theorem nativeCompletion_cell_partition (N : ℕ) :
    (⋃ n : ℕ, Ico ((n + N : ℕ) : ℝ) (((n + N : ℕ) : ℝ) + 1)) = Ici (N : ℝ) := by
  ext x
  simp only [mem_iUnion, mem_Ico, mem_Ici]
  constructor
  · rintro ⟨n, hn⟩
    have hN : (N : ℝ) ≤ ((n + N : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left N n
    exact hN.trans hn.1
  · intro hN
    have hfloor : N ≤ ⌊x⌋₊ := Nat.le_floor hN
    refine ⟨⌊x⌋₊ - N, ?_⟩
    rw [Nat.sub_add_cancel hfloor]
    have hx : 0 ≤ x := (Nat.cast_nonneg N).trans hN
    exact ⟨Nat.floor_le hx, Nat.lt_floor_add_one x⟩

private theorem nativeCompletion_cell_partition_disjoint (N : ℕ) :
    Pairwise (fun n m : ℕ => Disjoint
      (Ico ((n + N : ℕ) : ℝ) (((n + N : ℕ) : ℝ) + 1))
      (Ico ((m + N : ℕ) : ℝ) (((m + N : ℕ) : ℝ) + 1))) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro x hn hm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hsep : (((n + N : ℕ) : ℝ) + 1) ≤ ((m + N : ℕ) : ℝ) := by
      have hnat : n + N + 1 ≤ m + N := by omega
      exact_mod_cast hnat
    exact (not_lt_of_ge (hsep.trans hm.1)) hn.2
  · have hsep : (((m + N : ℕ) : ℝ) + 1) ≤ ((n + N : ℕ) : ℝ) := by
      have hnat : m + N + 1 ≤ n + N := by omega
      exact_mod_cast hnat
    exact (not_lt_of_ge (hsep.trans hn.1)) hm.2

/-- Countable assembly of actual cells at the unchanged integer seams. -/
theorem nativePositiveCompletionLogDensity_hasSum_tail_cells {N : ℕ} (hN : 1 ≤ N) :
    HasSum (fun n : ℕ =>
      ∫ u : ℝ in Ico ((n + N : ℕ) : ℝ) (((n + N : ℕ) : ℝ) + 1),
        nativePositiveCompletionLogDensity u)
      (∫ u : ℝ in Ioi (N : ℝ), nativePositiveCompletionLogDensity u) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi : IntegrableOn nativePositiveCompletionLogDensity (Ici (N : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact nativePositiveCompletionLogDensity_integrableOn.mono_set
      (fun u hu => hNreal.trans_lt hu)
  have h := hasSum_integral_iUnion
    (f := nativePositiveCompletionLogDensity)
    (fun n : ℕ => measurableSet_Ico)
    (nativeCompletion_cell_partition_disjoint N)
    (by rw [nativeCompletion_cell_partition N]; exact hi)
  simpa only [nativeCompletion_cell_partition N, integral_Ici_eq_integral_Ioi] using h

/-- The actual tail is bounded by the integrated linear cell caps.
This bound is sharper than the old exponential envelope tail. -/
theorem nativePositiveCompletionLogDensity_tail_integral_le {N : ℕ} (hN : 1 ≤ N) :
    (∫ u : ℝ in Ioi (N : ℝ), nativePositiveCompletionLogDensity u) ≤
      (N : ℝ) ^ (-1 / 2 : ℝ) + (N : ℝ) ^ (-3 / 2 : ℝ) / 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hN)
  let f : ℝ → ℝ := fun x => x ^ (-3 / 2 : ℝ) / 2
  have hanti : AntitoneOn f (Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (hNpos.trans_le hx) hxy (by norm_num)) (by norm_num)
  have hi : IntegrableOn f (Ioi (N : ℝ)) := by
    have h := (integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-3 / 2 : ℝ) < -1) hNpos).const_mul (1 / 2 : ℝ)
    change Integrable (fun x : ℝ => x ^ (-3 / 2 : ℝ) / 2)
      (volume.restrict (Ioi (N : ℝ)))
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using! h
  have hnonneg : ∀ x ∈ Ioi (N : ℝ), 0 ≤ f x := by
    intro x hx
    exact div_nonneg (Real.rpow_nonneg (hNpos.trans hx).le _) (by norm_num)
  have hs : Summable (fun n : ℕ => f n) :=
    hanti.summable_of_integrableOn_Ioi hi hnonneg
  have hshift : Summable (fun n : ℕ => f ((n + N : ℕ) : ℝ)) :=
    (summable_nat_add_iff N).2 hs
  have hsplit := hshift.tsum_eq_zero_add
  simp only [zero_add] at hsplit
  have hremaining := AntitoneOn.tsum_comp_add_le_integral N hanti hi hnonneg
  have hbound : (∑' n : ℕ, f ((n + N : ℕ) : ℝ)) ≤
      f (N : ℝ) + ∫ x : ℝ in Ioi (N : ℝ), f x := by
    rw [hsplit]
    have hrem : (∑' n : ℕ, f ((n + 1 + N : ℕ) : ℝ)) ≤
        ∫ x : ℝ in Ioi (N : ℝ), f x := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 N] using hremaining
    exact add_le_add le_rfl hrem
  have hsum := nativePositiveCompletionLogDensity_hasSum_tail_cells hN
  calc
    _ = ∑' n : ℕ, ∫ u : ℝ in Ico ((n + N : ℕ) : ℝ)
          (((n + N : ℕ) : ℝ) + 1), nativePositiveCompletionLogDensity u := hsum.tsum_eq.symm
    _ ≤ ∑' n : ℕ, f ((n + N : ℕ) : ℝ) := by
      apply le_of_tendsto_of_tendsto hsum.summable.tendsto_sum_tsum_nat
        hshift.tendsto_sum_tsum_nat
      exact Filter.Eventually.of_forall fun J => Finset.sum_le_sum (fun n hn => by
        rw [integral_Ico_eq_integral_Ioo]
        exact nativePositiveCompletionLogDensity_cell_integral_le
          (n := n + N) (by omega))
    _ ≤ f (N : ℝ) + ∫ x : ℝ in Ioi (N : ℝ), f x := hbound
    _ = _ := by
      dsimp only [f]
      rw [integral_div, integral_Ioi_rpow_of_lt
        (by norm_num : (-3 / 2 : ℝ) < -1) hNpos]
      norm_num only
      ring

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePositiveCompletionLogDensity_hasSum_tail_cells
#print axioms Zeta23.CCM.nativePositiveCompletionLogDensity_tail_integral_le
