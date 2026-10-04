import Zeta23.CCM.FirstCrossingProductionArithmetic

noncomputable section
namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate Interval ArithmeticFunction

/-!
# Congruence of the finite-aperture production functional

The complete physical RHS only sees values on [0,L]: both continuous
integrals are interval integrals there and every retained prime logarithm lies
in the same interval.
-/

theorem productionArithmeticComplexValue_congr_on_Icc
    {L : ℝ} (hL : 0 < L)
    {f g : ℝ → ℂ}
    (hfg : ∀ t ∈ Icc (0 : ℝ) L, f t = g t) :
    productionArithmeticComplexValue L f =
      productionArithmeticComplexValue L g := by
  unfold productionArithmeticComplexValue dictionaryCompletePhysicalRHS
  have hpole :
      (∫ t : ℝ in (0 : ℝ)..L,
          f t * (completeSourcePoleWeight t : ℂ)) =
        ∫ t : ℝ in (0 : ℝ)..L,
          g t * (completeSourcePoleWeight t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [hfg t ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
  have harch :
      (∫ t : ℝ in (0 : ℝ)..L,
          f t * (archDensity t : ℂ)) =
        ∫ t : ℝ in (0 : ℝ)..L,
          g t * (archDensity t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [hfg t ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
  have hprime :
      (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          primeSourceWeight q * f (Real.log q)) =
        ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          primeSourceWeight q * g (Real.log q) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hfg]
    · rfl
    · have hqmem := Finset.mem_Icc.mp hq
      have hq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
      have hqpos : (0 : ℝ) < q := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hqmem.1)
      have hqexp : (q : ℝ) ≤ Real.exp L :=
        (Nat.le_floor_iff (Real.exp_pos L).le).mp hqmem.2
      have hqL : Real.log q ≤ L := by
        rw [← Real.log_exp L]
        exact Real.log_le_log hqpos hqexp
      exact ⟨hq0, hqL⟩
  rw [hpole, harch, hprime]

theorem productionArithmeticRealValue_congr_on_Icc
    {L : ℝ} (hL : 0 < L)
    {f g : ℝ → ℝ}
    (hfg : ∀ t ∈ Icc (0 : ℝ) L, f t = g t) :
    productionArithmeticRealValue L f =
      productionArithmeticRealValue L g := by
  unfold productionArithmeticRealValue
  congr 1
  exact productionArithmeticComplexValue_congr_on_Icc hL
    (fun t ht => by rw [hfg t ht])

end Zeta23.CCM

#print axioms Zeta23.CCM.productionArithmeticRealValue_congr_on_Icc
