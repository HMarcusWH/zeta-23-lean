import Zeta23.OPICATerminal.LiteralEnergyGrowth
import Zeta23.OPICATerminal.PowerContract

/-! Supplier-free comparison of the literal energy with both native moment
slices at the original quartic cutoff. The strip supremum need not be attained.
The arithmetic upper is not an input to any theorem in this file. -/
noncomputable section
open Set Filter
open Zeta23.OPICARound4.ArithmeticFrontier
open Zeta23.OPICARound6.PrimeDeficit
open Zeta23.OPICARound3 Zeta23.CCM Zeta23.ExceptionalZero
namespace Zeta23.OPICATerminal

def displacementSet : Set ℝ :=
  insert 0 ((fun ρ : ℂ => |ρ.re-1/2|) '' zetaZeroConfig.carrier)

def displacement : ℝ := sSup displacementSet

theorem zero_mem_displacementSet : (0:ℝ) ∈ displacementSet := by
  simp [displacementSet]

theorem displacementSet_bddAbove : BddAbove displacementSet := by
  refine ⟨1/2,?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | ⟨ρ,hρ,rfl⟩
  · norm_num
  · exact abs_re_sub_half_le_half ρ hρ

theorem displacement_nonneg : 0 ≤ displacement :=
  le_csSup displacementSet_bddAbove zero_mem_displacementSet

theorem displacement_le_half : displacement ≤ 1/2 := by
  apply csSup_le ⟨0,zero_mem_displacementSet⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | ⟨ρ,hρ,rfl⟩
  · norm_num
  · exact abs_re_sub_half_le_half ρ hρ

theorem displacement_bound (ρ : ℂ) (hρ : ρ ∈ zetaZeroConfig.carrier) :
    |ρ.re-1/2| ≤ displacement := by
  apply le_csSup displacementSet_bddAbove
  exact Set.mem_insert_of_mem _ ⟨ρ,hρ,rfl⟩

theorem exists_right_zero_of_lt_displacement {θ : ℝ}
    (hθ : 1/2 ≤ θ) (ha : θ-1/2 < displacement) :
    ∃ ρ ∈ zetaZeroConfig.carrier, θ < ρ.re := by
  by_contra hn
  have hbound : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ θ :=
    fun ρ hρ => le_of_not_gt (fun hgt => hn ⟨ρ,hρ,hgt⟩)
  have hs : displacement ≤ θ-1/2 := by
    apply csSup_le ⟨0,zero_mem_displacementSet⟩
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨ρ,hρ,rfl⟩
    · linarith
    · exact abs_re_sub_half_le_of_re_le hbound ρ hρ
  exact (not_le_of_gt ha) hs

/-- Sharp open exponent range for the fixed 3/2 window. -/
theorem eventual_literalGEnergy_ge_rpow {h : ℝ} (hh : 0 < h)
    (hha : h < 3*displacement) :
    ∀ᶠ Y in atTop, Y^h ≤ literalGEnergy Y := by
  let a := displacement
  have ha : 0 < a := by dsimp [a]; linarith
  have hhalf : a ≤ 1/2 := displacement_le_half
  have hratio : h/(2*a) < 3/2 :=
    (div_lt_iff₀ (by positivity : 0 < 2*a)).2 (by dsimp [a]; linarith)
  have hmax : max (1:ℝ) (h/(2*a)) < 3/2 :=
    max_lt_iff.mpr ⟨by norm_num,hratio⟩
  obtain ⟨c,hc,hc'⟩ := exists_between hmax
  have hc1 : 1 < c := (le_max_left _ _).trans_lt hc
  have hcpos : 0 < c := by linarith
  have hhc : h < 2*a*c := by
    have ht := (div_lt_iff₀ (by positivity : 0 < 2*a)).1 ((le_max_right _ _).trans_lt hc)
    linarith
  have ht : h/(2*c) < a :=
    (div_lt_iff₀ (by positivity : 0 < 2*c)).2 (by nlinarith [hhc])
  obtain ⟨t,ht1,ht2⟩ := exists_between ht
  have ht0 : 0 < t := (div_pos hh (by positivity : 0 < 2*c)).trans ht1
  let θ := 1/2+t
  have hθ : 1/2 < θ := by dsimp [θ]; linarith
  have hθ' : θ < 1 := by dsimp [θ]; linarith
  have hm : h < c*(2*θ-1) := by
    have := (div_lt_iff₀ (by positivity : 0 < 2*c)).1 ht1
    dsimp [θ]
    nlinarith
  obtain ⟨ρ,hρ,hr⟩ := exists_right_zero_of_lt_displacement hθ.le
    (show θ-1/2 < displacement by
      change θ-1/2 < a
      dsimp [θ]
      linarith)
  exact eventual_energy_growth_of_right_zero hc1 hc' hθ hθ' hm ρ hρ hr

/-- Stronger than R2's disjunction: both original slices, same error and cutoff. -/
def BothParityPowerComparison (δ : ℝ) : Prop :=
  ∃ Y₀ : ℝ, ∀ Y : ℝ, max Y₀ 2 ≤ Y →
    EvenMomentSliceLowerBound (Real.log Y) (originalDetectorQuarticCutoff (Real.log Y))
      (literalGEnergy Y / Y^δ) ∧
    OddMomentSliceLowerBound (Real.log Y) (originalDetectorQuarticCutoff (Real.log Y))
      (literalGEnergy Y / Y^δ)

theorem bothParityPowerComparison_proved :
    ∃ δ : ℝ, 0 < δ ∧ BothParityPowerComparison δ := by
  by_cases hz : displacement = 0
  · have hline : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1/2 := by
      intro ρ hρ
      have h := displacement_bound ρ hρ
      rw [hz] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    refine ⟨1,one_pos,Real.exp 1,fun Y hY => ?_⟩
    have hY2 : 2 ≤ Y := (le_max_right _ _).trans hY
    have hYpos : 0 < Y := by linarith
    have hlog : 1 ≤ Real.log Y := by
      rw [← Real.log_exp (1:ℝ)]
      exact Real.log_le_log (Real.exp_pos _) ((le_max_left _ _).trans hY)
    have hL : 0 < Real.log Y := by linarith
    have herr : 0 ≤ literalGEnergy Y / Y^(1:ℝ) :=
      div_nonneg (literalGEnergy_nonneg hY2) (Real.rpow_nonneg hYpos.le _)
    exact ⟨(evenMomentSliceLowerBound_zero_of_critical_line hline hL _).mono herr,
      (oddMomentSliceLowerBound_zero_of_critical_line hline hL _).mono herr⟩
  · let a := displacement
    have ha : 0 < a := lt_of_le_of_ne displacement_nonneg (Ne.symm hz)
    have hs : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re-1/2| ≤ a := displacement_bound
    obtain ⟨Ce,hCe,he⟩ := evenMomentSliceLowerBound_explicit_of_zeroStrip
      (α := 5*a/4) (by linarith) hs
    obtain ⟨Co,hCo,ho⟩ := oddMomentSliceLowerBound_explicit_of_zeroStrip
      (α := 5*a/4) (by linarith) hs
    have hga : 2*a < 3*displacement := by dsimp [a] at *; linarith
    obtain ⟨B,hB⟩ := eventually_atTop.1
      (eventual_literalGEnergy_ge_rpow (show 0 < 2*a by positivity) hga)
    obtain ⟨D,hD⟩ := eventually_atTop.1
      ((tendsto_rpow_atTop (show 0 < a/4 by positivity)).eventually_ge_atTop (max Ce Co))
    refine ⟨a/2,by positivity,max (Real.exp 1) (max B D),fun Y hY => ?_⟩
    have hY2 : 2 ≤ Y := (le_max_right _ _).trans hY
    have hYpos : 0 < Y := by linarith
    have hY0 : max (Real.exp 1) (max B D) ≤ Y := (le_max_left _ _).trans hY
    have hBD : max B D ≤ Y := (le_max_right _ _).trans hY0
    have hE := hB Y ((le_max_left _ _).trans hBD)
    have hC := hD Y ((le_max_right _ _).trans hBD)
    have hlog : 1 ≤ Real.log Y := by
      rw [← Real.log_exp (1:ℝ)]
      exact Real.log_le_log (Real.exp_pos _) ((le_max_left _ _).trans hY0)
    have hpow : Real.exp (5*a/4*Real.log Y) = Y^(5*a/4:ℝ) := by
      rw [Real.rpow_def_of_pos hYpos, mul_comm]
    have hfinal : Y^(3*a/2:ℝ) ≤ literalGEnergy Y / Y^(a/2:ℝ) := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hYpos _)).2
      rw [← Real.rpow_add hYpos, show 3*a/2+a/2=2*a by ring]
      exact hE
    have herr (C : ℝ) (hC' : C ≤ max Ce Co) :
        C * Real.exp (5*a/4*Real.log Y) ≤ literalGEnergy Y / Y^(a/2:ℝ) := by
      rw [hpow]
      calc
        _ ≤ Y^(a/4:ℝ)*Y^(5*a/4:ℝ) :=
          mul_le_mul_of_nonneg_right (hC'.trans hC) (Real.rpow_nonneg hYpos.le _)
        _ = Y^(3*a/2:ℝ) := by rw [← Real.rpow_add hYpos, show a/4+5*a/4=3*a/2 by ring]
        _ ≤ _ := hfinal
    exact ⟨(he _ hlog).mono (herr Ce (le_max_left _ _)),
      (ho _ hlog).mono (herr Co (le_max_right _ _))⟩

theorem powerDetectorSupply_proved : OPICAR2.PowerDetectorSupply := by
  obtain ⟨δ,hδ,Y₀,hY₀⟩ := bothParityPowerComparison_proved
  refine ⟨δ,1,hδ,zero_le_one,Y₀,fun Y hY => Or.inl ?_⟩
  simpa only [one_mul] using (hY₀ Y hY).1

theorem directEnergyToC1_proved : OPICAExtractionR1.DirectEnergyToC1 :=
  OPICAR2.directEnergyToC1_of_power_supply powerDetectorSupply_proved

theorem cofinal_moment_slice_bounds_of_nativeEnergySubpower
    (h : OPICAExtractionR1.NativeEnergySubpower) : CofinalMomentSliceVanishingErrorBounds :=
  directEnergyToC1_proved h

theorem riemannHypothesis_of_nativeEnergySubpower
    (h : OPICAExtractionR1.NativeEnergySubpower) : RiemannHypothesis :=
  riemannHypothesis_of_cofinal_moment_slice_bounds
    (cofinal_moment_slice_bounds_of_nativeEnergySubpower h)

end Zeta23.OPICATerminal
