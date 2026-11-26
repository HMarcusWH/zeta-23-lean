import Zeta23.OPICATerminal.LiteralEnergyGrowth

/-! Supplier-free maximal-displacement lower bound; exact declarations moved from PowerDetectorSupply. -/
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

end Zeta23.OPICATerminal
