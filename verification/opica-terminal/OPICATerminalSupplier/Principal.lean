import Zeta23.OPICATerminal.Common
import Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG

/-! Extract the arithmetic estimate *before* the Landau/zero-free consumer.
    Original source pin. No Main, RH, or GRH proof is an input. -/
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top
namespace OPICAExtractionR1

theorem principal_kept_singleton :
    (Level.cyc PChar.one).KEPT = {PChar.one} := by
  classical
  ext ψ
  constructor
  · intro h
    change ψ ∈ (Level.ofSub (Subgroup.zpowers PChar.one.χ)).KEPT at h
    obtain ⟨χ, _, hψ⟩ := (Level.mem_ofSub _ _).mp h
    have hχ : χ = 1 := DirichletCharacter.level_one χ
    rw [hχ, PChar.of_one] at hψ
    simpa only [Finset.mem_singleton] using hψ.symm
  · intro h
    rw [Finset.mem_singleton] at h
    subst ψ
    exact Level.mem_cyc _

theorem principal_level_eq_discreteG (y : ℝ) :
    (Level.cyc PChar.one).Gm y = discreteG y := by
  classical
  have hn : (Level.cyc PChar.one).Nt = ∅ := by
    simp [Level.Nt, principal_kept_singleton]
  rw [Level.Gm, hn, Finset.sum_empty, add_zero]
  rfl

/-- Principal-only connectedness: no requirement for every other character.
    This is a new OPEN supplier target, not a closed proof. -/
def PrincipalConnected : Prop :=
  FamilyClassConnected ((GChi PChar.one).cls (3 / 2 : ℝ))

theorem principal_connected_of_topG_host
    (hG : TopG) (hS : HostExW (3 / 2 : ℝ) (GChi PChar.one).req) :
    PrincipalConnected :=
  hG (3 / 2) (GChi PChar.one) (by norm_num) hS (hypV_of_cls PChar.one (3 / 2))

/-- The complete original arithmetic window estimate, with the principal host
    and connectedness retained. The final zero exclusion is not used. -/
theorem principal_ramp_windows_of_connected
    (h : PrincipalConnected) : RampWindows := by
  obtain ⟨eD, eL, ε₁, h₁, h₂⟩ := h
  intro θ hθ hθ₁
  obtain ⟨ε, hε, hε₁, hCe⟩ := exists_small_eps (eD + eL + 7) (sub_pos.mpr hθ) h₁
  obtain ⟨Fm, hc, hd⟩ := h₂ ε hε hε₁
  obtain ⟨x₁, hx₁⟩ :=
    UpperTheory.Comparison₂.level_gm_le_on_family_scales (Level.cyc PChar.one)
      eD eL ε hε Fm (eFamC_of_cls PChar.one (3 / 2) Fm hc) hd
  refine ⟨1, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hw⟩ := hc.1 (max Y₀ (max x₁ 1))
  refine ⟨Y, (le_max_left _ _).trans hY, fun y hy => ?_⟩
  have hmax : max x₁ 1 ≤ y := (le_max_right Y₀ (max x₁ 1)).trans (hY.trans hy.1)
  have hxy : x₁ ≤ y := (le_max_left x₁ 1).trans hmax
  have h1y : 1 ≤ y := (le_max_right x₁ 1).trans hmax
  rw [← discreteG_eq_rampG, ← principal_level_eq_discreteG, one_mul]
  exact (hx₁ y hxy (hw y hy.1 hy.2)).trans
    (Real.rpow_le_rpow_of_exponent_le h1y (by linarith))

theorem principal_ramp_windows_of_topG_host
    (hG : TopG) (hS : HostExW (3 / 2 : ℝ) (GChi PChar.one).req) :
    RampWindows :=
  principal_ramp_windows_of_connected (principal_connected_of_topG_host hG hS)

/-- Conditional two-premise supplier cut; principal specialization does not
    eliminate the auxiliary growing fields in VWinAt. -/
theorem principal_ramp_windows_of_topG_vwin
    (hG : TopG) (hV : VWinAt PChar.one 401) : RampWindows :=
  principal_ramp_windows_of_topG_host hG (supplyChi PChar.one hV)

theorem principal_vwin_of_all (h : VWin) : VWinAt PChar.one 401 := h PChar.one

end OPICAExtractionR1
#print axioms OPICAExtractionR1.principal_vwin_of_all
#print axioms OPICAExtractionR1.principal_kept_singleton
#print axioms OPICAExtractionR1.principal_level_eq_discreteG
#print axioms OPICAExtractionR1.principal_ramp_windows_of_topG_host
#print axioms OPICAExtractionR1.principal_ramp_windows_of_topG_vwin

#print axioms OPICAExtractionR1.principal_connected_of_topG_host
#print axioms OPICAExtractionR1.principal_ramp_windows_of_connected
