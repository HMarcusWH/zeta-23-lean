import Zeta23WindowArithmetic.PrincipalNormalization
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG

/-!
# Extract complete arithmetic windows before the zero-free consumer

The fixed family exponents are selected before the small positive exponent.
After that choice, a single complete real window is selected beyond both the
requested threshold and the arithmetic onset.  No cofinal assertion is promoted
to an eventual assertion, and the coefficient in the resulting bound is one.

`ZeroFreeAllOfTopG` owns the `TopG` definition and the family-class adapters used
below.  Its zero-free theorem is deliberately not used.
-/

noncomputable section

namespace Zeta23WindowArithmetic

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC
open UpperTheory.Top GlobalTheory.EX

/-- Extract the principal literal bound using only the two arithmetic inputs. -/
theorem principal_original_windows_of_inputs
    (hTop : UpperTheory.Top.TopG)
    (hSupply : HostExW (3 / 2) (GChi PChar.one).req) :
    ∀ t : ℝ, 0 < t → ∀ B : ℝ, ∃ Y : ℝ,
      max B 2 ≤ Y ∧
      ∀ x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)),
        Formalism.Gz x ≤ x ^ (1 / 2 + t) := by
  intro t ht B
  obtain ⟨eD, eL, ε₁, hε₁, hFamilies⟩ :=
    hTop (3 / 2) (GChi PChar.one) (by norm_num) hSupply
      (hypV_of_cls PChar.one (3 / 2))
  obtain ⟨eps, heps, hsmall, hcoeff⟩ :=
    exists_small_eps (eD + eL + 7) ht hε₁
  obtain ⟨Fm, hcls, hTied⟩ := hFamilies eps heps hsmall
  obtain ⟨x₁, hpointwise⟩ :=
    UpperTheory.Comparison₂.level_gm_le_on_family_scales
      (Level.cyc PChar.one) eD eL eps heps Fm
      (eFamC_of_cls PChar.one (3 / 2) Fm hcls) hTied
  obtain ⟨Y, hY, hWin⟩ :=
    ((windows_iff Fm.toFamCore (3 / 2)).1 hcls.1)
      (max (max B 2) x₁)
  have hYB : max B 2 ≤ Y :=
    (le_max_left (max B 2) x₁).trans hY
  have hY₁ : x₁ ≤ Y :=
    (le_max_right (max B 2) x₁).trans hY
  refine ⟨Y, hYB, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := (le_max_right B 2).trans (hYB.trans hx.1)
  have hx1 : 1 ≤ x := by linarith
  have hraw := hpointwise x (hY₁.trans hx.1) (hWin x hx.1 hx.2)
  rw [principal_level_gm_eq_Gz] at hraw
  exact hraw.trans
    (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))

end Zeta23WindowArithmetic
