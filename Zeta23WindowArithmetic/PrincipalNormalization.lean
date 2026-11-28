import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

/-!
# Principal cyclic-level normalization

At modulus one every Dirichlet character is the principal character.  Therefore
the original cyclic level has no nonprincipal summands and its `Gm` is exactly
the original literal `Formalism.Gz`.  This is a finite algebraic normalization;
it uses no zero-free conclusion.
-/

noncomputable section

namespace Zeta23WindowArithmetic

open Formalism.HC

/-- The original principal cyclic level retains only the principal character. -/
theorem principal_level_kept :
    (Level.cyc PChar.one).KEPT = {PChar.one} := by
  classical
  ext ψ
  simp only [Finset.mem_singleton]
  constructor
  · intro hψ
    obtain ⟨χ, _, hχ⟩ :=
      (Level.mem_ofSub (Subgroup.zpowers PChar.one.χ) ψ).1 hψ
    have hχone : χ = 1 := DirichletCharacter.level_one χ
    rw [hχone, PChar.of_one] at hχ
    exact hχ.symm
  · intro hψ
    subst ψ
    exact Level.mem_cyc PChar.one

/-- Erasing the principal character removes the entire additional sum. -/
theorem principal_level_gm_eq_Gz (x : ℝ) :
    (Level.cyc PChar.one).Gm x = Formalism.Gz x := by
  classical
  simp [Level.Gm, Level.Nt, principal_level_kept]

end Zeta23WindowArithmetic
