import Zeta23.CCM.GlobalParityBottomSimplicity
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section

namespace Zeta23.CCM

/-!
# Multiplicity of the parity-split legal ground space

The product represents both legal parity ground spaces at their common minimum.
No conclusion is made about the unconstrained full-space ground; this does not
discharge the original unconstrained CCM even-simple gate.
-/

/-- Both eigenspaces at the SAME minimum, not independent sector ground values.
A reducible type alias retains the product's inherited algebraic instances. -/
abbrev paritySplitGroundSpace (L : ℝ) (N : ℕ) :=
  (Module.End.eigenspace (parityCompressedCanonical .even L (N + 1))
    (globalParitySuccessorBottom L N : ℂ)) ×
  (Module.End.eigenspace (parityCompressedCanonical .odd L (N + 1))
    (globalParitySuccessorBottom L N : ℂ))

/-- There is no eigenvector strictly below a sector's Rayleigh bottom. -/
theorem parityEigenspace_eq_bot_of_lt_bottom
    (p : ReversalParity) (L : ℝ) (K : ℕ) (a : ℝ)
    (ha : a < parityRayleighBottom p L K) :
    Module.End.eigenspace (parityCompressedCanonical p L K) (a : ℂ) = ⊥ := by
  apply le_antisymm
  · intro x hx
    change x = 0
    by_contra hxne
    have he := Module.End.mem_eigenspace_iff.mp hx
    have hp := shiftedParityCompressed_pos_of_lt_bottom p L K ha x hxne
    change 0 < Complex.re (inner ℂ
      (parityCompressedCanonical p L K x - (a : ℂ) • x) x) at hp
    rw [he, sub_self] at hp
    simpa using hp
  · exact bot_le

/-- On the strict-even branch only the even eigenline contributes. -/
theorem paritySplitGroundSpace_finrank_eq_one_of_even_strict
    {L : ℝ} (hL : 0 < L) (N : ℕ) (hN : 1 ≤ N)
    (h : parityRayleighBottom .even L (N + 1) <
      parityRayleighBottom .odd L (N + 1)) :
    Module.finrank ℂ (paritySplitGroundSpace L N) = 1 := by
  have hb : globalParitySuccessorBottom L N =
      parityRayleighBottom .even L (N + 1) := min_eq_left h.le
  have hz := parityEigenspace_eq_bot_of_lt_bottom .odd L (N + 1) _ h
  have he := evenGround_eigenspace_finrank_eq_one_of_strict hL N hN h
  unfold paritySplitGroundSpace
  rw [Module.finrank_prod, hb, hz, finrank_bot, he]

/-- On the strict-odd branch only the odd eigenline contributes. -/
theorem paritySplitGroundSpace_finrank_eq_one_of_odd_strict
    {L : ℝ} (hL : 0 < L) (N : ℕ) (hN : 1 ≤ N)
    (h : parityRayleighBottom .odd L (N + 1) <
      parityRayleighBottom .even L (N + 1)) :
    Module.finrank ℂ (paritySplitGroundSpace L N) = 1 := by
  have hb : globalParitySuccessorBottom L N =
      parityRayleighBottom .odd L (N + 1) := min_eq_right h.le
  have hz := parityEigenspace_eq_bot_of_lt_bottom .even L (N + 1) _ h
  have ho := oddGround_eigenspace_finrank_eq_one_of_strict hL N hN h
  unfold paritySplitGroundSpace
  rw [Module.finrank_prod, hb, hz, finrank_bot, ho]

/-- A parity tie contributes a nonzero mode in each carrier. This lower bound
of two does NOT assume that either tied sector is simple. -/
theorem two_le_paritySplitGroundSpace_finrank_of_tie
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (h : parityRayleighBottom .even L (N + 1) =
      parityRayleighBottom .odd L (N + 1)) :
    2 ≤ Module.finrank ℂ (paritySplitGroundSpace L N) := by
  obtain ⟨⟨v, hvne, hv⟩, ⟨w, hwne, hw⟩⟩ :=
    exists_bothParityGrounds_at_tie L N hN h
  let E := Module.End.eigenspace (parityCompressedCanonical .even L (N + 1))
    (globalParitySuccessorBottom L N : ℂ)
  let O := Module.End.eigenspace (parityCompressedCanonical .odd L (N + 1))
    (globalParitySuccessorBottom L N : ℂ)
  let v' : E := ⟨v, Module.End.mem_eigenspace_iff.mpr hv⟩
  let w' : O := ⟨w, Module.End.mem_eigenspace_iff.mpr hw⟩
  have hv' : v' ≠ 0 := fun hz => hvne (congrArg Subtype.val hz)
  have hw' : w' ≠ 0 := fun hz => hwne (congrArg Subtype.val hz)
  letI : Nontrivial E := nontrivial_of_ne v' 0 hv'
  letI : Nontrivial O := nontrivial_of_ne w' 0 hw'
  have he : 0 < Module.finrank ℂ E := Module.finrank_pos
  have ho : 0 < Module.finrank ℂ O := Module.finrank_pos
  change 2 ≤ Module.finrank ℂ (E × O)
  rw [Module.finrank_prod]
  omega

/-- Simplicity in parity coordinates is exactly strict sector separation. -/
theorem paritySplitGroundSpace_simple_iff_ne
    {L : ℝ} (hL : 0 < L) (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (paritySplitGroundSpace L N) = 1 ↔
      parityRayleighBottom .even L (N + 1) ≠
        parityRayleighBottom .odd L (N + 1) := by
  constructor
  · intro hsimple htie
    have htwo := two_le_paritySplitGroundSpace_finrank_of_tie L N hN htie
    omega
  · intro hne
    rcases lt_or_gt_of_ne hne with he | ho
    · exact paritySplitGroundSpace_finrank_eq_one_of_even_strict hL N hN he
    · exact paritySplitGroundSpace_finrank_eq_one_of_odd_strict hL N hN ho

end Zeta23.CCM

#print axioms Zeta23.CCM.paritySplitGroundSpace_simple_iff_ne
#print axioms Zeta23.CCM.two_le_paritySplitGroundSpace_finrank_of_tie
