import Zeta23.CCM.GlobalParityBottomIntertwining
import Zeta23.CCM.RankOneEigenline

noncomputable section

namespace Zeta23.CCM

/-!
# Strict parity separation forces a one-dimensional ground eigenspace

D is used only as an injective algebraic map (or its algebraic inverse).
No isometry or metric transport through D is assumed. These theorems concern
the exact boundary-flat parity compressions, not the unconstrained operator.
They do not prove that either parity is always lower, that ties are absent,
or that any ground eigenvalue is nonnegative.
-/

/-- The scalar cubic functional is faithful on an even eigenspace lying below
the entire odd spectrum. -/
theorem evenEigenmode_eq_zero_of_source_eq_zero_below_odd
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (a : ℝ) (ha : a < parityRayleighBottom .odd L K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hv : parityCompressedCanonical .even L K v = (a : ℂ) • v)
    (hS : cubicDefectFunctional L K v = 0) : v = 0 := by
  by_contra hvne
  let D := euclideanEvenToOddIndexLinearMap K
  have hDv : D v ≠ 0 := by
    intro hz
    apply hvne
    apply euclideanEvenToOddIndexLinearMap_injective K
    exact hz.trans (map_zero D).symm
  have hi := evenEigenmode_shiftedOdd_eq_sourceCubic hL K hK a v hv
  rw [← cubicDefectFunctional_eq_evenQuadraticSourceMoment hL K hK v,
    hS, zero_smul] at hi
  have hp := shiftedParityCompressed_pos_of_lt_bottom .odd L K ha (D v) hDv
  change 0 < Complex.re (inner ℂ
    (oddCompressedCanonical L K (D v) - (a : ℂ) • D v) (D v)) at hp
  change oddCompressedCanonical L K (D v) - (a : ℂ) • D v = 0 at hi
  rw [hi] at hp
  simpa using hp

/-- Reverse-branch source functional, pulled back by the algebraic D-map. -/
def oddPulledBackSourceFunctional (L : ℝ) (K : ℕ) (hK : 1 ≤ K) :
    euclideanOddBoundaryFlatSubspace K →ₗ[ℂ] ℂ :=
  (cubicDefectFunctional L K).comp
    (euclideanEvenOddBoundaryFlatLinearEquiv K hK).symm.toLinearMap

/-- The pulled-back source functional is faithful on an odd eigenspace below
the even spectrum. -/
theorem oddEigenmode_eq_zero_of_source_eq_zero_below_even
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (a : ℝ) (ha : a < parityRayleighBottom .even L K)
    (w : euclideanOddBoundaryFlatSubspace K)
    (hw : parityCompressedCanonical .odd L K w = (a : ℂ) • w)
    (hS : oddPulledBackSourceFunctional L K (by omega) w = 0) : w = 0 := by
  have hK1 : 1 ≤ K := by omega
  let E := euclideanEvenOddBoundaryFlatLinearEquiv K hK1
  let v := E.symm w
  have hSv : cubicDefectFunctional L K v = 0 := hS
  have hi := oddEigenmode_pulledBack_shiftedEven_eq_neg_sourceCubic
    hL K hK a w hw
  dsimp only at hi
  change evenCompressedCanonical L K v - (a : ℂ) • v =
    -(evenQuadraticSourceMoment L K v) • pulledBackCubicCompressionVector K hK at hi
  rw [← cubicDefectFunctional_eq_evenQuadraticSourceMoment hL K hK v,
    hSv, neg_zero, zero_smul] at hi
  have hvzero : v = 0 := by
    by_contra hvne
    have hp := shiftedParityCompressed_pos_of_lt_bottom .even L K ha v hvne
    change 0 < Complex.re (inner ℂ
      (evenCompressedCanonical L K v - (a : ℂ) • v) v) at hp
    rw [hi] at hp
    simpa using hp
  have hm := congrArg E hvzero
  simpa [v] using hm

/-- Strict-even ground simplicity, proved for the complete even ground
 eigenspace. No chosen-ground-vector premise is present. -/
theorem evenGround_eigenspace_finrank_eq_one_of_strict
    {L : ℝ} (hL : 0 < L) (N : ℕ) (hN : 1 ≤ N)
    (hstrict : parityRayleighBottom .even L (N + 1) <
      parityRayleighBottom .odd L (N + 1)) :
    Module.finrank ℂ
      (Module.End.eigenspace (parityCompressedCanonical .even L (N + 1))
        (parityRayleighBottom .even L (N + 1) : ℂ)) = 1 := by
  apply eigenspace_finrank_eq_one_of_functional_kernel
    _ _ (cubicDefectFunctional L (N + 1))
  · intro v hv hS
    exact evenEigenmode_eq_zero_of_source_eq_zero_below_odd
      hL (N + 1) (by omega) _ hstrict v hv hS
  · exact exists_eigenmode_at_parityRayleighBottom_succ .even L N hN

/-- Strict-odd ground simplicity. The reverse branch uses the algebraic inverse
of D but never treats it as unitary. -/
theorem oddGround_eigenspace_finrank_eq_one_of_strict
    {L : ℝ} (hL : 0 < L) (N : ℕ) (hN : 1 ≤ N)
    (hstrict : parityRayleighBottom .odd L (N + 1) <
      parityRayleighBottom .even L (N + 1)) :
    Module.finrank ℂ
      (Module.End.eigenspace (parityCompressedCanonical .odd L (N + 1))
        (parityRayleighBottom .odd L (N + 1) : ℂ)) = 1 := by
  apply eigenspace_finrank_eq_one_of_functional_kernel
    _ _ (oddPulledBackSourceFunctional L (N + 1) (by omega))
  · intro w hw hS
    exact oddEigenmode_eq_zero_of_source_eq_zero_below_even
      hL (N + 1) (by omega) _ hstrict w hw hS
  · exact exists_eigenmode_at_parityRayleighBottom_succ .odd L N hN

/-- At a parity tie both parity ground modes attain the same global bottom.
They are in different parity carriers; this statement does not collapse the
carriers or claim a preferred vector at a multiple ground. -/
theorem exists_bothParityGrounds_at_tie
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (htie : parityRayleighBottom .even L (N + 1) =
      parityRayleighBottom .odd L (N + 1)) :
    (∃ v : euclideanEvenBoundaryFlatSubspace (N + 1), v ≠ 0 ∧
      parityCompressedCanonical .even L (N + 1) v =
        (globalParitySuccessorBottom L N : ℂ) • v) ∧
    (∃ w : euclideanOddBoundaryFlatSubspace (N + 1), w ≠ 0 ∧
      parityCompressedCanonical .odd L (N + 1) w =
        (globalParitySuccessorBottom L N : ℂ) • w) := by
  have hb : globalParitySuccessorBottom L N =
      parityRayleighBottom .even L (N + 1) := by
    simp [globalParitySuccessorBottom, htie]
  constructor
  · rw [hb]
    exact exists_eigenmode_at_parityRayleighBottom_succ .even L N hN
  · rw [hb, htie]
    exact exists_eigenmode_at_parityRayleighBottom_succ .odd L N hN

end Zeta23.CCM

#print axioms Zeta23.CCM.evenGround_eigenspace_finrank_eq_one_of_strict
#print axioms Zeta23.CCM.oddGround_eigenspace_finrank_eq_one_of_strict
#print axioms Zeta23.CCM.exists_bothParityGrounds_at_tie
