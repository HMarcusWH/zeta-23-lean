import Zeta23.CCM.CanonicalPrimeRemainder
import Zeta23.CCM.GlobalParityBottomSpectrum

noncomputable section

namespace Zeta23.CCM

/-!
# Exact arithmetic form of a lower certificate

This file fixes the signs and Euclidean norm in the remaining estimate.
It does not construct any certificate. The error must bound ALL legal vectors
at the same size, not just a computed trial vector.
-/

/-- The signed arithmetic estimate is equivalent to a canonical energy lower
bound, without an absolute-value relaxation or normalization loss. -/
theorem canonicalSourceChannelEnergy_lowerBound_iff
    {L : ℝ} (hL : 0 < L) (K : ℕ) (ε : ℝ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    -ε * ‖x‖ ^ 2 ≤ canonicalSourceChannelEnergy L K x ↔
      canonicalPrimeFreeBudget L K x + canonicalPrimeRemainderEnergy L K x ≤
        ε * ‖x‖ ^ 2 := by
  rw [canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget hL K x]
  constructor <;> intro h <;> linarith

/-- All-vector lower-bound obligation on the existing Euclidean boundary-flat
subspace. This is not satisfied by a finite vector sample. -/
def CanonicalArithmeticLowerBound (L : ℝ) (K : ℕ) (ε : ℝ) : Prop :=
  ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
    x ∈ euclideanBoundaryFlatSubspace K →
      canonicalPrimeFreeBudget L K x + canonicalPrimeRemainderEnergy L K x ≤
        ε * ‖x‖ ^ 2

/-- Exact equivalence of the two all-vector formulations. -/
theorem canonicalArithmeticLowerBound_iff_energy
    {L : ℝ} (hL : 0 < L) (K : ℕ) (ε : ℝ) :
    CanonicalArithmeticLowerBound L K ε ↔
      ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
        x ∈ euclideanBoundaryFlatSubspace K →
          -ε * ‖x‖ ^ 2 ≤ canonicalSourceChannelEnergy L K x := by
  constructor
  · intro h x hx
    exact (canonicalSourceChannelEnergy_lowerBound_iff hL K ε x).mpr (h x hx)
  · intro h x hx
    exact (canonicalSourceChannelEnergy_lowerBound_iff hL K ε x).mp (h x hx)

/-- A uniform arithmetic certificate on the complete legal boundary-flat
carrier gives the same lower bound on its exact Rayleigh bottom.  The
nontrivial-carrier hypothesis is explicit because the bottom is an infimum over
nonzero legal vectors. -/
theorem boundaryFlatRayleighBottom_lowerBound_of_canonicalArithmeticLowerBound
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K) (ε : ℝ)
    (hcert : CanonicalArithmeticLowerBound L K ε) :
    -ε ≤ boundaryFlatRayleighBottom L K := by
  have hfin :
      0 < Module.finrank ℂ (euclideanBoundaryFlatSubspace K) := by
    rw [finrank_euclideanBoundaryFlatSubspace K (by omega)]
    omega
  letI : Nontrivial (euclideanBoundaryFlatSubspace K) :=
    Module.nontrivial_of_finrank_pos hfin
  letI : Nonempty
      {z : euclideanBoundaryFlatSubspace K // z ≠ 0} := by
    obtain ⟨z, hz⟩ : ∃ z : euclideanBoundaryFlatSubspace K, z ≠ 0 :=
      exists_ne 0
    exact ⟨⟨z, hz⟩⟩
  unfold boundaryFlatRayleighBottom
  refine le_ciInf fun z => ?_
  let x : EuclideanSpace ℂ (Fin (2 * K + 1)) :=
    (z : euclideanBoundaryFlatSubspace K)
  have hxmem : x ∈ euclideanBoundaryFlatSubspace K :=
    (z : euclideanBoundaryFlatSubspace K).property
  have henergy :=
    (canonicalArithmeticLowerBound_iff_energy hL K ε).mp hcert x hxmem
  have hmatrix :
      -ε * ‖x‖ ^ 2 ≤
        Complex.re
          (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin x) x) := by
    rw [← matrixRealEnergy_eq_re_inner_apply_self,
      matrixRealEnergy_canonicalSourceMatrix_eq_channels hL K x]
    exact henergy
  have hden :
      0 < ‖(z : euclideanBoundaryFlatSubspace K)‖ ^ 2 := by
    simpa only [sq_pos_iff, norm_ne_zero_iff] using z.property
  rw [le_div_iff₀ hden]
  simpa [x] using hmatrix

/-- Successor-size specialization on the exact legal ground object introduced
in the post-#247 spectrum and identified with the boundary-flat carrier in
#268. -/
theorem globalParitySuccessorBottom_lowerBound_of_canonicalArithmeticLowerBound
    {L : ℝ} (hL : 0 < L) (N : ℕ) (hN : 1 ≤ N) (ε : ℝ)
    (hcert : CanonicalArithmeticLowerBound L (N + 1) ε) :
    -ε ≤ globalParitySuccessorBottom L N := by
  have hbf :=
    boundaryFlatRayleighBottom_lowerBound_of_canonicalArithmeticLowerBound
      hL (N + 1) (by omega) ε hcert
  rw [(canonicalCarrierBottom_hierarchy L N hN).2.2] at hbf
  exact hbf

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalSourceChannelEnergy_lowerBound_iff
#print axioms Zeta23.CCM.canonicalArithmeticLowerBound_iff_energy
#print axioms Zeta23.CCM.boundaryFlatRayleighBottom_lowerBound_of_canonicalArithmeticLowerBound
#print axioms Zeta23.CCM.globalParitySuccessorBottom_lowerBound_of_canonicalArithmeticLowerBound
