import Zeta23.OPICARound3.NewbornSource

noncomputable section

namespace Zeta23.OPICARound3.Validation

open CCM Matrix

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

/-- Independently restated D05 type: own births, exact common cutoff and
both non-strict selected-parity clauses, so tied arrivals retain both. -/
theorem first_simultaneous_newborn_source_witnesses_consumer {L : ℝ} (hL : 0 < L)
    {K : ℕ} (hK : 3 ≤ K) (hboth : BothNeutralNegative L K) :
    ∃ Ke Ko : ℕ, 3 ≤ Ke ∧ 3 ≤ Ko ∧
      EvenNeutralNegative L Ke ∧ OddNeutralNegative L Ko ∧
      (∀ M, 3 ≤ M → EvenNeutralNegative L M → Ke ≤ M) ∧
      (∀ M, 3 ≤ M → OddNeutralNegative L M → Ko ≤ M) ∧
      BothNeutralNegative L (max Ke Ko) ∧
      (∀ M, 3 ≤ M → BothNeutralNegative L M → max Ke Ko ≤ M) ∧
      Nonempty (NativeNewbornSourceWitness .even L Ke hL) ∧
      Nonempty (NativeNewbornSourceWitness .odd L Ko hL) ∧
      (Ko ≤ Ke → Nonempty (NativeNewbornSourceWitness .even L (max Ke Ko) hL)) ∧
      (Ke ≤ Ko → Nonempty (NativeNewbornSourceWitness .odd L (max Ke Ko) hL)) := by
  exact Zeta23.OPICARound3.first_simultaneous_newborn_source_witnesses hL hK hboth

/-- The entire actual shifted output projects to zero. No source-alone
range or kernel claim is substituted for this equation. -/
theorem newborn_source_full_output_projection_consumer {L : ℝ} (hL : 0 < L)
    (p : ReversalParity) (K : ℕ) (W : NativeNewbornSourceWitness p L K hL) (lam : ℝ) :
    (nativePoleNeutralParityShifted (sourceOppositeParity p) L K lam).ker.starProjection
      (nativeParitySourceOutput p hL K W.w lam) = 0 := by
  exact W.source_kernel lam

/-- The same constructed w has both literal physical pole moments and
negative COMPLETE source quadratic form; this is not another chosen witness. -/
theorem newborn_source_physical_consumer {L : ℝ} (hL : 0 < L)
    (p : ReversalParity) (K : ℕ) (W : NativeNewbornSourceWitness p L K hL) :
    let u := nativePoleNeutralParityAmbient p L K W.w
    u ≠ 0 ∧ u ∈ euclideanBoundaryFlatSubspace K ∧
      canonicalPoleExponentialMoment 1 L K ((EuclideanSpace.equiv _ ℂ) u) = 0 ∧
      canonicalPoleExponentialMoment (-1) L K ((EuclideanSpace.equiv _ ℂ) u) = 0 ∧
      (quadraticForm (canonicalSourceMatrix L K) ((EuclideanSpace.equiv _ ℂ) u)).re < 0 := by
  refine ⟨negative_fullCanonicalEnergy_ne_zero W.full_negative,
    nativePoleNeutralParityAmbient_legal p L K W.w, W.physical_poles.1, W.physical_poles.2, ?_⟩
  rw [quadraticForm_re_eq_re_inner_apply_self]
  exact W.full_negative

/-- At K=3 the actual predecessor is zero-dimensional, so the resonant
projection is impossible and the very same constructed w is regular. -/
theorem newborn_source_K3_regular_consumer {L : ℝ} (hL : 0 < L)
    (p : ReversalParity) (W : NativeNewbornSourceWitness p L 3 hL) :
    let J := newbornCutoffInclusion p L 3
    let T := nativePoleNeutralParityCanonical p L 3
    ∃ hb : J.toLinearMap.adjoint (T W.e.val) ∈ (predecessorBlock J T).range,
      oneShellSchurScalar J T W.e hb < 0 ∧ W.w = regularSchurWitness J T W.e hb ∧
        (inner ℂ (T W.w) W.w).re = oneShellSchurScalar J T W.e hb := by
  have hdim : Module.finrank ℂ (nativePoleNeutralParitySpace p L 2) = 0 :=
    finrank_nativePoleNeutralParitySpace p hL 2 (by omega)
  letI : Subsingleton (nativePoleNeutralParitySpace p L 2) := Module.finrank_zero_iff.mp hdim
  have hreal := W.realization
  unfold NativeSchurWitnessRealization at hreal
  rcases hreal with hres | hreg
  · exact False.elim (hres.1 (Subsingleton.elim _ _))
  · exact hreg

end Zeta23.OPICARound3.Validation

#print axioms Zeta23.OPICARound3.Validation.first_simultaneous_newborn_source_witnesses_consumer
#print axioms Zeta23.OPICARound3.Validation.newborn_source_full_output_projection_consumer
#print axioms Zeta23.OPICARound3.Validation.newborn_source_physical_consumer
#print axioms Zeta23.OPICARound3.Validation.newborn_source_K3_regular_consumer
