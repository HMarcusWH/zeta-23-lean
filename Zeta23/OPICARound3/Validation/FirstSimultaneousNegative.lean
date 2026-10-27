import Zeta23.OPICARound3.FirstSimultaneousNegative

namespace Zeta23.OPICARound3.Validation

open CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

/-- Independent literal expansion on the existing actual native-even
interface, whose definitions reduce to the original physical source space. -/
theorem even_newborn_schur_consumer {L : ℝ} (hL : 0 < L)
    (h : ∃ K, 3 ≤ K ∧ EvenNeutralNegative L K) :
    let K := firstNeutralCutoff .even L h
    letI := nativePoleNeutralParitySpace_normedAddCommGroup .even L (K - 1)
    letI := nativePoleNeutralParitySpace_innerProductSpace .even L (K - 1)
    letI := nativePoleNeutralParitySpace_normedAddCommGroup .even L K
    letI := nativePoleNeutralParitySpace_innerProductSpace .even L K
    let J := nativePoleNeutralParityCenteredZeroExtend .even L (show K - 1 ≤ K by omega)
    let T := nativePoleNeutralParityCanonical .even L K
    let A := predecessorBlock J T
    Module.finrank ℂ (isometricDetectorComplement J) = 1 ∧
      ∃ e : isometricDetectorComplement J, ‖e‖ = 1 ∧
        (let b : nativePoleNeutralParitySpace .even L (K - 1) := J.toLinearMap.adjoint (T e.val);
          A.ker.starProjection b ≠ 0 ∨ ∃ hb : b ∈ A.range,
            (inner ℂ (T e.val) e.val).re -
              (inner ℂ b (kernelSafeResponse A b hb)).re < 0) := by
  simpa only [NeutralNewbornSchur, oneShellSchurScalar] using (firstNeutralCutoff_schur hL .even h)

/-- K=3 has zero actual coupling into its zero-dimensional predecessor.
The literal Schur correction vanishes for every response, including the
kernel-safe response of the proved generic scalar theorem. -/
theorem even_K3_schur_scalar {L : ℝ} (hL : 0 < L) :
    letI := nativePoleNeutralParitySpace_normedAddCommGroup .even L 2
    letI := nativePoleNeutralParitySpace_innerProductSpace .even L 2
    letI := nativePoleNeutralParitySpace_normedAddCommGroup .even L 3
    letI := nativePoleNeutralParitySpace_innerProductSpace .even L 3
    let J := nativePoleNeutralParityCenteredZeroExtend .even L (show 2 ≤ 3 by omega)
    let T := nativePoleNeutralParityCanonical .even L 3
    ∀ e : isometricDetectorComplement J,
      let b : nativePoleNeutralParitySpace .even L 2 := J.toLinearMap.adjoint (T e.val);
      b = 0 ∧ ∀ r : nativePoleNeutralParitySpace .even L 2,
        (inner ℂ (T e.val) e.val).re - (inner ℂ b r).re =
          (inner ℂ (T e.val) e.val).re := by
  letI := nativePoleNeutralParitySpace_normedAddCommGroup .even L 2
  letI := nativePoleNeutralParitySpace_innerProductSpace .even L 2
  letI := nativePoleNeutralParitySpace_normedAddCommGroup .even L 3
  letI := nativePoleNeutralParitySpace_innerProductSpace .even L 3
  have hdim : Module.finrank ℂ (nativePoleNeutralParitySpace .even L 2) = 0 :=
    finrank_nativePoleNeutralParitySpace .even hL 2 (by omega)
  letI : Subsingleton (nativePoleNeutralParitySpace .even L 2) := Module.finrank_zero_iff.mp hdim
  dsimp only
  intro e
  have hz : (nativePoleNeutralParityCenteredZeroExtend .even L (show 2 ≤ 3 by omega)).toLinearMap.adjoint
      (nativePoleNeutralParityCanonical .even L 3 e.val) = 0 :=
    Subsingleton.elim _ _
  refine ⟨hz, ?_⟩
  intro r
  rw [hz, inner_zero_left (𝕜 := ℂ) r, Complex.zero_re, sub_zero]

/-- Independent consumer retains both separate least cutoffs, newborn-only
PSD predecessors, both actual Schur branches and unequal arrival behavior. -/
theorem first_simultaneous_neutral_negative_cutoff_consumer
    {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 3 ≤ K)
    (hboth : BothNeutralNegative L K) :
    ∃ Ke Ko : ℕ, 3 ≤ Ke ∧ 3 ≤ Ko ∧
      EvenNeutralNegative L Ke ∧ OddNeutralNegative L Ko ∧
      (∀ M, 3 ≤ M → EvenNeutralNegative L M → Ke ≤ M) ∧
      (∀ M, 3 ≤ M → OddNeutralNegative L M → Ko ≤ M) ∧
      BothNeutralNegative L (max Ke Ko) ∧
      (∀ M, 3 ≤ M → BothNeutralNegative L M → max Ke Ko ≤ M) ∧
      PoleNeutralParityPSD .even L (Ke - 1) ∧
      PoleNeutralParityPSD .odd L (Ko - 1) ∧
      NeutralNewbornSchur .even L Ke ∧ NeutralNewbornSchur .odd L Ko ∧
      (Ke < Ko → EvenNeutralNegative L (Ko - 1)) ∧
      (Ko < Ke → OddNeutralNegative L (Ke - 1)) :=
  first_simultaneous_neutral_negative_cutoff hL hK hboth

example {L : ℝ} (hL : 0 < L) (p : ReversalParity) : PoleNeutralParityPSD p L 2 :=
  poleNeutralParityPSD_two hL p

end Zeta23.OPICARound3.Validation

#print axioms Zeta23.OPICARound3.Validation.even_newborn_schur_consumer
#print axioms Zeta23.OPICARound3.Validation.even_K3_schur_scalar
#print axioms Zeta23.OPICARound3.Validation.first_simultaneous_neutral_negative_cutoff_consumer
