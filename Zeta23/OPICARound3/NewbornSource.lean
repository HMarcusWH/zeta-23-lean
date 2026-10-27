import Zeta23.OPICARound3.SchurNegativeWitness
import Zeta23.OPICARound3.FirstSimultaneousNegative
import Zeta23.CCM.CanonicalPoleNeutralTiePackage

noncomputable section

namespace Zeta23.OPICARound3

open CCM Matrix
open scoped ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

def sourceOppositeParity : ReversalParity → ReversalParity
  | .even => .odd
  | .odd => .even

/-- Same-parity cutoff inclusion. This is not the parity transfer below. -/
def newbornCutoffInclusion (p : ReversalParity) (L : ℝ) (K : ℕ) :=
  nativePoleNeutralParityCenteredZeroExtend p L (show K - 1 ≤ K by omega)

/-- The actual full arithmetic scalar, including the removed output. -/
def fullCorrectedSourceScalar (L : ℝ) (K : ℕ) (u : poleNeutralEvenSubspace L K) : ℂ :=
  explicitCanonicalSourceMoment L K u.val -
    canonicalPoleQuadraticNormalCoefficient L K * poleNeutralEvenOutputCoefficient L K u

theorem fullCorrectedSourceScalar_eq {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (u : poleNeutralEvenSubspace L K) :
    fullCorrectedSourceScalar L K u = poleNeutralCorrectedCubicSource L K u :=
  (poleNeutralCorrectedCubicSource_eq_explicitCanonicalSourceMoment hL K (by omega) u).symm

/-- Actual same-cutoff parity transfer: D in the even direction and D-adjoint
in the odd direction. No isometry or sign-preservation assertion is made. -/
def nativeParityTransfer (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    nativePoleNeutralParitySpace p L K →ₗ[ℂ]
      nativePoleNeutralParitySpace (sourceOppositeParity p) L K := by
  cases p
  · exact poleNeutralIndexLinearMap hL K
  · letI := nativePoleNeutralParitySpace_normedAddCommGroup .even L K
    letI := nativePoleNeutralParitySpace_innerProductSpace .even L K
    letI := nativePoleNeutralParitySpace_normedAddCommGroup .odd L K
    letI := nativePoleNeutralParitySpace_innerProductSpace .odd L K
    exact (poleNeutralIndexLinearMap hL K).adjoint

def nativeParitySourceDefect (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ)
    (w : nativePoleNeutralParitySpace p L K) :
    nativePoleNeutralParitySpace (sourceOppositeParity p) L K := by
  cases p
  · exact fullCorrectedSourceScalar L K w • poleNeutralCubicCompressionVector L K
  · exact -(poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K)

/-- Retain the transformed shifted output as well as the corrected source. -/
def nativeParitySourceOutput (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ)
    (w : nativePoleNeutralParitySpace p L K) (lam : ℝ) :
    nativePoleNeutralParitySpace (sourceOppositeParity p) L K :=
  nativeParityTransfer p hL K (nativePoleNeutralParityShifted p L K lam w) +
    nativeParitySourceDefect p hL K w

theorem nativeParitySource_equation (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : nativePoleNeutralParitySpace p L K) :
    nativePoleNeutralParityCanonical (sourceOppositeParity p) L K (nativeParityTransfer p hL K w) =
      nativeParityTransfer p hL K (nativePoleNeutralParityCanonical p L K w) +
        nativeParitySourceDefect p hL K w := by
  cases p
  · have hr := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K (by omega) w
    change poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K w) -
      poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K w) = _ at hr
    have heq := sub_eq_iff_eq_add'.mp hr
    simpa only [nativePoleNeutralParityCanonical, sourceOppositeParity, nativeParityTransfer,
      nativeParitySourceDefect, fullCorrectedSourceScalar_eq hL K hK] using! heq
  · have hr := poleNeutral_adjoint_rankOne_identity hL K hK w
    have heq : poleNeutralEvenCompressedCanonical L K ((poleNeutralIndexLinearMap hL K).adjoint w) =
        (poleNeutralIndexLinearMap hL K).adjoint (poleNeutralOddCompressedCanonical L K w) +
          -(poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K) := by
      rw [← hr]
      abel
    simpa only [nativePoleNeutralParityCanonical, sourceOppositeParity, nativeParityTransfer,
      nativeParitySourceDefect] using! heq

theorem nativeParitySource_shifted_equation (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : nativePoleNeutralParitySpace p L K) (lam : ℝ) :
    nativePoleNeutralParityShifted (sourceOppositeParity p) L K lam (nativeParityTransfer p hL K w) =
      nativeParitySourceOutput p hL K w lam := by
  simp only [nativeParitySourceOutput, nativePoleNeutralParityShifted,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
  rw [nativeParitySource_equation p hL K hK w]
  abel

theorem nativeParitySource_output_mem_range (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : nativePoleNeutralParitySpace p L K) (lam : ℝ) :
    nativeParitySourceOutput p hL K w lam ∈
      (nativePoleNeutralParityShifted (sourceOppositeParity p) L K lam).range :=
  ⟨nativeParityTransfer p hL K w, nativeParitySource_shifted_equation p hL K hK w lam⟩

theorem nativeParitySource_whole_output_kernel (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : nativePoleNeutralParitySpace p L K) (lam : ℝ) :
    (nativePoleNeutralParityShifted (sourceOppositeParity p) L K lam).ker.starProjection
      (nativeParitySourceOutput p hL K w lam) = 0 :=
  (kernel_projection_zero_iff_range _
    (nativePoleNeutralParityShifted_isSymmetric (sourceOppositeParity p) L K lam) _).mpr
      (nativeParitySource_output_mem_range p hL K hK w lam)

/-- The odd corrected-source Riesz vector is exposed by the same COMPLETE
arithmetic functional, tested against actual even coefficients. -/
def NativeSourceArithmeticExposure (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (w : nativePoleNeutralParitySpace p L K) : Prop :=
  match p with
  | .even => nativeParitySourceDefect .even hL K w =
      fullCorrectedSourceScalar L K w • poleNeutralCubicCompressionVector L K
  | .odd => ∀ x : poleNeutralEvenSubspace L K,
      inner ℂ x.val.val (nativeParitySourceDefect .odd hL K w).val.val =
        -(poleNeutralCubicPairingFunctional L K w) * star (fullCorrectedSourceScalar L K x)

theorem nativeParitySource_arithmetic_exposure (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : nativePoleNeutralParitySpace p L K) :
    NativeSourceArithmeticExposure p hL K w := by
  cases p
  · rfl
  · intro x
    have hsource := inner_poleNeutralCorrectedCubicRieszVector L K x
    change inner ℂ (poleNeutralCorrectedCubicRieszVector L K).val.val x.val.val =
      poleNeutralCorrectedCubicSource L K x at hsource
    have hinner : inner ℂ x.val.val (poleNeutralCorrectedCubicRieszVector L K).val.val =
        star (fullCorrectedSourceScalar L K x) := by
      have hc := (inner_conj_symm (𝕜 := ℂ) x.val.val
        (poleNeutralCorrectedCubicRieszVector L K).val.val).symm
      rw [hsource, ← fullCorrectedSourceScalar_eq hL K hK x] at hc
      simpa only [Complex.star_def] using hc
    change inner ℂ x.val.val
        (-(poleNeutralCubicPairingFunctional L K w •
          (poleNeutralCorrectedCubicRieszVector L K).val.val)) = _
    simp only [inner_neg_right, inner_smul_right, hinner, neg_mul]

def NativeSchurWitnessRealization (p : ReversalParity) (L : ℝ) (K : ℕ)
    (e : isometricDetectorComplement (newbornCutoffInclusion p L K))
    (w : nativePoleNeutralParitySpace p L K) : Prop :=
  let J := newbornCutoffInclusion p L K
  let T := nativePoleNeutralParityCanonical p L K
  ((predecessorBlock J T).ker.starProjection (J.toLinearMap.adjoint (T e.val)) ≠ 0 ∧
    w = resonantSchurWitness J T e ∧ (inner ℂ (T w) w).re = -1) ∨
  (∃ hb : J.toLinearMap.adjoint (T e.val) ∈ (predecessorBlock J T).range,
    oneShellSchurScalar J T e hb < 0 ∧ w = regularSchurWitness J T e hb ∧
      (inner ℂ (T w) w).re = oneShellSchurScalar J T e hb)

/-- Produced data, never an assumed arithmetic restriction. The one w in
all fields is constructed from the actual newborn regular/resonant branch. -/
structure NativeNewbornSourceWitness (p : ReversalParity) (L : ℝ) (K : ℕ) (hL : 0 < L) where
  cutoff_lower : 3 ≤ K
  minimal : ∀ M, 3 ≤ M → PoleNeutralParityNegative p L M → K ≤ M
  predecessor_psd : PoleNeutralParityPSD p L (K - 1)
  shell_rank : Module.finrank ℂ (isometricDetectorComplement (newbornCutoffInclusion p L K)) = 1
  e : isometricDetectorComplement (newbornCutoffInclusion p L K)
  e_unit : ‖e‖ = 1
  w : nativePoleNeutralParitySpace p L K
  realization : NativeSchurWitnessRealization p L K e w
  w_ne_zero : w ≠ 0
  native_negative : (inner ℂ (nativePoleNeutralParityCanonical p L K w) w).re < 0
  full_negative : fullCanonicalEnergy L K (nativePoleNeutralParityAmbient p L K w) < 0
  physical_poles :
    canonicalPoleExponentialMoment 1 L K ((EuclideanSpace.equiv _ ℂ)
      (nativePoleNeutralParityAmbient p L K w)) = 0 ∧
    canonicalPoleExponentialMoment (-1) L K ((EuclideanSpace.equiv _ ℂ)
      (nativePoleNeutralParityAmbient p L K w)) = 0
  arithmetic : NativeSourceArithmeticExposure p hL K w
  source_equation : ∀ lam : ℝ,
    nativePoleNeutralParityShifted (sourceOppositeParity p) L K lam (nativeParityTransfer p hL K w) =
      nativeParitySourceOutput p hL K w lam
  source_range : ∀ lam : ℝ, nativeParitySourceOutput p hL K w lam ∈
    (nativePoleNeutralParityShifted (sourceOppositeParity p) L K lam).range
  source_kernel : ∀ lam : ℝ,
    (nativePoleNeutralParityShifted (sourceOppositeParity p) L K lam).ker.starProjection
      (nativeParitySourceOutput p hL K w lam) = 0

theorem first_neutral_newborn_source_witness {L : ℝ} (hL : 0 < L)
    (p : ReversalParity) (h : ∃ K, 3 ≤ K ∧ PoleNeutralParityNegative p L K) :
    Nonempty (NativeNewbornSourceWitness p L (firstNeutralCutoff p L h) hL) := by
  let K := firstNeutralCutoff p L h
  let J := newbornCutoffInclusion p L K
  let T := nativePoleNeutralParityCanonical p L K
  have hK : 3 ≤ K := (firstNeutralCutoff_spec p L h).1
  have hs := firstNeutralCutoff_schur hL p h
  change Module.finrank ℂ (isometricDetectorComplement J) = 1 ∧
    ∃ e : isometricDetectorComplement J, ‖e‖ = 1 ∧
      ((predecessorBlock J T).ker.starProjection (J.toLinearMap.adjoint (T e.val)) ≠ 0 ∨
        ∃ hb : J.toLinearMap.adjoint (T e.val) ∈ (predecessorBlock J T).range,
          oneShellSchurScalar J T e hb < 0) at hs
  obtain ⟨hshell, e, he, hcases⟩ := hs
  have hT : T.IsSymmetric := by
    cases p
    · exact poleNeutralEvenCompressedCanonical_isSymmetric L K
    · exact poleNeutralOddCompressedCanonical_isSymmetric L K
  have hw : ∃ w : nativePoleNeutralParitySpace p L K,
      NativeSchurWitnessRealization p L K e w ∧ (inner ℂ (T w) w).re < 0 := by
    rcases hcases with hres | ⟨hb, hneg⟩
    · have hq := resonantSchurWitness_energy J T hT e hres
      exact ⟨resonantSchurWitness J T e, Or.inl ⟨hres, rfl, hq⟩, by rw [hq]; norm_num⟩
    · have hq := regularSchurWitness_energy J T hT e hb
      exact ⟨regularSchurWitness J T e hb, Or.inr ⟨hb, hneg, rfl, hq⟩, by rw [hq]; exact hneg⟩
  obtain ⟨w, hreal, hneg⟩ := hw
  have hne : w ≠ 0 := by
    intro hz
    simp only [hz, map_zero, inner_zero_left, Complex.zero_re] at hneg
    exact (lt_irrefl 0) hneg
  have hfull : fullCanonicalEnergy L K (nativePoleNeutralParityAmbient p L K w) < 0 := by
    unfold fullCanonicalEnergy
    rw [nativePoleNeutralParityAmbient_energy]
    exact hneg
  exact ⟨{
    cutoff_lower := hK
    minimal := fun M hM hn => firstNeutralCutoff_le p L h hM hn
    predecessor_psd := firstNeutralCutoff_predecessor_psd hL p h
    shell_rank := hshell
    e := e
    e_unit := he
    w := w
    realization := hreal
    w_ne_zero := hne
    native_negative := hneg
    full_negative := hfull
    physical_poles := (canonicalPoleExponentialMoments_iff_profiles hL K _).mpr
      (nativePoleNeutralParityAmbient_poles p L K w)
    arithmetic := nativeParitySource_arithmetic_exposure p hL K hK w
    source_equation := nativeParitySource_shifted_equation p hL K hK w
    source_range := nativeParitySource_output_mem_range p hL K hK w
    source_kernel := nativeParitySource_whole_output_kernel p hL K hK w }⟩

/-- D05: each actual first newborn has a Schur-created negative witness with
the full source equation. At the first common cutoff the later parity is
newborn; equal arrival gives both packets there. No sign leaf is assumed. -/
theorem first_simultaneous_newborn_source_witnesses {L : ℝ} (hL : 0 < L)
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
  let he : ∃ M, 3 ≤ M ∧ EvenNeutralNegative L M := ⟨K, hK, hboth.1⟩
  let ho : ∃ M, 3 ≤ M ∧ OddNeutralNegative L M := ⟨K, hK, hboth.2⟩
  let Ke := firstNeutralCutoff .even L he
  let Ko := firstNeutralCutoff .odd L ho
  have hcommon := firstBothNeutralCutoff_least hL he ho
  have hwe := first_neutral_newborn_source_witness hL .even he
  have hwo := first_neutral_newborn_source_witness hL .odd ho
  refine ⟨Ke, Ko, (firstNeutralCutoff_spec .even L he).1,
    (firstNeutralCutoff_spec .odd L ho).1, (firstNeutralCutoff_spec .even L he).2,
    (firstNeutralCutoff_spec .odd L ho).2,
    (fun M hM hn => firstNeutralCutoff_le .even L he hM hn),
    (fun M hM hn => firstNeutralCutoff_le .odd L ho hM hn),
    hcommon.2.1, hcommon.2.2, hwe, hwo, ?_, ?_⟩
  · intro hle
    simpa only [max_eq_left hle] using hwe
  · intro hle
    simpa only [max_eq_right hle] using hwo

end Zeta23.OPICARound3

#print axioms Zeta23.OPICARound3.nativeParitySource_shifted_equation
#print axioms Zeta23.OPICARound3.first_neutral_newborn_source_witness
#print axioms Zeta23.OPICARound3.first_simultaneous_newborn_source_witnesses
