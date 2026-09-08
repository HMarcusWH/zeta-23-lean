import Zeta23.CCM.CrossParityQuotientTransport

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-- Exact predecessor forcing produced by transporting the even canonical trial
vector through D. -/
def crossParityPredecessorForcing
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    intrinsicParityPredecessorSubspace .odd N :=
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
  let phi := evenParityCubicDefectFunctional L (N + 1) uPlus
  Fplus • oddIndexCubicShellPredecessorPart N +
    phi • oddCubicGeneratorPredecessorPart N

/-- Full transported residual decomposition, retaining both predecessor
corrections. -/
theorem evenTrial_oddResidual_eq_forcing_add_shell
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
    let Du := evenIndexParityLinearMap (N + 1) uPlus
    let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
    let phi := evenParityCubicDefectFunctional L (N + 1) uPlus
    parityCompressedCanonical .odd L (N + 1) Du - (lam : ℂ) • Du =
      (crossParityPredecessorForcing hL N hprevEven lam hlam :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (Fplus + phi) •
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  dsimp
  let D := evenIndexParityLinearMap (N + 1)
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
  let phi := evenParityCubicDefectFunctional L (N + 1) uPlus
  let cPlus : euclideanParityBoundaryFlatSubspace .even (N + 1) :=
    intrinsicCubicShellPart .even N
  let cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    intrinsicCubicShellPart .odd N
  let dW := oddIndexCubicShellPredecessorPart N
  let a := oddCubicGeneratorPredecessorPart N
  let f := crossParityPredecessorForcing hL N hprevEven lam hlam
  have hresPlus :=
    cubicSecularResidual_eq_scalar_smul_intrinsicCubicShellPart
      .even hL N hN hprevEven lam hlam
  have hDres :
      D (cubicSecularResidual .even hL N hprevEven lam hlam) =
        Fplus • D cPlus := by
    calc
      D (cubicSecularResidual .even hL N hprevEven lam hlam) =
          D (Fplus • cPlus) := congrArg D hresPlus
      _ = Fplus • D cPlus := D.map_smul Fplus cPlus
  have hdefNative :=
    evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul
      hL (N + 1) (by omega) uPlus
  have hdef :
      evenOddParityIntertwiningDefect L (N + 1) uPlus =
        phi • successorParityCubicVector .odd N := by
    change
      evenOddCompressedIntertwiningDefect L (N + 1) uPlus =
        cubicDefectFunctional L (N + 1) uPlus •
          oddCubicCompressionVector (N + 1)
    exact hdefNative
  have hbase :
      parityCompressedCanonical .odd L (N + 1) (D uPlus) -
          (lam : ℂ) • D uPlus =
        D (cubicSecularResidual .even hL N hprevEven lam hlam) +
          evenOddParityIntertwiningDefect L (N + 1) uPlus := by
    change
      parityCompressedCanonical .odd L (N + 1) (D uPlus) -
          (lam : ℂ) • D uPlus =
        D
            (parityCompressedCanonical .even L (N + 1) uPlus -
              (lam : ℂ) • uPlus) +
          (parityCompressedCanonical .odd L (N + 1) (D uPlus) -
            D (parityCompressedCanonical .even L (N + 1) uPlus))
    have hDsub := D.map_sub
      (parityCompressedCanonical .even L (N + 1) uPlus)
      ((lam : ℂ) • uPlus)
    have hDsmul := D.map_smul (lam : ℂ) uPlus
    rw [hDsub, hDsmul]
    abel
  have hDc :=
    evenIndex_cubicShellPart_eq_predecessor_add_oddCubicShellPart N hN
  have hg := oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N
  have hmain :
      parityCompressedCanonical .odd L (N + 1) (D uPlus) -
          (lam : ℂ) • D uPlus =
        (f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (Fplus + phi) • cMinus := by
    calc
      parityCompressedCanonical .odd L (N + 1) (D uPlus) -
          (lam : ℂ) • D uPlus =
        D (cubicSecularResidual .even hL N hprevEven lam hlam) +
          evenOddParityIntertwiningDefect L (N + 1) uPlus := hbase
      _ = Fplus • D cPlus + phi • successorParityCubicVector .odd N := by
        rw [hDres, hdef]
      _ = Fplus •
            ((dW : euclideanParityBoundaryFlatSubspace .odd (N + 1)) + cMinus) +
          phi •
            ((a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) + cMinus) := by
        rw [hDc, hg]
      _ =
        ((Fplus • dW + phi • a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (Fplus + phi) • cMinus := by
        simp only [Submodule.coe_add, Submodule.coe_smul, smul_add, add_smul]
        abel
      _ = (f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (Fplus + phi) • cMinus := by
        rfl
  exact hmain

/-- The transported even trial vector has the canonical odd shell component. -/
theorem intrinsicShellPart_evenIndex_cubicSecularTrialVector
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    intrinsicShellPart .odd N
        (evenIndexParityLinearMap (N + 1)
          (cubicSecularTrialVector .even hL N hprevEven lam hlam)) =
      intrinsicCubicShellPart .odd N := by
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let Du := evenIndexParityLinearMap (N + 1) uPlus
  have hqPlus :=
    intrinsicCubicQuotientCoordinate_cubicSecularTrialVector
      .even hL N hN hprevEven lam hlam
  have hqTransport := intrinsicCubicQuotientCoordinate_evenIndex N hN uPlus
  have hqDu : intrinsicCubicQuotientCoordinate .odd N Du = 1 :=
    hqTransport.trans hqPlus
  have hrep := intrinsicCubicShellCoordinate_smul_cubic_eq
    .odd N hN (intrinsicShellPart .odd N Du)
  change
    intrinsicCubicShellCoordinate .odd N (intrinsicShellPart .odd N Du) = 1
      at hqDu
  rw [hqDu] at hrep
  simpa only [one_smul] using hrep.symm

set_option maxHeartbeats 500000 in
/-- Exact reconstruction of the odd canonical trial vector from D of the even
canonical trial vector and the safe odd predecessor resolvent. -/
theorem cubicSecularTrialVector_odd_eq_evenIndex_sub_resolvent_forcing
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicSecularTrialVector .odd hL N hprevOdd lam hlam =
      evenIndexParityLinearMap (N + 1)
          (cubicSecularTrialVector .even hL N hprevEven lam hlam) -
        ((shiftedIntrinsicPredecessorResolvent
            .odd hL N hprevOdd lam hlam
            (crossParityPredecessorForcing hL N hprevEven lam hlam) :
          intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let D := evenIndexParityLinearMap (N + 1)
  let uD : euclideanParityBoundaryFlatSubspace .odd (N + 1) := D uPlus
  let f := crossParityPredecessorForcing hL N hprevEven lam hlam
  let c := intrinsicCubicShellPart .odd N
  let b := intrinsicShellToPredecessor .odd L N c
  let R := shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam
  let wD := intrinsicPredecessorPart .odd N uD
  have hsD : intrinsicShellPart .odd N uD = c := by
    simpa [uD, D, uPlus, c] using
      intrinsicShellPart_evenIndex_cubicSecularTrialVector
        hL N hN hprevEven lam hlam
  have hrecD := intrinsicPredecessorPart_add_shellPart .odd N uD
  have huDdecomp :
      uD =
        (wD : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    calc
      uD =
          (intrinsicPredecessorPart .odd N uD :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (intrinsicShellPart .odd N uD :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := hrecD.symm
      _ =
          (wD : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
        rw [hsD]
  have hTuPred :
      intrinsicPredecessorPart .odd N
          (parityCompressedCanonical .odd L (N + 1) uD) =
        intrinsicPredecessorBlock .odd L N wD + b := by
    calc
      intrinsicPredecessorPart .odd N
          (parityCompressedCanonical .odd L (N + 1) uD) =
        intrinsicPredecessorPart .odd N
          (parityCompressedCanonical .odd L (N + 1)
            ((wD : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
              (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)))) := by
          rw [huDdecomp]
      _ =
        intrinsicPredecessorPart .odd N
            (parityCompressedCanonical .odd L (N + 1)
              (wD : euclideanParityBoundaryFlatSubspace .odd (N + 1))) +
          intrinsicPredecessorPart .odd N
            (parityCompressedCanonical .odd L (N + 1)
              (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) := by
          rw [map_add, map_add]
      _ = intrinsicPredecessorBlock .odd L N wD + b := by
          rfl
  have hfull :=
    evenTrial_oddResidual_eq_forcing_add_shell
      hL N hN hprevEven lam hlam
  have hfSelf :
      intrinsicPredecessorPart .odd N
          (f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = f := by
    change
      Submodule.projectionOnto
          (intrinsicParityPredecessorSubspace .odd N)
          (intrinsicParitySuccShell .odd N)
          (intrinsicPredecessor_isCompl_shell .odd N)
          (f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = f
    exact Submodule.projectionOnto_apply_left
      (intrinsicPredecessor_isCompl_shell .odd N) f
  have hcZero :
      intrinsicPredecessorPart .odd N
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = 0 := by
    change
      Submodule.projectionOnto
          (intrinsicParityPredecessorSubspace .odd N)
          (intrinsicParitySuccShell .odd N)
          (intrinsicPredecessor_isCompl_shell .odd N)
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = 0
    exact Submodule.projectionOnto_apply_right
      (intrinsicPredecessor_isCompl_shell .odd N) c
  have hpredResidual :
      intrinsicPredecessorPart .odd N
          (parityCompressedCanonical .odd L (N + 1) uD -
            (lam : ℂ) • uD) = f := by
    calc
      intrinsicPredecessorPart .odd N
          (parityCompressedCanonical .odd L (N + 1) uD -
            (lam : ℂ) • uD) =
        intrinsicPredecessorPart .odd N
          ((f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
            (cubicSecularScalar .even hL N hprevEven lam hlam +
              evenParityCubicDefectFunctional L (N + 1) uPlus) •
              (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) := by
          exact congrArg (intrinsicPredecessorPart .odd N) hfull
      _ = f := by
        rw [map_add, map_smul, hfSelf, hcZero, smul_zero, add_zero]
  rw [map_sub, hTuPred, map_smul] at hpredResidual
  change
    intrinsicPredecessorBlock .odd L N wD + b - (lam : ℂ) • wD = f
      at hpredResidual
  have hshiftWD' :
      intrinsicPredecessorBlock .odd L N wD - (lam : ℂ) • wD = f - b := by
    calc
      intrinsicPredecessorBlock .odd L N wD - (lam : ℂ) • wD =
          (intrinsicPredecessorBlock .odd L N wD + b - (lam : ℂ) • wD) - b := by
        abel
      _ = f - b := by rw [hpredResidual]
  have hshiftWD :
      shiftedIntrinsicPredecessorBlock .odd L N lam wD = f - b := by
    change intrinsicPredecessorBlock .odd L N wD - (lam : ℂ) • wD = f - b
    exact hshiftWD'
  have hRf : shiftedIntrinsicPredecessorBlock .odd L N lam (R f) = f := by
    simpa [R] using
      shiftedIntrinsicPredecessorBlock_resolvent_apply
        .odd hL N hprevOdd lam hlam f
  have hRb : shiftedIntrinsicPredecessorBlock .odd L N lam (R b) = b := by
    simpa [R] using
      shiftedIntrinsicPredecessorBlock_resolvent_apply
        .odd hL N hprevOdd lam hlam b
  have hshiftTarget :
      shiftedIntrinsicPredecessorBlock .odd L N lam (R f - R b) = f - b := by
    rw [map_sub, hRf, hRb]
  have hinj := shiftedIntrinsicPredecessorBlock_injective .odd hL N hprevOdd hlam
  have hwD : wD = R f - R b := hinj (hshiftWD.trans hshiftTarget.symm)
  have huD :
      uD =
        ((R f - R b : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    rw [huDdecomp, hwD]
  change
    ((- R b : intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
    uD -
      ((R f : intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1))
  rw [huD]
  simp only [Submodule.coe_sub, Submodule.coe_neg]
  abel

/-- Linear odd correction functional generated by the safe predecessor
resolvent. -/
def oddSafeSecularCorrectionFunctional
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    intrinsicParityPredecessorSubspace .odd N →ₗ[ℂ] ℂ :=
  (intrinsicCubicQuotientCoordinate .odd N).comp
    ((parityCompressedCanonical .odd L (N + 1)).comp
      ((intrinsicParityPredecessorSubspace .odd N).subtype.comp
        (shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam)))

/-- Coefficient multiplying the even secular scalar after predecessor
correction. -/
def crossParitySecularAlpha
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) : ℂ :=
  1 - oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
    (oddIndexCubicShellPredecessorPart N)

/-- Coefficient multiplying the cubic/source defect after predecessor
correction. -/
def crossParitySecularGamma
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) : ℂ :=
  1 - oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
    (oddCubicGeneratorPredecessorPart N)

end Zeta23.CCM
