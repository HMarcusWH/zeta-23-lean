import Zeta23.CCM.KernelSourceTransport

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4b0: direct zero-shift cross-parity transfer

This module composes the denominator-free kernel/source transport with the
already-proved zero-shift shell response.  It works with explicit preimages
`A x₀ = b`; no inverse or pseudoinverse of the zero-shift predecessor block is
introduced.

The zero-shift coefficients below are attached to a selected odd preimage.
They are not asserted individually independent of that choice, and no limit
relation to the negative-shift `alpha` or `Gamma` coefficients is claimed.

Firewalls:
* no Laurent expansion or resolvent limit;
* no division by alpha, Gamma, overlap, or source moment;
* no D-isometry/unitarity;
* no source sign/nonzeroness claim;
* no branch exclusion, negative-root exclusion, or RH theorem.
-/

/-- Direct zero-shift alpha coefficient for a selected odd cubic-coupling
preimage. -/
def crossParityZeroShiftAlpha
    (N : ℕ)
    (xMinus : intrinsicParityPredecessorSubspace .odd N) : ℂ :=
  1 -
    inner ℂ
        (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
        ((oddIndexCubicShellPredecessorPart N :
            intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) /
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))

/-- Direct zero-shift Gamma coefficient for a selected odd cubic-coupling
preimage. -/
def crossParityZeroShiftGamma
    (N : ℕ)
    (xMinus : intrinsicParityPredecessorSubspace .odd N) : ℂ :=
  1 -
    inner ℂ
        (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
        ((oddCubicGeneratorPredecessorPart N :
            intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) /
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))

/-- Every canonical zero-shift trial vector has cubic quotient coordinate one. -/
theorem intrinsicCubicQuotientCoordinate_cubicZeroShiftTrialVector
    (p : ReversalParity) (L : ℝ)
    (N : ℕ) (hN : 1 ≤ N)
    (x₀ : intrinsicParityPredecessorSubspace p N) :
    intrinsicCubicQuotientCoordinate p N
        (cubicZeroShiftTrialVector p L N x₀) = 1 := by
  change
    intrinsicCubicShellCoordinate p N
      (intrinsicShellPart p N (cubicZeroShiftTrialVector p L N x₀)) = 1
  rw [intrinsicShellPart_cubicZeroShiftTrialVector]
  exact intrinsicCubicShellCoordinate_cubic p N hN

/-- D carries an even zero-shift trial to an odd vector with the canonical odd
shell component. -/
theorem intrinsicShellPart_evenIndex_cubicZeroShiftTrialVector
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (xPlus : intrinsicParityPredecessorSubspace .even N) :
    intrinsicShellPart .odd N
        (evenIndexParityLinearMap (N + 1)
          (cubicZeroShiftTrialVector .even L N xPlus)) =
      intrinsicCubicShellPart .odd N := by
  let uPlus := cubicZeroShiftTrialVector .even L N xPlus
  let Du := evenIndexParityLinearMap (N + 1) uPlus
  have hqPlus :=
    intrinsicCubicQuotientCoordinate_cubicZeroShiftTrialVector
      .even L N hN xPlus
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

/-- Direct full-carrier transport of an even regular zero-shift trial. -/
theorem parityCompressedCanonical_odd_evenIndex_zeroShiftTrial_eq
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (xPlus : intrinsicParityPredecessorSubspace .even N)
    (hxPlus : intrinsicPredecessorBlock .even L N xPlus =
      intrinsicShellToPredecessor .even L N
        (intrinsicCubicShellPart .even N)) :
    let uPlus := cubicZeroShiftTrialVector .even L N xPlus
    let sigmaPlus := cubicZeroShiftShellResponseScalar .even L N xPlus
    let mu := explicitCanonicalSourceMoment L (N + 1) uPlus
    let d := oddIndexCubicShellPredecessorPart N
    let a := oddCubicGeneratorPredecessorPart N
    let cMinus := intrinsicCubicShellPart .odd N
    parityCompressedCanonical .odd L (N + 1)
        (evenIndexParityLinearMap (N + 1) uPlus) =
      ((sigmaPlus • d + mu • a :
          intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (sigmaPlus + mu) •
        (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  dsimp
  let uPlus := cubicZeroShiftTrialVector .even L N xPlus
  let sigmaPlus := cubicZeroShiftShellResponseScalar .even L N xPlus
  let mu := explicitCanonicalSourceMoment L (N + 1) uPlus
  let D := evenIndexParityLinearMap (N + 1)
  let cPlus : euclideanParityBoundaryFlatSubspace .even (N + 1) :=
    intrinsicCubicShellPart .even N
  let cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    intrinsicCubicShellPart .odd N
  let d := oddIndexCubicShellPredecessorPart N
  let a := oddCubicGeneratorPredecessorPart N
  have hresponse :
      sigmaPlus • cPlus =
        parityCompressedCanonical .even L (N + 1) uPlus := by
    simpa [sigmaPlus, cPlus, uPlus] using
      cubicZeroShiftShellResponseScalar_smul_cubic_eq
        .even L N hN xPlus hxPlus
  have hdefNative :=
    evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul
      hL (N + 1) (by omega) uPlus
  have hsource : cubicDefectFunctional L (N + 1) uPlus = mu := by
    simpa [mu, uPlus] using
      cubicDefectFunctional_eq_explicitCanonicalSourceMoment
        hL (N + 1) (by omega) uPlus
  have hdef :
      parityCompressedCanonical .odd L (N + 1) (D uPlus) =
        D (parityCompressedCanonical .even L (N + 1) uPlus) +
          mu • successorParityCubicVector .odd N := by
    rw [hsource] at hdefNative
    have hsub :
        parityCompressedCanonical .odd L (N + 1) (D uPlus) -
          D (parityCompressedCanonical .even L (N + 1) uPlus) =
          mu • successorParityCubicVector .odd N := by
      simpa [D, evenIndexParityLinearMap,
        evenOddCompressedIntertwiningDefect,
        evenCompressedCanonical, oddCompressedCanonical,
        successorParityCubicVector] using hdefNative
    exact sub_eq_iff_eq_add.mp hsub
  have hDc :=
    evenIndex_cubicShellPart_eq_predecessor_add_oddCubicShellPart N hN
  have hg := oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N
  calc
    parityCompressedCanonical .odd L (N + 1) (D uPlus) =
      D (parityCompressedCanonical .even L (N + 1) uPlus) +
        mu • successorParityCubicVector .odd N := hdef
    _ = D (sigmaPlus • cPlus) +
        mu • successorParityCubicVector .odd N := by
      rw [← hresponse]
    _ = sigmaPlus • D cPlus +
        mu • successorParityCubicVector .odd N := by
      rw [map_smul]
    _ = sigmaPlus •
          (((d : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) + cMinus) +
        mu •
          (((a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) + cMinus) := by
      rw [hDc, hg]
    _ =
      ((sigmaPlus • d + mu • a :
          intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (sigmaPlus + mu) • cMinus := by
      simp only [Submodule.coe_add, Submodule.coe_smul, smul_add, add_smul]
      abel

/-- Predecessor coordinate of the transported even regular zero-shift trial. -/
theorem intrinsicPredecessorPart_odd_evenIndex_zeroShiftTrial_eq
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (xPlus : intrinsicParityPredecessorSubspace .even N)
    (hxPlus : intrinsicPredecessorBlock .even L N xPlus =
      intrinsicShellToPredecessor .even L N
        (intrinsicCubicShellPart .even N)) :
    intrinsicPredecessorPart .odd N
        (parityCompressedCanonical .odd L (N + 1)
          (evenIndexParityLinearMap (N + 1)
            (cubicZeroShiftTrialVector .even L N xPlus))) =
      cubicZeroShiftShellResponseScalar .even L N xPlus •
          oddIndexCubicShellPredecessorPart N +
        explicitCanonicalSourceMoment L (N + 1)
            (cubicZeroShiftTrialVector .even L N xPlus) •
          oddCubicGeneratorPredecessorPart N := by
  have hfull := parityCompressedCanonical_odd_evenIndex_zeroShiftTrial_eq
    hL N hN xPlus hxPlus
  dsimp at hfull
  have hp := congrArg (intrinsicPredecessorPart .odd N) hfull
  rw [map_add, intrinsicPredecessorPart_coe_predecessor,
    map_smul, intrinsicPredecessorPart_coe_shell, smul_zero, add_zero] at hp
  exact hp

/-- Even regularity determines the entire odd cubic-coupling kernel component
from the even zero-shift shell response and the exact source moment. -/
theorem oddCubicCouplingKernelPart_eq_evenZeroShiftResponse_add_source
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (xPlus : intrinsicParityPredecessorSubspace .even N)
    (hxPlus : intrinsicPredecessorBlock .even L N xPlus =
      intrinsicShellToPredecessor .even L N
        (intrinsicCubicShellPart .even N)) :
    cubicCouplingKernelPart .odd L N =
      cubicZeroShiftShellResponseScalar .even L N xPlus •
        intrinsicPredecessorKernelPart .odd L N
          (oddIndexCubicShellPredecessorPart N) +
      explicitCanonicalSourceMoment L (N + 1)
          (cubicZeroShiftTrialVector .even L N xPlus) •
        intrinsicPredecessorKernelPart .odd L N
          (oddCubicGeneratorPredecessorPart N) := by
  let uD := evenIndexParityLinearMap (N + 1)
    (cubicZeroShiftTrialVector .even L N xPlus)
  let wD := intrinsicPredecessorPart .odd N uD
  let cMinus := intrinsicCubicShellPart .odd N
  let bMinus := intrinsicShellToPredecessor .odd L N cMinus
  have hsD : intrinsicShellPart .odd N uD = cMinus := by
    simpa [uD, cMinus] using
      intrinsicShellPart_evenIndex_cubicZeroShiftTrialVector L N hN xPlus
  have hrecD := intrinsicPredecessorPart_add_shellPart .odd N uD
  have huD :
      uD =
        (wD : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    calc
      uD =
          (intrinsicPredecessorPart .odd N uD :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (intrinsicShellPart .odd N uD :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := hrecD.symm
      _ =
          (wD : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
        rw [hsD]
  have hpredBlock :
      intrinsicPredecessorPart .odd N
          (parityCompressedCanonical .odd L (N + 1) uD) =
        intrinsicPredecessorBlock .odd L N wD + bMinus := by
    rw [huD, map_add, map_add]
    rfl
  have hforcing :=
    intrinsicPredecessorPart_odd_evenIndex_zeroShiftTrial_eq
      hL N hN xPlus hxPlus
  have hAeq :
      intrinsicPredecessorBlock .odd L N wD + bMinus =
        cubicZeroShiftShellResponseScalar .even L N xPlus •
            oddIndexCubicShellPredecessorPart N +
          explicitCanonicalSourceMoment L (N + 1)
              (cubicZeroShiftTrialVector .even L N xPlus) •
            oddCubicGeneratorPredecessorPart N := by
    rw [← hpredBlock]
    simpa [uD] using hforcing
  have hk := congrArg (intrinsicPredecessorKernelPart .odd L N) hAeq
  rw [map_add,
    intrinsicPredecessorKernelPart_intrinsicPredecessorBlock_eq_zero] at hk
  change
    0 + cubicCouplingKernelPart .odd L N = _ at hk
  rw [map_add, map_smul, map_smul] at hk
  simpa using hk

/-- Zero-shift Gamma has the exact trial/full-cubic-generator overlap
interpretation for every selected odd preimage. -/
theorem crossParityZeroShiftGamma_eq_trial_cubic_overlap_div
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (xMinus : intrinsicParityPredecessorSubspace .odd N) :
    crossParityZeroShiftGamma N xMinus =
      inner ℂ
          (cubicZeroShiftTrialVector .odd L N xMinus)
          (successorParityCubicVector .odd N) /
        inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let c := intrinsicCubicShellPart .odd N
  let a := oddCubicGeneratorPredecessorPart N
  let den := inner ℂ
    (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))
    (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))
  have hg := oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N
  have hxc :
      inner ℂ
          (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = 0 :=
    inner_intrinsicPredecessor_shell_eq_zero .odd N xMinus c
  have hca :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = 0 :=
    inner_intrinsicShell_predecessor_eq_zero .odd N c a
  change
    1 - inner ℂ
          (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den = _
  rw [show successorParityCubicVector .odd N =
      (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) by
        simpa [a, c] using hg]
  change
    1 - inner ℂ
          (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den =
      inner ℂ
        (-(xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)))
        ((a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1) +
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) / den
  rw [inner_add_right, inner_add_left, inner_add_left,
    inner_neg_left, hxc, hca]
  simp only [neg_zero, zero_add, add_zero]
  ring

/-- Direct zero-shift cross-parity transfer.  It is proved at zero itself from
explicit predecessor preimages, not by taking a limit of the safe negative
resolvent formula. -/
theorem cubicZeroShiftShellResponseScalar_crossParity_explicitSource_transfer
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (xPlus : intrinsicParityPredecessorSubspace .even N)
    (hxPlus : intrinsicPredecessorBlock .even L N xPlus =
      intrinsicShellToPredecessor .even L N
        (intrinsicCubicShellPart .even N))
    (xMinus : intrinsicParityPredecessorSubspace .odd N)
    (hxMinus : intrinsicPredecessorBlock .odd L N xMinus =
      intrinsicShellToPredecessor .odd L N
        (intrinsicCubicShellPart .odd N)) :
    cubicZeroShiftShellResponseScalar .odd L N xMinus =
      crossParityZeroShiftAlpha N xMinus *
          cubicZeroShiftShellResponseScalar .even L N xPlus +
        crossParityZeroShiftGamma N xMinus *
          explicitCanonicalSourceMoment L (N + 1)
            (cubicZeroShiftTrialVector .even L N xPlus) := by
  let uPlus := cubicZeroShiftTrialVector .even L N xPlus
  let uMinus := cubicZeroShiftTrialVector .odd L N xMinus
  let Du := evenIndexParityLinearMap (N + 1) uPlus
  let w := intrinsicPredecessorPart .odd N (Du - uMinus)
  let cMinus := intrinsicCubicShellPart .odd N
  let d := oddIndexCubicShellPredecessorPart N
  let a := oddCubicGeneratorPredecessorPart N
  let sigmaPlus := cubicZeroShiftShellResponseScalar .even L N xPlus
  let sigmaMinus := cubicZeroShiftShellResponseScalar .odd L N xMinus
  let mu := explicitCanonicalSourceMoment L (N + 1) uPlus
  let den := inner ℂ
    (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
    (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
  have hden : den ≠ 0 := by
    exact inner_intrinsicCubicShellPart_self_ne_zero .odd N hN
  have hqDu : intrinsicCubicQuotientCoordinate .odd N Du = 1 := by
    exact
      (intrinsicCubicQuotientCoordinate_evenIndex N hN uPlus).trans
        (intrinsicCubicQuotientCoordinate_cubicZeroShiftTrialVector
          .even L N hN xPlus)
  have hqMinus : intrinsicCubicQuotientCoordinate .odd N uMinus = 1 :=
    intrinsicCubicQuotientCoordinate_cubicZeroShiftTrialVector
      .odd L N hN xMinus
  have hqDiff : intrinsicCubicQuotientCoordinate .odd N (Du - uMinus) = 0 := by
    rw [map_sub, hqDu, hqMinus, sub_self]
  have hmem : Du - uMinus ∈ intrinsicParityPredecessorSubspace .odd N :=
    (intrinsicCubicQuotientCoordinate_eq_zero_iff .odd N hN).1 hqDiff
  have hwCarrier :
      (w : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = Du - uMinus := by
    change
      ((intrinsicPredecessorPart .odd N (Du - uMinus) :
          intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) = Du - uMinus
    have hp := Submodule.projectionOnto_apply_left
      (intrinsicPredecessor_isCompl_shell .odd N)
      ⟨Du - uMinus, hmem⟩
    exact congrArg Subtype.val hp
  have hfull := parityCompressedCanonical_odd_evenIndex_zeroShiftTrial_eq
    hL N hN xPlus hxPlus
  dsimp at hfull
  have hminusResponse :
      sigmaMinus •
          (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        parityCompressedCanonical .odd L (N + 1) uMinus := by
    simpa [sigmaMinus, cMinus, uMinus] using
      cubicZeroShiftShellResponseScalar_smul_cubic_eq
        .odd L N hN xMinus hxMinus
  have hTw :
      parityCompressedCanonical .odd L (N + 1)
          (w : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        ((sigmaPlus • d + mu • a :
            intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (sigmaPlus + mu - sigmaMinus) •
          (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    rw [hwCarrier, map_sub, hfull, ← hminusResponse]
    simp only [smul_sub, sub_smul]
    abel
  have hpred :
      intrinsicPredecessorBlock .odd L N w =
        sigmaPlus • d + mu • a := by
    have hp := congrArg (intrinsicPredecessorPart .odd N) hTw
    rw [map_add, intrinsicPredecessorPart_coe_predecessor,
      map_smul, intrinsicPredecessorPart_coe_shell, smul_zero, add_zero] at hp
    change intrinsicPredecessorPart .odd N
      (parityCompressedCanonical .odd L (N + 1)
        (w : euclideanParityBoundaryFlatSubspace .odd (N + 1))) = _
    exact hp
  have hQTw :
      intrinsicCubicQuotientCoordinate .odd N
        (parityCompressedCanonical .odd L (N + 1)
          (w : euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        sigmaPlus + mu - sigmaMinus := by
    have hq := congrArg (intrinsicCubicQuotientCoordinate .odd N) hTw
    rw [map_add,
      intrinsicCubicQuotientCoordinate_predecessor_eq_zero .odd N hN,
      map_smul,
      intrinsicCubicQuotientCoordinate_cubicShellPart .odd N hN] at hq
    simpa using hq
  have hQmetric :=
    intrinsicCubicQuotientCoordinate_parityCompressedCanonical_predecessor_eq
      .odd L N hN w
  have hsym :
      inner ℂ
          ((intrinsicShellToPredecessor .odd L N cMinus :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (w : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((intrinsicPredecessorBlock .odd L N w :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    rw [← hxMinus]
    exact intrinsicPredecessorBlock_isSymmetric .odd L N xMinus w
  have hscalar :
      sigmaPlus + mu - sigmaMinus =
        (sigmaPlus * inner ℂ
            (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
            ((d : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          mu * inner ℂ
            (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
            ((a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) / den := by
    rw [← hQTw, hQmetric]
    change _ = _
    rw [hsym, hpred]
    rw [show
      (((sigmaPlus • d + mu • a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        sigmaPlus •
            ((d : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          mu •
            ((a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) by rfl]
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    simp only [smul_eq_mul]
  change sigmaMinus =
    (1 - inner ℂ
        (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
        ((d : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den) * sigmaPlus +
      (1 - inner ℂ
        (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
        ((a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den) * mu
  field_simp [hden] at hscalar ⊢
  ring_nf at hscalar ⊢
  linear_combination hscalar

/-- If both cubic couplings admit zero-shift preimages, the selected odd
zero-shift Gamma annihilates the exact #131 source functional on the entire
even predecessor kernel. -/
theorem crossParityZeroShiftGamma_mul_explicitSource_eq_zero_on_evenKernel
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (xPlus : intrinsicParityPredecessorSubspace .even N)
    (hxPlus : intrinsicPredecessorBlock .even L N xPlus =
      intrinsicShellToPredecessor .even L N
        (intrinsicCubicShellPart .even N))
    (xMinus : intrinsicParityPredecessorSubspace .odd N)
    (hxMinus : intrinsicPredecessorBlock .odd L N xMinus =
      intrinsicShellToPredecessor .odd L N
        (intrinsicCubicShellPart .odd N))
    (z : intrinsicParityPredecessorSubspace .even N)
    (hz : intrinsicPredecessorBlock .even L N z = 0) :
    crossParityZeroShiftGamma N xMinus *
      explicitCanonicalSourceMoment L (N + 1)
        (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) = 0 := by
  let beta := cubicShellCouplingCoefficient .even L N z
  let mu := explicitCanonicalSourceMoment L (N + 1)
    (z : euclideanParityBoundaryFlatSubspace .even (N + 1))
  let a := oddCubicGeneratorPredecessorPart N
  let Dz := evenIndexIntrinsicPredecessorLinearMap N z
  let cMinus := intrinsicCubicShellPart .odd N
  let bMinus := intrinsicShellToPredecessor .odd L N cMinus
  let den := inner ℂ
    (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
    (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
  have hden : den ≠ 0 :=
    inner_intrinsicCubicShellPart_self_ne_zero .odd N hN
  have hbeta : beta = 0 := by
    have hsym := intrinsicPredecessorBlock_isSymmetric
      .even L N xPlus z
    rw [hxPlus, hz] at hsym
    simp at hsym
    change
      inner ℂ
          ((intrinsicShellToPredecessor .even L N
              (intrinsicCubicShellPart .even N) :
            intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1))
          (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) /
        inner ℂ
          (intrinsicCubicShellPart .even N :
            euclideanParityBoundaryFlatSubspace .even (N + 1))
          (intrinsicCubicShellPart .even N :
            euclideanParityBoundaryFlatSubspace .even (N + 1)) = 0
    rw [hsym]
    simp
  have hpred :=
    oddPredecessorBlock_evenIndex_eq_beta_add_source_of_evenKernel
      hL N hN z hz
  change intrinsicPredecessorBlock .odd L N Dz =
    beta • oddIndexCubicShellPredecessorPart N + mu • a at hpred
  rw [hbeta, zero_smul, zero_add] at hpred
  have hqSource :=
    oddCubicCouplingQuotient_evenIndex_eq_beta_add_source_of_evenKernel
      hL N hN z hz
  rw [hbeta, zero_add] at hqSource
  have hqMetric :=
    intrinsicCubicQuotientCoordinate_parityCompressedCanonical_predecessor_eq
      .odd L N hN Dz
  rw [coe_evenIndexIntrinsicPredecessorLinearMap] at hqMetric
  have hQeq :
      mu = inner ℂ
          (bMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (Dz : euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
    rw [← hqSource, hqMetric]
    rfl
  have hsymMinus :
      inner ℂ
          (bMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (Dz : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((intrinsicPredecessorBlock .odd L N Dz :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    rw [← hxMinus]
    exact intrinsicPredecessorBlock_isSymmetric .odd L N xMinus Dz
  have hmu :
      mu = mu *
        inner ℂ
          (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
    rw [hQeq, hsymMinus, hpred]
    rw [show
      (((mu • a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        mu •
          ((a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) by rfl]
    rw [inner_smul_right]
    simp only [smul_eq_mul]
  change
    (1 - inner ℂ
        (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
        ((a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den) * mu = 0
  field_simp [hden] at hmu ⊢
  ring_nf at hmu ⊢
  linear_combination hmu

/-- Safe nonzero-Gamma corollary: no division is hidden in the primary
annihilation theorem. -/
theorem explicitCanonicalSourceMoment_eq_zero_on_evenKernel_of_zeroShiftGamma_ne_zero
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (xPlus : intrinsicParityPredecessorSubspace .even N)
    (hxPlus : intrinsicPredecessorBlock .even L N xPlus =
      intrinsicShellToPredecessor .even L N
        (intrinsicCubicShellPart .even N))
    (xMinus : intrinsicParityPredecessorSubspace .odd N)
    (hxMinus : intrinsicPredecessorBlock .odd L N xMinus =
      intrinsicShellToPredecessor .odd L N
        (intrinsicCubicShellPart .odd N))
    (hGamma : crossParityZeroShiftGamma N xMinus ≠ 0)
    (z : intrinsicParityPredecessorSubspace .even N)
    (hz : intrinsicPredecessorBlock .even L N z = 0) :
    explicitCanonicalSourceMoment L (N + 1)
      (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) = 0 := by
  have h :=
    crossParityZeroShiftGamma_mul_explicitSource_eq_zero_on_evenKernel
      hL N hN xPlus hxPlus xMinus hxMinus z hz
  exact (mul_eq_zero.mp h).resolve_left hGamma

end Zeta23.CCM

#print axioms Zeta23.CCM.oddCubicCouplingKernelPart_eq_evenZeroShiftResponse_add_source
#print axioms Zeta23.CCM.cubicZeroShiftShellResponseScalar_crossParity_explicitSource_transfer
#print axioms Zeta23.CCM.crossParityZeroShiftGamma_mul_explicitSource_eq_zero_on_evenKernel