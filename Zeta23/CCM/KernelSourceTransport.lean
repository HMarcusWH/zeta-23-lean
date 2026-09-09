import Zeta23.CCM.CrossParityQuotientTransport
import Zeta23.CCM.ZeroShiftBranchResponse
import Zeta23.CCM.SourceMomentDecomposition

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4b0: denominator-free kernel/source transport

This module turns the exact #129 parity defect and #131 canonical source
moment into zero-shift kernel geometry.  The identities are finite and
algebraic: no zero-shift inverse, pseudoinverse, Laurent expansion, resolvent
limit, kernel-dimension assumption, D-isometry, coefficient sign, or
coefficient nonzeroness is used.

For the projected predecessor blocks `A₊`, `A₋`, the centered-index transport
`D`, the canonical cubic shell vectors `c₊`, `c₋`, and the two odd predecessor
corrections `d`, `a`, an even predecessor-kernel vector `z` satisfies

  A₋ (D z) = beta(z) d + mu(z) a,

where `beta(z)` is the normalized even cubic-shell coupling and `mu(z)` is the
exact production source moment from PR #131.

The strongest specialization projects this identity to the entire odd
predecessor kernel for the actual even cubic coupling kernel component.  It is
a vector identity; no one-dimensional-kernel claim is made.
-/

/-- Compiler-facing bridge from the parity-native #129 defect functional to
PR #131's exact production source moment. -/
theorem evenParityCubicDefectFunctional_eq_explicitCanonicalSourceMoment
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanParityBoundaryFlatSubspace .even K) :
    evenParityCubicDefectFunctional L K v =
      explicitCanonicalSourceMoment L K v := by
  change cubicDefectFunctional L K v = explicitCanonicalSourceMoment L K v
  exact cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK v

/-- Centered-index transport restricted to the native one-step predecessor
carriers.  This is purely algebraic; no metric compatibility is asserted. -/
def evenIndexIntrinsicPredecessorLinearMap
    (N : ℕ) :
    intrinsicParityPredecessorSubspace .even N →ₗ[ℂ]
      intrinsicParityPredecessorSubspace .odd N where
  toFun := fun z => by
    let v : euclideanParityBoundaryFlatSubspace .even (N + 1) := z
    let y : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
      evenIndexParityLinearMap (N + 1) v
    have hvAmbient :
        (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
          euclideanParityEmbeddedSuccSubspace .even N := z.property
    have hyAmbient :
        (y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
          euclideanParityEmbeddedSuccSubspace .odd N := by
      exact
        evenIndex_mem_oddIntrinsicPredecessor_of_mem_evenIntrinsicPredecessor
          N v hvAmbient
    exact ⟨y, hyAmbient⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    change
      evenIndexParityLinearMap (N + 1)
          (((x + y : intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1))) =
        evenIndexParityLinearMap (N + 1)
            (x : euclideanParityBoundaryFlatSubspace .even (N + 1)) +
          evenIndexParityLinearMap (N + 1)
            (y : euclideanParityBoundaryFlatSubspace .even (N + 1))
    simpa only [Submodule.coe_add] using
      (evenIndexParityLinearMap (N + 1)).map_add
        (x : euclideanParityBoundaryFlatSubspace .even (N + 1))
        (y : euclideanParityBoundaryFlatSubspace .even (N + 1))
  map_smul' := by
    intro c x
    apply Subtype.ext
    change
      evenIndexParityLinearMap (N + 1)
          (((c • x : intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1))) =
        c • evenIndexParityLinearMap (N + 1)
          (x : euclideanParityBoundaryFlatSubspace .even (N + 1))
    simpa only [Submodule.coe_smul] using
      (evenIndexParityLinearMap (N + 1)).map_smul c
        (x : euclideanParityBoundaryFlatSubspace .even (N + 1))

/-- The native predecessor restriction is literally the already-validated
successor-carrier centered-index map after coercion. -/
theorem coe_evenIndexIntrinsicPredecessorLinearMap
    (N : ℕ)
    (z : intrinsicParityPredecessorSubspace .even N) :
    ((evenIndexIntrinsicPredecessorLinearMap N z :
        intrinsicParityPredecessorSubspace .odd N) :
      euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      evenIndexParityLinearMap (N + 1)
        (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) := rfl

/-- The predecessor coordinate fixes an inherited predecessor vector. -/
@[simp] theorem intrinsicPredecessorPart_coe_predecessor
    (p : ReversalParity) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorPart p N
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) = w := by
  apply Subtype.ext
  have hrec := intrinsicPredecessorPart_add_shellPart p N
    (w : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hs0 :
      intrinsicShellPart p N
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 :=
    (intrinsicShellPart_eq_zero_iff p N).2 w.property
  rw [hs0] at hrec
  simpa using hrec

/-- The predecessor coordinate kills a native shell vector. -/
@[simp] theorem intrinsicPredecessorPart_coe_shell
    (p : ReversalParity) (N : ℕ)
    (s : intrinsicParitySuccShell p N) :
    intrinsicPredecessorPart p N
        (s : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
  exact
    (Submodule.projectionOnto_apply_eq_zero_iff
      (intrinsicPredecessor_isCompl_shell p N)).2 s.property

/-- Normalized shell-coupling coefficient of a predecessor vector. -/
def cubicShellCouplingCoefficient
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) : ℂ :=
  inner ℂ
      ((intrinsicShellToPredecessor p L N
          (intrinsicCubicShellPart p N) :
        intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1))
      (w : euclideanParityBoundaryFlatSubspace p (N + 1)) /
    inner ℂ
      (intrinsicCubicShellPart p N :
        euclideanParityBoundaryFlatSubspace p (N + 1))
      (intrinsicCubicShellPart p N :
        euclideanParityBoundaryFlatSubspace p (N + 1))

/-- On a predecessor vector, the quotient coordinate of the full successor
image is exactly the normalized shell-coupling coefficient. -/
theorem intrinsicCubicQuotientCoordinate_parityCompressedCanonical_predecessor_eq
    (p : ReversalParity) (L : ℝ)
    (N : ℕ) (hN : 1 ≤ N)
    (w : intrinsicParityPredecessorSubspace p N) :
    intrinsicCubicQuotientCoordinate p N
        (parityCompressedCanonical p L (N + 1)
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))) =
      cubicShellCouplingCoefficient p L N w := by
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let y := parityCompressedCanonical p L (N + 1)
    (c : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hsym :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (parityCompressedCanonical p L (N + 1)
            (w : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        inner ℂ y
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    exact
      (parityCompressedCanonical_isSymmetric p L (N + 1)
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))).symm
  have hrec := intrinsicPredecessorPart_add_shellPart p N y
  have hort := inner_intrinsicShell_predecessor_eq_zero
    p N (intrinsicShellPart p N y) w
  have hyw :
      inner ℂ y
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        inner ℂ
          ((b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    calc
      inner ℂ y
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        inner ℂ
          (((intrinsicPredecessorPart p N y :
              intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) +
            ((intrinsicShellPart p N y : intrinsicParitySuccShell p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)))
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
            rw [hrec]
      _ = inner ℂ
          ((intrinsicPredecessorPart p N y :
              intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
            rw [inner_add_left, hort, add_zero]
      _ = inner ℂ
          ((b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
            rfl
  rw [intrinsicCubicQuotientCoordinate_eq_inner_div p N hN]
  change
    inner ℂ
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
        (parityCompressedCanonical p L (N + 1)
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))) /
      inner ℂ
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
        (c : euclideanParityBoundaryFlatSubspace p (N + 1)) = _
  rw [hsym, hyw]
  rfl

/-- An even predecessor-kernel vector is sent by the full even successor
operator into the one-dimensional shell, with the exact normalized coupling
coefficient. -/
theorem parityCompressedCanonical_evenKernel_eq_beta_smul_cubic
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (z : intrinsicParityPredecessorSubspace .even N)
    (hz : intrinsicPredecessorBlock .even L N z = 0) :
    parityCompressedCanonical .even L (N + 1)
        (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) =
      cubicShellCouplingCoefficient .even L N z •
        (intrinsicCubicShellPart .even N :
          euclideanParityBoundaryFlatSubspace .even (N + 1)) := by
  let y := parityCompressedCanonical .even L (N + 1)
    (z : euclideanParityBoundaryFlatSubspace .even (N + 1))
  have hyPred : intrinsicPredecessorPart .even N y = 0 := by
    change intrinsicPredecessorBlock .even L N z = 0
    exact hz
  have hrec := intrinsicPredecessorPart_add_shellPart .even N y
  have hyShell :
      ((intrinsicShellPart .even N y : intrinsicParitySuccShell .even N) :
        euclideanParityBoundaryFlatSubspace .even (N + 1)) = y := by
    rw [hyPred] at hrec
    simpa only [Submodule.coe_zero, zero_add] using hrec
  have hrep := intrinsicCubicShellCoordinate_smul_cubic_eq
    .even N hN (intrinsicShellPart .even N y)
  have hrepCarrier := congrArg
    (fun s : intrinsicParitySuccShell .even N =>
      (s : euclideanParityBoundaryFlatSubspace .even (N + 1))) hrep
  have hcoord :
      intrinsicCubicShellCoordinate .even N
          (intrinsicShellPart .even N y) =
        cubicShellCouplingCoefficient .even L N z := by
    change intrinsicCubicQuotientCoordinate .even N y = _
    exact
      intrinsicCubicQuotientCoordinate_parityCompressedCanonical_predecessor_eq
        .even L N hN z
  calc
    parityCompressedCanonical .even L (N + 1)
        (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) = y := rfl
    _ = ((intrinsicShellPart .even N y : intrinsicParitySuccShell .even N) :
          euclideanParityBoundaryFlatSubspace .even (N + 1)) := hyShell.symm
    _ = intrinsicCubicShellCoordinate .even N
          (intrinsicShellPart .even N y) •
        (intrinsicCubicShellPart .even N :
          euclideanParityBoundaryFlatSubspace .even (N + 1)) := by
      exact hrepCarrier.symm
    _ = cubicShellCouplingCoefficient .even L N z •
        (intrinsicCubicShellPart .even N :
          euclideanParityBoundaryFlatSubspace .even (N + 1)) := by
      rw [hcoord]

/-- Full successor-carrier transport identity for an even predecessor-kernel
vector, before taking predecessor or shell coordinates. -/
theorem parityCompressedCanonical_odd_evenIndex_kernel_eq
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (z : intrinsicParityPredecessorSubspace .even N)
    (hz : intrinsicPredecessorBlock .even L N z = 0) :
    let beta := cubicShellCouplingCoefficient .even L N z
    let mu := explicitCanonicalSourceMoment L (N + 1)
      (z : euclideanParityBoundaryFlatSubspace .even (N + 1))
    let d := oddIndexCubicShellPredecessorPart N
    let a := oddCubicGeneratorPredecessorPart N
    let cMinus := intrinsicCubicShellPart .odd N
    parityCompressedCanonical .odd L (N + 1)
        (evenIndexParityLinearMap (N + 1)
          (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) =
      ((beta • d + mu • a : intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (beta + mu) •
        (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  dsimp
  let beta := cubicShellCouplingCoefficient .even L N z
  let mu := explicitCanonicalSourceMoment L (N + 1)
    (z : euclideanParityBoundaryFlatSubspace .even (N + 1))
  let D := evenIndexParityLinearMap (N + 1)
  let cPlus : euclideanParityBoundaryFlatSubspace .even (N + 1) :=
    intrinsicCubicShellPart .even N
  let cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    intrinsicCubicShellPart .odd N
  let d := oddIndexCubicShellPredecessorPart N
  let a := oddCubicGeneratorPredecessorPart N
  have hkernel :=
    parityCompressedCanonical_evenKernel_eq_beta_smul_cubic
      L N hN z hz
  have hdefNative :=
    evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul
      hL (N + 1) (by omega)
      (z : euclideanParityBoundaryFlatSubspace .even (N + 1))
  have hsource :
      cubicDefectFunctional L (N + 1)
          (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) = mu := by
    simpa [mu] using
      cubicDefectFunctional_eq_explicitCanonicalSourceMoment
        hL (N + 1) (by omega)
          (z : euclideanParityBoundaryFlatSubspace .even (N + 1))
  have hdef :
      parityCompressedCanonical .odd L (N + 1)
          (D (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) =
        D (parityCompressedCanonical .even L (N + 1)
          (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) +
        mu • successorParityCubicVector .odd N := by
    change
      oddCompressedCanonical L (N + 1)
          (euclideanEvenToOddIndexLinearMap (N + 1)
            (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) =
        euclideanEvenToOddIndexLinearMap (N + 1)
            (evenCompressedCanonical L (N + 1)
              (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) +
          mu • oddCubicCompressionVector (N + 1)
    change
      oddCompressedCanonical L (N + 1)
          (euclideanEvenToOddIndexLinearMap (N + 1)
            (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) -
        euclideanEvenToOddIndexLinearMap (N + 1)
            (evenCompressedCanonical L (N + 1)
              (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) =
          cubicDefectFunctional L (N + 1)
              (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) •
            oddCubicCompressionVector (N + 1) at hdefNative
    rw [hsource] at hdefNative
    calc
      oddCompressedCanonical L (N + 1)
          (euclideanEvenToOddIndexLinearMap (N + 1)
            (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) =
        (oddCompressedCanonical L (N + 1)
            (euclideanEvenToOddIndexLinearMap (N + 1)
              (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) -
          euclideanEvenToOddIndexLinearMap (N + 1)
            (evenCompressedCanonical L (N + 1)
              (z : euclideanParityBoundaryFlatSubspace .even (N + 1)))) +
          euclideanEvenToOddIndexLinearMap (N + 1)
            (evenCompressedCanonical L (N + 1)
              (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) := by
        abel
      _ = mu • oddCubicCompressionVector (N + 1) +
          euclideanEvenToOddIndexLinearMap (N + 1)
            (evenCompressedCanonical L (N + 1)
              (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) := by
        rw [hdefNative]
      _ = euclideanEvenToOddIndexLinearMap (N + 1)
            (evenCompressedCanonical L (N + 1)
              (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) +
          mu • oddCubicCompressionVector (N + 1) := by
        abel
  have hDc :=
    evenIndex_cubicShellPart_eq_predecessor_add_oddCubicShellPart N hN
  have hg := oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N
  calc
    parityCompressedCanonical .odd L (N + 1)
        (D (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) =
      D (parityCompressedCanonical .even L (N + 1)
        (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) +
        mu • successorParityCubicVector .odd N := hdef
    _ = D (beta • cPlus) + mu • successorParityCubicVector .odd N := by
      rw [hkernel]
    _ = beta • D cPlus + mu • successorParityCubicVector .odd N := by
      rw [map_smul]
    _ = beta •
          (((d : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) + cMinus) +
        mu •
          (((a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) + cMinus) := by
      rw [hDc, hg]
    _ =
      ((beta • d + mu • a : intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (beta + mu) • cMinus := by
      simp only [Submodule.coe_add, Submodule.coe_smul, smul_add, add_smul]
      abel

/-- Main denominator-free predecessor transport: on every even predecessor
kernel vector the odd predecessor block of D z is an exact linear combination
of the two already-validated odd predecessor corrections, with the #131
production source moment as the second coefficient. -/
theorem oddPredecessorBlock_evenIndex_eq_beta_add_source_of_evenKernel
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (z : intrinsicParityPredecessorSubspace .even N)
    (hz : intrinsicPredecessorBlock .even L N z = 0) :
    intrinsicPredecessorBlock .odd L N
        (evenIndexIntrinsicPredecessorLinearMap N z) =
      cubicShellCouplingCoefficient .even L N z •
          oddIndexCubicShellPredecessorPart N +
        explicitCanonicalSourceMoment L (N + 1)
            (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) •
          oddCubicGeneratorPredecessorPart N := by
  have hfull := parityCompressedCanonical_odd_evenIndex_kernel_eq
    hL N hN z hz
  dsimp at hfull
  have hp := congrArg (intrinsicPredecessorPart .odd N) hfull
  change
    intrinsicPredecessorPart .odd N
        (parityCompressedCanonical .odd L (N + 1)
          (((evenIndexIntrinsicPredecessorLinearMap N z :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)))) = _
  rw [coe_evenIndexIntrinsicPredecessorLinearMap]
  calc
    intrinsicPredecessorPart .odd N
        (parityCompressedCanonical .odd L (N + 1)
          (evenIndexParityLinearMap (N + 1)
            (z : euclideanParityBoundaryFlatSubspace .even (N + 1)))) =
      intrinsicPredecessorPart .odd N
        (((cubicShellCouplingCoefficient .even L N z •
              oddIndexCubicShellPredecessorPart N +
            explicitCanonicalSourceMoment L (N + 1)
                (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) •
              oddCubicGeneratorPredecessorPart N :
            intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (cubicShellCouplingCoefficient .even L N z +
            explicitCanonicalSourceMoment L (N + 1)
              (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) •
            (intrinsicCubicShellPart .odd N :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) := hp
    _ = cubicShellCouplingCoefficient .even L N z •
          oddIndexCubicShellPredecessorPart N +
        explicitCanonicalSourceMoment L (N + 1)
            (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) •
          oddCubicGeneratorPredecessorPart N := by
      rw [(intrinsicPredecessorPart .odd N).map_add,
        intrinsicPredecessorPart_coe_predecessor,
        (intrinsicPredecessorPart .odd N).map_smul,
        intrinsicPredecessorPart_coe_shell, smul_zero, add_zero]

/-- Shell/quotient half of the same kernel transport. -/
theorem oddCubicCouplingQuotient_evenIndex_eq_beta_add_source_of_evenKernel
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (z : intrinsicParityPredecessorSubspace .even N)
    (hz : intrinsicPredecessorBlock .even L N z = 0) :
    intrinsicCubicQuotientCoordinate .odd N
        (parityCompressedCanonical .odd L (N + 1)
          (evenIndexParityLinearMap (N + 1)
            (z : euclideanParityBoundaryFlatSubspace .even (N + 1)))) =
      cubicShellCouplingCoefficient .even L N z +
        explicitCanonicalSourceMoment L (N + 1)
          (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) := by
  have hfull := parityCompressedCanonical_odd_evenIndex_kernel_eq
    hL N hN z hz
  dsimp at hfull
  have hq := congrArg (intrinsicCubicQuotientCoordinate .odd N) hfull
  calc
    intrinsicCubicQuotientCoordinate .odd N
        (parityCompressedCanonical .odd L (N + 1)
          (evenIndexParityLinearMap (N + 1)
            (z : euclideanParityBoundaryFlatSubspace .even (N + 1)))) =
      intrinsicCubicQuotientCoordinate .odd N
        (((cubicShellCouplingCoefficient .even L N z •
              oddIndexCubicShellPredecessorPart N +
            explicitCanonicalSourceMoment L (N + 1)
                (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) •
              oddCubicGeneratorPredecessorPart N :
            intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (cubicShellCouplingCoefficient .even L N z +
            explicitCanonicalSourceMoment L (N + 1)
              (z : euclideanParityBoundaryFlatSubspace .even (N + 1))) •
            (intrinsicCubicShellPart .odd N :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) := hq
    _ = cubicShellCouplingCoefficient .even L N z +
        explicitCanonicalSourceMoment L (N + 1)
          (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) := by
      rw [(intrinsicCubicQuotientCoordinate .odd N).map_add,
        intrinsicCubicQuotientCoordinate_predecessor_eq_zero .odd N hN,
        (intrinsicCubicQuotientCoordinate .odd N).map_smul,
        intrinsicCubicQuotientCoordinate_cubicShellPart .odd N hN]
      simp

/-- Projecting the kernel transport to the entire odd predecessor kernel gives
an exact vector compatibility identity. -/
theorem evenKernel_crossParity_projected_compatibility
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (z : intrinsicParityPredecessorSubspace .even N)
    (hz : intrinsicPredecessorBlock .even L N z = 0) :
    cubicShellCouplingCoefficient .even L N z •
        intrinsicPredecessorKernelPart .odd L N
          (oddIndexCubicShellPredecessorPart N) +
      explicitCanonicalSourceMoment L (N + 1)
          (z : euclideanParityBoundaryFlatSubspace .even (N + 1)) •
        intrinsicPredecessorKernelPart .odd L N
          (oddCubicGeneratorPredecessorPart N) = 0 := by
  have htransport :=
    oddPredecessorBlock_evenIndex_eq_beta_add_source_of_evenKernel
      hL N hN z hz
  have hp := congrArg (intrinsicPredecessorKernelPart .odd L N) htransport
  rw [intrinsicPredecessorKernelPart_intrinsicPredecessorBlock_eq_zero] at hp
  rw [map_add, map_smul, map_smul] at hp
  simpa using hp.symm

/-- On the actual even cubic coupling kernel component the normalized coupling
coefficient is its self-inner value divided by the canonical shell norm. -/
theorem cubicShellCouplingCoefficient_cubicCouplingKernelPart
    (L : ℝ) (N : ℕ) :
    cubicShellCouplingCoefficient .even L N
        (cubicCouplingKernelPart .even L N :
          intrinsicParityPredecessorSubspace .even N) =
      inner ℂ
          (((cubicCouplingKernelPart .even L N :
              LinearMap.ker (intrinsicPredecessorBlock .even L N)) :
            intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1))
          (((cubicCouplingKernelPart .even L N :
              LinearMap.ker (intrinsicPredecessorBlock .even L N)) :
            intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1)) /
        inner ℂ
          (intrinsicCubicShellPart .even N :
            euclideanParityBoundaryFlatSubspace .even (N + 1))
          (intrinsicCubicShellPart .even N :
            euclideanParityBoundaryFlatSubspace .even (N + 1)) := by
  let b := intrinsicShellToPredecessor .even L N
    (intrinsicCubicShellPart .even N)
  let k := cubicCouplingKernelPart .even L N
  have hkb := inner_intrinsicPredecessorKernelPart_coupling_eq_self
    .even L N b
  have hkb' :
      inner ℂ
          (((k : LinearMap.ker (intrinsicPredecessorBlock .even L N)) :
            intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1))
          (b : euclideanParityBoundaryFlatSubspace .even (N + 1)) =
        inner ℂ
          (((k : LinearMap.ker (intrinsicPredecessorBlock .even L N)) :
            intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1))
          (((k : LinearMap.ker (intrinsicPredecessorBlock .even L N)) :
            intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1)) := by
    simpa [k, b, cubicCouplingKernelPart] using hkb
  have hbk :
      inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .even (N + 1))
          (((k : LinearMap.ker (intrinsicPredecessorBlock .even L N)) :
            intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1)) =
        inner ℂ
          (((k : LinearMap.ker (intrinsicPredecessorBlock .even L N)) :
            intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1))
          (((k : LinearMap.ker (intrinsicPredecessorBlock .even L N)) :
            intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1)) := by
    rw [← inner_conj_symm]
    rw [hkb']
    rw [inner_self_conj]
  change
    inner ℂ
        (b : euclideanParityBoundaryFlatSubspace .even (N + 1))
        (((k : LinearMap.ker (intrinsicPredecessorBlock .even L N)) :
          intrinsicParityPredecessorSubspace .even N) :
          euclideanParityBoundaryFlatSubspace .even (N + 1)) / _ = _
  rw [hbk]

/-- Headline projected compatibility for the actual canonical cubic coupling
kernel component.  This is an identity in the whole odd predecessor kernel. -/
theorem cubicCouplingKernelPart_crossParity_projected_compatibility
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N) :
    (inner ℂ
        (((cubicCouplingKernelPart .even L N :
            LinearMap.ker (intrinsicPredecessorBlock .even L N)) :
          intrinsicParityPredecessorSubspace .even N) :
          euclideanParityBoundaryFlatSubspace .even (N + 1))
        (((cubicCouplingKernelPart .even L N :
            LinearMap.ker (intrinsicPredecessorBlock .even L N)) :
          intrinsicParityPredecessorSubspace .even N) :
          euclideanParityBoundaryFlatSubspace .even (N + 1)) /
      inner ℂ
        (intrinsicCubicShellPart .even N :
          euclideanParityBoundaryFlatSubspace .even (N + 1))
        (intrinsicCubicShellPart .even N :
          euclideanParityBoundaryFlatSubspace .even (N + 1))) •
        intrinsicPredecessorKernelPart .odd L N
          (oddIndexCubicShellPredecessorPart N) +
      explicitCanonicalSourceMoment L (N + 1)
          ((cubicCouplingKernelPart .even L N :
            intrinsicParityPredecessorSubspace .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1)) •
        intrinsicPredecessorKernelPart .odd L N
          (oddCubicGeneratorPredecessorPart N) = 0 := by
  let k := cubicCouplingKernelPart .even L N
  have hk : intrinsicPredecessorBlock .even L N
      (k : intrinsicParityPredecessorSubspace .even N) = 0 := k.property
  have h := evenKernel_crossParity_projected_compatibility
    hL N hN (k : intrinsicParityPredecessorSubspace .even N) hk
  rw [cubicShellCouplingCoefficient_cubicCouplingKernelPart L N] at h
  exact h

end Zeta23.CCM

#print axioms Zeta23.CCM.oddPredecessorBlock_evenIndex_eq_beta_add_source_of_evenKernel
#print axioms Zeta23.CCM.evenKernel_crossParity_projected_compatibility
#print axioms Zeta23.CCM.cubicCouplingKernelPart_crossParity_projected_compatibility