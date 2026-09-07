import Zeta23.CCM.SourceExplicitCubicDefect
import Zeta23.CCM.CubicSecularMetric

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A3c: cross-parity secular transfer

This module combines the exact algebraic D-intertwining defect with the
one-dimensional intrinsic N-flow shell and the safe negative-shift predecessor
resolvent.

At one common `L`, predecessor size `N`, and safe shift `lam < 0`, the even
canonical cubic trial vector is transported by the centered-index map D.  D is
used only algebraically.  Its transported shell coordinate is exactly the odd
canonical cubic shell coordinate, while the two unavoidable predecessor
corrections are retained explicitly.

The resulting exact scalar identity has the form

  F_- = alpha * F_+ + Gamma * phi(u_+),

where `F_±` are the already canonical secular scalars and `phi` is the exact
cubic parity-defect coefficient.  The source-explicit theorem from the sibling
module then replaces `phi(u_+)` by the actual canonical-source quadratic normal
moment.

Firewalls:
* D is not asserted unitary/isometric;
* the predecessor corrections are not dropped;
* no sign or nonzeroness is asserted for `alpha`, `Gamma`, or the source
  moment;
* no parity root exclusion, branch exclusion, positivity closure,
  finite-to-infinite closure, or RH theorem is claimed.
-/

/-- The cubic quotient coordinate is literally the normalized inner product
with the canonical cubic shell vector.  Orthogonality to the predecessor makes
this true on the full successor carrier, not only on pure shell vectors. -/
theorem intrinsicCubicQuotientCoordinate_eq_inner_div
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N)
    (v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
    intrinsicCubicQuotientCoordinate p N v =
      inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) v /
        inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let c := intrinsicCubicShellPart p N
  let w := intrinsicPredecessorPart p N v
  let s := intrinsicShellPart p N v
  have hrec := intrinsicPredecessorPart_add_shellPart p N v
  have hort :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 :=
    inner_intrinsicShell_predecessor_eq_zero p N c w
  change
    inner ℂ
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
        (s : euclideanParityBoundaryFlatSubspace p (N + 1)) /
      inner ℂ
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
        (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
    inner ℂ
        (c : euclideanParityBoundaryFlatSubspace p (N + 1)) v /
      inner ℂ
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hv :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) v =
        inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    rw [← hrec, inner_add_right, hort, zero_add]
  rw [hv]

/-- Quotient coordinate of an inherited predecessor vector vanishes. -/
theorem intrinsicCubicQuotientCoordinate_predecessor_eq_zero
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N)
    (w : intrinsicParityPredecessorSubspace p N) :
    intrinsicCubicQuotientCoordinate p N
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
  exact
    (intrinsicCubicQuotientCoordinate_eq_zero_iff p N hN).2 w.property

/-- The canonical cubic shell vector itself has quotient coordinate one. -/
theorem intrinsicCubicQuotientCoordinate_cubicShellPart
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    intrinsicCubicQuotientCoordinate p N
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1)) = 1 := by
  rw [intrinsicCubicQuotientCoordinate_eq_inner_div p N hN]
  exact div_self (inner_intrinsicCubicShellPart_self_ne_zero p N hN)

/-- Every canonical secular residual is exactly its scalar times the canonical
cubic shell direction. -/
theorem cubicSecularResidual_eq_scalar_smul_intrinsicCubicShellPart
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicSecularResidual p hL N hprev lam hlam =
      cubicSecularScalar p hL N hprev lam hlam •
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let r := cubicSecularResidual p hL N hprev lam hlam
  let s := intrinsicShellPart p N r
  have hrPred : intrinsicPredecessorPart p N r = 0 := by
    simpa [r] using
      intrinsicPredecessorPart_cubicSecularResidual_eq_zero
        p hL N hprev lam hlam
  have hrRec := intrinsicPredecessorPart_add_shellPart p N r
  have hsCarrier :
      (s : euclideanParityBoundaryFlatSubspace p (N + 1)) = r := by
    rw [hrPred] at hrRec
    simpa [s] using hrRec
  have hrep := intrinsicCubicShellCoordinate_smul_cubic_eq p N hN s
  have hrepCarrier := congrArg
    (fun t : intrinsicParitySuccShell p N =>
      (t : euclideanParityBoundaryFlatSubspace p (N + 1))) hrep
  have hscalar :
      intrinsicCubicShellCoordinate p N s =
        cubicSecularScalar p hL N hprev lam hlam := by
    rfl
  rw [← hscalar]
  exact hrepCarrier.trans hsCarrier

/-- Algebraic D transport preserves the canonical one-step quotient
coordinate.  This uses only: D sends the even predecessor into the odd
predecessor, D sends the distinguished pulled-back cubic generator to the odd
cubic generator, and both quotient coordinates normalize that generator to
one. -/
theorem intrinsicCubicQuotientCoordinate_evenIndex
    (N : ℕ) (hN : 1 ≤ N)
    (v : euclideanEvenBoundaryFlatSubspace (N + 1)) :
    intrinsicCubicQuotientCoordinate .odd N
        (euclideanEvenToOddIndexLinearMap (N + 1) v) =
      intrinsicCubicQuotientCoordinate .even N v := by
  let k := intrinsicCubicQuotientCoordinate .even N v
  let g := successorPulledBackCubicCompressionVector N
  let r : euclideanEvenBoundaryFlatSubspace (N + 1) := v - k • g
  have hgcoord :
      intrinsicCubicQuotientCoordinate .even N g = 1 := by
    simpa [g, successorParityCubicVector] using
      intrinsicCubicQuotientCoordinate_successorParityCubicVector .even N hN
  have hrcoord :
      intrinsicCubicQuotientCoordinate .even N r = 0 := by
    dsimp [r, k]
    rw [map_sub, map_smul, hgcoord]
    simp
  have hrPred :
      (r : euclideanParityBoundaryFlatSubspace .even (N + 1)) ∈
        intrinsicParityPredecessorSubspace .even N :=
    (intrinsicCubicQuotientCoordinate_eq_zero_iff .even N hN).1 hrcoord
  have hrAmbient :
      (r : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanParityEmbeddedSuccSubspace .even N := by
    exact hrPred
  have hDpred :=
    evenIndex_mem_oddIntrinsicPredecessor_of_mem_evenIntrinsicPredecessor
      N r hrAmbient
  have hDrPred :
      (euclideanEvenToOddIndexLinearMap (N + 1) r :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) ∈
          intrinsicParityPredecessorSubspace .odd N := by
    exact hDpred
  have hDrCoord :
      intrinsicCubicQuotientCoordinate .odd N
          (euclideanEvenToOddIndexLinearMap (N + 1) r) = 0 :=
    (intrinsicCubicQuotientCoordinate_eq_zero_iff .odd N hN).2 hDrPred
  have hDg := evenIndex_successorPulledBackCubicCompressionVector N
  have hoddgcoord :
      intrinsicCubicQuotientCoordinate .odd N
          (oddCubicCompressionVector (N + 1)) = 1 := by
    simpa [successorParityCubicVector] using
      intrinsicCubicQuotientCoordinate_successorParityCubicVector .odd N hN
  dsimp [r, k] at hDrCoord
  rw [map_sub, map_smul, hDg, map_sub, map_smul, hoddgcoord] at hDrCoord
  simpa using (sub_eq_zero.mp hDrCoord)

/-- D sends the even canonical cubic shell vector to an odd vector whose shell
coordinate is exactly the odd canonical cubic shell vector.  The transported
vector may still have a predecessor component. -/
theorem intrinsicShellPart_evenIndex_cubicShellPart
    (N : ℕ) (hN : 1 ≤ N) :
    intrinsicShellPart .odd N
        (euclideanEvenToOddIndexLinearMap (N + 1)
          (intrinsicCubicShellPart .even N :
            euclideanParityBoundaryFlatSubspace .even (N + 1))) =
      intrinsicCubicShellPart .odd N := by
  let y : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    euclideanEvenToOddIndexLinearMap (N + 1)
      (intrinsicCubicShellPart .even N :
        euclideanParityBoundaryFlatSubspace .even (N + 1))
  have hqEven := intrinsicCubicQuotientCoordinate_cubicShellPart .even N hN
  have hq : intrinsicCubicQuotientCoordinate .odd N y = 1 := by
    simpa [y, hqEven] using
      intrinsicCubicQuotientCoordinate_evenIndex N hN
        (intrinsicCubicShellPart .even N :
          euclideanParityBoundaryFlatSubspace .even (N + 1))
  have hrep := intrinsicCubicShellCoordinate_smul_cubic_eq
    .odd N hN (intrinsicShellPart .odd N y)
  change
    intrinsicCubicShellCoordinate .odd N (intrinsicShellPart .odd N y) = 1 at hq
  rw [hq] at hrep
  simpa [y] using hrep.symm

/-- Predecessor correction carried by D of the even cubic shell vector. -/
def oddIndexCubicShellPredecessorPart
    (N : ℕ) : intrinsicParityPredecessorSubspace .odd N :=
  intrinsicPredecessorPart .odd N
    (euclideanEvenToOddIndexLinearMap (N + 1)
      (intrinsicCubicShellPart .even N :
        euclideanParityBoundaryFlatSubspace .even (N + 1)))

/-- Predecessor correction carried by the full odd cubic generator. -/
def oddCubicGeneratorPredecessorPart
    (N : ℕ) : intrinsicParityPredecessorSubspace .odd N :=
  intrinsicPredecessorPart .odd N
    (oddCubicCompressionVector (N + 1) :
      euclideanParityBoundaryFlatSubspace .odd (N + 1))

/-- Exact D-cubic-shell decomposition; the predecessor correction is retained. -/
theorem evenIndex_cubicShellPart_eq_predecessor_add_oddCubicShellPart
    (N : ℕ) (hN : 1 ≤ N) :
    euclideanEvenToOddIndexLinearMap (N + 1)
        (intrinsicCubicShellPart .even N :
          euclideanParityBoundaryFlatSubspace .even (N + 1)) =
      (oddIndexCubicShellPredecessorPart N :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (intrinsicCubicShellPart .odd N :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let y : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    euclideanEvenToOddIndexLinearMap (N + 1)
      (intrinsicCubicShellPart .even N :
        euclideanParityBoundaryFlatSubspace .even (N + 1))
  have hrec := intrinsicPredecessorPart_add_shellPart .odd N y
  have hs := intrinsicShellPart_evenIndex_cubicShellPart N hN
  simpa [y, oddIndexCubicShellPredecessorPart, hs] using hrec.symm

/-- Exact full odd cubic-generator decomposition into predecessor plus shell. -/
theorem oddCubicCompressionVector_eq_predecessor_add_cubicShellPart
    (N : ℕ) :
    (oddCubicCompressionVector (N + 1) :
      euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      (oddCubicGeneratorPredecessorPart N :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (intrinsicCubicShellPart .odd N :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let g : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    oddCubicCompressionVector (N + 1)
  have hrec := intrinsicPredecessorPart_add_shellPart .odd N g
  simpa [g, oddCubicGeneratorPredecessorPart,
    intrinsicCubicShellPart, successorParityCubicVector] using hrec.symm

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
  let phi := cubicDefectFunctional L (N + 1) uPlus
  Fplus • oddIndexCubicShellPredecessorPart N +
    phi • oddCubicGeneratorPredecessorPart N

/-- Full transported residual decomposition.  This is the vector-level heart
of the transfer theorem and explicitly retains both predecessor corrections. -/
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
    let Du := euclideanEvenToOddIndexLinearMap (N + 1) uPlus
    let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
    let phi := cubicDefectFunctional L (N + 1) uPlus
    oddCompressedCanonical L (N + 1) Du - (lam : ℂ) • Du =
      (crossParityPredecessorForcing hL N hprevEven lam hlam :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (Fplus + phi) •
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  dsimp
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let D := euclideanEvenToOddIndexLinearMap (N + 1)
  let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
  let phi := cubicDefectFunctional L (N + 1) uPlus
  let cPlus := intrinsicCubicShellPart .even N
  let cMinus := intrinsicCubicShellPart .odd N
  let dW := oddIndexCubicShellPredecessorPart N
  let a := oddCubicGeneratorPredecessorPart N
  have hresPlus :=
    cubicSecularResidual_eq_scalar_smul_intrinsicCubicShellPart
      .even hL N hN hprevEven lam hlam
  have hDres :
      D (cubicSecularResidual .even hL N hprevEven lam hlam) =
        Fplus • D
          (cPlus : euclideanParityBoundaryFlatSubspace .even (N + 1)) := by
    have h := congrArg D hresPlus
    simpa [D, Fplus, cPlus, map_smul] using h
  have hdef :=
    evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul
      hL (N + 1) (by omega) uPlus
  have hDc :=
    evenIndex_cubicShellPart_eq_predecessor_add_oddCubicShellPart N hN
  have hg := oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N
  have hbase :
      oddCompressedCanonical L (N + 1) (D uPlus) -
          (lam : ℂ) • D uPlus =
        D (cubicSecularResidual .even hL N hprevEven lam hlam) +
          evenOddCompressedIntertwiningDefect L (N + 1) uPlus := by
    change
      oddCompressedCanonical L (N + 1) (D uPlus) -
          (lam : ℂ) • D uPlus =
        D
            (evenCompressedCanonical L (N + 1) uPlus -
              (lam : ℂ) • uPlus) +
          (oddCompressedCanonical L (N + 1) (D uPlus) -
            D (evenCompressedCanonical L (N + 1) uPlus))
    rw [map_sub, map_smul]
    abel
  rw [hbase, hDres, hdef]
  rw [hDc, hg]
  simp only [smul_add]
  change
    Fplus •
        ((dW : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      Fplus •
        (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      phi •
        ((a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      phi •
        (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
    ((Fplus • dW + phi • a : intrinsicParityPredecessorSubspace .odd N) :
      euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (Fplus + phi) •
        (cMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
  simp only [map_add, map_smul, add_smul]
  abel

/-- The transported even trial vector itself has the canonical odd shell
component. -/
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
        (euclideanEvenToOddIndexLinearMap (N + 1)
          (cubicSecularTrialVector .even hL N hprevEven lam hlam)) =
      intrinsicCubicShellPart .odd N := by
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let Du := euclideanEvenToOddIndexLinearMap (N + 1) uPlus
  have hqPlus :=
    intrinsicCubicQuotientCoordinate_cubicSecularTrialVector
      .even hL N hN hprevEven lam hlam
  have hqDu : intrinsicCubicQuotientCoordinate .odd N Du = 1 := by
    simpa [Du, uPlus, hqPlus] using
      intrinsicCubicQuotientCoordinate_evenIndex N hN uPlus
  have hrep := intrinsicCubicShellCoordinate_smul_cubic_eq
    .odd N hN (intrinsicShellPart .odd N Du)
  change
    intrinsicCubicShellCoordinate .odd N (intrinsicShellPart .odd N Du) = 1
      at hqDu
  rw [hqDu] at hrep
  simpa [Du] using hrep.symm

/-- Exact reconstruction of the odd canonical trial vector from D of the even
canonical trial vector and the safe odd predecessor resolvent applied to the
explicit forcing. -/
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
      euclideanEvenToOddIndexLinearMap (N + 1)
          (cubicSecularTrialVector .even hL N hprevEven lam hlam) -
        ((shiftedIntrinsicPredecessorResolvent
            .odd hL N hprevOdd lam hlam
            (crossParityPredecessorForcing hL N hprevEven lam hlam) :
          intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let uD : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    euclideanEvenToOddIndexLinearMap (N + 1) uPlus
  let f := crossParityPredecessorForcing hL N hprevEven lam hlam
  let c := intrinsicCubicShellPart .odd N
  let b := intrinsicShellToPredecessor .odd L N c
  let R := shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam
  let wD := intrinsicPredecessorPart .odd N uD
  have hsD : intrinsicShellPart .odd N uD = c := by
    simpa [uD, uPlus, c] using
      intrinsicShellPart_evenIndex_cubicSecularTrialVector
        hL N hN hprevEven lam hlam
  have hrecD := intrinsicPredecessorPart_add_shellPart .odd N uD
  have hTuPred :
      intrinsicPredecessorPart .odd N
          (oddCompressedCanonical L (N + 1) uD) =
        intrinsicPredecessorBlock .odd L N wD + b := by
    calc
      intrinsicPredecessorPart .odd N
          (oddCompressedCanonical L (N + 1) uD) =
        intrinsicPredecessorPart .odd N
          (oddCompressedCanonical L (N + 1)
            (((wD : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
              (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)))) := by
                rw [← hsD]
                rw [hrecD]
      _ = intrinsicPredecessorBlock .odd L N wD + b := by
        simp [intrinsicPredecessorBlock, intrinsicShellToPredecessor,
          map_add, b]
  have hfull :=
    evenTrial_oddResidual_eq_forcing_add_shell
      hL N hN hprevEven lam hlam
  have hpred := congrArg (intrinsicPredecessorPart .odd N) hfull
  have hpredResidual :
      intrinsicPredecessorPart .odd N
          (oddCompressedCanonical L (N + 1) uD - (lam : ℂ) • uD) = f := by
    simpa [uD, uPlus, f, c,
      intrinsicPredecessorPart, hN] using hpred
  rw [map_sub, hTuPred, map_smul] at hpredResidual
  change
    intrinsicPredecessorBlock .odd L N wD + b - (lam : ℂ) • wD = f
      at hpredResidual
  have hshiftWD :
      shiftedIntrinsicPredecessorBlock .odd L N lam wD = f - b := by
    change intrinsicPredecessorBlock .odd L N wD - (lam : ℂ) • wD = f - b
    abel_nf at hpredResidual ⊢
    exact hpredResidual
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
  have hinj :=
    shiftedIntrinsicPredecessorBlock_injective .odd hL N hprevOdd hlam
  have hwD : wD = R f - R b := hinj hshiftWD hshiftTarget
  have hrecD' :
      ((wD : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = uD := by
    simpa [hsD] using hrecD
  have huD :
      uD =
        ((R f - R b : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    rw [← hrecD', hwD]
  change
    ((- R b : intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
    uD -
      ((R f : intrinsicParityPredecessorSubspace .odd N) :
        euclideanParityBoundaryFlatSubspace .odd (N + 1))
  rw [huD]
  simp only [map_sub]
  abel

/-- Linear odd correction functional generated by the safe predecessor
resolvent.  Its argument is a predecessor forcing, not a successor vector. -/
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
    ((oddCompressedCanonical L (N + 1)).comp
      ((intrinsicParityPredecessorSubspace .odd N).subtype.comp
        (shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam)))

/-- Coefficient multiplying the even secular scalar after the predecessor
correction is removed. -/
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

/-- Coefficient multiplying the cubic/source defect after the predecessor
correction is removed. -/
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

/-- Quotient coordinate of the transported even residual before canonical odd
predecessor correction. -/
theorem evenTrial_oddResidual_quotient_eq
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
    let Du := euclideanEvenToOddIndexLinearMap (N + 1) uPlus
    intrinsicCubicQuotientCoordinate .odd N
        (oddCompressedCanonical L (N + 1) Du - (lam : ℂ) • Du) =
      cubicSecularScalar .even hL N hprevEven lam hlam +
        cubicDefectFunctional L (N + 1) uPlus := by
  dsimp
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
  let phi := cubicDefectFunctional L (N + 1) uPlus
  let f := crossParityPredecessorForcing hL N hprevEven lam hlam
  let c := intrinsicCubicShellPart .odd N
  have hfull :=
    evenTrial_oddResidual_eq_forcing_add_shell
      hL N hN hprevEven lam hlam
  have hq := congrArg (intrinsicCubicQuotientCoordinate .odd N) hfull
  have hf0 := intrinsicCubicQuotientCoordinate_predecessor_eq_zero
    .odd N hN f
  have hc1 := intrinsicCubicQuotientCoordinate_cubicShellPart .odd N hN
  simpa [uPlus, Fplus, phi, f, c, map_add, map_smul, hf0, hc1]
    using hq

/-- Main exact cross-parity secular transfer. -/
theorem cubicSecularScalar_odd_eq_alpha_mul_even_add_gamma_mul_defect
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
    cubicSecularScalar .odd hL N hprevOdd lam hlam =
      crossParitySecularAlpha hL N hprevOdd lam hlam *
          cubicSecularScalar .even hL N hprevEven lam hlam +
        crossParitySecularGamma hL N hprevOdd lam hlam *
          cubicDefectFunctional L (N + 1)
            (cubicSecularTrialVector .even hL N hprevEven lam hlam) := by
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let uMinus := cubicSecularTrialVector .odd hL N hprevOdd lam hlam
  let Du : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    euclideanEvenToOddIndexLinearMap (N + 1) uPlus
  let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
  let Fminus := cubicSecularScalar .odd hL N hprevOdd lam hlam
  let phi := cubicDefectFunctional L (N + 1) uPlus
  let f := crossParityPredecessorForcing hL N hprevEven lam hlam
  let R := shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam
  let chi := oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
  let dW := oddIndexCubicShellPredecessorPart N
  let a := oddCubicGeneratorPredecessorPart N
  have htrial :=
    cubicSecularTrialVector_odd_eq_evenIndex_sub_resolvent_forcing
      hL N hN hprevEven hprevOdd lam hlam
  have hqDuResidual :=
    evenTrial_oddResidual_quotient_eq hL N hN hprevEven lam hlam
  have hRf0 := intrinsicCubicQuotientCoordinate_predecessor_eq_zero
    .odd N hN (R f)
  have hresMinus :
      cubicSecularResidual .odd hL N hprevOdd lam hlam =
        (oddCompressedCanonical L (N + 1) Du - (lam : ℂ) • Du) -
          (oddCompressedCanonical L (N + 1)
              ((R f : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1)) -
            (lam : ℂ) •
              ((R f : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) := by
    change
      oddCompressedCanonical L (N + 1) uMinus - (lam : ℂ) • uMinus = _
    have htrial' :
        uMinus =
          Du -
            ((R f : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
      simpa [uMinus, Du, uPlus, R, f] using htrial
    rw [htrial', map_sub, smul_sub]
    abel
  have hqMinus := congrArg (intrinsicCubicQuotientCoordinate .odd N) hresMinus
  have hchi :
      intrinsicCubicQuotientCoordinate .odd N
          (oddCompressedCanonical L (N + 1)
            ((R f : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) = chi f := by
    rfl
  have hFminus : Fminus = Fplus + phi - chi f := by
    change
      intrinsicCubicQuotientCoordinate .odd N
          (cubicSecularResidual .odd hL N hprevOdd lam hlam) = _
    rw [hresMinus, map_sub, map_sub, map_smul, hRf0, smul_zero, sub_zero,
      hchi]
    simpa [Du, uPlus, Fplus, phi] using hqDuResidual
  have hf : f = Fplus • dW + phi • a := by rfl
  have hchif : chi f = Fplus * chi dW + phi * chi a := by
    rw [hf, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
  change Fminus =
    (1 - chi dW) * Fplus + (1 - chi a) * phi
  rw [hFminus, hchif]
  ring

/-- The Gamma coefficient has a metric overlap interpretation involving only
the canonical odd trial vector and full odd cubic generator. -/
theorem crossParitySecularGamma_eq_trial_cubic_overlap_div
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    crossParitySecularGamma hL N hprevOdd lam hlam =
      inner ℂ
          (cubicSecularTrialVector .odd hL N hprevOdd lam hlam)
          (oddCubicCompressionVector (N + 1) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) /
        inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let c := intrinsicCubicShellPart .odd N
  let a := oddCubicGeneratorPredecessorPart N
  let b := intrinsicShellToPredecessor .odd L N c
  let R := shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam
  let chi := oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
  let u := cubicSecularTrialVector .odd hL N hprevOdd lam hlam
  let g : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    oddCubicCompressionVector (N + 1)
  let cc := inner ℂ
    (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))
    (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))
  have hcc : cc ≠ 0 := by
    simpa [cc, c] using inner_intrinsicCubicShellPart_self_ne_zero .odd N hN
  have hchiInner :
      chi a =
        inner ℂ
            (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (oddCompressedCanonical L (N + 1)
              ((R a : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) / cc := by
    change
      intrinsicCubicQuotientCoordinate .odd N
          (oddCompressedCanonical L (N + 1)
            ((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) = _
    simpa [cc, c] using
      intrinsicCubicQuotientCoordinate_eq_inner_div
        .odd N hN
        (oddCompressedCanonical L (N + 1)
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)))
  have hsymT :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (oddCompressedCanonical L (N + 1)
            ((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        inner ℂ
          (oddCompressedCanonical L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    exact
      (parityCompressedCanonical_isSymmetric .odd L (N + 1)
        (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))
        ((R a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))).symm
  have hTcRa :
      inner ℂ
          (oddCompressedCanonical L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    let y := oddCompressedCanonical L (N + 1)
      (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))
    have hrec := intrinsicPredecessorPart_add_shellPart .odd N y
    have hort := inner_intrinsicShell_predecessor_eq_zero
      .odd N (intrinsicShellPart .odd N y) (R a)
    change inner ℂ y ((R a : intrinsicParityPredecessorSubspace .odd N) :
      euclideanParityBoundaryFlatSubspace .odd (N + 1)) = _
    rw [← hrec, inner_add_left, hort, add_zero]
    rfl
  have hRba :
      inner ℂ
          ((R b : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    simpa [R] using
      shiftedIntrinsicPredecessorResolvent_isSymmetric
        .odd hL N hprevOdd hlam b a
  have hchi :
      chi a =
        inner ℂ
            ((R b : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) / cc := by
    rw [hchiInner, hsymT, hTcRa, ← hRba]
  have hg := oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N
  have hRaC := inner_intrinsicPredecessor_shell_eq_zero .odd N (R b) c
  have hCa := inner_intrinsicShell_predecessor_eq_zero .odd N c a
  have huInner :
      inner ℂ u g =
        cc -
          inner ℂ
            ((R b : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    change
      inner ℂ
        (((- R b : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) g = _
    rw [hg]
    simp only [inner_add_left, inner_add_right, inner_neg_left]
    rw [hRaC, hCa]
    simp [cc]
    ring
  change 1 - chi a = inner ℂ u g / cc
  rw [hchi, huInner]
  field_simp [hcc]
  ring

/-- Source-explicit version of the exact cross-parity transfer. -/
theorem cubicSecularScalar_crossParity_source_transfer
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
    cubicSecularScalar .odd hL N hprevOdd lam hlam =
      crossParitySecularAlpha hL N hprevOdd lam hlam *
          cubicSecularScalar .even hL N hprevEven lam hlam +
        crossParitySecularGamma hL N hprevOdd lam hlam *
          evenQuadraticSourceMoment L (N + 1)
            (cubicSecularTrialVector .even hL N hprevEven lam hlam) := by
  rw [cubicSecularScalar_odd_eq_alpha_mul_even_add_gamma_mul_defect
    hL N hN hprevEven hprevOdd lam hlam]
  rw [cubicDefectFunctional_eq_evenQuadraticSourceMoment
    hL (N + 1) (by omega)
    (cubicSecularTrialVector .even hL N hprevEven lam hlam)]

/-- Headline root specialization: if the even canonical secular scalar vanishes
at the common safe shift, the odd scalar is exactly an overlap factor times the
actual canonical-source quadratic normal moment.  No nonzeroness or sign of
either factor is asserted. -/
theorem cubicSecularScalar_odd_eq_overlap_mul_source_of_even_root
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
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicSecularScalar .even hL N hprevEven lam hlam = 0) :
    cubicSecularScalar .odd hL N hprevOdd lam hlam =
      (inner ℂ
          (cubicSecularTrialVector .odd hL N hprevOdd lam hlam)
          (oddCubicCompressionVector (N + 1) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) /
        inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))) *
        evenQuadraticSourceMoment L (N + 1)
          (cubicSecularTrialVector .even hL N hprevEven lam hlam) := by
  rw [cubicSecularScalar_crossParity_source_transfer
    hL N hN hprevEven hprevOdd lam hlam, hroot]
  simp only [mul_zero, zero_add]
  rw [crossParitySecularGamma_eq_trial_cubic_overlap_div
    hL N hN hprevOdd lam hlam]

end Zeta23.CCM

#print axioms Zeta23.CCM.intrinsicCubicQuotientCoordinate_evenIndex
#print axioms Zeta23.CCM.cubicSecularResidual_eq_scalar_smul_intrinsicCubicShellPart
#print axioms Zeta23.CCM.cubicSecularTrialVector_odd_eq_evenIndex_sub_resolvent_forcing
#print axioms Zeta23.CCM.cubicSecularScalar_odd_eq_alpha_mul_even_add_gamma_mul_defect
#print axioms Zeta23.CCM.crossParitySecularGamma_eq_trial_cubic_overlap_div
#print axioms Zeta23.CCM.cubicSecularScalar_crossParity_source_transfer
#print axioms Zeta23.CCM.cubicSecularScalar_odd_eq_overlap_mul_source_of_even_root
