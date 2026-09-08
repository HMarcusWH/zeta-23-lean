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

The implementation deliberately uses parity-native views of the already
validated even/odd maps.  This keeps every intermediate subtraction, scalar
multiple, projection, and residual in one Lean carrier.  The views are
judgmentally the existing concrete maps; no new mathematical assumption is
introduced.

At one common `L`, predecessor size `N`, and safe shift `lam < 0`, the even
canonical cubic trial vector is transported by the centered-index map D.  D is
used only algebraically.  Its transported shell coordinate is exactly the odd
canonical cubic shell coordinate, while the two unavoidable predecessor
corrections are retained explicitly.

The resulting exact scalar identity has the form

  F_- = alpha * F_+ + Gamma * phi(u_+),

and the source-explicit sibling theorem then replaces `phi(u_+)` by the actual
canonical-source quadratic normal moment.

Firewalls:
* D is not asserted unitary/isometric;
* the predecessor corrections are not dropped;
* no sign or nonzeroness is asserted for `alpha`, `Gamma`, or the source
  moment;
* no parity root exclusion, branch exclusion, positivity closure,
  finite-to-infinite closure, or RH theorem is claimed.
-/

/-- Parity-native view of the already validated Euclidean centered-index map. -/
def evenIndexParityLinearMap
    (K : ℕ) :
    euclideanParityBoundaryFlatSubspace .even K →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace .odd K :=
  euclideanEvenToOddIndexLinearMap K

/-- Parity-native view of the already validated rank-one intertwining defect. -/
def evenOddParityIntertwiningDefect
    (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace .even K →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace .odd K :=
  evenOddCompressedIntertwiningDefect L K

/-- Parity-native view of the already validated cubic defect functional. -/
def evenParityCubicDefectFunctional
    (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace .even K →ₗ[ℂ] ℂ :=
  cubicDefectFunctional L K

/-- The parity-native defect functional is exactly the source-explicit moment. -/
theorem evenParityCubicDefectFunctional_eq_evenQuadraticSourceMoment
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanParityBoundaryFlatSubspace .even K) :
    evenParityCubicDefectFunctional L K v =
      evenQuadraticSourceMoment L K v := by
  change cubicDefectFunctional L K v = evenQuadraticSourceMoment L K v
  exact cubicDefectFunctional_eq_evenQuadraticSourceMoment hL K hK v

/-- The cubic quotient coordinate is the normalized inner product with the
canonical cubic shell vector. -/
theorem intrinsicCubicQuotientCoordinate_eq_inner_div
    (p : ReversalParity) (N : ℕ) (_hN : 1 ≤ N)
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
  let c := intrinsicCubicShellPart p N
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
  have hrepCarrierRaw := congrArg
    (fun t : intrinsicParitySuccShell p N =>
      (t : euclideanParityBoundaryFlatSubspace p (N + 1))) hrep
  have hrepCarrier :
      intrinsicCubicShellCoordinate p N s •
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        (s : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    change
      ((intrinsicCubicShellCoordinate p N s • c : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) =
        (s : euclideanParityBoundaryFlatSubspace p (N + 1))
    exact hrepCarrierRaw
  have hscalar :
      intrinsicCubicShellCoordinate p N s =
        cubicSecularScalar p hL N hprev lam hlam := by
    rfl
  calc
    cubicSecularResidual p hL N hprev lam hlam = r := rfl
    _ = (s : euclideanParityBoundaryFlatSubspace p (N + 1)) := hsCarrier.symm
    _ = intrinsicCubicShellCoordinate p N s •
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) :=
      hrepCarrier.symm
    _ = cubicSecularScalar p hL N hprev lam hlam •
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
      rw [hscalar]

/-- Algebraic D transport preserves the canonical one-step quotient
coordinate.  Only the validated predecessor transport and cubic-generator
transport are used. -/
theorem intrinsicCubicQuotientCoordinate_evenIndex
    (N : ℕ) (hN : 1 ≤ N)
    (v : euclideanParityBoundaryFlatSubspace .even (N + 1)) :
    intrinsicCubicQuotientCoordinate .odd N
        (evenIndexParityLinearMap (N + 1) v) =
      intrinsicCubicQuotientCoordinate .even N v := by
  let D := evenIndexParityLinearMap (N + 1)
  let k := intrinsicCubicQuotientCoordinate .even N v
  let g : euclideanParityBoundaryFlatSubspace .even (N + 1) :=
    successorParityCubicVector .even N
  let r : euclideanParityBoundaryFlatSubspace .even (N + 1) := v - k • g
  have hgcoord : intrinsicCubicQuotientCoordinate .even N g = 1 := by
    simpa [g] using
      intrinsicCubicQuotientCoordinate_successorParityCubicVector .even N hN
  have hrcoord : intrinsicCubicQuotientCoordinate .even N r = 0 := by
    dsimp [r]
    rw [map_sub, map_smul, hgcoord]
    simp [k]
  have hrPred : r ∈ intrinsicParityPredecessorSubspace .even N :=
    (intrinsicCubicQuotientCoordinate_eq_zero_iff .even N hN).1 hrcoord
  have hrAmbient :
      (r : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanParityEmbeddedSuccSubspace .even N := by
    exact hrPred
  have hDpredNative :=
    evenIndex_mem_oddIntrinsicPredecessor_of_mem_evenIntrinsicPredecessor
      N r hrAmbient
  have hDrPred : D r ∈ intrinsicParityPredecessorSubspace .odd N := by
    exact hDpredNative
  have hDrCoord : intrinsicCubicQuotientCoordinate .odd N (D r) = 0 :=
    (intrinsicCubicQuotientCoordinate_eq_zero_iff .odd N hN).2 hDrPred
  have hDg : D g = successorParityCubicVector .odd N := by
    change
      euclideanEvenToOddIndexLinearMap (N + 1)
          (successorPulledBackCubicCompressionVector N) =
        oddCubicCompressionVector (N + 1)
    exact evenIndex_successorPulledBackCubicCompressionVector N
  have hoddgcoord :
      intrinsicCubicQuotientCoordinate .odd N
          (successorParityCubicVector .odd N) = 1 :=
    intrinsicCubicQuotientCoordinate_successorParityCubicVector .odd N hN
  have hDrDecomp : D r = D v - k • D g := by
    dsimp [r]
    rw [map_sub, map_smul]
  rw [hDrDecomp, map_sub, map_smul, hDg, hoddgcoord] at hDrCoord
  simp only [smul_eq_mul, mul_one] at hDrCoord
  exact sub_eq_zero.mp hDrCoord

/-- D sends the even canonical cubic shell vector to an odd vector whose shell
coordinate is exactly the odd canonical cubic shell vector. -/
theorem intrinsicShellPart_evenIndex_cubicShellPart
    (N : ℕ) (hN : 1 ≤ N) :
    intrinsicShellPart .odd N
        (evenIndexParityLinearMap (N + 1)
          (intrinsicCubicShellPart .even N :
            euclideanParityBoundaryFlatSubspace .even (N + 1))) =
      intrinsicCubicShellPart .odd N := by
  let cPlus : euclideanParityBoundaryFlatSubspace .even (N + 1) :=
    intrinsicCubicShellPart .even N
  let y : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    evenIndexParityLinearMap (N + 1) cPlus
  have hqEven : intrinsicCubicQuotientCoordinate .even N cPlus = 1 :=
    intrinsicCubicQuotientCoordinate_cubicShellPart .even N hN
  have hqTransport := intrinsicCubicQuotientCoordinate_evenIndex N hN cPlus
  have hq : intrinsicCubicQuotientCoordinate .odd N y = 1 := by
    exact hqTransport.trans hqEven
  have hrep := intrinsicCubicShellCoordinate_smul_cubic_eq
    .odd N hN (intrinsicShellPart .odd N y)
  change
    intrinsicCubicShellCoordinate .odd N (intrinsicShellPart .odd N y) = 1 at hq
  rw [hq] at hrep
  simpa only [one_smul] using hrep.symm

/-- Predecessor correction carried by D of the even cubic shell vector. -/
def oddIndexCubicShellPredecessorPart
    (N : ℕ) : intrinsicParityPredecessorSubspace .odd N :=
  intrinsicPredecessorPart .odd N
    (evenIndexParityLinearMap (N + 1)
      (intrinsicCubicShellPart .even N :
        euclideanParityBoundaryFlatSubspace .even (N + 1)))

/-- Predecessor correction carried by the full odd cubic generator. -/
def oddCubicGeneratorPredecessorPart
    (N : ℕ) : intrinsicParityPredecessorSubspace .odd N :=
  intrinsicPredecessorPart .odd N
    (successorParityCubicVector .odd N)

/-- Exact D-cubic-shell decomposition; the predecessor correction is retained. -/
theorem evenIndex_cubicShellPart_eq_predecessor_add_oddCubicShellPart
    (N : ℕ) (hN : 1 ≤ N) :
    evenIndexParityLinearMap (N + 1)
        (intrinsicCubicShellPart .even N :
          euclideanParityBoundaryFlatSubspace .even (N + 1)) =
      (oddIndexCubicShellPredecessorPart N :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (intrinsicCubicShellPart .odd N :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let y : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    evenIndexParityLinearMap (N + 1)
      (intrinsicCubicShellPart .even N :
        euclideanParityBoundaryFlatSubspace .even (N + 1))
  have hrec := intrinsicPredecessorPart_add_shellPart .odd N y
  have hs := intrinsicShellPart_evenIndex_cubicShellPart N hN
  calc
    y =
        (intrinsicPredecessorPart .odd N y :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (intrinsicShellPart .odd N y :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := hrec.symm
    _ =
        (oddIndexCubicShellPredecessorPart N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
      rw [hs]

/-- Exact full odd cubic-generator decomposition into predecessor plus shell. -/
theorem oddCubicCompressionVector_eq_predecessor_add_cubicShellPart
    (N : ℕ) :
    successorParityCubicVector .odd N =
      (oddCubicGeneratorPredecessorPart N :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (intrinsicCubicShellPart .odd N :
        euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let g : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    successorParityCubicVector .odd N
  have hrec := intrinsicPredecessorPart_add_shellPart .odd N g
  have hs : intrinsicShellPart .odd N g = intrinsicCubicShellPart .odd N := by
    change
      intrinsicShellPart .odd N (successorParityCubicVector .odd N) =
        intrinsicCubicShellPart .odd N
    rfl
  calc
    g =
        (intrinsicPredecessorPart .odd N g :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (intrinsicShellPart .odd N g :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := hrec.symm
    _ =
        (oddCubicGeneratorPredecessorPart N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
      rw [hs]

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
  have hresPlus :=
    cubicSecularResidual_eq_scalar_smul_intrinsicCubicShellPart
      .even hL N hN hprevEven lam hlam
  have hDres :
      D (cubicSecularResidual .even hL N hprevEven lam hlam) =
        Fplus • D cPlus := by
    calc
      D (cubicSecularResidual .even hL N hprevEven lam hlam) =
          D (Fplus • cPlus) := by
        exact congrArg D hresPlus
      _ = Fplus • D cPlus := by
        rw [map_smul]
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
    rw [map_sub, map_smul]
    abel
  have hDc :=
    evenIndex_cubicShellPart_eq_predecessor_add_oddCubicShellPart N hN
  have hg := oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N
  rw [hbase, hDres, hdef, hDc, hg]
  simp only [smul_add]
  change
    Fplus •
        (dW : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      Fplus • cMinus +
      phi • (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      phi • cMinus =
    ((Fplus • dW + phi • a : intrinsicParityPredecessorSubspace .odd N) :
      euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
      (Fplus + phi) • cMinus
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
    simp [intrinsicPredecessorPart]
  have hcZero :
      intrinsicPredecessorPart .odd N
          (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = 0 := by
    simp [intrinsicPredecessorPart]
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
  have hinj := shiftedIntrinsicPredecessorBlock_injective .odd hL N hprevOdd hlam
  have hwD : wD = R f - R b := hinj hshiftWD hshiftTarget
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
  simp only [map_sub]
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
    let Du := evenIndexParityLinearMap (N + 1) uPlus
    intrinsicCubicQuotientCoordinate .odd N
        (parityCompressedCanonical .odd L (N + 1) Du - (lam : ℂ) • Du) =
      cubicSecularScalar .even hL N hprevEven lam hlam +
        evenParityCubicDefectFunctional L (N + 1) uPlus := by
  dsimp
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let Du := evenIndexParityLinearMap (N + 1) uPlus
  let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
  let phi := evenParityCubicDefectFunctional L (N + 1) uPlus
  let f := crossParityPredecessorForcing hL N hprevEven lam hlam
  let c := intrinsicCubicShellPart .odd N
  have hfull :=
    evenTrial_oddResidual_eq_forcing_add_shell
      hL N hN hprevEven lam hlam
  have hq := congrArg (intrinsicCubicQuotientCoordinate .odd N) hfull
  have hf0 := intrinsicCubicQuotientCoordinate_predecessor_eq_zero .odd N hN f
  have hc1 := intrinsicCubicQuotientCoordinate_cubicShellPart .odd N hN
  calc
    intrinsicCubicQuotientCoordinate .odd N
        (parityCompressedCanonical .odd L (N + 1) Du - (lam : ℂ) • Du) =
      intrinsicCubicQuotientCoordinate .odd N
        ((f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          (Fplus + phi) •
            (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) := hq
    _ = intrinsicCubicQuotientCoordinate .odd N
          (f : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        intrinsicCubicQuotientCoordinate .odd N
          ((Fplus + phi) •
            (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))) := by
      rw [map_add]
    _ = 0 + (Fplus + phi) * 1 := by
      rw [hf0, map_smul, hc1]
      simp only [smul_eq_mul]
    _ = Fplus + phi := by ring

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
          evenParityCubicDefectFunctional L (N + 1)
            (cubicSecularTrialVector .even hL N hprevEven lam hlam) := by
  let uPlus := cubicSecularTrialVector .even hL N hprevEven lam hlam
  let uMinus := cubicSecularTrialVector .odd hL N hprevOdd lam hlam
  let D := evenIndexParityLinearMap (N + 1)
  let Du : euclideanParityBoundaryFlatSubspace .odd (N + 1) := D uPlus
  let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
  let Fminus := cubicSecularScalar .odd hL N hprevOdd lam hlam
  let phi := evenParityCubicDefectFunctional L (N + 1) uPlus
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
  have htrial' :
      uMinus =
        Du -
          ((R f : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    simpa [uMinus, Du, D, uPlus, R, f] using htrial
  have hresMinus :
      cubicSecularResidual .odd hL N hprevOdd lam hlam =
        (parityCompressedCanonical .odd L (N + 1) Du - (lam : ℂ) • Du) -
          (parityCompressedCanonical .odd L (N + 1)
              ((R f : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1)) -
            (lam : ℂ) •
              ((R f : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) := by
    change
      parityCompressedCanonical .odd L (N + 1) uMinus -
          (lam : ℂ) • uMinus = _
    rw [htrial', map_sub, smul_sub]
    abel
  have hchi :
      intrinsicCubicQuotientCoordinate .odd N
          (parityCompressedCanonical .odd L (N + 1)
            ((R f : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) = chi f := by
    rfl
  have hFminus : Fminus = Fplus + phi - chi f := by
    change
      intrinsicCubicQuotientCoordinate .odd N
          (cubicSecularResidual .odd hL N hprevOdd lam hlam) = _
    calc
      intrinsicCubicQuotientCoordinate .odd N
          (cubicSecularResidual .odd hL N hprevOdd lam hlam) =
        intrinsicCubicQuotientCoordinate .odd N
          ((parityCompressedCanonical .odd L (N + 1) Du -
              (lam : ℂ) • Du) -
            (parityCompressedCanonical .odd L (N + 1)
                ((R f : intrinsicParityPredecessorSubspace .odd N) :
                  euclideanParityBoundaryFlatSubspace .odd (N + 1)) -
              (lam : ℂ) •
                ((R f : intrinsicParityPredecessorSubspace .odd N) :
                  euclideanParityBoundaryFlatSubspace .odd (N + 1)))) :=
        congrArg (intrinsicCubicQuotientCoordinate .odd N) hresMinus
      _ = intrinsicCubicQuotientCoordinate .odd N
            (parityCompressedCanonical .odd L (N + 1) Du -
              (lam : ℂ) • Du) -
          (intrinsicCubicQuotientCoordinate .odd N
              (parityCompressedCanonical .odd L (N + 1)
                ((R f : intrinsicParityPredecessorSubspace .odd N) :
                  euclideanParityBoundaryFlatSubspace .odd (N + 1))) -
            intrinsicCubicQuotientCoordinate .odd N
              ((lam : ℂ) •
                ((R f : intrinsicParityPredecessorSubspace .odd N) :
                  euclideanParityBoundaryFlatSubspace .odd (N + 1)))) := by
        rw [map_sub, map_sub]
      _ = (Fplus + phi) - (chi f - 0) := by
        rw [hqDuResidual, hchi, map_smul, hRf0, smul_zero]
      _ = Fplus + phi - chi f := by ring
  have hf : f = Fplus • dW + phi • a := by rfl
  have hchif : chi f = Fplus * chi dW + phi * chi a := by
    calc
      chi f = chi (Fplus • dW + phi • a) := congrArg chi hf
      _ = chi (Fplus • dW) + chi (phi • a) := by rw [map_add]
      _ = Fplus * chi dW + phi * chi a := by
        rw [map_smul, map_smul]
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
          (successorParityCubicVector .odd N) /
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
    successorParityCubicVector .odd N
  let cV : euclideanParityBoundaryFlatSubspace .odd (N + 1) := c
  let den := inner ℂ cV cV
  have hden : den ≠ 0 := by
    change
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) ≠ 0
    exact inner_intrinsicCubicShellPart_self_ne_zero .odd N hN
  have hchiInner :
      chi a =
        inner ℂ cV
            (parityCompressedCanonical .odd L (N + 1)
              ((R a : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) / den := by
    change
      intrinsicCubicQuotientCoordinate .odd N
          (parityCompressedCanonical .odd L (N + 1)
            ((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        inner ℂ cV
            (parityCompressedCanonical .odd L (N + 1)
              ((R a : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) /
          inner ℂ cV cV
    exact
      intrinsicCubicQuotientCoordinate_eq_inner_div
        .odd N hN
        (parityCompressedCanonical .odd L (N + 1)
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)))
  have hsymT :
      inner ℂ cV
          (parityCompressedCanonical .odd L (N + 1)
            ((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        inner ℂ
          (parityCompressedCanonical .odd L (N + 1) cV)
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    exact
      (parityCompressedCanonical_isSymmetric .odd L (N + 1)
        cV
        ((R a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))).symm
  have hTcRa :
      inner ℂ
          (parityCompressedCanonical .odd L (N + 1) cV)
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    let y := parityCompressedCanonical .odd L (N + 1) cV
    have hrec := intrinsicPredecessorPart_add_shellPart .odd N y
    have hpredY : intrinsicPredecessorPart .odd N y = b := by
      rfl
    have hort := inner_intrinsicShell_predecessor_eq_zero
      .odd N (intrinsicShellPart .odd N y) (R a)
    calc
      inner ℂ y
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          ((intrinsicPredecessorPart .odd N y :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        inner ℂ
          ((intrinsicShellPart .odd N y : intrinsicParitySuccShell .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
          rw [← inner_add_left]
          exact congrArg
            (fun z : euclideanParityBoundaryFlatSubspace .odd (N + 1) =>
              inner ℂ z
                ((R a : intrinsicParityPredecessorSubspace .odd N) :
                  euclideanParityBoundaryFlatSubspace .odd (N + 1))) hrec.symm
      _ = inner ℂ
          ((intrinsicPredecessorPart .odd N y :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
        rw [hort, add_zero]
      _ = inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
        rw [hpredY]
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
            (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
    calc
      chi a = inner ℂ cV
          (parityCompressedCanonical .odd L (N + 1)
            ((R a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) / den := hchiInner
      _ = inner ℂ
          (parityCompressedCanonical .odd L (N + 1) cV)
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
        rw [hsymT]
      _ = inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R a : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
        rw [hTcRa]
      _ = inner ℂ
          ((R b : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
        rw [← hRba]
  have hRaC := inner_intrinsicPredecessor_shell_eq_zero .odd N (R b) c
  have hCa := inner_intrinsicShell_predecessor_eq_zero .odd N c a
  have hg :
      g =
        (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (c : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    change
      successorParityCubicVector .odd N =
        (oddCubicGeneratorPredecessorPart N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
    exact oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N
  have huInner :
      inner ℂ u g =
        den -
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
    simp only [neg_zero, zero_add, sub_eq_add_neg]
    change
      - inner ℂ
          ((R b : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) + den =
        den +
          - inner ℂ
            ((R b : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (a : euclideanParityBoundaryFlatSubspace .odd (N + 1))
    ac_rfl
  change 1 - chi a = inner ℂ u g / den
  rw [hchi, huInner]
  field_simp [hden]
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
  rw [evenParityCubicDefectFunctional_eq_evenQuadraticSourceMoment
    hL (N + 1) (by omega)
    (cubicSecularTrialVector .even hL N hprevEven lam hlam)]

/-- Headline root specialization: if the even canonical secular scalar vanishes
at the common safe shift, the odd scalar is exactly an overlap factor times the
actual canonical-source quadratic normal moment. -/
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
          (successorParityCubicVector .odd N) /
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
