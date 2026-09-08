import Zeta23.CCM.SourceExplicitCubicDefect
import Zeta23.CCM.CubicSecularMetric

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A3c: quotient and shell transport

Compiler-facing parity-native wrappers around the already validated even/odd
maps.  They introduce no new mathematical assumptions and are used only to
keep all intermediate additive/module operations on one Lean carrier.
-/

/-- Parity-native view of the validated Euclidean centered-index map. -/
def evenIndexParityLinearMap
    (K : ℕ) :
    euclideanParityBoundaryFlatSubspace .even K →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace .odd K :=
  euclideanEvenToOddIndexLinearMap K

/-- Parity-native view of the validated rank-one intertwining defect. -/
def evenOddParityIntertwiningDefect
    (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace .even K →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace .odd K :=
  evenOddCompressedIntertwiningDefect L K

/-- Parity-native view of the validated cubic defect functional. -/
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

/-- The canonical cubic shell vector has quotient coordinate one. -/
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
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := hrepCarrier.symm
    _ = cubicSecularScalar p hL N hprev lam hlam •
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
      rw [hscalar]

/-- Algebraic D transport preserves the canonical one-step quotient
coordinate. -/
theorem intrinsicCubicQuotientCoordinate_evenIndex
    (N : ℕ) (hN : 1 ≤ N)
    (v : euclideanParityBoundaryFlatSubspace .even (N + 1)) :
    intrinsicCubicQuotientCoordinate .odd N
        (evenIndexParityLinearMap (N + 1) v) =
      intrinsicCubicQuotientCoordinate .even N v := by
  let D := evenIndexParityLinearMap (N + 1)
  let Qe := intrinsicCubicQuotientCoordinate .even N
  let Qo := intrinsicCubicQuotientCoordinate .odd N
  let k := Qe v
  let g : euclideanParityBoundaryFlatSubspace .even (N + 1) :=
    successorParityCubicVector .even N
  let r : euclideanParityBoundaryFlatSubspace .even (N + 1) := v - k • g
  have hgcoord : Qe g = 1 := by
    simpa [Qe, g] using
      intrinsicCubicQuotientCoordinate_successorParityCubicVector .even N hN
  have hqSub : Qe (v - k • g) = Qe v - Qe (k • g) :=
    Qe.map_sub v (k • g)
  have hqSmul : Qe (k • g) = k • Qe g :=
    Qe.map_smul k g
  have hrcoord : Qe r = 0 := by
    calc
      Qe r = Qe (v - k • g) := rfl
      _ = Qe v - Qe (k • g) := hqSub
      _ = Qe v - k • Qe g := by rw [hqSmul]
      _ = Qe v - k • (1 : ℂ) := by rw [hgcoord]
      _ = 0 := by simp [k]
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
  have hDrCoord : Qo (D r) = 0 := by
    exact (intrinsicCubicQuotientCoordinate_eq_zero_iff .odd N hN).2 hDrPred
  have hDg : D g = successorParityCubicVector .odd N := by
    change
      euclideanEvenToOddIndexLinearMap (N + 1)
          (successorPulledBackCubicCompressionVector N) =
        oddCubicCompressionVector (N + 1)
    exact evenIndex_successorPulledBackCubicCompressionVector N
  have hoddgcoord : Qo (successorParityCubicVector .odd N) = 1 := by
    simpa [Qo] using
      intrinsicCubicQuotientCoordinate_successorParityCubicVector .odd N hN
  have hDSub : D (v - k • g) = D v - D (k • g) :=
    D.map_sub v (k • g)
  have hDSmul : D (k • g) = k • D g := D.map_smul k g
  have hDrDecomp : D r = D v - k • D g := by
    calc
      D r = D (v - k • g) := rfl
      _ = D v - D (k • g) := hDSub
      _ = D v - k • D g := by rw [hDSmul]
  have hQoSub : Qo (D v - k • D g) = Qo (D v) - Qo (k • D g) :=
    Qo.map_sub (D v) (k • D g)
  have hQoSmul : Qo (k • D g) = k • Qo (D g) := Qo.map_smul k (D g)
  rw [hDrDecomp] at hDrCoord
  calc
    Qo (D v) = k := by
      have hz : Qo (D v) - k = 0 := by
        calc
          Qo (D v) - k = Qo (D v) - k • (1 : ℂ) := by simp
          _ = Qo (D v) - k • Qo (successorParityCubicVector .odd N) := by
            rw [hoddgcoord]
          _ = Qo (D v) - k • Qo (D g) := by rw [hDg]
          _ = Qo (D v) - Qo (k • D g) := by rw [hQoSmul]
          _ = Qo (D v - k • D g) := hQoSub.symm
          _ = 0 := hDrCoord
      exact sub_eq_zero.mp hz
    _ = Qe v := rfl

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
  have hq : intrinsicCubicQuotientCoordinate .odd N y = 1 :=
    hqTransport.trans hqEven
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
  intrinsicPredecessorPart .odd N (successorParityCubicVector .odd N)

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
  have hp : intrinsicPredecessorPart .odd N y = oddIndexCubicShellPredecessorPart N := by
    rfl
  calc
    evenIndexParityLinearMap (N + 1)
        (intrinsicCubicShellPart .even N :
          euclideanParityBoundaryFlatSubspace .even (N + 1)) = y := rfl
    _ =
        (intrinsicPredecessorPart .odd N y :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (intrinsicShellPart .odd N y :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := hrec.symm
    _ =
        (oddIndexCubicShellPredecessorPart N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
      rw [hp, hs]

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
    rfl
  have hp : intrinsicPredecessorPart .odd N g = oddCubicGeneratorPredecessorPart N := by
    rfl
  calc
    successorParityCubicVector .odd N = g := rfl
    _ =
        (intrinsicPredecessorPart .odd N g :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (intrinsicShellPart .odd N g :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := hrec.symm
    _ =
        (oddCubicGeneratorPredecessorPart N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
      rw [hp, hs]

end Zeta23.CCM
