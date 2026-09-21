import Zeta23.CCM.CubicNormalizedSchur
import Zeta23.CCM.CutoffFreeMatrix

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Canonical conjugation geometry

The finite canonical CCM matrix has real entries.  This module records the
coordinatewise complex-conjugation structure needed to fix the phase of the
canonical cubic-normalized negative-root state.

Conjugation is deliberately not packaged as a complex-linear map: it is
conjugate-linear.  The theorems below state only the identities actually used
by the retained first-bad route.
-/

/-- Coordinatewise complex conjugation on finite Euclidean coefficient space. -/
def euclideanConj
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => star (x i))

@[simp] theorem euclideanConj_apply
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℂ ι) (i : ι) :
    euclideanConj x i = star (x i) := rfl

@[simp] theorem euclideanConj_coordinates
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℂ ι) :
    (EuclideanSpace.equiv ι ℂ) (euclideanConj x) =
      star ((EuclideanSpace.equiv ι ℂ) x) := by
  funext i
  rfl

@[simp] theorem euclideanConj_zero
    {ι : Type*} [Fintype ι] :
    euclideanConj (0 : EuclideanSpace ℂ ι) = 0 := by
  ext i
  simp

@[simp] theorem euclideanConj_add
    {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) :
    euclideanConj (x + y) = euclideanConj x + euclideanConj y := by
  ext i
  simp

@[simp] theorem euclideanConj_neg
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℂ ι) :
    euclideanConj (-x) = -euclideanConj x := by
  ext i
  simp

@[simp] theorem euclideanConj_sub
    {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) :
    euclideanConj (x - y) = euclideanConj x - euclideanConj y := by
  ext i
  simp

@[simp] theorem euclideanConj_smul
    {ι : Type*} [Fintype ι]
    (a : ℂ) (x : EuclideanSpace ℂ ι) :
    euclideanConj (a • x) = star a • euclideanConj x := by
  ext i
  simp

@[simp] theorem euclideanConj_involutive
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℂ ι) :
    euclideanConj (euclideanConj x) = x := by
  ext i
  simp

/-- Conjugating both vectors conjugates their complex inner product. -/
theorem inner_euclideanConj
    {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) :
    inner ℂ (euclideanConj x) (euclideanConj y) =
      star (inner ℂ x y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [euclideanConj_apply]
  ring

/-- Centered moments commute with coordinatewise conjugation. -/
theorem centeredMoment_star_coefficients
    (N k : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment N k (star u) =
      star (centeredMoment N k u) := by
  unfold centeredMoment
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.star_apply, starRingEnd_apply, star_mul]
  have hreal :
      star (((centeredIndex N i : ℤ) : ℂ) ^ k) =
        (((centeredIndex N i : ℤ) : ℂ) ^ k) := by
    simp
  rw [hreal]
  ring

/-- Coefficient reversal commutes with coordinatewise conjugation. -/
theorem reverseCoefficients_star
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    reverseCoefficients N (star u) =
      star (reverseCoefficients N u) := by
  funext i
  simp [reverseCoefficients]

/-- The boundary-flat equations are stable under coordinate conjugation. -/
theorem star_mem_boundaryFlatSubspace
    (N : ℕ) {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ boundaryFlatSubspace N) :
    star u ∈ boundaryFlatSubspace N := by
  rw [mem_boundaryFlatSubspace_iff] at hu ⊢
  rcases hu with ⟨h0, h1, h2⟩
  constructor
  · rw [centeredMoment_star_coefficients, h0]
    simp
  · constructor
    · rw [centeredMoment_star_coefficients, h1]
      simp
    · rw [centeredMoment_star_coefficients, h2]
      simp

/-- Each parity-resolved boundary-flat sector is stable under conjugation. -/
theorem star_mem_parityBoundaryFlatSubspace
    (p : ReversalParity) (N : ℕ)
    {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ parityBoundaryFlatSubspace p N) :
    star u ∈ parityBoundaryFlatSubspace p N := by
  cases p with
  | even =>
      rcases hu with ⟨hflat, heven⟩
      refine ⟨star_mem_boundaryFlatSubspace N hflat, ?_⟩
      apply (mem_evenCoefficientSubspace_iff N _).2
      have h := (mem_evenCoefficientSubspace_iff N u).1 heven
      rw [reverseCoefficients_star, h]
  | odd =>
      rcases hu with ⟨hflat, hodd⟩
      refine ⟨star_mem_boundaryFlatSubspace N hflat, ?_⟩
      apply (mem_oddCoefficientSubspace_iff N _).2
      have h := (mem_oddCoefficientSubspace_iff N u).1 hodd
      rw [reverseCoefficients_star, h]
      simp

/-- Euclidean parity carriers are stable under coordinate conjugation. -/
theorem euclideanConj_mem_euclideanParityBoundaryFlatSubspace
    (p : ReversalParity) (N : ℕ)
    {x : EuclideanSpace ℂ (Fin (2 * N + 1))}
    (hx : x ∈ euclideanParityBoundaryFlatSubspace p N) :
    euclideanConj x ∈ euclideanParityBoundaryFlatSubspace p N := by
  rw [mem_euclideanParityBoundaryFlatSubspace_iff] at hx ⊢
  rw [euclideanConj_coordinates]
  exact star_mem_parityBoundaryFlatSubspace p N hx

/-- Conjugation internalized on an exact parity carrier. -/
def parityConj
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p N) :
    euclideanParityBoundaryFlatSubspace p N :=
  ⟨euclideanConj
      (v : EuclideanSpace ℂ (Fin (2 * N + 1))),
    euclideanConj_mem_euclideanParityBoundaryFlatSubspace p N v.property⟩

@[simp] theorem coe_parityConj
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p N) :
    ((parityConj p N v : euclideanParityBoundaryFlatSubspace p N) :
      EuclideanSpace ℂ (Fin (2 * N + 1))) =
      euclideanConj
        (v : EuclideanSpace ℂ (Fin (2 * N + 1))) := rfl

@[simp] theorem parityConj_involutive
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p N) :
    parityConj p N (parityConj p N v) = v := by
  apply Subtype.ext
  exact euclideanConj_involutive _

/-- Centered zero extension commutes with raw coordinate conjugation. -/
theorem centeredZeroExtend_star
    {N M : ℕ} (hNM : N ≤ M)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredZeroExtend hNM (star u) =
      star (centeredZeroExtend hNM u) := by
  funext j
  by_cases hj : j ∈ Set.range (centeredEmbedding N M hNM)
  · obtain ⟨i, rfl⟩ := hj
    simp
  · have hleft :=
      centeredZeroExtend_apply_of_not_mem_range hNM (star u) j hj
    have hright :=
      centeredZeroExtend_apply_of_not_mem_range hNM u j hj
    change centeredZeroExtend hNM (star u) j =
      star (centeredZeroExtend hNM u j)
    rw [hleft, hright]
    simp

/-- Euclidean centered zero extension commutes with conjugation. -/
theorem euclideanCenteredZeroExtend_conj
    {N M : ℕ} (hNM : N ≤ M)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    euclideanCenteredZeroExtend hNM (euclideanConj x) =
      euclideanConj (euclideanCenteredZeroExtend hNM x) := by
  apply (EuclideanSpace.equiv (Fin (2 * M + 1)) ℂ).injective
  rw [euclideanCenteredZeroExtend_coordinates,
    euclideanConj_coordinates]
  rw [euclideanConj_coordinates]
  exact centeredZeroExtend_star hNM
    ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x)

/-- The embedded predecessor carrier is stable under conjugation. -/
theorem euclideanConj_mem_euclideanParityEmbeddedSuccSubspace
    (p : ReversalParity) (N : ℕ)
    {x : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))}
    (hx : x ∈ euclideanParityEmbeddedSuccSubspace p N) :
    euclideanConj x ∈ euclideanParityEmbeddedSuccSubspace p N := by
  rcases hx with ⟨y, hy, rfl⟩
  refine ⟨euclideanConj y,
    euclideanConj_mem_euclideanParityBoundaryFlatSubspace p N hy, ?_⟩
  exact (euclideanCenteredZeroExtend_conj (Nat.le_succ N) y).symm

/-- Orthogonal complements of conjugation-stable parity subspaces are stable. -/
theorem euclideanConj_mem_orthogonal_of_mem
    {ι : Type*} [Fintype ι]
    (K : Submodule ℂ (EuclideanSpace ℂ ι))
    (hK : ∀ {x : EuclideanSpace ℂ ι}, x ∈ K → euclideanConj x ∈ K)
    {x : EuclideanSpace ℂ ι}
    (hx : x ∈ Kᗮ) :
    euclideanConj x ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  have hyc : euclideanConj y ∈ K := hK hy
  have h0 := hx (euclideanConj y) hyc
  have hc :=
    inner_euclideanConj x (euclideanConj y)
  rw [euclideanConj_involutive] at hc
  rw [h0] at hc
  simpa using hc

/-- The ambient successor shell is stable under conjugation. -/
theorem euclideanConj_mem_euclideanParitySuccShell
    (p : ReversalParity) (N : ℕ)
    {x : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))}
    (hx : x ∈ euclideanParitySuccShell p N) :
    euclideanConj x ∈ euclideanParitySuccShell p N := by
  rcases hx with ⟨horth, hpar⟩
  refine ⟨?_, euclideanConj_mem_euclideanParityBoundaryFlatSubspace
    p (N + 1) hpar⟩
  exact euclideanConj_mem_orthogonal_of_mem
    (euclideanParityEmbeddedSuccSubspace p N)
    (fun {_} h =>
      euclideanConj_mem_euclideanParityEmbeddedSuccSubspace p N h)
    horth

/-- Conjugation internalized on the intrinsic predecessor. -/
def intrinsicPredecessorConj
    (p : ReversalParity) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) :
    intrinsicParityPredecessorSubspace p N :=
  ⟨parityConj p (N + 1)
      (w : euclideanParityBoundaryFlatSubspace p (N + 1)),
    euclideanConj_mem_euclideanParityEmbeddedSuccSubspace p N w.property⟩

/-- Conjugation internalized on the intrinsic shell. -/
def intrinsicShellConj
    (p : ReversalParity) (N : ℕ)
    (s : intrinsicParitySuccShell p N) :
    intrinsicParitySuccShell p N :=
  ⟨parityConj p (N + 1)
      (s : euclideanParityBoundaryFlatSubspace p (N + 1)),
    euclideanConj_mem_euclideanParitySuccShell p N s.property⟩

@[simp] theorem coe_intrinsicPredecessorConj
    (p : ReversalParity) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) :
    ((intrinsicPredecessorConj p N w :
        intrinsicParityPredecessorSubspace p N) :
      euclideanParityBoundaryFlatSubspace p (N + 1)) =
      parityConj p (N + 1)
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) := rfl

@[simp] theorem coe_intrinsicShellConj
    (p : ReversalParity) (N : ℕ)
    (s : intrinsicParitySuccShell p N) :
    ((intrinsicShellConj p N s : intrinsicParitySuccShell p N) :
      euclideanParityBoundaryFlatSubspace p (N + 1)) =
      parityConj p (N + 1)
        (s : euclideanParityBoundaryFlatSubspace p (N + 1)) := rfl

/-- Algebraic predecessor projection commutes with conjugation. -/
theorem intrinsicPredecessorPart_conj
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
    intrinsicPredecessorPart p N (parityConj p (N + 1) v) =
      intrinsicPredecessorConj p N (intrinsicPredecessorPart p N v) := by
  let w := intrinsicPredecessorPart p N v
  let s := intrinsicShellPart p N v
  have hrec := intrinsicPredecessorPart_add_shellPart p N v
  have hrecC :
      parityConj p (N + 1) v =
        (intrinsicPredecessorConj p N w :
          euclideanParityBoundaryFlatSubspace p (N + 1)) +
        (intrinsicShellConj p N s :
          euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    apply Subtype.ext
    have hc := congrArg euclideanConj
      (congrArg Subtype.val hrec)
    simpa [w, s, euclideanConj_add] using hc.symm
  rw [hrecC, map_add]
  rw [Submodule.projectionOnto_apply_of_mem_left,
    Submodule.projectionOnto_apply_of_mem_right]
  simp [intrinsicPredecessorPart]

/-- Algebraic shell projection commutes with conjugation. -/
theorem intrinsicShellPart_conj
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
    intrinsicShellPart p N (parityConj p (N + 1) v) =
      intrinsicShellConj p N (intrinsicShellPart p N v) := by
  let w := intrinsicPredecessorPart p N v
  let s := intrinsicShellPart p N v
  have hrec := intrinsicPredecessorPart_add_shellPart p N v
  have hrecC :
      parityConj p (N + 1) v =
        (intrinsicPredecessorConj p N w :
          euclideanParityBoundaryFlatSubspace p (N + 1)) +
        (intrinsicShellConj p N s :
          euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    apply Subtype.ext
    have hc := congrArg euclideanConj
      (congrArg Subtype.val hrec)
    simpa [w, s, euclideanConj_add] using hc.symm
  rw [hrecC, map_add]
  rw [Submodule.projectionOnto_apply_of_mem_right,
    Submodule.projectionOnto_apply_of_mem_left]
  simp [intrinsicShellPart]

/-- The canonical source matrix action commutes with coordinate conjugation. -/
theorem canonicalSourceMatrix_mulVec_star
    (L : ℝ) (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    canonicalSourceMatrix L N *ᵥ star u =
      star (canonicalSourceMatrix L N *ᵥ u) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.star_apply, starRingEnd_apply,
    star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hentry :
      star (canonicalSourceMatrix L N i j) =
        canonicalSourceMatrix L N i j := by
    simp [canonicalSourceMatrix, cutoffFreeMatrix]
  rw [hentry]
  ring

/-- The Euclidean canonical source action commutes with conjugation. -/
theorem canonicalSourceMatrix_toEuclideanLin_conj
    (L : ℝ) (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    (canonicalSourceMatrix L N).toEuclideanLin (euclideanConj x) =
      euclideanConj
        ((canonicalSourceMatrix L N).toEuclideanLin x) := by
  apply (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).injective
  change
    canonicalSourceMatrix L N *ᵥ
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) (euclideanConj x)) =
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
        (euclideanConj
          ((canonicalSourceMatrix L N).toEuclideanLin x))
  rw [euclideanConj_coordinates, euclideanConj_coordinates]
  change
    canonicalSourceMatrix L N *ᵥ
        star ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x) =
      star
        (canonicalSourceMatrix L N *ᵥ
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x))
  exact canonicalSourceMatrix_mulVec_star L N _

/-- Orthogonal projection onto a parity carrier commutes with conjugation. -/
theorem parityOrthogonalProjection_conj
    (p : ReversalParity) (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    (euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto
        (euclideanConj x) =
      ⟨euclideanConj
          (((euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto x :
            euclideanParityBoundaryFlatSubspace p N) :
            EuclideanSpace ℂ (Fin (2 * N + 1))),
        euclideanConj_mem_euclideanParityBoundaryFlatSubspace p N
          ((euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto x).property⟩ := by
  let K := euclideanParityBoundaryFlatSubspace p N
  let y : EuclideanSpace ℂ (Fin (2 * N + 1)) :=
    euclideanConj (((K.orthogonalProjectionOnto x : K) :
      EuclideanSpace ℂ (Fin (2 * N + 1))))
  have hy : y ∈ K :=
    euclideanConj_mem_euclideanParityBoundaryFlatSubspace
      p N (K.orthogonalProjectionOnto x).property
  have horth : ∀ w ∈ K, inner ℂ (euclideanConj x - y) w = 0 := by
    intro w hw
    have hwc : euclideanConj w ∈ K :=
      euclideanConj_mem_euclideanParityBoundaryFlatSubspace p N hw
    have h0 := K.starProjection_inner_eq_zero x
      (euclideanConj w) hwc
    have hc := inner_euclideanConj
      (x - ((K.orthogonalProjectionOnto x : K) :
        EuclideanSpace ℂ (Fin (2 * N + 1))))
      (euclideanConj w)
    rw [euclideanConj_involutive] at hc
    have hconjsub :
        euclideanConj
          (x - ((K.orthogonalProjectionOnto x : K) :
            EuclideanSpace ℂ (Fin (2 * N + 1)))) =
          euclideanConj x - y := by
      simp [y, sub_eq_add_neg]
    rw [hconjsub, h0] at hc
    simpa using hc
  apply Subtype.ext
  change K.starProjection (euclideanConj x) = y
  exact K.eq_starProjection_of_mem_of_inner_eq_zero hy horth

/-- The parity-compressed canonical operator commutes with conjugation. -/
theorem parityCompressedCanonical_conj
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p N) :
    parityCompressedCanonical p L N (parityConj p N v) =
      parityConj p N (parityCompressedCanonical p L N v) := by
  change
    (euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto
      ((canonicalSourceMatrix L N).toEuclideanLin
        (euclideanConj
          (v : EuclideanSpace ℂ (Fin (2 * N + 1))))) =
    parityConj p N (parityCompressedCanonical p L N v)
  rw [canonicalSourceMatrix_toEuclideanLin_conj]
  simpa [parityConj] using
    parityOrthogonalProjection_conj p N
      ((canonicalSourceMatrix L N).toEuclideanLin
        (v : EuclideanSpace ℂ (Fin (2 * N + 1))))


/-- Centered polynomial vectors have real coordinates. -/
theorem centeredPowerVector_conj_fixed
    (N k : ℕ) :
    euclideanConj (centeredPowerVector N k) =
      centeredPowerVector N k := by
  apply (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).injective
  ext i
  change star (((centeredIndex N i : ℤ) : ℂ) ^ k) =
    (((centeredIndex N i : ℤ) : ℂ) ^ k)
  simp

/-- The centered-index operator commutes with conjugation. -/
theorem euclideanIndexLinearMap_conj
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    euclideanIndexLinearMap N (euclideanConj x) =
      euclideanConj (euclideanIndexLinearMap N x) := by
  apply (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).injective
  rw [euclideanIndexLinearMap_coordinates,
    euclideanIndexLinearMap_coordinates,
    euclideanConj_coordinates, euclideanConj_coordinates]
  ext i
  rw [indexMatrix_mulVec_apply, indexMatrix_mulVec_apply]
  simp

/-- The even-to-odd centered-index restriction commutes with conjugation. -/
theorem euclideanEvenToOddIndexLinearMap_conj
    (N : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace N) :
    euclideanEvenToOddIndexLinearMap N
        (parityConj .even N v) =
      parityConj .odd N
        (euclideanEvenToOddIndexLinearMap N v) := by
  apply Subtype.ext
  simpa only [coe_euclideanEvenToOddIndexLinearMap, coe_parityConj] using
    euclideanIndexLinearMap_conj N
      (v : EuclideanSpace ℂ (Fin (2 * N + 1)))

/-- The odd cubic compression vector is fixed by conjugation. -/
theorem oddCubicCompressionVector_conj_fixed
    (N : ℕ) :
    parityConj .odd N (oddCubicCompressionVector N) =
      oddCubicCompressionVector N := by
  have h :=
    parityOrthogonalProjection_conj .odd N (centeredPowerVector N 3)
  rw [centeredPowerVector_conj_fixed] at h
  apply Subtype.ext
  exact congrArg Subtype.val h.symm

/-- The pulled-back even cubic compression vector is fixed by conjugation. -/
theorem successorPulledBackCubicCompressionVector_conj_fixed
    (N : ℕ) :
    parityConj .even (N + 1)
        (successorPulledBackCubicCompressionVector N) =
      successorPulledBackCubicCompressionVector N := by
  apply euclideanEvenToOddIndexLinearMap_injective (N + 1)
  rw [euclideanEvenToOddIndexLinearMap_conj,
    evenIndex_successorPulledBackCubicCompressionVector,
    evenIndex_successorPulledBackCubicCompressionVector,
    oddCubicCompressionVector_conj_fixed]

/-- The parity-uniform cubic successor vector is fixed by conjugation. -/
theorem successorParityCubicVector_conj_fixed
    (p : ReversalParity) (N : ℕ) :
    parityConj p (N + 1) (successorParityCubicVector p N) =
      successorParityCubicVector p N := by
  cases p with
  | odd =>
      exact oddCubicCompressionVector_conj_fixed (N + 1)
  | even =>
      exact successorPulledBackCubicCompressionVector_conj_fixed N

/-- The canonical intrinsic cubic shell vector is fixed by conjugation. -/
theorem intrinsicCubicShellPart_conj_fixed
    (p : ReversalParity) (N : ℕ) :
    intrinsicShellConj p N (intrinsicCubicShellPart p N) =
      intrinsicCubicShellPart p N := by
  have h :=
    intrinsicShellPart_conj p N (successorParityCubicVector p N)
  rw [successorParityCubicVector_conj_fixed] at h
  exact h.symm

/-- Canonical cubic shell coordinates conjugate as expected. -/
theorem intrinsicCubicShellCoordinate_conj
    (p : ReversalParity) (N : ℕ)
    (s : intrinsicParitySuccShell p N) :
    intrinsicCubicShellCoordinate p N (intrinsicShellConj p N s) =
      star (intrinsicCubicShellCoordinate p N s) := by
  let c := intrinsicCubicShellPart p N
  have hcShell : intrinsicShellConj p N c = c := by
    simpa [c] using intrinsicCubicShellPart_conj_fixed p N
  have hcCarrier :
      parityConj p (N + 1)
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simpa only [coe_intrinsicShellConj] using
      congrArg
        (fun z : intrinsicParitySuccShell p N =>
          (z : euclideanParityBoundaryFlatSubspace p (N + 1)))
        hcShell
  have hcAmbient :
      euclideanConj
          (((c : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) =
        (((c : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
    exact congrArg Subtype.val hcCarrier
  have hnum0 := inner_euclideanConj
    (((c : intrinsicParitySuccShell p N) :
      euclideanParityBoundaryFlatSubspace p (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
    (((s : intrinsicParitySuccShell p N) :
      euclideanParityBoundaryFlatSubspace p (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
  rw [hcAmbient] at hnum0
  have hden0 := inner_euclideanConj
    (((c : intrinsicParitySuccShell p N) :
      euclideanParityBoundaryFlatSubspace p (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
    (((c : intrinsicParitySuccShell p N) :
      euclideanParityBoundaryFlatSubspace p (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
  rw [hcAmbient] at hden0
  have hdenReal :
      star
          (inner ℂ
            ((c : intrinsicParitySuccShell p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            ((c : intrinsicParitySuccShell p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1))) =
        inner ℂ
          ((c : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          ((c : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simpa using hden0.symm
  change
    inner ℂ
        ((c : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        ((intrinsicShellConj p N s : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) /
      inner ℂ
        ((c : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        ((c : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) =
    star
      (inner ℂ
          ((c : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (s : euclideanParityBoundaryFlatSubspace p (N + 1)) /
        inner ℂ
          ((c : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          ((c : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)))
  have hnum :
      inner ℂ
          ((c : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          ((intrinsicShellConj p N s : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) =
        star
          (inner ℂ
            ((c : intrinsicParitySuccShell p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (s : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
    simpa only [coe_intrinsicShellConj, coe_parityConj] using hnum0
  rw [hnum, star_div₀, hdenReal]

/-- The canonical cubic quotient coordinate commutes with conjugation. -/
theorem intrinsicCubicQuotientCoordinate_conj
    (p : ReversalParity) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p (N + 1)) :
    intrinsicCubicQuotientCoordinate p N (parityConj p (N + 1) v) =
      star (intrinsicCubicQuotientCoordinate p N v) := by
  change
    intrinsicCubicShellCoordinate p N
        (intrinsicShellPart p N (parityConj p (N + 1) v)) =
      star
        (intrinsicCubicShellCoordinate p N
          (intrinsicShellPart p N v))
  rw [intrinsicShellPart_conj]
  exact intrinsicCubicShellCoordinate_conj p N
    (intrinsicShellPart p N v)

end Zeta23.CCM

#print axioms Zeta23.CCM.parityCompressedCanonical_conj
#print axioms Zeta23.CCM.intrinsicShellPart_conj
#print axioms Zeta23.CCM.canonicalSourceMatrix_toEuclideanLin_conj
