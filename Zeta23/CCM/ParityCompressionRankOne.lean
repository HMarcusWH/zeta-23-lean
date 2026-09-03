import Zeta23.CCM.ParityNormalSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-C: rank-one compressed parity defect

The centered-index operator D maps the even boundary-flat sector to the odd
boundary-flat sector.  The ambient canonical operator commutes with D on every
even boundary-flat vector, while the even compression residual lies in the
normal space span{1,d^2}.  After odd orthogonal compression the d term is
killed, leaving only the projected d^3 channel.

The principal endpoint is therefore an operator-level range theorem:

  range (T_- D - D T_+) <= C * P_- d^3,

hence the defect has complex finrank at most one.  For N >= 2 the explicit
cubic generator P_- d^3 is nonzero.  For N >= 1 the odd compressed operator
can also be transported back to the even sector through the algebraic D
linear equivalence, giving a same-space rank-at-most-one defect.

No unitary equivalence, equal-spectrum theorem, sign theorem, Schur/Feshbach
formula, positivity theorem, finite-to-infinite theorem, or RH theorem is
claimed.
-/

/-- Euclidean centered-index action. -/
def euclideanIndexLinearMap
    (N : ℕ) :
    EuclideanSpace ℂ (Fin (2 * N + 1)) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin (2 * N + 1)) :=
  (indexMatrix N).toEuclideanLin

theorem euclideanIndexLinearMap_coordinates
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
        (euclideanIndexLinearMap N x) =
      indexMatrix N *ᵥ
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x) := by
  change
    WithLp.ofLp ((indexMatrix N).toEuclideanLin x) =
      indexMatrix N *ᵥ WithLp.ofLp x
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]

/-- Euclidean restriction of D from the even constrained sector to the odd
constrained sector. -/
def euclideanEvenToOddIndexLinearMap
    (N : ℕ) :
    euclideanEvenBoundaryFlatSubspace N →ₗ[ℂ]
      euclideanOddBoundaryFlatSubspace N where
  toFun := fun x => by
    let y := euclideanIndexLinearMap N
      (x : EuclideanSpace ℂ (Fin (2 * N + 1)))
    have hxraw :
        (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
            (x : EuclideanSpace ℂ (Fin (2 * N + 1))) ∈
          evenBoundaryFlatSubspace N :=
      (mem_euclideanEvenBoundaryFlatSubspace_iff N _).mp x.property
    let xr : evenBoundaryFlatSubspace N :=
      ⟨(EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
          (x : EuclideanSpace ℂ (Fin (2 * N + 1))), hxraw⟩
    have hyraw :
        indexMatrix N *ᵥ
            ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
              (x : EuclideanSpace ℂ (Fin (2 * N + 1)))) ∈
          oddBoundaryFlatSubspace N := by
      change
        ((evenToOddIndexLinearMap N xr : oddBoundaryFlatSubspace N) :
          Fin (2 * N + 1) → ℂ) ∈ oddBoundaryFlatSubspace N
      exact (evenToOddIndexLinearMap N xr).property
    have hy : y ∈ euclideanOddBoundaryFlatSubspace N := by
      rw [mem_euclideanOddBoundaryFlatSubspace_iff]
      rw [euclideanIndexLinearMap_coordinates]
      exact hyraw
    exact ⟨y, hy⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp [euclideanIndexLinearMap]
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp [euclideanIndexLinearMap]

@[simp] theorem coe_euclideanEvenToOddIndexLinearMap
    (N : ℕ)
    (x : euclideanEvenBoundaryFlatSubspace N) :
    ((euclideanEvenToOddIndexLinearMap N x :
        euclideanOddBoundaryFlatSubspace N) :
      EuclideanSpace ℂ (Fin (2 * N + 1))) =
      euclideanIndexLinearMap N
        (x : EuclideanSpace ℂ (Fin (2 * N + 1))) := rfl

/-- D is injective on the Euclidean even constrained sector. -/
theorem euclideanEvenToOddIndexLinearMap_injective
    (N : ℕ) :
    Function.Injective (euclideanEvenToOddIndexLinearMap N) := by
  intro x y hxy
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).injective
  let xr : evenBoundaryFlatSubspace N :=
    ⟨(EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
        (x : EuclideanSpace ℂ (Fin (2 * N + 1))),
      (mem_euclideanEvenBoundaryFlatSubspace_iff N _).mp x.property⟩
  let yr : evenBoundaryFlatSubspace N :=
    ⟨(EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
        (y : EuclideanSpace ℂ (Fin (2 * N + 1))),
      (mem_euclideanEvenBoundaryFlatSubspace_iff N _).mp y.property⟩
  have hxy' := congrArg Subtype.val hxy
  rw [coe_euclideanEvenToOddIndexLinearMap,
    coe_euclideanEvenToOddIndexLinearMap] at hxy'
  have hcoords := congrArg
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) hxy'
  rw [euclideanIndexLinearMap_coordinates,
    euclideanIndexLinearMap_coordinates] at hcoords
  have hraw :
      evenToOddIndexLinearMap N xr =
        evenToOddIndexLinearMap N yr := by
    apply Subtype.ext
    exact hcoords
  have hxyr := evenToOddIndexLinearMap_injective N hraw
  change (xr : Fin (2 * N + 1) → ℂ) =
    (yr : Fin (2 * N + 1) → ℂ)
  exact congrArg Subtype.val hxyr

/-- For N >= 1, equal parity dimensions turn injectivity of D into
surjectivity. -/
theorem euclideanEvenToOddIndexLinearMap_surjective
    (N : ℕ) (hN : 1 ≤ N) :
    Function.Surjective (euclideanEvenToOddIndexLinearMap N) := by
  have hdim :
      Module.finrank ℂ (euclideanEvenBoundaryFlatSubspace N) =
        Module.finrank ℂ (euclideanOddBoundaryFlatSubspace N) := by
    rw [finrank_euclideanEvenBoundaryFlatSubspace N hN,
      finrank_euclideanOddBoundaryFlatSubspace N hN]
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (euclideanEvenToOddIndexLinearMap_injective N)

/-- Algebraic Euclidean D-equivalence for the nontrivial finite sectors.
This is deliberately not asserted to be an isometry or unitary equivalence. -/
def euclideanEvenOddBoundaryFlatLinearEquiv
    (N : ℕ) (hN : 1 ≤ N) :
    euclideanEvenBoundaryFlatSubspace N ≃ₗ[ℂ]
      euclideanOddBoundaryFlatSubspace N :=
  LinearEquiv.ofBijective
    (euclideanEvenToOddIndexLinearMap N)
    ⟨euclideanEvenToOddIndexLinearMap_injective N,
      euclideanEvenToOddIndexLinearMap_surjective N hN⟩

/-- Explicitly typed even parity compression. -/
def evenCompressedCanonical
    (L : ℝ) (N : ℕ) :
    euclideanEvenBoundaryFlatSubspace N →ₗ[ℂ]
      euclideanEvenBoundaryFlatSubspace N :=
  parityCompressedCanonical .even L N

/-- Explicitly typed odd parity compression. -/
def oddCompressedCanonical
    (L : ℝ) (N : ℕ) :
    euclideanOddBoundaryFlatSubspace N →ₗ[ℂ]
      euclideanOddBoundaryFlatSubspace N :=
  parityCompressedCanonical .odd L N

/-- D sends the centered power d^k to d^(k+1). -/
theorem euclideanIndexLinearMap_centeredPowerVector
    (N k : ℕ) :
    euclideanIndexLinearMap N (centeredPowerVector N k) =
      centeredPowerVector N (k + 1) := by
  apply (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).injective
  rw [euclideanIndexLinearMap_coordinates]
  ext i
  rw [indexMatrix_mulVec_apply]
  simp [centeredPowerVector_apply, pow_succ, mul_comm]

/-- Ambient residual of arbitrary even orthogonal compression. -/
def evenCompressionResidual
    (L : ℝ) (N : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace N) :
    EuclideanSpace ℂ (Fin (2 * N + 1)) :=
  (canonicalSourceMatrix L N).toEuclideanLin
      (v : EuclideanSpace ℂ (Fin (2 * N + 1))) -
    (evenCompressedCanonical L N v :
      EuclideanSpace ℂ (Fin (2 * N + 1)))

theorem evenCompressionResidual_mem_orthogonal
    (L : ℝ) (N : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace N) :
    evenCompressionResidual L N v ∈
      (euclideanEvenBoundaryFlatSubspace N)ᗮ := by
  let V := euclideanEvenBoundaryFlatSubspace N
  let z :=
    (canonicalSourceMatrix L N).toEuclideanLin
      (v : EuclideanSpace ℂ (Fin (2 * N + 1)))
  have horth := V.sub_starProjection_mem_orthogonal z
  have hproj :
      V.starProjection z =
        (evenCompressedCanonical L N v :
          EuclideanSpace ℂ (Fin (2 * N + 1))) := by
    change
      ((V.orthogonalProjectionOnto z : V) :
          EuclideanSpace ℂ (Fin (2 * N + 1))) =
        (evenCompressedCanonical L N v :
          EuclideanSpace ℂ (Fin (2 * N + 1)))
    rfl
  rw [hproj] at horth
  simpa [evenCompressionResidual, z] using horth

theorem evenCompressionResidual_mem_evenCoefficient
    (L : ℝ) (N : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace N) :
    evenCompressionResidual L N v ∈
      euclideanEvenCoefficientSubspace N := by
  have hv :
      (v : EuclideanSpace ℂ (Fin (2 * N + 1))) ∈
        euclideanEvenCoefficientSubspace N :=
    ((mem_euclideanEvenBoundaryFlatSubspace_iff N _).mp v.property).2
  have hMv :=
    canonicalSourceMatrix_toEuclideanLin_mem_evenCoefficient L N hv
  have hTv :
      (evenCompressedCanonical L N v :
        EuclideanSpace ℂ (Fin (2 * N + 1))) ∈
          euclideanEvenCoefficientSubspace N :=
    ((mem_euclideanEvenBoundaryFlatSubspace_iff N _).mp
      (evenCompressedCanonical L N v).property).2
  exact (euclideanEvenCoefficientSubspace N).sub_mem hMv hTv

/-- The arbitrary even compression residual lies in the exact normal channel
span{1,d^2}. -/
theorem evenCompressionResidual_mem_evenNormalSubspace
    (L : ℝ) (N : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace N) :
    evenCompressionResidual L N v ∈ evenNormalSubspace N := by
  have h :
      evenCompressionResidual L N v ∈
        (euclideanEvenBoundaryFlatSubspace N)ᗮ ⊓
          euclideanEvenCoefficientSubspace N :=
    ⟨evenCompressionResidual_mem_orthogonal L N v,
      evenCompressionResidual_mem_evenCoefficient L N v⟩
  rw [evenBoundaryFlat_normal_eq_evenNormalSubspace N] at h
  exact h

/-- Explicit arbitrary-vector even compression residual formula. -/
theorem exists_evenCompressionResidual_coefficients
    (L : ℝ) (N : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace N) :
    ∃ a0 a2 : ℂ,
      (canonicalSourceMatrix L N).toEuclideanLin
          (v : EuclideanSpace ℂ (Fin (2 * N + 1))) =
        (evenCompressedCanonical L N v :
          EuclideanSpace ℂ (Fin (2 * N + 1))) +
        a0 • centeredPowerVector N 0 +
        a2 • centeredPowerVector N 2 := by
  have hr := evenCompressionResidual_mem_evenNormalSubspace L N v
  rw [evenNormalSubspace, Submodule.mem_sup] at hr
  rcases hr with ⟨y, hy, z, hz, hyz⟩
  rw [Submodule.mem_span_singleton] at hy
  rw [Submodule.mem_span_singleton] at hz
  rcases hy with ⟨a0, rfl⟩
  rcases hz with ⟨a2, rfl⟩
  refine ⟨a0, a2, ?_⟩
  dsimp [evenCompressionResidual] at hyz
  have hadd := congrArg
    (fun t =>
      t + (evenCompressedCanonical L N v :
        EuclideanSpace ℂ (Fin (2 * N + 1)))) hyz.symm
  simpa [add_assoc, add_left_comm, add_comm] using hadd

/-- Euclidean form of the exact even commutator collapse: M(Du)=D(Mu). -/
theorem canonicalSourceMatrix_toEuclideanLin_commutes_index_on_even
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace N) :
    (canonicalSourceMatrix L N).toEuclideanLin
        (euclideanIndexLinearMap N
          (v : EuclideanSpace ℂ (Fin (2 * N + 1)))) =
      euclideanIndexLinearMap N
        ((canonicalSourceMatrix L N).toEuclideanLin
          (v : EuclideanSpace ℂ (Fin (2 * N + 1)))) := by
  apply (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).injective
  rw [canonicalSourceMatrix_toEuclideanLin_coordinates,
    euclideanIndexLinearMap_coordinates,
    euclideanIndexLinearMap_coordinates,
    canonicalSourceMatrix_toEuclideanLin_coordinates]
  let u :=
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
      (v : EuclideanSpace ℂ (Fin (2 * N + 1)))
  have hflat : u ∈ boundaryFlatSubspace N :=
    ((mem_euclideanEvenBoundaryFlatSubspace_iff N _).mp v.property).1
  have heven : u ∈ evenCoefficientSubspace N :=
    ((mem_euclideanEvenBoundaryFlatSubspace_iff N _).mp v.property).2
  have hcomm :=
    canonicalSourceMatrix_displacement_mulVec_even_boundaryFlat
      hL N u hflat heven
  rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec] at hcomm
  exact (sub_eq_zero.mp hcomm).symm

/-- The explicit surviving cubic odd compression channel. -/
def oddCubicCompressionVector
    (N : ℕ) :
    euclideanOddBoundaryFlatSubspace N :=
  (euclideanOddBoundaryFlatSubspace N).orthogonalProjectionOnto
    (centeredPowerVector N 3)

theorem centeredPowerVector_three_mem_oddCoefficient
    (N : ℕ) :
    centeredPowerVector N 3 ∈ euclideanOddCoefficientSubspace N := by
  rw [mem_euclideanOddCoefficientSubspace_iff]
  apply (mem_oddCoefficientSubspace_iff N _).2
  ext i
  simp [reverseCoefficients, centeredPowerVector, pow_succ]

/-- For N >= 2 the cubic channel does not vanish after odd constrained
projection. -/
theorem oddCubicCompressionVector_ne_zero
    (N : ℕ) (hN : 2 ≤ N) :
    oddCubicCompressionVector N ≠ 0 := by
  intro hg
  have horth :
      centeredPowerVector N 3 ∈
        (euclideanOddBoundaryFlatSubspace N)ᗮ := by
    exact
      ((euclideanOddBoundaryFlatSubspace N).orthogonalProjectionOnto_eq_zero_iff).mp
        (by simpa [oddCubicCompressionVector] using hg)
  have hnormal :
      centeredPowerVector N 3 ∈ oddNormalSubspace N := by
    have hi :
        centeredPowerVector N 3 ∈
          (euclideanOddBoundaryFlatSubspace N)ᗮ ⊓
            euclideanOddCoefficientSubspace N :=
      ⟨horth, centeredPowerVector_three_mem_oddCoefficient N⟩
    rw [oddBoundaryFlat_normal_eq_oddNormalSubspace N] at hi
    exact hi
  rw [oddNormalSubspace, Submodule.mem_span_singleton] at hnormal
  rcases hnormal with ⟨a, ha⟩
  let i1 : Fin (2 * N + 1) := ⟨N + 1, by omega⟩
  let i2 : Fin (2 * N + 1) := ⟨N + 2, by omega⟩
  have hi1 : centeredIndex N i1 = 1 := by
    simp [i1, centeredIndex]
  have hi2 : centeredIndex N i2 = 2 := by
    simp [i2, centeredIndex]
  have h1 := congrArg
    (fun x : EuclideanSpace ℂ (Fin (2 * N + 1)) => x i1) ha
  have h2 := congrArg
    (fun x : EuclideanSpace ℂ (Fin (2 * N + 1)) => x i2) ha
  simp [centeredPowerVector_apply, hi1, hi2, smul_eq_mul] at h1 h2
  rw [h1] at h2
  norm_num at h2

/-- Failure of compressed D-intertwining. -/
def evenOddCompressedIntertwiningDefect
    (L : ℝ) (N : ℕ) :
    euclideanEvenBoundaryFlatSubspace N →ₗ[ℂ]
      euclideanOddBoundaryFlatSubspace N :=
  (oddCompressedCanonical L N).comp
      (euclideanEvenToOddIndexLinearMap N) -
    (euclideanEvenToOddIndexLinearMap N).comp
      (evenCompressedCanonical L N)

/-- Pointwise defect formula: every defect value is a scalar multiple of the
single cubic odd compression vector. -/
theorem exists_evenOddCompressedIntertwiningDefect_eq_smul_cubic
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace N) :
    ∃ a2 : ℂ,
      evenOddCompressedIntertwiningDefect L N v =
        a2 • oddCubicCompressionVector N := by
  obtain ⟨a0, a2, hres⟩ :=
    exists_evenCompressionResidual_coefficients L N v
  have hDres := congrArg (euclideanIndexLinearMap N) hres
  have hDres' :
      euclideanIndexLinearMap N
          ((canonicalSourceMatrix L N).toEuclideanLin
            (v : EuclideanSpace ℂ (Fin (2 * N + 1)))) =
        euclideanIndexLinearMap N
            (evenCompressedCanonical L N v :
              EuclideanSpace ℂ (Fin (2 * N + 1))) +
          a0 • centeredPowerVector N 1 +
          a2 • centeredPowerVector N 3 := by
    simpa [map_add, map_smul,
      euclideanIndexLinearMap_centeredPowerVector,
      add_assoc] using hDres
  have hMD :
      (canonicalSourceMatrix L N).toEuclideanLin
          ((euclideanEvenToOddIndexLinearMap N v :
              euclideanOddBoundaryFlatSubspace N) :
            EuclideanSpace ℂ (Fin (2 * N + 1))) =
        euclideanIndexLinearMap N
            (evenCompressedCanonical L N v :
              EuclideanSpace ℂ (Fin (2 * N + 1))) +
          a0 • centeredPowerVector N 1 +
          a2 • centeredPowerVector N 3 := by
    rw [coe_euclideanEvenToOddIndexLinearMap,
      canonicalSourceMatrix_toEuclideanLin_commutes_index_on_even hL N v]
    exact hDres'
  have hp1 :
      (euclideanOddBoundaryFlatSubspace N).orthogonalProjectionOnto
          (centeredPowerVector N 1) = 0 := by
    exact
      ((euclideanOddBoundaryFlatSubspace N).orthogonalProjectionOnto_eq_zero_iff).2
        (centeredPowerVector_one_mem_oddBoundaryFlat_orthogonal N)
  have hproj' :
      oddCompressedCanonical L N
          (euclideanEvenToOddIndexLinearMap N v) =
        euclideanEvenToOddIndexLinearMap N
            (evenCompressedCanonical L N v) +
          a2 • oddCubicCompressionVector N := by
    change
      (euclideanOddBoundaryFlatSubspace N).orthogonalProjectionOnto
          ((canonicalSourceMatrix L N).toEuclideanLin
            ((euclideanEvenToOddIndexLinearMap N v :
                euclideanOddBoundaryFlatSubspace N) :
              EuclideanSpace ℂ (Fin (2 * N + 1)))) =
        euclideanEvenToOddIndexLinearMap N
            (evenCompressedCanonical L N v) +
          a2 • oddCubicCompressionVector N
    rw [hMD]
    simp only [map_add, map_smul]
    have hindex :
        euclideanIndexLinearMap N
            (evenCompressedCanonical L N v :
              EuclideanSpace ℂ (Fin (2 * N + 1))) =
          ((euclideanEvenToOddIndexLinearMap N
              (evenCompressedCanonical L N v) :
                euclideanOddBoundaryFlatSubspace N) :
            EuclideanSpace ℂ (Fin (2 * N + 1))) :=
      (coe_euclideanEvenToOddIndexLinearMap N
        (evenCompressedCanonical L N v)).symm
    rw [hindex, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, hp1]
    simp [oddCubicCompressionVector, add_assoc]
  refine ⟨a2, ?_⟩
  change
    oddCompressedCanonical L N
        (euclideanEvenToOddIndexLinearMap N v) -
      euclideanEvenToOddIndexLinearMap N
        (evenCompressedCanonical L N v) =
      a2 • oddCubicCompressionVector N
  rw [hproj']
  abel

theorem evenOddCompressedIntertwiningDefect_mem_span
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace N) :
    evenOddCompressedIntertwiningDefect L N v ∈
      ℂ ∙ oddCubicCompressionVector N := by
  obtain ⟨a2, h⟩ :=
    exists_evenOddCompressedIntertwiningDefect_eq_smul_cubic hL N v
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- Operator-level endpoint: the compressed parity intertwining defect has
range in one explicit line. -/
theorem range_evenOddCompressedIntertwiningDefect_le
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) :
    LinearMap.range (evenOddCompressedIntertwiningDefect L N) ≤
      ℂ ∙ oddCubicCompressionVector N := by
  intro y hy
  rcases hy with ⟨v, rfl⟩
  exact evenOddCompressedIntertwiningDefect_mem_span hL N v

/-- Finrank formulation of the rank-at-most-one endpoint. -/
theorem finrank_range_evenOddCompressedIntertwiningDefect_le_one
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) :
    Module.finrank ℂ
      (LinearMap.range (evenOddCompressedIntertwiningDefect L N)) ≤ 1 := by
  calc
    Module.finrank ℂ
        (LinearMap.range (evenOddCompressedIntertwiningDefect L N))
        ≤ Module.finrank ℂ (ℂ ∙ oddCubicCompressionVector N) :=
      Submodule.finrank_mono
        (range_evenOddCompressedIntertwiningDefect_le hL N)
    _ ≤ 1 := by
      exact le_trans
        (finrank_span_le_card
          ({oddCubicCompressionVector N} :
            Set (euclideanOddBoundaryFlatSubspace N)))
        (by simp)

/-- Odd compressed canonical operator transported back to the even constrained
space by the algebraic D-equivalence. -/
def oddCompressedCanonicalConjugated
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    euclideanEvenBoundaryFlatSubspace N →ₗ[ℂ]
      euclideanEvenBoundaryFlatSubspace N :=
  (euclideanEvenOddBoundaryFlatLinearEquiv N hN).symm.toLinearMap.comp
    ((oddCompressedCanonical L N).comp
      (euclideanEvenOddBoundaryFlatLinearEquiv N hN).toLinearMap)

/-- Same-space defect after conjugating the odd compression through D. -/
def conjugatedParityCompressionDefect
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    euclideanEvenBoundaryFlatSubspace N →ₗ[ℂ]
      euclideanEvenBoundaryFlatSubspace N :=
  oddCompressedCanonicalConjugated L N hN -
    evenCompressedCanonical L N

/-- The conjugated same-space parity defect also has finrank at most one. -/
theorem finrank_range_conjugatedParityCompressionDefect_le_one
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ
      (LinearMap.range (conjugatedParityCompressionDefect L N hN)) ≤ 1 := by
  let E := euclideanEvenOddBoundaryFlatLinearEquiv N hN
  let F := evenOddCompressedIntertwiningDefect L N
  have hdef :
      conjugatedParityCompressionDefect L N hN =
        E.symm.toLinearMap.comp F := by
    apply LinearMap.ext
    intro v
    change
      E.symm (oddCompressedCanonical L N (E v)) -
          evenCompressedCanonical L N v =
        E.symm
          (oddCompressedCanonical L N (E v) -
            E (evenCompressedCanonical L N v))
    rw [map_sub, E.symm_apply_apply]
  rw [hdef]
  have hrange :
      LinearMap.range (E.symm.toLinearMap.comp F) ≤
        (LinearMap.range F).map E.symm.toLinearMap := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨F x, ⟨x, rfl⟩, rfl⟩
  calc
    Module.finrank ℂ
        (LinearMap.range (E.symm.toLinearMap.comp F))
        ≤ Module.finrank ℂ ((LinearMap.range F).map E.symm.toLinearMap) :=
      Submodule.finrank_mono hrange
    _ ≤ Module.finrank ℂ (LinearMap.range F) :=
      Submodule.finrank_map_le _ _
    _ ≤ 1 := by
      simpa [F] using
        finrank_range_evenOddCompressedIntertwiningDefect_le_one hL N