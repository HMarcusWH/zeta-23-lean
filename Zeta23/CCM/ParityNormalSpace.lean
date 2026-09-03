import Zeta23.CCM.FirstBadRigidity
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-B: parity normal spaces and KKT residuals

This module identifies the exact normal spaces of the even and odd
boundary-flat sectors inside their reversal-parity ambient spaces. The normal
vectors are the explicit centered power vectors 1, d, d². It then converts
an eigenmode of the parity-compressed canonical operator into an ambient KKT
residual with only those parity-legal normal components.

No shell invariance, negative-index theorem, Schur/Feshbach formula,
positivity theorem, finite-to-infinite theorem, or RH theorem is claimed.
-/

/-- Euclidean transport of the raw even coefficient sector. -/
def euclideanEvenCoefficientSubspace
    (N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 1))) :=
  (evenCoefficientSubspace N).comap
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).toLinearEquiv.toLinearMap

/-- Euclidean transport of the raw odd coefficient sector. -/
def euclideanOddCoefficientSubspace
    (N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 1))) :=
  (oddCoefficientSubspace N).comap
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).toLinearEquiv.toLinearMap

def euclideanParityCoefficientSubspace
    (p : ReversalParity) (N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 1))) :=
  match p with
  | .even => euclideanEvenCoefficientSubspace N
  | .odd => euclideanOddCoefficientSubspace N

@[simp] theorem mem_euclideanEvenCoefficientSubspace_iff
    (N : ℕ) (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    x ∈ euclideanEvenCoefficientSubspace N ↔
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x ∈
        evenCoefficientSubspace N := Iff.rfl

@[simp] theorem mem_euclideanOddCoefficientSubspace_iff
    (N : ℕ) (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    x ∈ euclideanOddCoefficientSubspace N ↔
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x ∈
        oddCoefficientSubspace N := Iff.rfl

@[simp] theorem mem_euclideanParityCoefficientSubspace_iff
    (p : ReversalParity) (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    x ∈ euclideanParityCoefficientSubspace p N ↔
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x ∈
        (match p with
        | .even => evenCoefficientSubspace N
        | .odd => oddCoefficientSubspace N) := by
  cases p <;> rfl

theorem euclideanParityBoundaryFlatSubspace_le_coefficientSubspace
    (p : ReversalParity) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p N ≤
      euclideanParityCoefficientSubspace p N := by
  cases p with
  | even =>
      intro x hx
      exact ((mem_euclideanEvenBoundaryFlatSubspace_iff N x).mp hx).2
  | odd =>
      intro x hx
      exact ((mem_euclideanOddBoundaryFlatSubspace_iff N x).mp hx).2

/-- Explicit Euclidean vector with coordinate d_i^k. -/
def centeredPowerVector
    (N k : ℕ) :
    EuclideanSpace ℂ (Fin (2 * N + 1)) :=
  WithLp.toLp 2 (fun i => (((centeredIndex N i : ℤ) : ℂ) ^ k))

@[simp] theorem centeredPowerVector_apply
    (N k : ℕ) (i : Fin (2 * N + 1)) :
    centeredPowerVector N k i =
      (((centeredIndex N i : ℤ) : ℂ) ^ k) := rfl

/-- The centered power vectors are the Riesz representatives of the centered
moment functionals. -/
theorem inner_centeredPowerVector
    (N k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    inner ℂ (centeredPowerVector N k) x =
      centeredMoment N k
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct centeredMoment
  apply Finset.sum_congr rfl
  intro i hi
  simp [centeredPowerVector, mul_comm]

theorem centeredMoment_one_eq_zero_of_even
    {N : ℕ} {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ evenCoefficientSubspace N) :
    centeredMoment N 1 u = 0 := by
  have h := centeredMoment_reverseCoefficients N 1 u
  rw [(mem_evenCoefficientSubspace_iff N u).mp hu] at h
  norm_num at h
  linear_combination (1 / 2 : ℂ) * h

theorem centeredMoment_zero_eq_zero_of_odd
    {N : ℕ} {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ oddCoefficientSubspace N) :
    centeredMoment N 0 u = 0 := by
  have h := centeredMoment_reverseCoefficients N 0 u
  rw [(mem_oddCoefficientSubspace_iff N u).mp hu] at h
  norm_num at h
  linear_combination (-1 / 2 : ℂ) * h

theorem centeredMoment_two_eq_zero_of_odd
    {N : ℕ} {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ oddCoefficientSubspace N) :
    centeredMoment N 2 u = 0 := by
  have h := centeredMoment_reverseCoefficients N 2 u
  rw [(mem_oddCoefficientSubspace_iff N u).mp hu] at h
  norm_num at h
  linear_combination (-1 / 2 : ℂ) * h

theorem centeredPowerVector_zero_mem_evenCoefficient
    (N : ℕ) :
    centeredPowerVector N 0 ∈ euclideanEvenCoefficientSubspace N := by
  rw [mem_euclideanEvenCoefficientSubspace_iff]
  apply (mem_evenCoefficientSubspace_iff N _).2
  ext i
  simp [reverseCoefficients, centeredPowerVector]

theorem centeredPowerVector_one_mem_oddCoefficient
    (N : ℕ) :
    centeredPowerVector N 1 ∈ euclideanOddCoefficientSubspace N := by
  rw [mem_euclideanOddCoefficientSubspace_iff]
  apply (mem_oddCoefficientSubspace_iff N _).2
  ext i
  simp [reverseCoefficients, centeredPowerVector]

theorem centeredPowerVector_two_mem_evenCoefficient
    (N : ℕ) :
    centeredPowerVector N 2 ∈ euclideanEvenCoefficientSubspace N := by
  rw [mem_euclideanEvenCoefficientSubspace_iff]
  apply (mem_evenCoefficientSubspace_iff N _).2
  ext i
  simp [reverseCoefficients, centeredPowerVector]
  ring

/-- The exact two-dimensional candidate normal channel in the even parity
ambient sector. -/
def evenNormalSubspace
    (N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 1))) :=
  (ℂ ∙ centeredPowerVector N 0) ⊔
    (ℂ ∙ centeredPowerVector N 2)

/-- The exact one-dimensional candidate normal channel in the odd parity
ambient sector. -/
def oddNormalSubspace
    (N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 1))) :=
  ℂ ∙ centeredPowerVector N 1

theorem evenNormalSubspace_le_evenCoefficient
    (N : ℕ) :
    evenNormalSubspace N ≤ euclideanEvenCoefficientSubspace N := by
  apply sup_le
  · rw [Submodule.span_singleton_le_iff_mem]
    exact centeredPowerVector_zero_mem_evenCoefficient N
  · rw [Submodule.span_singleton_le_iff_mem]
    exact centeredPowerVector_two_mem_evenCoefficient N

theorem oddNormalSubspace_le_oddCoefficient
    (N : ℕ) :
    oddNormalSubspace N ≤ euclideanOddCoefficientSubspace N := by
  rw [oddNormalSubspace, Submodule.span_singleton_le_iff_mem]
  exact centeredPowerVector_one_mem_oddCoefficient N

theorem centeredPowerVector_zero_mem_evenBoundaryFlat_orthogonal
    (N : ℕ) :
    centeredPowerVector N 0 ∈ (euclideanEvenBoundaryFlatSubspace N)ᗮ := by
  rw [(euclideanEvenBoundaryFlatSubspace N).mem_orthogonal]
  intro x hx
  rw [inner_centeredPowerVector]
  have hflat :=
    ((mem_euclideanEvenBoundaryFlatSubspace_iff N x).mp hx).1
  exact ((mem_boundaryFlatSubspace_iff N _).mp hflat).1

theorem centeredPowerVector_two_mem_evenBoundaryFlat_orthogonal
    (N : ℕ) :
    centeredPowerVector N 2 ∈ (euclideanEvenBoundaryFlatSubspace N)ᗮ := by
  rw [(euclideanEvenBoundaryFlatSubspace N).mem_orthogonal]
  intro x hx
  rw [inner_centeredPowerVector]
  have hflat :=
    ((mem_euclideanEvenBoundaryFlatSubspace_iff N x).mp hx).1
  exact ((mem_boundaryFlatSubspace_iff N _).mp hflat).2.2

theorem centeredPowerVector_one_mem_oddBoundaryFlat_orthogonal
    (N : ℕ) :
    centeredPowerVector N 1 ∈ (euclideanOddBoundaryFlatSubspace N)ᗮ := by
  rw [(euclideanOddBoundaryFlatSubspace N).mem_orthogonal]
  intro x hx
  rw [inner_centeredPowerVector]
  have hflat :=
    ((mem_euclideanOddBoundaryFlatSubspace_iff N x).mp hx).1
  exact ((mem_boundaryFlatSubspace_iff N _).mp hflat).2.1

theorem evenNormalSubspace_le_evenBoundaryFlat_orthogonal
    (N : ℕ) :
    evenNormalSubspace N ≤ (euclideanEvenBoundaryFlatSubspace N)ᗮ := by
  apply sup_le
  · rw [Submodule.span_singleton_le_iff_mem]
    exact centeredPowerVector_zero_mem_evenBoundaryFlat_orthogonal N
  · rw [Submodule.span_singleton_le_iff_mem]
    exact centeredPowerVector_two_mem_evenBoundaryFlat_orthogonal N

theorem oddNormalSubspace_le_oddBoundaryFlat_orthogonal
    (N : ℕ) :
    oddNormalSubspace N ≤ (euclideanOddBoundaryFlatSubspace N)ᗮ := by
  rw [oddNormalSubspace, Submodule.span_singleton_le_iff_mem]
  exact centeredPowerVector_one_mem_oddBoundaryFlat_orthogonal N

/-- Exact even normal space inside the even reversal sector. -/
theorem evenBoundaryFlat_normal_eq_evenNormalSubspace
    (N : ℕ) :
    (euclideanEvenBoundaryFlatSubspace N)ᗮ ⊓
        euclideanEvenCoefficientSubspace N =
      evenNormalSubspace N := by
  apply le_antisymm
  · intro r hr
    rcases hr with ⟨hrorth, hreven⟩
    let S := evenNormalSubspace N
    let q : EuclideanSpace ℂ (Fin (2 * N + 1)) := S.starProjection r
    let s : EuclideanSpace ℂ (Fin (2 * N + 1)) := r - q
    have hqS : q ∈ S := by
      dsimp [q]
      change
        ((S.orthogonalProjectionOnto r : S) :
          EuclideanSpace ℂ (Fin (2 * N + 1))) ∈ S
      exact (S.orthogonalProjectionOnto r).property
    have hqeven :
        q ∈ euclideanEvenCoefficientSubspace N :=
      (evenNormalSubspace_le_evenCoefficient N) hqS
    have hqorth :
        q ∈ (euclideanEvenBoundaryFlatSubspace N)ᗮ :=
      (evenNormalSubspace_le_evenBoundaryFlat_orthogonal N) hqS
    have hsSorth : s ∈ Sᗮ := by
      dsimp [s, q]
      exact S.sub_starProjection_mem_orthogonal r
    have hseven :
        s ∈ euclideanEvenCoefficientSubspace N := by
      exact (euclideanEvenCoefficientSubspace N).sub_mem hreven hqeven
    have hsorth :
        s ∈ (euclideanEvenBoundaryFlatSubspace N)ᗮ := by
      exact ((euclideanEvenBoundaryFlatSubspace N)ᗮ).sub_mem hrorth hqorth
    have hp0S : centeredPowerVector N 0 ∈ S := by
      exact
        (show ℂ ∙ centeredPowerVector N 0 ≤ S from le_sup_left)
          (Submodule.mem_span_singleton_self (centeredPowerVector N 0))
    have hp2S : centeredPowerVector N 2 ∈ S := by
      exact
        (show ℂ ∙ centeredPowerVector N 2 ≤ S from le_sup_right)
          (Submodule.mem_span_singleton_self (centeredPowerVector N 2))
    have hs0 :
        centeredMoment N 0
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) s) = 0 := by
      have hi := (S.mem_orthogonal s).mp hsSorth
        (centeredPowerVector N 0) hp0S
      simpa only [inner_centeredPowerVector] using hi
    have hs2 :
        centeredMoment N 2
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) s) = 0 := by
      have hi := (S.mem_orthogonal s).mp hsSorth
        (centeredPowerVector N 2) hp2S
      simpa only [inner_centeredPowerVector] using hi
    have hsevenRaw :
        (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) s ∈
          evenCoefficientSubspace N :=
      (mem_euclideanEvenCoefficientSubspace_iff N s).mp hseven
    have hs1 :
        centeredMoment N 1
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) s) = 0 :=
      centeredMoment_one_eq_zero_of_even hsevenRaw
    have hsV : s ∈ euclideanEvenBoundaryFlatSubspace N := by
      rw [mem_euclideanEvenBoundaryFlatSubspace_iff]
      refine ⟨?_, hsevenRaw⟩
      rw [mem_boundaryFlatSubspace_iff]
      exact ⟨hs0, hs1, hs2⟩
    have hss : inner ℂ s s = 0 :=
      ((euclideanEvenBoundaryFlatSubspace N).mem_orthogonal s).mp
        hsorth s hsV
    have hszero : s = 0 := (inner_self_eq_zero).mp hss
    have hrq : r = q := by
      dsimp [s] at hszero
      exact sub_eq_zero.mp hszero
    rw [hrq]
    exact hqS
  · exact le_inf
      (evenNormalSubspace_le_evenBoundaryFlat_orthogonal N)
      (evenNormalSubspace_le_evenCoefficient N)

/-- Exact odd normal space inside the odd reversal sector. -/
theorem oddBoundaryFlat_normal_eq_oddNormalSubspace
    (N : ℕ) :
    (euclideanOddBoundaryFlatSubspace N)ᗮ ⊓
        euclideanOddCoefficientSubspace N =
      oddNormalSubspace N := by
  apply le_antisymm
  · intro r hr
    rcases hr with ⟨hrorth, hrodd⟩
    let S := oddNormalSubspace N
    let q : EuclideanSpace ℂ (Fin (2 * N + 1)) := S.starProjection r
    let s : EuclideanSpace ℂ (Fin (2 * N + 1)) := r - q
    have hqS : q ∈ S := by
      dsimp [q]
      change
        ((S.orthogonalProjectionOnto r : S) :
          EuclideanSpace ℂ (Fin (2 * N + 1))) ∈ S
      exact (S.orthogonalProjectionOnto r).property
    have hqodd :
        q ∈ euclideanOddCoefficientSubspace N :=
      (oddNormalSubspace_le_oddCoefficient N) hqS
    have hqorth :
        q ∈ (euclideanOddBoundaryFlatSubspace N)ᗮ :=
      (oddNormalSubspace_le_oddBoundaryFlat_orthogonal N) hqS
    have hsSorth : s ∈ Sᗮ := by
      dsimp [s, q]
      exact S.sub_starProjection_mem_orthogonal r
    have hsodd :
        s ∈ euclideanOddCoefficientSubspace N :=
      (euclideanOddCoefficientSubspace N).sub_mem hrodd hqodd
    have hsorth :
        s ∈ (euclideanOddBoundaryFlatSubspace N)ᗮ :=
      ((euclideanOddBoundaryFlatSubspace N)ᗮ).sub_mem hrorth hqorth
    have hp1S : centeredPowerVector N 1 ∈ S := by
      exact Submodule.mem_span_singleton_self (centeredPowerVector N 1)
    have hs1 :
        centeredMoment N 1
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) s) = 0 := by
      have hi := (S.mem_orthogonal s).mp hsSorth
        (centeredPowerVector N 1) hp1S
      simpa only [inner_centeredPowerVector] using hi
    have hsoddRaw :
        (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) s ∈
          oddCoefficientSubspace N :=
      (mem_euclideanOddCoefficientSubspace_iff N s).mp hsodd
    have hs0 :
        centeredMoment N 0
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) s) = 0 :=
      centeredMoment_zero_eq_zero_of_odd hsoddRaw
    have hs2 :
        centeredMoment N 2
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) s) = 0 :=
      centeredMoment_two_eq_zero_of_odd hsoddRaw
    have hsV : s ∈ euclideanOddBoundaryFlatSubspace N := by
      rw [mem_euclideanOddBoundaryFlatSubspace_iff]
      refine ⟨?_, hsoddRaw⟩
      rw [mem_boundaryFlatSubspace_iff]
      exact ⟨hs0, hs1, hs2⟩
    have hss : inner ℂ s s = 0 :=
      ((euclideanOddBoundaryFlatSubspace N).mem_orthogonal s).mp
        hsorth s hsV
    have hszero : s = 0 := (inner_self_eq_zero).mp hss
    have hrq : r = q := by
      dsimp [s] at hszero
      exact sub_eq_zero.mp hszero
    rw [hrq]
    exact hqS
  · exact le_inf
      (oddNormalSubspace_le_oddBoundaryFlat_orthogonal N)
      (oddNormalSubspace_le_oddCoefficient N)

/-- Coordinates of the Euclidean matrix action are the raw matrix-vector
product. -/
theorem canonicalSourceMatrix_toEuclideanLin_coordinates
    (L : ℝ) (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
        ((canonicalSourceMatrix L N).toEuclideanLin x) =
      canonicalSourceMatrix L N *ᵥ
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x) := by
  change
    WithLp.ofLp ((canonicalSourceMatrix L N).toEuclideanLin x) =
      canonicalSourceMatrix L N *ᵥ WithLp.ofLp x
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]

theorem canonicalSourceMatrix_toEuclideanLin_mem_evenCoefficient
    (L : ℝ) (N : ℕ)
    {x : EuclideanSpace ℂ (Fin (2 * N + 1))}
    (hx : x ∈ euclideanEvenCoefficientSubspace N) :
    (canonicalSourceMatrix L N).toEuclideanLin x ∈
      euclideanEvenCoefficientSubspace N := by
  rw [mem_euclideanEvenCoefficientSubspace_iff] at hx ⊢
  apply (mem_evenCoefficientSubspace_iff N _).2
  rw [canonicalSourceMatrix_toEuclideanLin_coordinates]
  rw [← canonicalSourceMatrix_mulVec_reverseCoefficients]
  rw [(mem_evenCoefficientSubspace_iff N _).mp hx]

theorem canonicalSourceMatrix_toEuclideanLin_mem_oddCoefficient
    (L : ℝ) (N : ℕ)
    {x : EuclideanSpace ℂ (Fin (2 * N + 1))}
    (hx : x ∈ euclideanOddCoefficientSubspace N) :
    (canonicalSourceMatrix L N).toEuclideanLin x ∈
      euclideanOddCoefficientSubspace N := by
  rw [mem_euclideanOddCoefficientSubspace_iff] at hx ⊢
  apply (mem_oddCoefficientSubspace_iff N _).2
  rw [canonicalSourceMatrix_toEuclideanLin_coordinates]
  rw [← canonicalSourceMatrix_mulVec_reverseCoefficients]
  rw [(mem_oddCoefficientSubspace_iff N _).mp hx]
  exact Matrix.mulVec_neg _ _

/-- Ambient residual of a compressed parity eigenmode. -/
def parityEigenResidual
    (p : ReversalParity) (L : ℝ) (N : ℕ) (lam : ℝ)
    (v : euclideanParityBoundaryFlatSubspace p N) :
    EuclideanSpace ℂ (Fin (2 * N + 1)) :=
  (canonicalSourceMatrix L N).toEuclideanLin
      (v : EuclideanSpace ℂ (Fin (2 * N + 1))) -
    (lam : ℂ) •
      (v : EuclideanSpace ℂ (Fin (2 * N + 1)))

theorem parityEigenResidual_mem_orthogonal
    (p : ReversalParity) (L : ℝ) (N : ℕ) (lam : ℝ)
    (v : euclideanParityBoundaryFlatSubspace p N)
    (hveig :
      parityCompressedCanonical p L N v = (lam : ℂ) • v) :
    parityEigenResidual p L N lam v ∈
      (euclideanParityBoundaryFlatSubspace p N)ᗮ := by
  let V := euclideanParityBoundaryFlatSubspace p N
  let y :=
    (canonicalSourceMatrix L N).toEuclideanLin
      (v : EuclideanSpace ℂ (Fin (2 * N + 1)))
  have horth := V.sub_starProjection_mem_orthogonal y
  have hproj :
      V.starProjection y =
        (lam : ℂ) •
          (v : EuclideanSpace ℂ (Fin (2 * N + 1))) := by
    change
      ((V.orthogonalProjectionOnto y : V) :
          EuclideanSpace ℂ (Fin (2 * N + 1))) =
        (lam : ℂ) •
          (v : EuclideanSpace ℂ (Fin (2 * N + 1)))
    exact congrArg Subtype.val hveig
  rw [hproj] at horth
  exact horth

theorem parityEigenResidual_mem_parityCoefficient
    (p : ReversalParity) (L : ℝ) (N : ℕ) (lam : ℝ)
    (v : euclideanParityBoundaryFlatSubspace p N) :
    parityEigenResidual p L N lam v ∈
      euclideanParityCoefficientSubspace p N := by
  cases p with
  | even =>
      have hv :
          (v : EuclideanSpace ℂ (Fin (2 * N + 1))) ∈
            euclideanEvenCoefficientSubspace N :=
        ((mem_euclideanEvenBoundaryFlatSubspace_iff N _).mp v.property).2
      exact (euclideanEvenCoefficientSubspace N).sub_mem
        (canonicalSourceMatrix_toEuclideanLin_mem_evenCoefficient L N hv)
        ((euclideanEvenCoefficientSubspace N).smul_mem (lam : ℂ) hv)
  | odd =>
      have hv :
          (v : EuclideanSpace ℂ (Fin (2 * N + 1))) ∈
            euclideanOddCoefficientSubspace N :=
        ((mem_euclideanOddBoundaryFlatSubspace_iff N _).mp v.property).2
      exact (euclideanOddCoefficientSubspace N).sub_mem
        (canonicalSourceMatrix_toEuclideanLin_mem_oddCoefficient L N hv)
        ((euclideanOddCoefficientSubspace N).smul_mem (lam : ℂ) hv)

/-- Explicit parity-specific KKT residual form. -/
def ParityKKTResidual
    (p : ReversalParity) (L : ℝ) (N : ℕ) (lam : ℝ)
    (v : euclideanParityBoundaryFlatSubspace p N) : Prop :=
  match p with
  | .even =>
      ∃ a0 a2 : ℂ,
        (canonicalSourceMatrix L N).toEuclideanLin
            (v : EuclideanSpace ℂ (Fin (2 * N + 1))) =
          (lam : ℂ) •
              (v : EuclideanSpace ℂ (Fin (2 * N + 1))) +
            a0 • centeredPowerVector N 0 +
            a2 • centeredPowerVector N 2
  | .odd =>
      ∃ a1 : ℂ,
        (canonicalSourceMatrix L N).toEuclideanLin
            (v : EuclideanSpace ℂ (Fin (2 * N + 1))) =
          (lam : ℂ) •
              (v : EuclideanSpace ℂ (Fin (2 * N + 1))) +
            a1 • centeredPowerVector N 1

theorem parityKKTResidual_of_eigenmode
    (p : ReversalParity) (L : ℝ) (N : ℕ) (lam : ℝ)
    (v : euclideanParityBoundaryFlatSubspace p N)
    (hveig :
      parityCompressedCanonical p L N v = (lam : ℂ) • v) :
    ParityKKTResidual p L N lam v := by
  have hrorth :=
    parityEigenResidual_mem_orthogonal p L N lam v hveig
  have hrpar :=
    parityEigenResidual_mem_parityCoefficient p L N lam v
  cases p with
  | even =>
      have hr :
          parityEigenResidual .even L N lam v ∈
            evenNormalSubspace N := by
        have hi :
            parityEigenResidual .even L N lam v ∈
              (euclideanEvenBoundaryFlatSubspace N)ᗮ ⊓
                euclideanEvenCoefficientSubspace N :=
          ⟨hrorth, hrpar⟩
        rw [evenBoundaryFlat_normal_eq_evenNormalSubspace N] at hi
        exact hi
      rw [evenNormalSubspace, Submodule.mem_sup] at hr
      rcases hr with ⟨y, hy, z, hz, hyz⟩
      rw [Submodule.mem_span_singleton] at hy
      rw [Submodule.mem_span_singleton] at hz
      rcases hy with ⟨a0, rfl⟩
      rcases hz with ⟨a2, rfl⟩
      refine ⟨a0, a2, ?_⟩
      dsimp [parityEigenResidual] at hyz
      have hadd := congrArg
        (fun t =>
          t + (lam : ℂ) •
            (v : EuclideanSpace ℂ (Fin (2 * N + 1)))) hyz.symm
      simpa [add_assoc, add_left_comm, add_comm] using hadd
  | odd =>
      have hr :
          parityEigenResidual .odd L N lam v ∈
            oddNormalSubspace N := by
        have hi :
            parityEigenResidual .odd L N lam v ∈
              (euclideanOddBoundaryFlatSubspace N)ᗮ ⊓
                euclideanOddCoefficientSubspace N :=
          ⟨hrorth, hrpar⟩
        rw [oddBoundaryFlat_normal_eq_oddNormalSubspace N] at hi
        exact hi
      rw [oddNormalSubspace, Submodule.mem_span_singleton] at hr
      rcases hr with ⟨a1, hr⟩
      refine ⟨a1, ?_⟩
      dsimp [parityEigenResidual] at hr
      have hadd := congrArg
        (fun t =>
          t + (lam : ℂ) •
            (v : EuclideanSpace ℂ (Fin (2 * N + 1)))) hr.symm
      simpa [add_assoc, add_left_comm, add_comm] using hadd

end Zeta23.CCM

#print axioms Zeta23.CCM.evenBoundaryFlat_normal_eq_evenNormalSubspace
#print axioms Zeta23.CCM.oddBoundaryFlat_normal_eq_oddNormalSubspace
#print axioms Zeta23.CCM.parityEigenResidual_mem_orthogonal
#print axioms Zeta23.CCM.parityKKTResidual_of_eigenmode
