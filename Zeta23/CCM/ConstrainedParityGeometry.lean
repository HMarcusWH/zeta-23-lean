import Zeta23.CCM.ConstrainedParity
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PARITY-FLOW geometry

This module completes the algebraic parity decomposition of the exact
boundary-flat finite sector, identifies the centered-index operator as a
linear equivalence from the even constrained sector to the odd constrained
sector, derives the exact N-1 / N-1 parity dimensions, transports the sectors
to Euclidean space, and restricts the exact centered N-flow to each parity.

No spectral compression, Rayleigh minimizer, KKT equation, positivity theorem,
or RH claim is made here.
-/

/-- Even part for the centered reversal involution. -/
def evenPart
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    Fin (2 * N + 1) → ℂ :=
  fun i => (1 / 2 : ℂ) * (u i + u i.rev)

/-- Odd part for the centered reversal involution. -/
def oddPart
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    Fin (2 * N + 1) → ℂ :=
  fun i => (1 / 2 : ℂ) * (u i - u i.rev)

@[simp] theorem evenPart_add_oddPart
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    evenPart N u + oddPart N u = u := by
  ext i
  simp [evenPart, oddPart]
  ring

@[simp] theorem reverseCoefficients_evenPart
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    reverseCoefficients N (evenPart N u) = evenPart N u := by
  ext i
  simp [reverseCoefficients, evenPart, add_comm]

@[simp] theorem reverseCoefficients_oddPart
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    reverseCoefficients N (oddPart N u) = - oddPart N u := by
  ext i
  simp [reverseCoefficients, oddPart]
  ring

theorem evenPart_mem_boundaryFlatSubspace
    {N : ℕ} {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ boundaryFlatSubspace N) :
    evenPart N u ∈ boundaryFlatSubspace N := by
  have hru : reverseCoefficients N u ∈ boundaryFlatSubspace N :=
    reverseCoefficients_mem_boundaryFlatSubspace hu
  have hadd :
      u + reverseCoefficients N u ∈ boundaryFlatSubspace N :=
    (boundaryFlatSubspace N).add_mem hu hru
  have hsmul :
      (1 / 2 : ℂ) • (u + reverseCoefficients N u) ∈
        boundaryFlatSubspace N :=
    (boundaryFlatSubspace N).smul_mem (1 / 2 : ℂ) hadd
  have heq :
      evenPart N u =
        (1 / 2 : ℂ) • (u + reverseCoefficients N u) := by
    ext i
    simp [evenPart, reverseCoefficients, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact hsmul

theorem oddPart_mem_boundaryFlatSubspace
    {N : ℕ} {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ boundaryFlatSubspace N) :
    oddPart N u ∈ boundaryFlatSubspace N := by
  have hru : reverseCoefficients N u ∈ boundaryFlatSubspace N :=
    reverseCoefficients_mem_boundaryFlatSubspace hu
  have hsub :
      u - reverseCoefficients N u ∈ boundaryFlatSubspace N :=
    (boundaryFlatSubspace N).sub_mem hu hru
  have hsmul :
      (1 / 2 : ℂ) • (u - reverseCoefficients N u) ∈
        boundaryFlatSubspace N :=
    (boundaryFlatSubspace N).smul_mem (1 / 2 : ℂ) hsub
  have heq :
      oddPart N u =
        (1 / 2 : ℂ) • (u - reverseCoefficients N u) := by
    ext i
    simp [oddPart, reverseCoefficients, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact hsmul

theorem evenPart_mem_evenBoundaryFlatSubspace
    {N : ℕ} {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ boundaryFlatSubspace N) :
    evenPart N u ∈ evenBoundaryFlatSubspace N := by
  refine ⟨evenPart_mem_boundaryFlatSubspace hu, ?_⟩
  exact (mem_evenCoefficientSubspace_iff N (evenPart N u)).2
    (reverseCoefficients_evenPart N u)

theorem oddPart_mem_oddBoundaryFlatSubspace
    {N : ℕ} {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ boundaryFlatSubspace N) :
    oddPart N u ∈ oddBoundaryFlatSubspace N := by
  refine ⟨oddPart_mem_boundaryFlatSubspace hu, ?_⟩
  exact (mem_oddCoefficientSubspace_iff N (oddPart N u)).2
    (reverseCoefficients_oddPart N u)

/-- Even and odd constrained sectors meet only at zero. -/
theorem evenBoundaryFlatSubspace_inf_oddBoundaryFlatSubspace
    (N : ℕ) :
    evenBoundaryFlatSubspace N ⊓ oddBoundaryFlatSubspace N = ⊥ := by
  ext u
  constructor
  · intro hu
    rcases hu with ⟨he, ho⟩
    have hre : reverseCoefficients N u = u :=
      (mem_evenCoefficientSubspace_iff N u).mp he.2
    have hro : reverseCoefficients N u = -u :=
      (mem_oddCoefficientSubspace_iff N u).mp ho.2
    have huz : u = 0 := by
      have h : u = -u := hre.symm.trans hro
      ext i
      have hi : u i = -u i := by
        simpa only [Pi.neg_apply] using congrFun h i
      have hsum : u i + u i = 0 :=
        (eq_neg_iff_add_eq_zero.mp hi)
      have htwo : (2 : ℂ) * u i = 0 := by
        simpa [two_mul] using hsum
      exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    simpa [huz]
  · intro hu
    have huz : u = 0 := by simpa using hu
    subst u
    exact ⟨(evenBoundaryFlatSubspace N).zero_mem,
      (oddBoundaryFlatSubspace N).zero_mem⟩

/-- The full boundary-flat sector is the direct algebraic sum of its two
reversal parity sectors. -/
theorem evenBoundaryFlatSubspace_sup_oddBoundaryFlatSubspace
    (N : ℕ) :
    evenBoundaryFlatSubspace N ⊔ oddBoundaryFlatSubspace N =
      boundaryFlatSubspace N := by
  apply le_antisymm
  · exact sup_le inf_le_left inf_le_left
  · intro u hu
    have he := evenPart_mem_evenBoundaryFlatSubspace hu
    have ho := oddPart_mem_oddBoundaryFlatSubspace hu
    have he' :
        evenPart N u ∈
          evenBoundaryFlatSubspace N ⊔ oddBoundaryFlatSubspace N :=
      (show evenBoundaryFlatSubspace N ≤
        evenBoundaryFlatSubspace N ⊔ oddBoundaryFlatSubspace N from le_sup_left) he
    have ho' :
        oddPart N u ∈
          evenBoundaryFlatSubspace N ⊔ oddBoundaryFlatSubspace N :=
      (show oddBoundaryFlatSubspace N ≤
        evenBoundaryFlatSubspace N ⊔ oddBoundaryFlatSubspace N from le_sup_right) ho
    have hsum :
        evenPart N u + oddPart N u ∈
          evenBoundaryFlatSubspace N ⊔ oddBoundaryFlatSubspace N :=
      (evenBoundaryFlatSubspace N ⊔ oddBoundaryFlatSubspace N).add_mem he' ho'
    simpa using hsum

@[simp] theorem centeredIndex_eq_zero_iff
    (N : ℕ) (i : Fin (2 * N + 1)) :
    centeredIndex N i = 0 ↔ i = boundaryFlatZeroIndex N := by
  constructor
  · intro h
    apply Fin.ext
    simp [centeredIndex, boundaryFlatZeroIndex] at h ⊢
    omega
  · rintro rfl
    simp

@[simp] theorem boundaryFlatZeroIndex_rev
    (N : ℕ) :
    (boundaryFlatZeroIndex N).rev = boundaryFlatZeroIndex N := by
  apply Fin.ext
  simp [boundaryFlatZeroIndex, Fin.val_rev]
  omega

theorem centeredIndex_ne_zero_of_ne_zeroIndex
    (N : ℕ) {i : Fin (2 * N + 1)}
    (hi : i ≠ boundaryFlatZeroIndex N) :
    centeredIndex N i ≠ 0 := by
  simpa [centeredIndex_eq_zero_iff N i] using hi

/-- The centered-index operator restricted from the even constrained sector
to the odd constrained sector. -/
def evenToOddIndexLinearMap
    (N : ℕ) :
    evenBoundaryFlatSubspace N →ₗ[ℂ] oddBoundaryFlatSubspace N where
  toFun := fun u => by
    let w := indexMatrix N *ᵥ (u : Fin (2 * N + 1) → ℂ)
    have hflat : (u : Fin (2 * N + 1) → ℂ) ∈ boundaryFlatSubspace N :=
      u.property.1
    have heven : (u : Fin (2 * N + 1) → ℂ) ∈ evenCoefficientSubspace N :=
      u.property.2
    have hwodd :
        reverseCoefficients N w = -w := by
      dsimp [w]
      rw [reverseCoefficients_indexMatrix_mulVec]
      rw [(mem_evenCoefficientSubspace_iff N _).mp heven]
    have hbf : BoundaryFlatCoefficients N (u : Fin (2 * N + 1) → ℂ) :=
      (mem_boundaryFlatSubspace_iff N _).mp hflat
    have hw0 : centeredMoment N 0 w = 0 := by
      dsimp [w]
      rw [centeredMoment_indexMatrix_mulVec]
      exact hbf.2.1
    have hw1 : centeredMoment N 1 w = 0 := by
      dsimp [w]
      rw [centeredMoment_indexMatrix_mulVec]
      exact hbf.2.2
    have hw2 : centeredMoment N 2 w = 0 := by
      have hp := centeredMoment_reverseCoefficients N 2 w
      rw [hwodd] at hp
      have hneg :
          centeredMoment N 2 (-w) = -centeredMoment N 2 w := by
        simp [centeredMoment]
      rw [hneg] at hp
      norm_num at hp
      let m := centeredMoment N 2 w
      have hpm : -m = m := by simpa [m] using hp
      have hsum : m + m = 0 := by
        calc
          m + m = -m + m := by rw [hpm]
          _ = 0 := by ring
      have htwo : (2 : ℂ) * m = 0 := by
        simpa [two_mul] using hsum
      have hm : m = 0 :=
        (mul_eq_zero.mp htwo).resolve_left (by norm_num)
      simpa [m] using hm
    have hwflat : w ∈ boundaryFlatSubspace N := by
      rw [mem_boundaryFlatSubspace_iff]
      exact ⟨hw0, hw1, hw2⟩
    exact ⟨w, hwflat, (mem_oddCoefficientSubspace_iff N w).2 hwodd⟩
  map_add' := by
    intro u v
    apply Subtype.ext
    simp [Matrix.mulVec_add]
  map_smul' := by
    intro c u
    apply Subtype.ext
    simp [Matrix.mulVec_smul]

/-- The centered-index restriction is injective on the even constrained
sector.  Boundary-flatness removes the one ambient zero-index kernel. -/
theorem evenToOddIndexLinearMap_injective
    (N : ℕ) :
    Function.Injective (evenToOddIndexLinearMap N) := by
  intro u v huv
  apply Subtype.ext
  have huv_val :
      ((evenToOddIndexLinearMap N u : oddBoundaryFlatSubspace N) :
        Fin (2 * N + 1) → ℂ) =
      ((evenToOddIndexLinearMap N v : oddBoundaryFlatSubspace N) :
        Fin (2 * N + 1) → ℂ) :=
    congrArg (fun z : oddBoundaryFlatSubspace N =>
      (z : Fin (2 * N + 1) → ℂ)) huv
  have hD :
      indexMatrix N *ᵥ ((u : Fin (2 * N + 1) → ℂ) -
        (v : Fin (2 * N + 1) → ℂ)) = 0 := by
    ext i
    have hi := congrFun huv_val i
    change (indexMatrix N *ᵥ (u : Fin (2 * N + 1) → ℂ)) i =
      (indexMatrix N *ᵥ (v : Fin (2 * N + 1) → ℂ)) i at hi
    rw [Matrix.mulVec_sub]
    exact sub_eq_zero.mpr hi
  let z : Fin (2 * N + 1) → ℂ :=
    (u : Fin (2 * N + 1) → ℂ) - (v : Fin (2 * N + 1) → ℂ)
  have hzflat : z ∈ boundaryFlatSubspace N :=
    (boundaryFlatSubspace N).sub_mem u.property.1 v.property.1
  have hnoncenter :
      ∀ i : Fin (2 * N + 1),
        i ≠ boundaryFlatZeroIndex N → z i = 0 := by
    intro i hi
    have hcoord := congrFun hD i
    rw [indexMatrix_mulVec_apply] at hcoord
    have hd : ((centeredIndex N i : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast centeredIndex_ne_zero_of_ne_zeroIndex N hi
    exact (mul_eq_zero.mp hcoord).resolve_left hd
  have hz0 : z (boundaryFlatZeroIndex N) = 0 := by
    have hsum : ∑ i, z i = 0 :=
      sum_eq_zero_of_boundaryFlat
        ((mem_boundaryFlatSubspace_iff N z).mp hzflat)
    rw [Finset.sum_eq_single (boundaryFlatZeroIndex N)] at hsum
    · exact hsum
    · intro b hb hne
      exact hnoncenter b hne
    · simp
  ext i
  by_cases hi : i = boundaryFlatZeroIndex N
  · subst i
    apply sub_eq_zero.mp
    change z (boundaryFlatZeroIndex N) = 0
    exact hz0
  · apply sub_eq_zero.mp
    change z i = 0
    exact hnoncenter i hi

/-- Explicit primitive of an odd vector under the centered-index operator.
The central coefficient is the unique correction that enforces moment zero. -/
def oddIndexPrimitive
    (N : ℕ) (v : Fin (2 * N + 1) → ℂ) :
    Fin (2 * N + 1) → ℂ :=
  let z := boundaryFlatZeroIndex N
  let c :=
    - ∑ i ∈ Finset.univ.erase z,
        v i / ((centeredIndex N i : ℤ) : ℂ)
  fun i =>
    if i = z then c
    else v i / ((centeredIndex N i : ℤ) : ℂ)

theorem oddIndexPrimitive_even
    (N : ℕ) {v : Fin (2 * N + 1) → ℂ}
    (hvodd : reverseCoefficients N v = -v) :
    reverseCoefficients N (oddIndexPrimitive N v) =
      oddIndexPrimitive N v := by
  ext i
  by_cases hi : i = boundaryFlatZeroIndex N
  · subst i
    simp [reverseCoefficients, oddIndexPrimitive, boundaryFlatZeroIndex_rev]
  · have hirev : i.rev ≠ boundaryFlatZeroIndex N := by
      intro h
      apply hi
      have h' := congrArg Fin.rev h
      simpa [boundaryFlatZeroIndex_rev] using h'
    have hvi := congrFun hvodd i
    simp only [reverseCoefficients, Pi.neg_apply] at hvi
    simp [reverseCoefficients, oddIndexPrimitive, hi, hirev, hvi]

theorem indexMatrix_mulVec_oddIndexPrimitive
    (N : ℕ) {v : Fin (2 * N + 1) → ℂ}
    (hvodd : reverseCoefficients N v = -v) :
    indexMatrix N *ᵥ oddIndexPrimitive N v = v := by
  ext i
  rw [indexMatrix_mulVec_apply]
  by_cases hi : i = boundaryFlatZeroIndex N
  · subst i
    have hv0 : v (boundaryFlatZeroIndex N) = 0 := by
      have h := congrFun hvodd (boundaryFlatZeroIndex N)
      simp only [reverseCoefficients, boundaryFlatZeroIndex_rev, Pi.neg_apply] at h
      linear_combination (1 / 2 : ℂ) * h
    simp [oddIndexPrimitive, hv0]
  · have hd : ((centeredIndex N i : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast centeredIndex_ne_zero_of_ne_zeroIndex N hi
    rw [show oddIndexPrimitive N v i =
      v i / ((centeredIndex N i : ℤ) : ℂ) by
        simp [oddIndexPrimitive, hi]]
    field_simp [hd]

theorem centeredMoment_zero_oddIndexPrimitive
    (N : ℕ) (v : Fin (2 * N + 1) → ℂ) :
    centeredMoment N 0 (oddIndexPrimitive N v) = 0 := by
  rw [centeredMoment_zero_eq_sum]
  let z := boundaryFlatZeroIndex N
  have hzmem : z ∈ (Finset.univ : Finset (Fin (2 * N + 1))) := by simp
  rw [← Finset.sum_erase_add _ _ hzmem]
  have herase :
      ∑ i ∈ (Finset.univ.erase z), oddIndexPrimitive N v i =
        ∑ i ∈ (Finset.univ.erase z),
          v i / ((centeredIndex N i : ℤ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiz : i ≠ z := Finset.ne_of_mem_erase hi
    simp [oddIndexPrimitive, z, hiz]
  rw [herase]
  simp [oddIndexPrimitive, z]

theorem oddIndexPrimitive_mem_boundaryFlatSubspace
    (N : ℕ) {v : Fin (2 * N + 1) → ℂ}
    (hvflat : v ∈ boundaryFlatSubspace N)
    (hvodd : reverseCoefficients N v = -v) :
    oddIndexPrimitive N v ∈ boundaryFlatSubspace N := by
  rw [mem_boundaryFlatSubspace_iff]
  have hvbf := (mem_boundaryFlatSubspace_iff N v).mp hvflat
  have hD := indexMatrix_mulVec_oddIndexPrimitive N hvodd
  refine ⟨centeredMoment_zero_oddIndexPrimitive N v, ?_, ?_⟩
  · have hs := centeredMoment_indexMatrix_mulVec N 0 (oddIndexPrimitive N v)
    rw [hD] at hs
    exact hs.symm.trans hvbf.1
  · have hs := centeredMoment_indexMatrix_mulVec N 1 (oddIndexPrimitive N v)
    rw [hD] at hs
    exact hs.symm.trans hvbf.2.1

/-- The even-to-odd centered-index restriction is surjective. -/
theorem evenToOddIndexLinearMap_surjective
    (N : ℕ) :
    Function.Surjective (evenToOddIndexLinearMap N) := by
  intro v
  let u := oddIndexPrimitive N (v : Fin (2 * N + 1) → ℂ)
  have hvflat : (v : Fin (2 * N + 1) → ℂ) ∈ boundaryFlatSubspace N :=
    v.property.1
  have hvodd :
      reverseCoefficients N (v : Fin (2 * N + 1) → ℂ) =
        -(v : Fin (2 * N + 1) → ℂ) :=
    (mem_oddCoefficientSubspace_iff N _).mp v.property.2
  have huflat : u ∈ boundaryFlatSubspace N :=
    oddIndexPrimitive_mem_boundaryFlatSubspace N hvflat hvodd
  have hueven :
      u ∈ evenCoefficientSubspace N := by
    exact (mem_evenCoefficientSubspace_iff N u).2
      (oddIndexPrimitive_even N hvodd)
  refine ⟨⟨u, huflat, hueven⟩, ?_⟩
  apply Subtype.ext
  exact indexMatrix_mulVec_oddIndexPrimitive N hvodd

/-- Canonical complex-linear equivalence between the two constrained parity
sectors, induced by the centered-index operator. -/
def evenOddBoundaryFlatLinearEquiv
    (N : ℕ) :
    evenBoundaryFlatSubspace N ≃ₗ[ℂ] oddBoundaryFlatSubspace N :=
  LinearEquiv.ofBijective
    (evenToOddIndexLinearMap N)
    ⟨evenToOddIndexLinearMap_injective N,
      evenToOddIndexLinearMap_surjective N⟩

theorem finrank_even_eq_finrank_odd
    (N : ℕ) :
    Module.finrank ℂ (evenBoundaryFlatSubspace N) =
      Module.finrank ℂ (oddBoundaryFlatSubspace N) :=
  LinearEquiv.finrank_eq (evenOddBoundaryFlatLinearEquiv N)

/-- Exact parity dimensions of the raw constrained sector. -/
theorem finrank_evenBoundaryFlatSubspace
    (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (evenBoundaryFlatSubspace N) = N - 1 := by
  have hdim :=
    Submodule.finrank_sup_add_finrank_inf_eq
      (evenBoundaryFlatSubspace N) (oddBoundaryFlatSubspace N)
  rw [evenBoundaryFlatSubspace_sup_oddBoundaryFlatSubspace,
    evenBoundaryFlatSubspace_inf_oddBoundaryFlatSubspace,
    finrank_bot, add_zero, finrank_boundaryFlatSubspace N hN] at hdim
  have heq := finrank_even_eq_finrank_odd N
  omega

theorem finrank_oddBoundaryFlatSubspace
    (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (oddBoundaryFlatSubspace N) = N - 1 := by
  rw [← finrank_even_eq_finrank_odd N]
  exact finrank_evenBoundaryFlatSubspace N hN

/-- Euclidean copy of the even constrained sector. -/
def euclideanEvenBoundaryFlatSubspace
    (N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 1))) :=
  (evenBoundaryFlatSubspace N).comap
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).toLinearEquiv.toLinearMap

/-- Euclidean copy of the odd constrained sector. -/
def euclideanOddBoundaryFlatSubspace
    (N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 1))) :=
  (oddBoundaryFlatSubspace N).comap
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).toLinearEquiv.toLinearMap

@[simp] theorem mem_euclideanEvenBoundaryFlatSubspace_iff
    (N : ℕ) (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    x ∈ euclideanEvenBoundaryFlatSubspace N ↔
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x ∈
        evenBoundaryFlatSubspace N := Iff.rfl

@[simp] theorem mem_euclideanOddBoundaryFlatSubspace_iff
    (N : ℕ) (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    x ∈ euclideanOddBoundaryFlatSubspace N ↔
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x ∈
        oddBoundaryFlatSubspace N := Iff.rfl

theorem finrank_euclideanEvenBoundaryFlatSubspace
    (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (euclideanEvenBoundaryFlatSubspace N) = N - 1 := by
  have hmap :
      euclideanEvenBoundaryFlatSubspace N =
        (evenBoundaryFlatSubspace N).map
          (EuclideanSpace.equiv
            (Fin (2 * N + 1)) ℂ).symm.toLinearEquiv.toLinearMap := by
    simpa [euclideanEvenBoundaryFlatSubspace] using
      (Submodule.comap_equiv_eq_map_symm
        (EuclideanSpace.equiv
          (Fin (2 * N + 1)) ℂ).toLinearEquiv
        (evenBoundaryFlatSubspace N))
  rw [hmap, LinearEquiv.finrank_map_eq]
  exact finrank_evenBoundaryFlatSubspace N hN

theorem finrank_euclideanOddBoundaryFlatSubspace
    (N : ℕ) (hN : 1 ≤ N) :
    Module.finrank ℂ (euclideanOddBoundaryFlatSubspace N) = N - 1 := by
  have hmap :
      euclideanOddBoundaryFlatSubspace N =
        (oddBoundaryFlatSubspace N).map
          (EuclideanSpace.equiv
            (Fin (2 * N + 1)) ℂ).symm.toLinearEquiv.toLinearMap := by
    simpa [euclideanOddBoundaryFlatSubspace] using
      (Submodule.comap_equiv_eq_map_symm
        (EuclideanSpace.equiv
          (Fin (2 * N + 1)) ℂ).toLinearEquiv
        (oddBoundaryFlatSubspace N))
  rw [hmap, LinearEquiv.finrank_map_eq]
  exact finrank_oddBoundaryFlatSubspace N hN

/-- Exact centered Euclidean extension preserves the even constrained sector. -/
theorem euclideanCenteredZeroExtend_mem_euclideanEvenBoundaryFlatSubspace
    {N M : ℕ} (hNM : N ≤ M)
    {x : EuclideanSpace ℂ (Fin (2 * N + 1))}
    (hx : x ∈ euclideanEvenBoundaryFlatSubspace N) :
    euclideanCenteredZeroExtend hNM x ∈
      euclideanEvenBoundaryFlatSubspace M := by
  rw [mem_euclideanEvenBoundaryFlatSubspace_iff] at hx ⊢
  rcases hx with ⟨hxflat, hxeven⟩
  refine ⟨centeredZeroExtend_mem_boundaryFlatSubspace hNM hxflat, ?_⟩
  have hxeven' :
      reverseCoefficients N
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x) =
        (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x :=
    (mem_evenCoefficientSubspace_iff N _).1 hxeven
  apply (mem_evenCoefficientSubspace_iff M _).2
  rw [euclideanCenteredZeroExtend_coordinates]
  rw [← centeredZeroExtend_reverseCoefficients hNM]
  rw [hxeven']

/-- Exact centered Euclidean extension preserves the odd constrained sector. -/
theorem euclideanCenteredZeroExtend_mem_euclideanOddBoundaryFlatSubspace
    {N M : ℕ} (hNM : N ≤ M)
    {x : EuclideanSpace ℂ (Fin (2 * N + 1))}
    (hx : x ∈ euclideanOddBoundaryFlatSubspace N) :
    euclideanCenteredZeroExtend hNM x ∈
      euclideanOddBoundaryFlatSubspace M := by
  rw [mem_euclideanOddBoundaryFlatSubspace_iff] at hx ⊢
  rcases hx with ⟨hxflat, hxodd⟩
  refine ⟨centeredZeroExtend_mem_boundaryFlatSubspace hNM hxflat, ?_⟩
  have hxodd' :
      reverseCoefficients N
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x) =
        -((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x) :=
    (mem_oddCoefficientSubspace_iff N _).1 hxodd
  apply (mem_oddCoefficientSubspace_iff M _).2
  rw [euclideanCenteredZeroExtend_coordinates]
  rw [← centeredZeroExtend_reverseCoefficients hNM]
  rw [hxodd']
  exact map_neg (centeredZeroExtendLinearMap hNM)
    ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x)

end Zeta23.CCM

#print axioms Zeta23.CCM.evenBoundaryFlatSubspace_sup_oddBoundaryFlatSubspace
#print axioms Zeta23.CCM.evenOddBoundaryFlatLinearEquiv
#print axioms Zeta23.CCM.finrank_evenBoundaryFlatSubspace
#print axioms Zeta23.CCM.finrank_oddBoundaryFlatSubspace
#print axioms Zeta23.CCM.finrank_euclideanEvenBoundaryFlatSubspace
#print axioms Zeta23.CCM.finrank_euclideanOddBoundaryFlatSubspace
#print axioms Zeta23.CCM.euclideanCenteredZeroExtend_mem_euclideanEvenBoundaryFlatSubspace
#print axioms Zeta23.CCM.euclideanCenteredZeroExtend_mem_euclideanOddBoundaryFlatSubspace