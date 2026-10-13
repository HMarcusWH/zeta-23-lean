import Zeta23.CCM.ParitySourceMomentFourRigidity

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

/-!
Native elementary-pole kernels on the existing legal parity carriers.

The profiles here are the existing `poleEvenProfile` and `poleOddProfile`;
no replacement source or matrix is introduced. The index equivalence is
algebraic and carries no unitary, spectral, or positivity assertion.

This module supplies the carrier part of M07. Physical moment equivalence,
normal nonvanishing, dimensions, and the corrected compressed intertwining
remain separate obligations.
-/

/-- Native even elementary-pole functional on coefficient Euclidean space. -/
def canonicalPoleEvenFunctional (L : ℝ) (K : ℕ) :
    EuclideanSpace ℂ (Fin (2 * K + 1)) →ₗ[ℂ] ℂ where
  toFun x := ∑ i, poleEvenProfile L K i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    congr 1
    funext i
    ring

/-- Native odd elementary-pole functional on coefficient Euclidean space. -/
def canonicalPoleOddFunctional (L : ℝ) (K : ℕ) :
    EuclideanSpace ℂ (Fin (2 * K + 1)) →ₗ[ℂ] ℂ where
  toFun x := ∑ i, poleOddProfile L K i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    congr 1
    funext i
    ring

/-- The even legal carrier with its native elementary-pole condition. -/
def poleNeutralEvenSubspace (L : ℝ) (K : ℕ) :
    Submodule ℂ (euclideanEvenBoundaryFlatSubspace K) :=
  LinearMap.ker ((canonicalPoleEvenFunctional L K).comp
    (euclideanEvenBoundaryFlatSubspace K).subtype)

/-- The odd legal carrier with its native elementary-pole condition. -/
def poleNeutralOddSubspace (L : ℝ) (K : ℕ) :
    Submodule ℂ (euclideanOddBoundaryFlatSubspace K) :=
  LinearMap.ker ((canonicalPoleOddFunctional L K).comp
    (euclideanOddBoundaryFlatSubspace K).subtype)

@[simp] theorem mem_poleNeutralEvenSubspace (L : ℝ) (K : ℕ)
    (u : euclideanEvenBoundaryFlatSubspace K) :
    u ∈ poleNeutralEvenSubspace L K ↔
      canonicalPoleEvenFunctional L K u = 0 := Iff.rfl

@[simp] theorem mem_poleNeutralOddSubspace (L : ℝ) (K : ℕ)
    (u : euclideanOddBoundaryFlatSubspace K) :
    u ∈ poleNeutralOddSubspace L K ↔
      canonicalPoleOddFunctional L K u = 0 := Iff.rfl

/-- Exact coefficient identity for the native pole profiles. -/
theorem poleOddProfile_mul_centeredIndex {L : ℝ} (hL : 0 < L)
    (K : ℕ) (i : Fin (2 * K + 1)) :
    poleOddProfile L K i * (centeredIndex K i : ℂ) =
      ((1 / (4 * Real.pi) : ℝ) : ℂ) -
        ((L / (4 * Real.pi) : ℝ) : ℂ) * poleEvenProfile L K i := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hd := ne_of_gt (poleProfileDenominator_pos hL (centeredIndex K i))
  have hr :
      poleOddProfileReal (centeredIndex K i) L * (centeredIndex K i : ℝ) =
        1 / (4 * Real.pi) -
          (L / (4 * Real.pi)) * poleEvenProfileReal (centeredIndex K i) L := by
    unfold poleOddProfileReal poleEvenProfileReal
    field_simp [hp, hd]
    unfold poleProfileDenominator
    ring
  exact_mod_cast hr

/-- Native pole-neutrality is preserved by the legal centered-index map.
The zeroth-moment constraint is essential to this exact identity. -/
theorem canonicalPoleOddFunctional_evenIndex {L : ℝ} (hL : 0 < L)
    (K : ℕ) (u : euclideanEvenBoundaryFlatSubspace K) :
    canonicalPoleOddFunctional L K (euclideanEvenToOddIndexLinearMap K u) =
      -((L / (4 * Real.pi) : ℝ) : ℂ) * canonicalPoleEvenFunctional L K u := by
  have hzero : ∑ i, u.val i = 0 := by
    have hm := (evenBoundaryFlatRawCoefficients_boundaryFlat K u).1
    simpa [centeredMoment, evenBoundaryFlatRawCoefficients] using hm
  have hcoord : ∀ i,
      (euclideanEvenToOddIndexLinearMap K u).val i =
        (centeredIndex K i : ℂ) * u.val i := by
    intro i
    have hc := congrFun (euclideanIndexLinearMap_coordinates K u.val) i
    simpa [indexMatrix_mulVec_apply] using hc
  change (∑ i, poleOddProfile L K i * (euclideanEvenToOddIndexLinearMap K u).val i) = _
  simp_rw [hcoord, ← mul_assoc, poleOddProfile_mul_centeredIndex hL]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, mul_zero, zero_sub,
    ← Finset.mul_sum]
  rfl

theorem poleNeutral_evenIndex_mem {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    euclideanEvenToOddIndexLinearMap K u.val ∈ poleNeutralOddSubspace L K := by
  rw [mem_poleNeutralOddSubspace, canonicalPoleOddFunctional_evenIndex hL]
  have hu := (mem_poleNeutralEvenSubspace L K u.val).mp u.property
  rw [hu, mul_zero]

/-- The actual legal index map restricted to the native pole kernels. -/
def poleNeutralIndexLinearMap {L : ℝ} (hL : 0 < L) (K : ℕ) :
    poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K where
  toFun u := ⟨euclideanEvenToOddIndexLinearMap K u.val,
    poleNeutral_evenIndex_mem hL K u⟩
  map_add' u v := by ext; simp
  map_smul' c u := by ext; simp

theorem poleNeutralIndexLinearMap_injective {L : ℝ} (hL : 0 < L) (K : ℕ) :
    Function.Injective (poleNeutralIndexLinearMap hL K) := by
  intro u v huv
  apply Subtype.ext
  apply euclideanEvenToOddIndexLinearMap_injective K
  exact congrArg Subtype.val huv

theorem poleNeutralIndexLinearMap_surjective {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K) :
    Function.Surjective (poleNeutralIndexLinearMap hL K) := by
  intro w
  obtain ⟨u, hu⟩ := euclideanEvenToOddIndexLinearMap_surjective K hK w.val
  have hwu := (mem_poleNeutralOddSubspace L K w.val).mp w.property
  rw [← hu, canonicalPoleOddFunctional_evenIndex hL] at hwu
  have hc : -((L / (4 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (div_ne_zero hL.ne' (by positivity)))
  have humem : u ∈ poleNeutralEvenSubspace L K := by
    rw [mem_poleNeutralEvenSubspace]
    exact (mul_eq_zero.mp hwu).resolve_left hc
  refine ⟨⟨u, humem⟩, ?_⟩
  apply Subtype.ext
  exact hu

/-- Restricted centered-index equivalence between the native pole kernels. -/
def poleNeutralIndexEquiv {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K) :
    poleNeutralEvenSubspace L K ≃ₗ[ℂ] poleNeutralOddSubspace L K :=
  LinearEquiv.ofBijective (poleNeutralIndexLinearMap hL K)
    ⟨poleNeutralIndexLinearMap_injective hL K,
      poleNeutralIndexLinearMap_surjective hL K hK⟩

/-- The actual canonical pole matrix annihilates the simultaneous native
elementary-pole kernels. This is a vector identity, with no positivity claim. -/
theorem canonicalPoleMatrix_mulVec_eq_zero_of_profiles {L : ℝ} (hL : 0 < L)
    (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (he : poleEvenProfile L K ⬝ᵥ u = 0)
    (ho : poleOddProfile L K ⬝ᵥ u = 0) :
    canonicalPoleMatrix L K *ᵥ u = 0 := by
  rw [canonicalPoleMatrix_eq_rankTwoProfiles hL K, smul_mulVec,
    sub_mulVec, complex_vecMulVec_mulVec, complex_vecMulVec_mulVec, he, ho]
  simp

/-- On the exact native pole kernels, the unchanged canonical source action
is minus its Archimedean and prime actions. -/
theorem canonicalSourceMatrix_mulVec_eq_negative_arch_prime_of_profiles
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (he : poleEvenProfile L K ⬝ᵥ u = 0)
    (ho : poleOddProfile L K ⬝ᵥ u = 0) :
    canonicalSourceMatrix L K *ᵥ u =
      -(canonicalArchMatrix L K *ᵥ u) - canonicalPrimeMatrix L K *ᵥ u := by
  rw [canonicalSourceMatrix_eq_pole_sub_arch_sub_prime, sub_mulVec, sub_mulVec,
    canonicalPoleMatrix_mulVec_eq_zero_of_profiles hL K u he ho, zero_sub]

end Zeta23.CCM

#print axioms Zeta23.CCM.poleOddProfile_mul_centeredIndex
#print axioms Zeta23.CCM.canonicalPoleOddFunctional_evenIndex
#print axioms Zeta23.CCM.poleNeutralIndexLinearMap_injective
#print axioms Zeta23.CCM.poleNeutralIndexLinearMap_surjective
#print axioms Zeta23.CCM.canonicalPoleMatrix_mulVec_eq_zero_of_profiles
#print axioms Zeta23.CCM.canonicalSourceMatrix_mulVec_eq_negative_arch_prime_of_profiles
