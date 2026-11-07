import Zeta23.OPICARound4.ArithmeticFrontier.MomentSlices

/-!
# Pole-channel annihilation on the native carriers

The production theorems `canonicalPoleMatrix_mulVec_eq_zero_of_profiles` and
`canonicalPoleMatrix_mulVec_poleNeutralEven_eq_zero` already show that the
actual canonical pole matrix kills every vector orthogonal to both pole
profiles, and every even pole-neutral carrier vector. This module reuses them.
It adds the odd carrier, the sesquilinear statement, and the exact native
energy identity `Q = -arch - prime` on both pole-neutral carriers, hence on both
moment slices.

The identities keep every normalization of the production channels: the
Archimedean channel is the direct equation-(4.4) channel with its scalar terms,
and the prime channel contains every prime power. This is dependency
compression, not positivity. No sign of `-arch - prime` is asserted.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open CCM Matrix

/-- The even pole profile pairs to zero with every odd boundary-flat vector. -/
theorem poleEvenProfile_dot_oddBoundaryFlat_eq_zero (L : ℝ) (K : ℕ)
    (v : euclideanOddBoundaryFlatSubspace K) :
    poleEvenProfile L K ⬝ᵥ
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) (v : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
  have hvbf : (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
      (v : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈ oddBoundaryFlatSubspace K :=
    (mem_euclideanOddBoundaryFlatSubspace_iff K _).mp v.property
  have hodd := (mem_oddCoefficientSubspace_iff K _).mp hvbf.2
  rw [dotProduct_comm]
  exact dotProduct_eq_zero_of_reverse_odd_even K _ (poleEvenProfile L K) hodd
    (reverseCoefficients_poleEvenProfile L K)

/-- The actual canonical pole matrix annihilates every odd pole-neutral carrier
vector: the full output vector is zero. -/
theorem canonicalPoleMatrix_mulVec_poleNeutralOdd_eq_zero {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : poleNeutralOddSubspace L K) :
    canonicalPoleMatrix L K *ᵥ
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 :=
  canonicalPoleMatrix_mulVec_eq_zero_of_profiles hL K _
    (poleEvenProfile_dot_oddBoundaryFlat_eq_zero L K v.val)
    ((mem_poleNeutralOddSubspace L K v.val).mp v.property)

/-- Operator form on the even carrier. -/
theorem canonicalPole_toEuclideanLin_even_eq_zero {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    (canonicalPoleMatrix L K).toEuclideanLin (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 :=
  congrArg (WithLp.toLp 2) (canonicalPoleMatrix_mulVec_poleNeutralEven_eq_zero hL K u)

/-- Operator form on the odd carrier. -/
theorem canonicalPole_toEuclideanLin_odd_eq_zero {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : poleNeutralOddSubspace L K) :
    (canonicalPoleMatrix L K).toEuclideanLin (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 :=
  congrArg (WithLp.toLp 2) (canonicalPoleMatrix_mulVec_poleNeutralOdd_eq_zero hL K v)

/-- The pole sesquilinear form vanishes identically on the even carrier. -/
theorem canonicalPole_inner_even_eq_zero {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u w : poleNeutralEvenSubspace L K) :
    inner ℂ ((canonicalPoleMatrix L K).toEuclideanLin (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
      (w.val : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
  rw [canonicalPole_toEuclideanLin_even_eq_zero hL K u, inner_zero_left]

/-- The pole sesquilinear form vanishes identically on the odd carrier. -/
theorem canonicalPole_inner_odd_eq_zero {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v w : poleNeutralOddSubspace L K) :
    inner ℂ ((canonicalPoleMatrix L K).toEuclideanLin (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
      (w.val : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
  rw [canonicalPole_toEuclideanLin_odd_eq_zero hL K v, inner_zero_left]

private theorem source_toEuclideanLin_split (L : ℝ) (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hp : (canonicalPoleMatrix L K).toEuclideanLin x = 0) :
    (canonicalSourceMatrix L K).toEuclideanLin x =
      -((canonicalArchMatrix L K).toEuclideanLin x) - (canonicalPrimeMatrix L K).toEuclideanLin x := by
  rw [canonicalSourceMatrix_eq_pole_sub_arch_sub_prime, map_sub, map_sub, LinearMap.sub_apply,
    LinearMap.sub_apply, hp, zero_sub]

private theorem energy_split (L : ℝ) (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hp : (canonicalPoleMatrix L K).toEuclideanLin x = 0) :
    (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin x) x).re =
      -(inner ℂ ((canonicalArchMatrix L K).toEuclideanLin x) x).re -
        (inner ℂ ((canonicalPrimeMatrix L K).toEuclideanLin x) x).re := by
  rw [source_toEuclideanLin_split L K x hp, inner_sub_left, inner_neg_left, Complex.sub_re,
    Complex.neg_re]

/-- **Exact even native energy.** On the actual even pole-neutral carrier the
native self-energy is minus the direct Archimedean energy minus the prime
energy, with the unchanged production channels. -/
theorem evenNativeEnergy_eq_neg_arch_sub_prime {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    evenNativeEnergy L K u =
      -(inner ℂ ((canonicalArchMatrix L K).toEuclideanLin (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re -
        (inner ℂ ((canonicalPrimeMatrix L K).toEuclideanLin (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re := by
  unfold evenNativeEnergy
  rw [inner_poleNeutralEvenCompressedCanonical_self]
  exact energy_split L K _ (canonicalPole_toEuclideanLin_even_eq_zero hL K u)

/-- **Exact odd native energy.** -/
theorem oddNativeEnergy_eq_neg_arch_sub_prime {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : poleNeutralOddSubspace L K) :
    oddNativeEnergy L K v =
      -(inner ℂ ((canonicalArchMatrix L K).toEuclideanLin (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
          (v.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re -
        (inner ℂ ((canonicalPrimeMatrix L K).toEuclideanLin (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
          (v.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re := by
  unfold oddNativeEnergy
  rw [inner_poleNeutralOddCompressedCanonical_self]
  exact energy_split L K _ (canonicalPole_toEuclideanLin_odd_eq_zero hL K v)

/-- The even moment-slice lower bound is exactly a bound on `-arch - prime`. -/
theorem evenMomentSliceLowerBound_iff_arch_prime {L : ℝ} (hL : 0 < L) (K : ℕ) (ε : ℝ) :
    EvenMomentSliceLowerBound L K ε ↔ ∀ u : poleNeutralEvenSubspace L K, u ∈ evenMomentSlice L K →
      -ε * ‖u‖ ^ 2 ≤
        -(inner ℂ ((canonicalArchMatrix L K).toEuclideanLin (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
            (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re -
          (inner ℂ ((canonicalPrimeMatrix L K).toEuclideanLin (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
            (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re := by
  unfold EvenMomentSliceLowerBound
  simp only [← evenNativeEnergy_eq_neg_arch_sub_prime hL K]

/-- The odd moment-slice lower bound is exactly a bound on `-arch - prime`. -/
theorem oddMomentSliceLowerBound_iff_arch_prime {L : ℝ} (hL : 0 < L) (K : ℕ) (ε : ℝ) :
    OddMomentSliceLowerBound L K ε ↔ ∀ v : poleNeutralOddSubspace L K, v ∈ oddMomentSlice L K →
      -ε * ‖v‖ ^ 2 ≤
        -(inner ℂ ((canonicalArchMatrix L K).toEuclideanLin (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
            (v.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re -
          (inner ℂ ((canonicalPrimeMatrix L K).toEuclideanLin (v.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
            (v.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).re := by
  unfold OddMomentSliceLowerBound
  simp only [← oddNativeEnergy_eq_neg_arch_sub_prime hL K]

end Zeta23.OPICARound4.ArithmeticFrontier
