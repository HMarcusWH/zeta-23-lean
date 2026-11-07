import Zeta23.OPICARound4.RegularCells.NativePrimeGerms
import Zeta23.OPICARound4.RegularCells.NativeParityZeroPencils

noncomputable section
namespace Zeta23.OPICARound4.NativeParityPencils
open CCM RegularCells NativeParitySeparation PrimeSourceLaurent PrimeSourceGerms PrimeIsolation
open scoped BigOperators

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup

theorem native_zero_single_prime_pencil (Q K : ℕ) (p : boundedPrimeSet Q)
    (hQ : Q < p.val^2) (theta : ℝ) :
    nativePencilSylvester (E := zeroCarrier .even K) (F := zeroCarrier .odd K)
      (frameEnergy .even K 0 (formalScaledSourceMatrix Q 0
        (singlePrimePhase (boundedPrimeSet Q) p (circlePhase theta)) K))
      (frameGram .even K 0)
      (frameEnergy .odd K 0 (formalScaledSourceMatrix Q 0
        (singlePrimePhase (boundedPrimeSet Q) p (circlePhase theta)) K))
      (frameGram .odd K 0) =
        (4 * (isolatedPrimeCoefficient p.val : ℂ)) • nativeSylvester
          (E := nativeLimitingEvenCarrier K) (F := nativeLimitingOddCarrier K)
          (nativeWeightedCompression K (nativeLimitingEvenCarrier K)
            (nativeCosineWeights K theta)).toLinearMap
          (nativeWeightedCompression K (nativeLimitingOddCarrier K)
            (nativeCosineWeights K theta)).toLinearMap := by
  rw [formalScaledSourceMatrix_single_zero Q K p hQ theta]
  simp only [frameEnergy_smul, frameEnergy_sub, frameEnergy_zero_cosine,
    frameEnergy_identity, frameGram_zero]
  ext X : 1
  ext x : 1
  let Ce := (nativeWeightedCompression K (nativeLimitingEvenCarrier K)
    (nativeCosineWeights K theta)).toLinearMap
  let Co := (nativeWeightedCompression K (nativeLimitingOddCarrier K)
    (nativeCosineWeights K theta)).toLinearMap
  let c : ℂ := isolatedPrimeCoefficient p.val
  change c • ((2 : ℂ) • Co (X ((2 : ℂ) • x)) - (2 : ℂ) • X ((2 : ℂ) • x)) -
    (2 : ℂ) • X (c • ((2 : ℂ) • Ce x - (2 : ℂ) • x)) =
      (4*c) • (Co (X x) - X (Ce x))
  simp only [map_smul, map_sub]
  module

/-- Actual prime-factor weights provide a formal noncollision anchor. This is a
coefficient test, not a free choice of the physical prime phases. -/
theorem exists_native_formal_pencil_injective (Q K : ℕ) (hQ : 2 ≤ Q) (hK : 3 ≤ K) :
    ∃ X : boundedPrimeSet Q → ℂˣ, Function.Injective (nativePencilSylvester
      (E := zeroCarrier .even K) (F := zeroCarrier .odd K)
      (frameEnergy .even K 0 (formalScaledSourceMatrix Q 0 X K)) (frameGram .even K 0)
      (frameEnergy .odd K 0 (formalScaledSourceMatrix Q 0 X K)) (frameGram .odd K 0)) := by
  classical
  obtain ⟨p,hp,hpQ,hQp⟩ := exists_prime_below_cutoff_square_above Q hQ
  let r : boundedPrimeSet Q := ⟨p, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega),hp⟩⟩
  obtain ⟨theta,ht,ht1,hi⟩ := exists_nativeCosine_sylvester_injective K hK 1 (by norm_num)
  refine ⟨singlePrimePhase (boundedPrimeSet Q) r (circlePhase theta),?_⟩
  rw [native_zero_single_prime_pencil Q K r hQp theta]
  have hc : (4 * (isolatedPrimeCoefficient p : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (isolatedPrimeCoefficient_pos hp)))
  intro X Y h
  apply hi
  exact (smul_right_injective (zeroCarrier .even K →ₗ[ℂ] zeroCarrier .odd K) hc) h

end Zeta23.OPICARound4.NativeParityPencils
