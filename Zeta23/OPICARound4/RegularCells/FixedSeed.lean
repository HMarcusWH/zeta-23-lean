import Zeta23.CCM.CanonicalPoleNeutralPublicAPI
import Zeta23.CCM.SourceMomentVandermondeFiltration

noncomputable section

namespace Zeta23.OPICARound4.RegularCells

open CCM
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace

def fixedSeedParameter (L : ℝ) : ℝ := (L / (4 * Real.pi)) ^ 2

/-- The physical diagonal is positive, but is not a unitary change of frame. -/
def fixedSeedDiagonalEntry (L : ℝ) (K : ℕ) (i : Fin (2 * K + 1)) : ℝ :=
  fixedSeedParameter L + (centeredIndex K i : ℝ) ^ 2

theorem fixedSeedDiagonalEntry_pos {L : ℝ} (hL : 0 < L)
    (K : ℕ) (i : Fin (2 * K + 1)) : 0 < fixedSeedDiagonalEntry L K i := by
  unfold fixedSeedDiagonalEntry fixedSeedParameter
  have hp : 0 < (L / (4 * Real.pi)) ^ 2 := sq_pos_of_pos (by positivity)
  positivity

def fixedSeedDiagonal (L : ℝ) (K : ℕ) :
    (Fin (2 * K + 1) → ℂ) →ₗ[ℂ] (Fin (2 * K + 1) → ℂ) where
  toFun u i := (fixedSeedDiagonalEntry L K i : ℂ) * u i
  map_add' u v := by ext i; simp [mul_add]
  map_smul' c u := by ext i; simp; ring

@[simp] theorem fixedSeedDiagonal_apply (L : ℝ) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (i : Fin (2 * K + 1)) :
    fixedSeedDiagonal L K u i = (fixedSeedDiagonalEntry L K i : ℂ) * u i := rfl

def fixedSeedDiagonalEquiv {L : ℝ} (hL : 0 < L) (K : ℕ) :
    (Fin (2 * K + 1) → ℂ) ≃ₗ[ℂ] (Fin (2 * K + 1) → ℂ) where
  toLinearMap := fixedSeedDiagonal L K
  invFun u i := (fixedSeedDiagonalEntry L K i : ℂ)⁻¹ * u i
  left_inv u := by
    ext i
    have hi : (fixedSeedDiagonalEntry L K i : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (fixedSeedDiagonalEntry_pos hL K i))
    simp [hi]
  right_inv u := by
    ext i
    have hi : (fixedSeedDiagonalEntry L K i : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (fixedSeedDiagonalEntry_pos hL K i))
    simp [hi]

theorem centeredMoment_fixedSeedDiagonal (L : ℝ) (K k : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    centeredMoment K k (fixedSeedDiagonal L K u) =
      (fixedSeedParameter L : ℂ) * centeredMoment K k u + centeredMoment K (k + 2) u := by
  simp only [centeredMoment, fixedSeedDiagonal_apply, fixedSeedDiagonalEntry,
    Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_intCast]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  ring

theorem fixedSeedDiagonal_reverse (L : ℝ) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    reverseCoefficients K (fixedSeedDiagonal L K u) =
      fixedSeedDiagonal L K (reverseCoefficients K u) := by
  ext i
  simp [reverseCoefficients, fixedSeedDiagonalEntry, centeredIndex_rev]

theorem fixedSeedDiagonal_even_iff {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    fixedSeedDiagonal L K u ∈ evenCoefficientSubspace K ↔ u ∈ evenCoefficientSubspace K := by
  simp only [mem_evenCoefficientSubspace_iff, fixedSeedDiagonal_reverse]
  exact (fixedSeedDiagonalEquiv hL K).injective.eq_iff

theorem fixedSeedDiagonal_odd_iff {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    fixedSeedDiagonal L K u ∈ oddCoefficientSubspace K ↔ u ∈ oddCoefficientSubspace K := by
  simp only [mem_oddCoefficientSubspace_iff, fixedSeedDiagonal_reverse, ← map_neg]
  exact (fixedSeedDiagonalEquiv hL K).injective.eq_iff

theorem poleEvenProfile_fixedSeedDiagonalEntry {L : ℝ} (hL : 0 < L)
    (K : ℕ) (i : Fin (2 * K + 1)) :
    poleEvenProfile L K i * (fixedSeedDiagonalEntry L K i : ℂ) =
      ((L / (16 * Real.pi ^ 2) : ℝ) : ℂ) := by
  have hd := ne_of_gt (poleProfileDenominator_pos hL (centeredIndex K i))
  have hp := Real.pi_ne_zero
  have hr : poleEvenProfileReal (centeredIndex K i) L * fixedSeedDiagonalEntry L K i =
      L / (16 * Real.pi ^ 2) := by
    unfold poleEvenProfileReal fixedSeedDiagonalEntry fixedSeedParameter
    field_simp [hd, hp]
    unfold poleProfileDenominator
    ring
  change (poleEvenProfileReal (centeredIndex K i) L : ℂ) * _ = _
  exact_mod_cast hr

theorem poleOddProfile_fixedSeedDiagonalEntry {L : ℝ} (hL : 0 < L)
    (K : ℕ) (i : Fin (2 * K + 1)) :
    poleOddProfile L K i * (fixedSeedDiagonalEntry L K i : ℂ) =
      ((1 / (4 * Real.pi) : ℝ) : ℂ) * (centeredIndex K i : ℂ) := by
  have hd := ne_of_gt (poleProfileDenominator_pos hL (centeredIndex K i))
  have hp := Real.pi_ne_zero
  have hr : poleOddProfileReal (centeredIndex K i) L * fixedSeedDiagonalEntry L K i =
      (1 / (4 * Real.pi)) * (centeredIndex K i : ℝ) := by
    unfold poleOddProfileReal fixedSeedDiagonalEntry fixedSeedParameter
    field_simp [hd, hp]
    unfold poleProfileDenominator
    ring
  change (poleOddProfileReal (centeredIndex K i) L : ℂ) * _ = _
  exact_mod_cast hr

theorem even_pole_fixedSeedDiagonal {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    (∑ i, poleEvenProfile L K i * fixedSeedDiagonal L K u i) =
      ((L / (16 * Real.pi ^ 2) : ℝ) : ℂ) * centeredMoment K 0 u := by
  simp_rw [fixedSeedDiagonal_apply, ← mul_assoc, poleEvenProfile_fixedSeedDiagonalEntry hL]
  simp [Finset.mul_sum]

theorem odd_pole_fixedSeedDiagonal {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    (∑ i, poleOddProfile L K i * fixedSeedDiagonal L K u i) =
      ((1 / (4 * Real.pi) : ℝ) : ℂ) * centeredMoment K 1 u := by
  simp_rw [fixedSeedDiagonal_apply, ← mul_assoc, poleOddProfile_fixedSeedDiagonalEntry hL]
  simp [centeredMoment, Finset.mul_sum, mul_assoc]

def fixedEvenSeed (K : ℕ) : Submodule ℂ (Fin (2 * K + 1) → ℂ) :=
  evenCoefficientSubspace K ⊓ ((centeredMomentLinearMap K 0).ker ⊓
    ((centeredMomentLinearMap K 2).ker ⊓ (centeredMomentLinearMap K 4).ker))

def fixedOddSeed (K : ℕ) : Submodule ℂ (Fin (2 * K + 1) → ℂ) :=
  oddCoefficientSubspace K ⊓ ((centeredMomentLinearMap K 1).ker ⊓
    (centeredMomentLinearMap K 3).ker)

theorem mem_fixedEvenSeed_iff (K : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    u ∈ fixedEvenSeed K ↔ u ∈ evenCoefficientSubspace K ∧
      centeredMoment K 0 u = 0 ∧ centeredMoment K 2 u = 0 ∧ centeredMoment K 4 u = 0 := Iff.rfl

theorem mem_fixedOddSeed_iff (K : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    u ∈ fixedOddSeed K ↔ u ∈ oddCoefficientSubspace K ∧
      centeredMoment K 1 u = 0 ∧ centeredMoment K 3 u = 0 := Iff.rfl

/-- Exact G01 even raw equivalence, including every cutoff and no genericity. -/
theorem fixedEvenSeed_diagonal_iff {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    (fixedSeedDiagonal L K u ∈ evenBoundaryFlatSubspace K ∧
      (∑ i, poleEvenProfile L K i * fixedSeedDiagonal L K u i) = 0) ↔
        u ∈ fixedEvenSeed K := by
  rw [mem_fixedEvenSeed_iff]
  have hc : ((L / (16 * Real.pi ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  rw [even_pole_fixedSeedDiagonal hL, mul_eq_zero, or_iff_right hc]
  constructor
  · rintro ⟨⟨hf, he⟩, h0⟩
    have hp := (fixedSeedDiagonal_even_iff hL K u).mp he
    have hm := (mem_boundaryFlatSubspace_iff K _).mp hf
    unfold BoundaryFlatCoefficients at hm
    rw [centeredMoment_fixedSeedDiagonal, h0, mul_zero, zero_add] at hm
    have h2 := hm.1
    have h4 := hm.2.2
    rw [centeredMoment_fixedSeedDiagonal, h2, mul_zero, zero_add] at h4
    exact ⟨hp, h0, h2, h4⟩
  · rintro ⟨he, h0, h2, h4⟩
    refine ⟨⟨(mem_boundaryFlatSubspace_iff K _).mpr ?_,
      (fixedSeedDiagonal_even_iff hL K u).mpr he⟩, h0⟩
    refine ⟨?_, centeredMoment_odd_eq_zero_of_even
      ((fixedSeedDiagonal_even_iff hL K u).mpr he) (by decide), ?_⟩
    · simp [centeredMoment_fixedSeedDiagonal, h0, h2]
    · simp [centeredMoment_fixedSeedDiagonal, h2, h4]

/-- Exact G01 odd raw equivalence. -/
theorem fixedOddSeed_diagonal_iff {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    (fixedSeedDiagonal L K u ∈ oddBoundaryFlatSubspace K ∧
      (∑ i, poleOddProfile L K i * fixedSeedDiagonal L K u i) = 0) ↔
        u ∈ fixedOddSeed K := by
  rw [mem_fixedOddSeed_iff]
  have hc : ((1 / (4 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  rw [odd_pole_fixedSeedDiagonal hL, mul_eq_zero, or_iff_right hc]
  constructor
  · rintro ⟨⟨hf, ho⟩, h1⟩
    have hp := (fixedSeedDiagonal_odd_iff hL K u).mp ho
    have hm := (mem_boundaryFlatSubspace_iff K _).mp hf
    have h3 := hm.2.1
    rw [centeredMoment_fixedSeedDiagonal, h1, mul_zero, zero_add] at h3
    exact ⟨hp, h1, h3⟩
  · rintro ⟨ho, h1, h3⟩
    have hp := (fixedSeedDiagonal_odd_iff hL K u).mpr ho
    refine ⟨⟨(mem_boundaryFlatSubspace_iff K _).mpr ?_, hp⟩, h1⟩
    exact ⟨centeredMoment_even_eq_zero_of_odd hp (by decide),
      by simp [centeredMoment_fixedSeedDiagonal, h1, h3],
      centeredMoment_even_eq_zero_of_odd hp (by decide)⟩

def fixedEvenSeedToPhysical {L : ℝ} (hL : 0 < L) (K : ℕ) :
    fixedEvenSeed K →ₗ[ℂ] poleNeutralEvenSubspace L K where
  toFun u :=
    let h := (fixedEvenSeed_diagonal_iff hL K u).mpr u.property
    ⟨⟨WithLp.toLp 2 (fixedSeedDiagonal L K u), h.1⟩, h.2⟩
  map_add' u v := by ext i; simp; ring
  map_smul' c u := by ext i; simp; ring

def fixedOddSeedToPhysical {L : ℝ} (hL : 0 < L) (K : ℕ) :
    fixedOddSeed K →ₗ[ℂ] poleNeutralOddSubspace L K where
  toFun u :=
    let h := (fixedOddSeed_diagonal_iff hL K u).mpr u.property
    ⟨⟨WithLp.toLp 2 (fixedSeedDiagonal L K u), h.1⟩, h.2⟩
  map_add' u v := by ext i; simp; ring
  map_smul' c u := by ext i; simp; ring

def fixedEvenSeedPhysicalEquiv {L : ℝ} (hL : 0 < L) (K : ℕ) :
    fixedEvenSeed K ≃ₗ[ℂ] poleNeutralEvenSubspace L K :=
  LinearEquiv.ofBijective (fixedEvenSeedToPhysical hL K) (by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply (fixedSeedDiagonalEquiv hL K).injective
      exact congrArg (fun w : poleNeutralEvenSubspace L K => w.val.val.ofLp) huv
    · intro u
      let v := (fixedSeedDiagonalEquiv hL K).symm u.val.val.ofLp
      have hv : fixedSeedDiagonal L K v = u.val.val.ofLp :=
        (fixedSeedDiagonalEquiv hL K).apply_symm_apply _
      have hm : v ∈ fixedEvenSeed K := by
        apply (fixedEvenSeed_diagonal_iff hL K v).mp
        rw [hv]
        exact ⟨u.val.property, u.property⟩
      refine ⟨⟨v, hm⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (EuclideanSpace.equiv _ ℂ).injective hv)

def fixedOddSeedPhysicalEquiv {L : ℝ} (hL : 0 < L) (K : ℕ) :
    fixedOddSeed K ≃ₗ[ℂ] poleNeutralOddSubspace L K :=
  LinearEquiv.ofBijective (fixedOddSeedToPhysical hL K) (by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply (fixedSeedDiagonalEquiv hL K).injective
      exact congrArg (fun w : poleNeutralOddSubspace L K => w.val.val.ofLp) huv
    · intro u
      let v := (fixedSeedDiagonalEquiv hL K).symm u.val.val.ofLp
      have hv : fixedSeedDiagonal L K v = u.val.val.ofLp :=
        (fixedSeedDiagonalEquiv hL K).apply_symm_apply _
      have hm : v ∈ fixedOddSeed K := by
        apply (fixedOddSeed_diagonal_iff hL K v).mp
        rw [hv]
        exact ⟨u.val.property, u.property⟩
      refine ⟨⟨v, hm⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (EuclideanSpace.equiv _ ℂ).injective hv)

/-- The exact pulled-back Gram form retains the nonunitary diagonal weights. -/
def fixedSeedGram (L : ℝ) (K : ℕ) (u v : Fin (2 * K + 1) → ℂ) : ℂ :=
  ∑ i, (fixedSeedDiagonalEntry L K i : ℂ) ^ 2 * star (u i) * v i

theorem fixedSeedGram_eq_physical_inner (L : ℝ) (K : ℕ)
    (u v : Fin (2 * K + 1) → ℂ) :
    fixedSeedGram L K u v = inner ℂ
      (WithLp.toLp 2 (fixedSeedDiagonal L K u) : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (WithLp.toLp 2 (fixedSeedDiagonal L K v) : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp only [fixedSeedDiagonal_apply, Pi.star_apply, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  ring

theorem fixedSeedGram_pos {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (hu : u ≠ 0) :
    0 < (fixedSeedGram L K u u).re := by
  rw [fixedSeedGram_eq_physical_inner]
  apply (re_inner_self_pos (𝕜 := ℂ)).mpr
  intro hz
  have hraw := congrArg (fun w : EuclideanSpace ℂ (Fin (2 * K + 1)) => w.ofLp) hz
  have hzD : fixedSeedDiagonal L K u = fixedSeedDiagonal L K 0 := by
    simpa only [WithLp.ofLp_toLp, WithLp.ofLp_zero, map_zero] using hraw
  exact hu ((fixedSeedDiagonalEquiv hL K).injective hzD)

theorem fixedEvenSeedPhysicalEquiv_gram {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u v : fixedEvenSeed K) :
    inner ℂ (fixedEvenSeedPhysicalEquiv hL K u) (fixedEvenSeedPhysicalEquiv hL K v) =
      fixedSeedGram L K u v := by
  change inner ℂ (WithLp.toLp 2 (fixedSeedDiagonal L K u) : EuclideanSpace ℂ _)
    (WithLp.toLp 2 (fixedSeedDiagonal L K v) : EuclideanSpace ℂ _) = _
  exact (fixedSeedGram_eq_physical_inner L K u v).symm

theorem fixedOddSeedPhysicalEquiv_gram {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u v : fixedOddSeed K) :
    inner ℂ (fixedOddSeedPhysicalEquiv hL K u) (fixedOddSeedPhysicalEquiv hL K v) =
      fixedSeedGram L K u v := by
  change inner ℂ (WithLp.toLp 2 (fixedSeedDiagonal L K u) : EuclideanSpace ℂ _)
    (WithLp.toLp 2 (fixedSeedDiagonal L K v) : EuclideanSpace ℂ _) = _
  exact (fixedSeedGram_eq_physical_inner L K u v).symm

theorem fixedEvenSeedPhysicalEquiv_exponentialMoments {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : fixedEvenSeed K) :
    canonicalPoleExponentialMoment 1 L K (fixedSeedDiagonal L K u) = 0 ∧
      canonicalPoleExponentialMoment (-1) L K (fixedSeedDiagonal L K u) = 0 :=
  (poleNeutralEven_iff_exponentialMoments hL K (fixedEvenSeedPhysicalEquiv hL K u).val).mp
    (fixedEvenSeedPhysicalEquiv hL K u).property

theorem fixedOddSeedPhysicalEquiv_exponentialMoments {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : fixedOddSeed K) :
    canonicalPoleExponentialMoment 1 L K (fixedSeedDiagonal L K u) = 0 ∧
      canonicalPoleExponentialMoment (-1) L K (fixedSeedDiagonal L K u) = 0 :=
  (poleNeutralOdd_iff_exponentialMoments hL K (fixedOddSeedPhysicalEquiv hL K u).val).mp
    (fixedOddSeedPhysicalEquiv hL K u).property

end Zeta23.OPICARound4.RegularCells
