import Zeta23.OPICARound4.ArithmeticFrontier.MomentSlices
import Zeta23.OPICARound4.RegularCells.FixedSeed

/-!
# Fixed seed coordinates, dimensions and the physical Gram on the moment slices

The existing fixed-seed diagonal `x = D y`, with entries `(L/(4π))^2 + n^2`,
is the specification chart `L^2 + 16π^2 n^2` divided by the positive constant
`16π^2`; no second normalization is introduced. In these coordinates the even
slice is `{y even : M0 = M2 = M4 = M6 = 0}` and the odd slice is
`{y odd : M1 = M3 = M5 = M7 = 0}`. The diagonal is not unitary: every bound
is transported through the full Gram `D^2`, never through the identity.

The dimensions are exactly `K - 3` and `K - 4` (natural subtraction), so both
slices vanish at `K = 3` and the odd slice also at `K = 4`. Bounds at those
cutoffs are vacuous and carry no information about the quartic cutoff.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open CCM RegularCells Module
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace

/-- The fixed seed diagonal is the specification chart up to the constant `16π^2`. -/
theorem spec_chart_eq_fixedSeedDiagonalEntry (L : ℝ) (K : ℕ) (i : Fin (2 * K + 1)) :
    L ^ 2 + 16 * Real.pi ^ 2 * (centeredIndex K i : ℝ) ^ 2 =
      16 * Real.pi ^ 2 * fixedSeedDiagonalEntry L K i := by
  unfold fixedSeedDiagonalEntry fixedSeedParameter
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- Fixed even coordinates of the even slice. -/
def fixedEvenMomentSeed (K : ℕ) : Submodule ℂ (Fin (2 * K + 1) → ℂ) :=
  fixedEvenSeed K ⊓ LinearMap.ker (centeredMomentLinearMap K 6)

/-- Fixed odd coordinates of the odd slice. -/
def fixedOddMomentSeed (K : ℕ) : Submodule ℂ (Fin (2 * K + 1) → ℂ) :=
  fixedOddSeed K ⊓ (LinearMap.ker (centeredMomentLinearMap K 5) ⊓
    LinearMap.ker (centeredMomentLinearMap K 7))

theorem mem_fixedEvenMomentSeed_iff (K : ℕ) (y : Fin (2 * K + 1) → ℂ) :
    y ∈ fixedEvenMomentSeed K ↔ y ∈ evenCoefficientSubspace K ∧
      centeredMoment K 0 y = 0 ∧ centeredMoment K 2 y = 0 ∧
      centeredMoment K 4 y = 0 ∧ centeredMoment K 6 y = 0 := by
  change (y ∈ fixedEvenSeed K ∧ centeredMoment K 6 y = 0) ↔ _
  rw [mem_fixedEvenSeed_iff]
  tauto

theorem mem_fixedOddMomentSeed_iff (K : ℕ) (y : Fin (2 * K + 1) → ℂ) :
    y ∈ fixedOddMomentSeed K ↔ y ∈ oddCoefficientSubspace K ∧
      centeredMoment K 1 y = 0 ∧ centeredMoment K 3 y = 0 ∧
      centeredMoment K 5 y = 0 ∧ centeredMoment K 7 y = 0 := by
  change (y ∈ fixedOddSeed K ∧ centeredMoment K 5 y = 0 ∧ centeredMoment K 7 y = 0) ↔ _
  rw [mem_fixedOddSeed_iff]
  tauto

private theorem even_seed_coordinates {L : ℝ} (hL : 0 < L) (K : ℕ) (y : fixedEvenSeed K) :
    (EuclideanSpace.equiv _ ℂ) ((fixedEvenSeedPhysicalEquiv hL K y).val.val) =
      fixedSeedDiagonal L K y := rfl

private theorem odd_seed_coordinates {L : ℝ} (hL : 0 < L) (K : ℕ) (y : fixedOddSeed K) :
    (EuclideanSpace.equiv _ ℂ) ((fixedOddSeedPhysicalEquiv hL K y).val.val) =
      fixedSeedDiagonal L K y := rfl

/-- The physical fourth moment of a seed image is the seed's sixth moment. -/
theorem evenPhysicalMoment_four_of_seed {L : ℝ} (hL : 0 < L) (K : ℕ) (y : fixedEvenSeed K) :
    evenPhysicalMoment L K 4 (fixedEvenSeedPhysicalEquiv hL K y) =
      centeredMoment K 6 (y : Fin (2 * K + 1) → ℂ) := by
  rw [evenPhysicalMoment_apply, even_seed_coordinates, centeredMoment_fixedSeedDiagonal]
  have h4 := ((mem_fixedEvenSeed_iff K y).mp y.property).2.2.2
  rw [h4, mul_zero, zero_add]

/-- The physical third moment of an odd seed image is the seed's fifth moment. -/
theorem oddPhysicalMoment_three_of_seed {L : ℝ} (hL : 0 < L) (K : ℕ) (y : fixedOddSeed K) :
    oddPhysicalMoment L K 3 (fixedOddSeedPhysicalEquiv hL K y) =
      centeredMoment K 5 (y : Fin (2 * K + 1) → ℂ) := by
  rw [oddPhysicalMoment_apply, odd_seed_coordinates, centeredMoment_fixedSeedDiagonal]
  have h3 := ((mem_fixedOddSeed_iff K y).mp y.property).2.2
  rw [h3, mul_zero, zero_add]

/-- The physical fifth moment of an odd seed image retains the shift `β M5`. -/
theorem oddPhysicalMoment_five_of_seed {L : ℝ} (hL : 0 < L) (K : ℕ) (y : fixedOddSeed K) :
    oddPhysicalMoment L K 5 (fixedOddSeedPhysicalEquiv hL K y) =
      (fixedSeedParameter L : ℂ) * centeredMoment K 5 (y : Fin (2 * K + 1) → ℂ) +
        centeredMoment K 7 (y : Fin (2 * K + 1) → ℂ) := by
  rw [oddPhysicalMoment_apply, odd_seed_coordinates, centeredMoment_fixedSeedDiagonal]

theorem fixedEvenSeedPhysicalEquiv_mem_slice_iff {L : ℝ} (hL : 0 < L) (K : ℕ)
    (y : fixedEvenSeed K) :
    fixedEvenSeedPhysicalEquiv hL K y ∈ evenMomentSlice L K ↔
      (y : Fin (2 * K + 1) → ℂ) ∈ fixedEvenMomentSeed K := by
  change evenPhysicalMoment L K 4 _ = 0 ↔ (y : Fin (2 * K + 1) → ℂ) ∈ fixedEvenSeed K ∧
    centeredMoment K 6 (y : Fin (2 * K + 1) → ℂ) = 0
  rw [evenPhysicalMoment_four_of_seed]
  exact ⟨fun h => ⟨y.property, h⟩, fun h => h.2⟩

theorem fixedOddSeedPhysicalEquiv_mem_slice_iff {L : ℝ} (hL : 0 < L) (K : ℕ)
    (y : fixedOddSeed K) :
    fixedOddSeedPhysicalEquiv hL K y ∈ oddMomentSlice L K ↔
      (y : Fin (2 * K + 1) → ℂ) ∈ fixedOddMomentSeed K := by
  change (oddPhysicalMoment L K 3 _ = 0 ∧ oddPhysicalMoment L K 5 _ = 0) ↔
    (y : Fin (2 * K + 1) → ℂ) ∈ fixedOddSeed K ∧
      centeredMoment K 5 (y : Fin (2 * K + 1) → ℂ) = 0 ∧
      centeredMoment K 7 (y : Fin (2 * K + 1) → ℂ) = 0
  rw [oddPhysicalMoment_three_of_seed, oddPhysicalMoment_five_of_seed]
  constructor
  · rintro ⟨h5, h7⟩
    rw [h5, mul_zero, zero_add] at h7
    exact ⟨y.property, h5, h7⟩
  · rintro ⟨_, h5, h7⟩
    rw [h5, h7, mul_zero, add_zero]
    exact ⟨rfl, rfl⟩

private def evenSliceSeedMap {L : ℝ} (hL : 0 < L) (K : ℕ) :
    fixedEvenMomentSeed K →ₗ[ℂ] evenMomentSlice L K :=
  LinearMap.codRestrict (evenMomentSlice L K)
    ((fixedEvenSeedPhysicalEquiv hL K).toLinearMap.comp
      (Submodule.inclusion (inf_le_left : fixedEvenMomentSeed K ≤ fixedEvenSeed K)))
    (fun y => (fixedEvenSeedPhysicalEquiv_mem_slice_iff hL K _).mpr y.property)

private def oddSliceSeedMap {L : ℝ} (hL : 0 < L) (K : ℕ) :
    fixedOddMomentSeed K →ₗ[ℂ] oddMomentSlice L K :=
  LinearMap.codRestrict (oddMomentSlice L K)
    ((fixedOddSeedPhysicalEquiv hL K).toLinearMap.comp
      (Submodule.inclusion (inf_le_left : fixedOddMomentSeed K ≤ fixedOddSeed K)))
    (fun y => (fixedOddSeedPhysicalEquiv_mem_slice_iff hL K _).mpr y.property)

/-- Exact linear equivalence between fixed even moment seeds and the even slice. -/
def evenMomentSliceSeedEquiv {L : ℝ} (hL : 0 < L) (K : ℕ) :
    fixedEvenMomentSeed K ≃ₗ[ℂ] evenMomentSlice L K :=
  LinearEquiv.ofBijective (evenSliceSeedMap hL K) (by
    constructor
    · intro y z hyz
      have h := congrArg (fun w : evenMomentSlice L K => (w : poleNeutralEvenSubspace L K)) hyz
      have h' := (fixedEvenSeedPhysicalEquiv hL K).injective h
      exact Submodule.inclusion_injective _ h'
    · intro u
      let y := (fixedEvenSeedPhysicalEquiv hL K).symm u.val
      have hy : fixedEvenSeedPhysicalEquiv hL K y ∈ evenMomentSlice L K := by
        rw [LinearEquiv.apply_symm_apply]
        exact u.property
      refine ⟨⟨y.val, (fixedEvenSeedPhysicalEquiv_mem_slice_iff hL K y).mp hy⟩, ?_⟩
      apply Subtype.ext
      change fixedEvenSeedPhysicalEquiv hL K ⟨y.val, y.property⟩ = u.val
      exact LinearEquiv.apply_symm_apply _ _)

/-- Exact linear equivalence between fixed odd moment seeds and the odd slice. -/
def oddMomentSliceSeedEquiv {L : ℝ} (hL : 0 < L) (K : ℕ) :
    fixedOddMomentSeed K ≃ₗ[ℂ] oddMomentSlice L K :=
  LinearEquiv.ofBijective (oddSliceSeedMap hL K) (by
    constructor
    · intro y z hyz
      have h := congrArg (fun w : oddMomentSlice L K => (w : poleNeutralOddSubspace L K)) hyz
      have h' := (fixedOddSeedPhysicalEquiv hL K).injective h
      exact Submodule.inclusion_injective _ h'
    · intro u
      let y := (fixedOddSeedPhysicalEquiv hL K).symm u.val
      have hy : fixedOddSeedPhysicalEquiv hL K y ∈ oddMomentSlice L K := by
        rw [LinearEquiv.apply_symm_apply]
        exact u.property
      refine ⟨⟨y.val, (fixedOddSeedPhysicalEquiv_mem_slice_iff hL K y).mp hy⟩, ?_⟩
      apply Subtype.ext
      change fixedOddSeedPhysicalEquiv hL K ⟨y.val, y.property⟩ = u.val
      exact LinearEquiv.apply_symm_apply _ _)

/-- The physical inner product of slice images is the full nonunitary seed Gram. -/
theorem evenMomentSliceSeedEquiv_inner {L : ℝ} (hL : 0 < L) (K : ℕ)
    (y z : fixedEvenMomentSeed K) :
    inner ℂ ((evenMomentSliceSeedEquiv hL K y : evenMomentSlice L K) : poleNeutralEvenSubspace L K)
      ((evenMomentSliceSeedEquiv hL K z : evenMomentSlice L K) : poleNeutralEvenSubspace L K) =
      fixedSeedGram L K y z :=
  fixedEvenSeedPhysicalEquiv_gram hL K ⟨y.val, y.property.1⟩ ⟨z.val, z.property.1⟩

theorem oddMomentSliceSeedEquiv_inner {L : ℝ} (hL : 0 < L) (K : ℕ)
    (y z : fixedOddMomentSeed K) :
    inner ℂ ((oddMomentSliceSeedEquiv hL K y : oddMomentSlice L K) : poleNeutralOddSubspace L K)
      ((oddMomentSliceSeedEquiv hL K z : oddMomentSlice L K) : poleNeutralOddSubspace L K) =
      fixedSeedGram L K y z :=
  fixedOddSeedPhysicalEquiv_gram hL K ⟨y.val, y.property.1⟩ ⟨z.val, z.property.1⟩

theorem evenMomentSliceSeedEquiv_norm_sq {L : ℝ} (hL : 0 < L) (K : ℕ)
    (y : fixedEvenMomentSeed K) :
    ‖((evenMomentSliceSeedEquiv hL K y : evenMomentSlice L K) : poleNeutralEvenSubspace L K)‖ ^ 2 =
      (fixedSeedGram L K y y).re := by
  change ‖(WithLp.toLp 2 (fixedSeedDiagonal L K y) : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ ^ 2 = _
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), ← fixedSeedGram_eq_physical_inner]
  rfl

theorem oddMomentSliceSeedEquiv_norm_sq {L : ℝ} (hL : 0 < L) (K : ℕ)
    (y : fixedOddMomentSeed K) :
    ‖((oddMomentSliceSeedEquiv hL K y : oddMomentSlice L K) : poleNeutralOddSubspace L K)‖ ^ 2 =
      (fixedSeedGram L K y y).re := by
  change ‖(WithLp.toLp 2 (fixedSeedDiagonal L K y) : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ ^ 2 = _
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), ← fixedSeedGram_eq_physical_inner]
  rfl

/-- Congruence transport: the physical even slice bound is exactly the seed
form bound with the full Gram `D^2` as tolerance metric. -/
theorem evenMomentSliceLowerBound_iff_seed_gram {L : ℝ} (hL : 0 < L) (K : ℕ) (ε : ℝ) :
    EvenMomentSliceLowerBound L K ε ↔ ∀ y : fixedEvenMomentSeed K,
      -ε * (fixedSeedGram L K y y).re ≤
        evenNativeEnergy L K
          ((evenMomentSliceSeedEquiv hL K y : evenMomentSlice L K) : poleNeutralEvenSubspace L K) := by
  constructor
  · intro h y
    rw [← evenMomentSliceSeedEquiv_norm_sq hL]
    exact h _ (evenMomentSliceSeedEquiv hL K y).property
  · intro h u hu
    have hy := h ((evenMomentSliceSeedEquiv hL K).symm ⟨u, hu⟩)
    rw [← evenMomentSliceSeedEquiv_norm_sq hL, LinearEquiv.apply_symm_apply] at hy
    exact hy

/-- Congruence transport on the odd slice, with the full Gram metric. -/
theorem oddMomentSliceLowerBound_iff_seed_gram {L : ℝ} (hL : 0 < L) (K : ℕ) (ε : ℝ) :
    OddMomentSliceLowerBound L K ε ↔ ∀ y : fixedOddMomentSeed K,
      -ε * (fixedSeedGram L K y y).re ≤
        oddNativeEnergy L K
          ((oddMomentSliceSeedEquiv hL K y : oddMomentSlice L K) : poleNeutralOddSubspace L K) := by
  constructor
  · intro h y
    rw [← oddMomentSliceSeedEquiv_norm_sq hL]
    exact h _ (oddMomentSliceSeedEquiv hL K y).property
  · intro h v hv
    have hy := h ((oddMomentSliceSeedEquiv hL K).symm ⟨v, hv⟩)
    rw [← oddMomentSliceSeedEquiv_norm_sq hL, LinearEquiv.apply_symm_apply] at hy
    exact hy

/-- Unweighted coordinate square norm; it is not the physical norm. -/
def seedCoordinateNormSq (K : ℕ) (y : Fin (2 * K + 1) → ℂ) : ℝ :=
  ∑ i, ‖y i‖ ^ 2

theorem fixedSeedGram_re_eq (L : ℝ) (K : ℕ) (y : Fin (2 * K + 1) → ℂ) :
    (fixedSeedGram L K y y).re = ∑ i, fixedSeedDiagonalEntry L K i ^ 2 * ‖y i‖ ^ 2 := by
  unfold fixedSeedGram
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem centeredIndex_sq_le (K : ℕ) (i : Fin (2 * K + 1)) :
    (centeredIndex K i : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 := by
  have hlo : -(K : ℤ) ≤ centeredIndex K i := by dsimp [centeredIndex]; omega
  have hhi : centeredIndex K i ≤ (K : ℤ) := by dsimp [centeredIndex]; omega
  have hlo' : -(K : ℝ) ≤ (centeredIndex K i : ℝ) := by exact_mod_cast hlo
  have hhi' : (centeredIndex K i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hhi
  nlinarith

/-- Lower frozen-metric comparison: the physical Gram dominates `β^2` times the
coordinate norm, `β = (L/(4π))^2`. -/
theorem fixedSeedGram_re_ge (L : ℝ) (K : ℕ) (y : Fin (2 * K + 1) → ℂ) :
    fixedSeedParameter L ^ 2 * seedCoordinateNormSq K y ≤ (fixedSeedGram L K y y).re := by
  rw [fixedSeedGram_re_eq, seedCoordinateNormSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hβ : 0 ≤ fixedSeedParameter L := by unfold fixedSeedParameter; positivity
  have he : fixedSeedParameter L ≤ fixedSeedDiagonalEntry L K i := by
    unfold fixedSeedDiagonalEntry
    nlinarith [sq_nonneg (centeredIndex K i : ℝ)]
  have h2 : fixedSeedParameter L ^ 2 ≤ fixedSeedDiagonalEntry L K i ^ 2 :=
    pow_le_pow_left₀ hβ he 2
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-- Upper frozen-metric comparison, with the cutoff-dependent factor `(β+K^2)^2`. -/
theorem fixedSeedGram_re_le (L : ℝ) (K : ℕ) (y : Fin (2 * K + 1) → ℂ) :
    (fixedSeedGram L K y y).re ≤
      (fixedSeedParameter L + (K : ℝ) ^ 2) ^ 2 * seedCoordinateNormSq K y := by
  rw [fixedSeedGram_re_eq, seedCoordinateNormSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hβ : 0 ≤ fixedSeedParameter L := by unfold fixedSeedParameter; positivity
  have he0 : 0 ≤ fixedSeedDiagonalEntry L K i := by
    unfold fixedSeedDiagonalEntry
    positivity
  have he : fixedSeedDiagonalEntry L K i ≤ fixedSeedParameter L + (K : ℝ) ^ 2 := by
    unfold fixedSeedDiagonalEntry
    linarith [centeredIndex_sq_le K i]
  have h2 : fixedSeedDiagonalEntry L K i ^ 2 ≤ (fixedSeedParameter L + (K : ℝ) ^ 2) ^ 2 :=
    pow_le_pow_left₀ he0 he 2
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-- A coordinate-identity tolerance `ε` gives only the physical tolerance `ε/β^2`. -/
theorem evenMomentSliceLowerBound_of_coordinate_tolerance {L : ℝ} (hL : 0 < L) (K : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ y : fixedEvenMomentSeed K, -ε * seedCoordinateNormSq K y ≤
      evenNativeEnergy L K
        ((evenMomentSliceSeedEquiv hL K y : evenMomentSlice L K) : poleNeutralEvenSubspace L K)) :
    EvenMomentSliceLowerBound L K (ε / fixedSeedParameter L ^ 2) := by
  rw [evenMomentSliceLowerBound_iff_seed_gram hL]
  intro y
  have hβ : 0 < fixedSeedParameter L := by unfold fixedSeedParameter; positivity
  have hg := fixedSeedGram_re_ge L K y
  have hc : ε * seedCoordinateNormSq K y ≤ ε / fixedSeedParameter L ^ 2 * (fixedSeedGram L K y y).re := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  linarith [h y]

/-- A physical tolerance `ε` gives only the coordinate tolerance `ε (β+K^2)^2`. -/
theorem coordinate_tolerance_of_evenMomentSliceLowerBound {L : ℝ} (hL : 0 < L) (K : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (h : EvenMomentSliceLowerBound L K ε) :
    ∀ y : fixedEvenMomentSeed K,
      -(ε * (fixedSeedParameter L + (K : ℝ) ^ 2) ^ 2) * seedCoordinateNormSq K y ≤
        evenNativeEnergy L K
          ((evenMomentSliceSeedEquiv hL K y : evenMomentSlice L K) : poleNeutralEvenSubspace L K) := by
  intro y
  have hb := (evenMomentSliceLowerBound_iff_seed_gram hL K ε).mp h y
  have hg := fixedSeedGram_re_le L K y
  nlinarith

private def evenPart (K : ℕ) (w : Fin (2 * K + 1) → ℂ) : Fin (2 * K + 1) → ℂ :=
  (1 / 2 : ℂ) • (w + reverseCoefficients K w)

private def oddPart (K : ℕ) (w : Fin (2 * K + 1) → ℂ) : Fin (2 * K + 1) → ℂ :=
  (1 / 2 : ℂ) • (w - reverseCoefficients K w)

private theorem evenPart_mem (K : ℕ) (w : Fin (2 * K + 1) → ℂ) :
    evenPart K w ∈ evenCoefficientSubspace K := by
  rw [mem_evenCoefficientSubspace_iff]
  ext i
  simp only [evenPart, reverseCoefficients, Pi.smul_apply, Pi.add_apply, Fin.rev_rev, smul_eq_mul]
  ring

private theorem oddPart_mem (K : ℕ) (w : Fin (2 * K + 1) → ℂ) :
    oddPart K w ∈ oddCoefficientSubspace K := by
  rw [mem_oddCoefficientSubspace_iff]
  ext i
  simp only [oddPart, reverseCoefficients, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Fin.rev_rev, smul_eq_mul]
  ring

private theorem moment_evenPart (K k : ℕ) (w : Fin (2 * K + 1) → ℂ) :
    centeredMoment K k (evenPart K w) =
      (1 / 2 : ℂ) * (centeredMoment K k w + (-1 : ℂ) ^ k * centeredMoment K k w) := by
  change centeredMomentLinearMap K k ((1 / 2 : ℂ) • (w + reverseCoefficients K w)) = _
  rw [map_smul, map_add, smul_eq_mul]
  change (1 / 2 : ℂ) * (centeredMoment K k w + centeredMoment K k (reverseCoefficients K w)) = _
  rw [centeredMoment_reverseCoefficients]

private theorem moment_oddPart (K k : ℕ) (w : Fin (2 * K + 1) → ℂ) :
    centeredMoment K k (oddPart K w) =
      (1 / 2 : ℂ) * (centeredMoment K k w - (-1 : ℂ) ^ k * centeredMoment K k w) := by
  change centeredMomentLinearMap K k ((1 / 2 : ℂ) • (w - reverseCoefficients K w)) = _
  rw [map_smul, map_sub, smul_eq_mul]
  change (1 / 2 : ℂ) * (centeredMoment K k w - centeredMoment K k (reverseCoefficients K w)) = _
  rw [centeredMoment_reverseCoefficients]

private theorem exists_moment_vector (K r : ℕ) (hr : r ≤ 2 * K + 1) (j : Fin r) :
    ∃ w : Fin (2 * K + 1) → ℂ, ∀ k : ℕ, k < r →
      centeredMoment K k w = if k = (j : ℕ) then 1 else 0 := by
  obtain ⟨w, hw⟩ := momentPrefixMap_surjective K r hr (Pi.single j 1)
  refine ⟨w, fun k hk => ?_⟩
  have h := congrFun hw ⟨k, hk⟩
  rw [momentPrefixMap_apply] at h
  rw [h, Pi.single_apply]
  by_cases hkj : k = (j : ℕ)
  · have : (⟨k, hk⟩ : Fin r) = j := Fin.ext hkj
    simp [hkj]
  · have : (⟨k, hk⟩ : Fin r) ≠ j := fun e => hkj (congrArg Fin.val e)
    simp [this, hkj]

/-- The even slice is a genuine hyperplane of the even carrier for `K ≥ 3`. -/
theorem exists_fixedEvenSeed_sixth_moment_one (K : ℕ) (hK : 3 ≤ K) :
    ∃ y : Fin (2 * K + 1) → ℂ, y ∈ fixedEvenSeed K ∧ centeredMoment K 6 y = 1 := by
  obtain ⟨w, hw⟩ := exists_moment_vector K 7 (by omega) 6
  refine ⟨evenPart K w, (mem_fixedEvenSeed_iff K _).mpr ⟨evenPart_mem K w, ?_, ?_, ?_⟩, ?_⟩
  · rw [moment_evenPart, hw 0 (by norm_num)]; norm_num
  · rw [moment_evenPart, hw 2 (by norm_num)]; norm_num
  · rw [moment_evenPart, hw 4 (by norm_num)]; norm_num
  · rw [moment_evenPart, hw 6 (by norm_num)]; norm_num

theorem exists_fixedOddSeed_fifth_moment_one (K : ℕ) (hK : 3 ≤ K) :
    ∃ y : Fin (2 * K + 1) → ℂ, y ∈ fixedOddSeed K ∧ centeredMoment K 5 y = 1 := by
  obtain ⟨w, hw⟩ := exists_moment_vector K 6 (by omega) 5
  refine ⟨oddPart K w, (mem_fixedOddSeed_iff K _).mpr ⟨oddPart_mem K w, ?_, ?_⟩, ?_⟩
  · rw [moment_oddPart, hw 1 (by norm_num)]; norm_num
  · rw [moment_oddPart, hw 3 (by norm_num)]; norm_num
  · rw [moment_oddPart, hw 5 (by norm_num)]; norm_num

theorem exists_fixedOddSeed_seventh_moment_one (K : ℕ) (hK : 4 ≤ K) :
    ∃ y : Fin (2 * K + 1) → ℂ, y ∈ fixedOddSeed K ∧
      centeredMoment K 5 y = 0 ∧ centeredMoment K 7 y = 1 := by
  obtain ⟨w, hw⟩ := exists_moment_vector K 8 (by omega) 7
  refine ⟨oddPart K w, (mem_fixedOddSeed_iff K _).mpr ⟨oddPart_mem K w, ?_, ?_⟩, ?_, ?_⟩
  · rw [moment_oddPart, hw 1 (by norm_num)]; norm_num
  · rw [moment_oddPart, hw 3 (by norm_num)]; norm_num
  · rw [moment_oddPart, hw 5 (by norm_num)]; norm_num
  · rw [moment_oddPart, hw 7 (by norm_num)]; norm_num

/-- Exact even slice dimension `K - 3`, including the vanishing `K = 2, 3` cases. -/
theorem finrank_evenMomentSlice {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K) :
    finrank ℂ (evenMomentSlice L K) = K - 3 := by
  have hV := finrank_poleNeutralEvenSubspace hL K hK
  have hrn := (evenPhysicalMoment L K 4).finrank_range_add_finrank_ker
  rcases Nat.lt_or_ge K 3 with h3 | h3
  · have hle := Submodule.finrank_le (evenMomentSlice L K)
    omega
  · obtain ⟨y, hy, h6⟩ := exists_fixedEvenSeed_sixth_moment_one K h3
    have hsurj : Function.Surjective (evenPhysicalMoment L K 4) := by
      intro c
      refine ⟨c • fixedEvenSeedPhysicalEquiv hL K ⟨y, hy⟩, ?_⟩
      rw [map_smul, evenPhysicalMoment_four_of_seed, h6, smul_eq_mul, mul_one]
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hrn
    change finrank ℂ (LinearMap.ker (evenPhysicalMoment L K 4)) = K - 3
    omega

/-- Exact odd slice dimension `K - 4`, including the vanishing `K = 2, 3, 4` cases. -/
theorem finrank_oddMomentSlice {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K) :
    finrank ℂ (oddMomentSlice L K) = K - 4 := by
  have hV := finrank_poleNeutralOddSubspace hL K hK
  let g := (oddPhysicalMoment L K 3).prod (oddPhysicalMoment L K 5)
  have hker : oddMomentSlice L K = LinearMap.ker g := (LinearMap.ker_prod _ _).symm
  have hrn := g.finrank_range_add_finrank_ker
  rw [← hker] at hrn
  rcases Nat.lt_or_ge K 3 with h3 | h3
  · have hle := Submodule.finrank_le (oddMomentSlice L K)
    omega
  obtain ⟨y1, hy1, h51⟩ := exists_fixedOddSeed_fifth_moment_one K h3
  let u1 := fixedOddSeedPhysicalEquiv hL K ⟨y1, hy1⟩
  have hg1 : g u1 = (1, (fixedSeedParameter L : ℂ) + centeredMoment K 7 y1) := by
    change (oddPhysicalMoment L K 3 u1, oddPhysicalMoment L K 5 u1) = _
    rw [oddPhysicalMoment_three_of_seed, oddPhysicalMoment_five_of_seed]
    change (centeredMoment K 5 y1, _ * centeredMoment K 5 y1 + _) = _
    rw [h51, mul_one]
  rcases Nat.lt_or_ge K 4 with h4 | h4
  · have hpos : 0 < finrank ℂ (LinearMap.range g) := by
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      refine ⟨⟨g u1, LinearMap.mem_range_self g u1⟩, ?_⟩
      intro hz
      have h := congrArg (fun w : LinearMap.range g => (w : ℂ × ℂ).1) hz
      simp only [hg1, Submodule.coe_zero, Prod.fst_zero] at h
      exact one_ne_zero h
    omega
  · obtain ⟨y2, hy2, h52, h72⟩ := exists_fixedOddSeed_seventh_moment_one K h4
    let u2 := fixedOddSeedPhysicalEquiv hL K ⟨y2, hy2⟩
    have hg2 : g u2 = (0, 1) := by
      change (oddPhysicalMoment L K 3 u2, oddPhysicalMoment L K 5 u2) = _
      rw [oddPhysicalMoment_three_of_seed, oddPhysicalMoment_five_of_seed]
      change (centeredMoment K 5 y2, _ * centeredMoment K 5 y2 + centeredMoment K 7 y2) = _
      rw [h52, h72, mul_zero, zero_add]
    have hsurj : Function.Surjective g := by
      rintro ⟨a, b⟩
      refine ⟨a • u1 + (b - a * ((fixedSeedParameter L : ℂ) + centeredMoment K 7 y1)) • u2, ?_⟩
      rw [map_add, map_smul, map_smul, hg1, hg2]
      ext <;> simp
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod,
      Module.finrank_self] at hrn
    omega

/-- Nonvacuity at the literal quartic cutoff `K = ⌈L^4⌉ ≥ 16`: the even slice has
dimension at least 13 and the odd slice at least 12, so (C1) is not vacuous. -/
theorem quartic_moment_slices_nontrivial {L : ℝ} (hL : 2 ≤ L) :
    13 ≤ finrank ℂ (evenMomentSlice L (originalDetectorQuarticCutoff L)) ∧
      12 ≤ finrank ℂ (oddMomentSlice L (originalDetectorQuarticCutoff L)) := by
  have hK := originalDetectorQuarticCutoff_ge_sixteen hL
  have hLp : 0 < L := by linarith
  rw [finrank_evenMomentSlice hLp _ (by omega), finrank_oddMomentSlice hLp _ (by omega)]
  omega

theorem evenMomentSlice_eq_bot_of_le_three {L : ℝ} (hL : 0 < L) (K : ℕ)
    (h2 : 2 ≤ K) (h3 : K ≤ 3) : evenMomentSlice L K = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [finrank_evenMomentSlice hL K h2]
  omega

theorem oddMomentSlice_eq_bot_of_le_four {L : ℝ} (hL : 0 < L) (K : ℕ)
    (h2 : 2 ≤ K) (h4 : K ≤ 4) : oddMomentSlice L K = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [finrank_oddMomentSlice hL K h2]
  omega

/-- At `K = 3` the even slice is zero, so its bound holds for every tolerance,
including negative ones. A `K = 3` computation is therefore no substitute for
the nonzero quartic slice. -/
theorem evenMomentSliceLowerBound_three {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    EvenMomentSliceLowerBound L 3 ε := by
  intro u hu
  rw [evenMomentSlice_eq_bot_of_le_three hL 3 (by norm_num) le_rfl, Submodule.mem_bot] at hu
  subst hu
  simp [evenNativeEnergy]

/-- At `K = 3` and `K = 4` the odd slice is zero; its bound is vacuous. -/
theorem oddMomentSliceLowerBound_of_le_four {L : ℝ} (hL : 0 < L) (K : ℕ)
    (h2 : 2 ≤ K) (h4 : K ≤ 4) (ε : ℝ) : OddMomentSliceLowerBound L K ε := by
  intro v hv
  rw [oddMomentSlice_eq_bot_of_le_four hL K h2 h4, Submodule.mem_bot] at hv
  subst hv
  simp [oddNativeEnergy]

/-! ## Parity moment-shift algebra (independent of the prime source) -/

/-- Multiplication by the centered Fourier index, before the harmless derivative
factor `2π i/L`. This is a fixed-seed coordinate map, not an isometry. -/
def centeredMomentShift (K : ℕ) :
    (Fin (2 * K + 1) → ℂ) →ₗ[ℂ] (Fin (2 * K + 1) → ℂ) where
  toFun u i := (centeredIndex K i : ℂ) * u i
  map_add' u v := by
    ext i
    simp [mul_add]
  map_smul' c u := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

@[simp] theorem centeredMomentShift_apply (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (i : Fin (2 * K + 1)) :
    centeredMomentShift K u i = (centeredIndex K i : ℂ) * u i := rfl

/-- Multiplying frequencies by their index shifts every centered moment exactly. -/
theorem centeredMoment_shift (K r : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    centeredMoment K r (centeredMomentShift K u) =
      centeredMoment K (r + 1) u := by
  unfold centeredMoment
  apply Finset.sum_congr rfl
  intro i _
  change (centeredIndex K i : ℂ) ^ r *
      ((centeredIndex K i : ℂ) * u i) =
        (centeredIndex K i : ℂ) ^ (r + 1) * u i
  rw [pow_succ]
  ring

end Zeta23.OPICARound4.ArithmeticFrontier
