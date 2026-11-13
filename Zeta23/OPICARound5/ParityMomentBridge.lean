import Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceCoordinates

/-! # Post-299 successor: odd-to-even fixed quartic moment parity bridge
Historical OPICA Round4 source bytes remain frozen. This extension is a draft
formal candidate and requires an independently authorized successor source scope.
No signed prime inequality or RH closure is asserted. -/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open CCM RegularCells Module
open scoped BigOperators ComplexConjugate

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


/-! ## The odd-to-even exact sequence of fixed quartic moment seeds -/

/-- The unique centered Fourier index. -/
def centeredZeroIndex (K : ℕ) : Fin (2 * K + 1) :=
  ⟨K, by omega⟩

@[simp] theorem centeredIndex_centeredZeroIndex (K : ℕ) :
    centeredIndex K (centeredZeroIndex K) = 0 := by
  simp [centeredIndex, centeredZeroIndex]

theorem centeredIndex_eq_zero_iff_centeredZeroIndex
    (K : ℕ) (i : Fin (2 * K + 1)) :
    centeredIndex K i = 0 ↔ i = centeredZeroIndex K := by
  constructor
  · intro hi
    apply Fin.ext
    dsimp [centeredIndex] at hi
    omega
  · rintro rfl
    exact centeredIndex_centeredZeroIndex K

/-- Frequency multiplication anticommutes with coefficient reversal. -/
theorem centeredMomentShift_reverse (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    reverseCoefficients K (centeredMomentShift K u) =
      -(centeredMomentShift K (reverseCoefficients K u)) := by
  ext i
  simp only [reverseCoefficients, centeredMomentShift_apply, Pi.neg_apply,
    centeredIndex_rev, Int.cast_neg]
  ring

/-- Differentiation switches odd reversal to even reversal in seed coordinates. -/
theorem centeredMomentShift_even_of_odd (K : ℕ)
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ oddCoefficientSubspace K) :
    centeredMomentShift K u ∈ evenCoefficientSubspace K := by
  rw [mem_evenCoefficientSubspace_iff, centeredMomentShift_reverse,
    (mem_oddCoefficientSubspace_iff K u).mp hu]
  simp

/-- Fixed quartic odd moment conditions transfer to even moment conditions. -/
theorem centeredMomentShift_mem_fixedEvenMomentSeed (K : ℕ)
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ fixedOddMomentSeed K) :
    centeredMomentShift K u ∈ fixedEvenMomentSeed K := by
  obtain ⟨hp, h1, h3, h5, h7⟩ :=
    (mem_fixedOddMomentSeed_iff K u).mp hu
  apply (mem_fixedEvenMomentSeed_iff K _).mpr
  exact ⟨centeredMomentShift_even_of_odd K hp,
    by simpa only [centeredMoment_shift] using h1,
    by simpa only [centeredMoment_shift] using h3,
    by simpa only [centeredMoment_shift] using h5,
    by simpa only [centeredMoment_shift] using h7⟩

/-- Frequency multiplication restricted to the actual fixed quartic seed spaces. -/
def oddToEvenMomentShift (K : ℕ) :
    fixedOddMomentSeed K →ₗ[ℂ] fixedEvenMomentSeed K :=
  LinearMap.codRestrict (fixedEvenMomentSeed K)
    ((centeredMomentShift K).comp (Submodule.subtype (fixedOddMomentSeed K)))
    (fun u => centeredMomentShift_mem_fixedEvenMomentSeed K u.property)

/-- An odd vector has vanishing central coefficient (in characteristic zero). -/
theorem oddCoefficient_center_zero (K : ℕ)
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ oddCoefficientSubspace K) :
    u (centeredZeroIndex K) = 0 := by
  have hr := congrFun ((mem_oddCoefficientSubspace_iff K u).mp hu)
    (centeredZeroIndex K)
  have hrev : (centeredZeroIndex K).rev = centeredZeroIndex K := by
    apply Fin.ext
    simp only [Fin.val_rev]
    dsimp [centeredZeroIndex]
    omega
  simp only [reverseCoefficients, hrev, Pi.neg_apply] at hr
  have ht : (2 : ℂ) * u (centeredZeroIndex K) = 0 := by
    linear_combination hr
  exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

/-- Multiplication by the centered index has no kernel on the odd sector. -/
theorem centeredMomentShift_injective_on_odd (K : ℕ)
    {u v : Fin (2 * K + 1) → ℂ}
    (hu : u ∈ oddCoefficientSubspace K)
    (hv : v ∈ oddCoefficientSubspace K)
    (heq : centeredMomentShift K u = centeredMomentShift K v) : u = v := by
  funext i
  by_cases hi : i = centeredZeroIndex K
  · rw [hi, oddCoefficient_center_zero K hu, oddCoefficient_center_zero K hv]
  · have hn : centeredIndex K i ≠ 0 :=
      fun hz => hi ((centeredIndex_eq_zero_iff_centeredZeroIndex K i).mp hz)
    have hn' : (centeredIndex K i : ℂ) ≠ 0 := by exact_mod_cast hn
    have he := congrFun heq i
    simp only [centeredMomentShift_apply] at he
    exact (mul_left_cancel₀ hn') he

theorem oddToEvenMomentShift_injective (K : ℕ) :
    Function.Injective (oddToEvenMomentShift K) := by
  intro u v huv
  apply Subtype.ext
  apply centeredMomentShift_injective_on_odd K
    ((mem_fixedOddMomentSeed_iff K _).mp u.property).1
    ((mem_fixedOddMomentSeed_iff K _).mp v.property).1
  exact congrArg Subtype.val huv

/-- Evaluation of the central Fourier coefficient on the even quartic slice. -/
def evenMomentCenterEval (K : ℕ) : fixedEvenMomentSeed K →ₗ[ℂ] ℂ where
  toFun u := u (centeredZeroIndex K)
  map_add' u v := rfl
  map_smul' c u := rfl

/-- The odd-to-even map lands in the kernel of the central coordinate. -/
theorem evenMomentCenterEval_oddToEven_zero (K : ℕ)
    (u : fixedOddMomentSeed K) :
    evenMomentCenterEval K (oddToEvenMomentShift K u) = 0 := by
  change (centeredMomentShift K u) (centeredZeroIndex K) = 0
  simp only [centeredMomentShift_apply, centeredIndex_centeredZeroIndex,
    Int.cast_zero, zero_mul]

/-- Division by the frequency away from zero; the zero-frequency value is
defined as zero by field inversion. -/
def centeredMomentUnshift (K : ℕ) :
    (Fin (2 * K + 1) → ℂ) →ₗ[ℂ] (Fin (2 * K + 1) → ℂ) where
  toFun u i := (centeredIndex K i : ℂ)⁻¹ * u i
  map_add' u v := by ext i; simp [mul_add]
  map_smul' c u := by ext i; simp only [Pi.smul_apply, smul_eq_mul]; ring

@[simp] theorem centeredMomentUnshift_apply (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (i : Fin (2 * K + 1)) :
    centeredMomentUnshift K u i = (centeredIndex K i : ℂ)⁻¹ * u i := rfl

/-- The inverse is odd under reversal when its input is even. -/
theorem centeredMomentUnshift_odd_of_even (K : ℕ)
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ evenCoefficientSubspace K) :
    centeredMomentUnshift K u ∈ oddCoefficientSubspace K := by
  rw [mem_oddCoefficientSubspace_iff]
  ext i
  have hi := congrFun ((mem_evenCoefficientSubspace_iff K u).mp hu) i
  change (centeredIndex K i.rev : ℂ)⁻¹ * u i.rev =
    -((centeredIndex K i : ℂ)⁻¹ * u i)
  rw [hi, centeredIndex_rev]
  simp

/-- The inverse reverses the moment shift if the center coefficient vanishes. -/
theorem centeredMoment_unshift_succ (K r : ℕ)
    (u : Fin (2 * K + 1) → ℂ)
    (hzero : u (centeredZeroIndex K) = 0) :
    centeredMoment K (r + 1) (centeredMomentUnshift K u) =
      centeredMoment K r u := by
  unfold centeredMoment
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = centeredZeroIndex K
  · subst i
    simp [centeredMomentUnshift_apply,
      centeredIndex_centeredZeroIndex, hzero]
  · have hn : centeredIndex K i ≠ 0 :=
      fun hz => hi ((centeredIndex_eq_zero_iff_centeredZeroIndex K i).mp hz)
    have hn' : (centeredIndex K i : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [centeredMomentUnshift_apply, pow_succ]
    field_simp [hn']

/-- Inverse frequency division sends central-zero even seeds to odd seeds. -/
theorem centeredMomentUnshift_mem_fixedOddMomentSeed (K : ℕ)
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ fixedEvenMomentSeed K)
    (hzero : u (centeredZeroIndex K) = 0) :
    centeredMomentUnshift K u ∈ fixedOddMomentSeed K := by
  obtain ⟨hp, h0, h2, h4, h6⟩ :=
    (mem_fixedEvenMomentSeed_iff K u).mp hu
  apply (mem_fixedOddMomentSeed_iff K _).mpr
  exact ⟨centeredMomentUnshift_odd_of_even K hp,
    by simpa using (centeredMoment_unshift_succ K 0 u hzero).trans h0,
    by simpa using (centeredMoment_unshift_succ K 2 u hzero).trans h2,
    by simpa using (centeredMoment_unshift_succ K 4 u hzero).trans h4,
    by simpa using (centeredMoment_unshift_succ K 6 u hzero).trans h6⟩

theorem centeredMomentShift_unshift_of_center_zero (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ)
    (hzero : u (centeredZeroIndex K) = 0) :
    centeredMomentShift K (centeredMomentUnshift K u) = u := by
  funext i
  by_cases hi : i = centeredZeroIndex K
  · subst i
    simp [centeredMomentShift_apply, centeredMomentUnshift_apply,
      centeredIndex_centeredZeroIndex, hzero]
  · have hn : centeredIndex K i ≠ 0 :=
      fun hz => hi ((centeredIndex_eq_zero_iff_centeredZeroIndex K i).mp hz)
    have hn' : (centeredIndex K i : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [centeredMomentShift_apply, centeredMomentUnshift_apply]
    field_simp [hn']

/-- Exactness in the middle at *every* cutoff, including the zero-dimensional
degenerate cases K ≤ 3. -/
theorem oddToEvenMomentShift_range_eq_center_ker (K : ℕ) :
    LinearMap.range (oddToEvenMomentShift K) =
      LinearMap.ker (evenMomentCenterEval K) := by
  apply Submodule.ext
  intro u
  constructor
  · rintro ⟨v, rfl⟩
    exact LinearMap.mem_ker.mpr (evenMomentCenterEval_oddToEven_zero K v)
  · intro hu
    have hz : (u : Fin (2 * K + 1) → ℂ) (centeredZeroIndex K) = 0 :=
      LinearMap.mem_ker.mp hu
    let v : fixedOddMomentSeed K :=
      ⟨centeredMomentUnshift K (u : Fin (2 * K + 1) → ℂ),
        centeredMomentUnshift_mem_fixedOddMomentSeed K u.property hz⟩
    refine ⟨v, ?_⟩
    apply Subtype.ext
    exact centeredMomentShift_unshift_of_center_zero K u hz

/-- The even physical diagonal commutes with frequency multiplication, but
neither map is unitary and no Weil energy sign is transported. -/
theorem centeredMomentShift_fixedSeedDiagonal (L : ℝ) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    centeredMomentShift K (fixedSeedDiagonal L K u) =
      fixedSeedDiagonal L K (centeredMomentShift K u) := by
  funext i
  simp only [centeredMomentShift_apply, fixedSeedDiagonal_apply]
  ring



/-- Exact dimension of the even quartic seed, transported through the existing
nonunitary but bijective fixed-seed physical coordinate chart. -/
theorem finrank_fixedEvenMomentSeed (K : ℕ) (hK : 2 ≤ K) :
    finrank ℂ (fixedEvenMomentSeed K) = K - 3 := by
  calc
    finrank ℂ (fixedEvenMomentSeed K) =
        finrank ℂ (evenMomentSlice (1 : ℝ) K) :=
      (evenMomentSliceSeedEquiv (by norm_num : (0 : ℝ) < 1) K).finrank_eq
    _ = K - 3 := finrank_evenMomentSlice (by norm_num) K hK

/-- Exact dimension of the odd quartic seed. -/
theorem finrank_fixedOddMomentSeed (K : ℕ) (hK : 2 ≤ K) :
    finrank ℂ (fixedOddMomentSeed K) = K - 4 := by
  calc
    finrank ℂ (fixedOddMomentSeed K) =
        finrank ℂ (oddMomentSlice (1 : ℝ) K) :=
      (oddMomentSliceSeedEquiv (by norm_num : (0 : ℝ) < 1) K).finrank_eq
    _ = K - 4 := finrank_oddMomentSlice (by norm_num) K hK

/-- The center-coordinate quotient is nontrivial precisely in the range
needed for the short exact sequence. This uses the preexisting Lean-proved
slice dimensions and the new exact middle-kernel equivalence. -/
theorem evenMomentCenterEval_surjective (K : ℕ) (hK : 4 ≤ K) :
    Function.Surjective (evenMomentCenterEval K) := by
  have heven := finrank_fixedEvenMomentSeed K (by omega)
  have hodd := finrank_fixedOddMomentSeed K (by omega)
  have hinj := oddToEvenMomentShift_injective K
  have hkerT : LinearMap.ker (oddToEvenMomentShift K) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hrange := (oddToEvenMomentShift K).finrank_range_add_finrank_ker
  rw [hkerT, finrank_bot, add_zero, hodd] at hrange
  have hcenter := (evenMomentCenterEval K).finrank_range_add_finrank_ker
  rw [← oddToEvenMomentShift_range_eq_center_ker K, hrange, heven] at hcenter
  have hrank : finrank ℂ (LinearMap.range (evenMomentCenterEval K)) = 1 := by
    omega
  have hnonzero : ∃ u : fixedEvenMomentSeed K, evenMomentCenterEval K u ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : evenMomentCenterEval K = 0 := by
      ext u
      exact h u
    have hrank0 : finrank ℂ (LinearMap.range (evenMomentCenterEval K)) = 0 := by
      rw [hz]
      simp
    omega
  obtain ⟨u, hu⟩ := hnonzero
  intro c
  refine ⟨(c * (evenMomentCenterEval K u)⁻¹) • u, ?_⟩
  rw [map_smul, smul_eq_mul]
  field_simp [hu]

/-- **Complete fixed-quartic parity short exact sequence.**
There is one mean-bearing complex direction in the even seed beyond the
derivative image of the odd seed. This is not a positivity theorem. -/
theorem fixedMomentParityShortExact (K : ℕ) (hK : 4 ≤ K) :
    Function.Injective (oddToEvenMomentShift K) ∧
      LinearMap.range (oddToEvenMomentShift K) =
        LinearMap.ker (evenMomentCenterEval K) ∧
      Function.Surjective (evenMomentCenterEval K) :=
  ⟨oddToEvenMomentShift_injective K,
    oddToEvenMomentShift_range_eq_center_ker K,
    evenMomentCenterEval_surjective K hK⟩

/-- Transport of the parity shift to physical moment slices.
The two coordinate charts are invertible but explicitly NONUNITARY.
No energy-sign conclusion is made. -/
def oddToEvenPhysicalMomentShift {L : ℝ} (hL : 0 < L) (K : ℕ) :
    oddMomentSlice L K →ₗ[ℂ] evenMomentSlice L K :=
  ((evenMomentSliceSeedEquiv hL K).toLinearMap.comp
      (oddToEvenMomentShift K)).comp
    ((oddMomentSliceSeedEquiv hL K).symm.toLinearMap)


end Zeta23.OPICARound4.ArithmeticFrontier


/-! Exact-head theorem-specific axiom printouts for the candidate compiler gate. -/
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.centeredMoment_shift
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddToEvenMomentShift_range_eq_center_ker
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.fixedMomentParityShortExact
#print axioms Zeta23.OPICARound4.ArithmeticFrontier.oddToEvenPhysicalMomentShift
