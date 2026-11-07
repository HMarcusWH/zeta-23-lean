import Zeta23.OPICARound4.RegularCells.FixedSeed
import Mathlib.Algebra.BigOperators.Fin
import Zeta23.OPICARound4.RegularCells.NativeCompressionSeparation

noncomputable section
namespace Zeta23.OPICARound4.NativeZeroFrame
open CCM RegularCells NativeParitySeparation
open scoped BigOperators ComplexConjugate

def center (K : ℕ) : Fin (2 * K + 1) := ⟨K, by omega⟩
def pos (K : ℕ) (i : Fin K) : Fin (2 * K + 1) := ⟨K + i.val + 1, by omega⟩
def neg (K : ℕ) (i : Fin K) : Fin (2 * K + 1) := ⟨K - (i.val + 1), by omega⟩

@[simp] theorem centered_center (K : ℕ) : centeredIndex K (center K) = 0 := by
  simp [center, centeredIndex]
@[simp] theorem centered_pos (K : ℕ) (i : Fin K) :
    centeredIndex K (pos K i) = (i.val : ℤ) + 1 := by
  simp only [pos, centeredIndex, Nat.cast_add, Nat.cast_one]
  ring
@[simp] theorem centered_neg (K : ℕ) (i : Fin K) :
    centeredIndex K (neg K i) = -((i.val : ℤ) + 1) := by
  simp only [neg, centeredIndex]
  omega

def foldIndex (K : ℕ) : Unit ⊕ (Fin K ⊕ Fin K) → Fin (2 * K + 1)
  | .inl _ => center K
  | .inr (.inl i) => pos K i
  | .inr (.inr i) => neg K i

theorem foldIndex_bijective (K : ℕ) : Function.Bijective (foldIndex K) := by
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => rfl
      | inr y =>
        cases y <;> simp only [foldIndex] at h
        all_goals have hh := congrArg Fin.val h
        all_goals simp only [center, pos, neg] at hh
        all_goals omega
    | inr x =>
      cases y with
      | inl y =>
        cases x <;> simp only [foldIndex] at h
        all_goals have hh := congrArg Fin.val h
        all_goals simp only [center, pos, neg] at hh
        all_goals omega
      | inr y =>
        cases x <;> cases y <;> simp only [foldIndex] at h
        all_goals have hh := congrArg Fin.val h
        all_goals simp only [pos, neg] at hh
        · congr 2
          apply Fin.ext
          omega
        · omega
        · omega
        · congr 2
          apply Fin.ext
          omega
  · intro i
    by_cases h : i.val = K
    · refine ⟨.inl (), ?_⟩
      apply Fin.ext
      exact h.symm
    · by_cases hp : K < i.val
      · refine ⟨.inr (.inl ⟨i.val - K - 1, by omega⟩), ?_⟩
        apply Fin.ext
        simp only [foldIndex, pos]
        omega
      · refine ⟨.inr (.inr ⟨K - i.val - 1, by omega⟩), ?_⟩
        apply Fin.ext
        simp only [foldIndex, neg]
        omega

def foldEquiv (K : ℕ) : Unit ⊕ (Fin K ⊕ Fin K) ≃ Fin (2 * K + 1) :=
  Equiv.ofBijective (foldIndex K) (foldIndex_bijective K)

theorem sum_fold (K : ℕ) {A : Type*} [AddCommMonoid A]
    (f : Fin (2 * K + 1) → A) :
    ∑ i, f i = f (center K) + (∑ i : Fin K, f (pos K i)) +
      ∑ i : Fin K, f (neg K i) := by
  rw [← Equiv.sum_comp (foldEquiv K)]
  simp [foldEquiv, foldIndex, Fintype.sum_sum_type, add_assoc]

@[simp] theorem rev_pos (K : ℕ) (i : Fin K) : (pos K i).rev = neg K i := by
  apply Fin.ext
  simp only [Fin.val_rev, pos, neg]
  omega

@[simp] theorem rev_center (K : ℕ) : (center K).rev = center K := by
  apply Fin.ext
  simp only [Fin.val_rev, center]
  omega

@[simp] theorem rev_neg (K : ℕ) (i : Fin K) : (neg K i).rev = pos K i := by
  rw [← rev_pos, Fin.rev_rev]

def foldLift (K : ℕ) (c : ℂ) (x y : Fin K → ℂ) : Fin (2 * K + 1) → ℂ :=
  fun i => match (foldEquiv K).symm i with
    | .inl _ => c
    | .inr (.inl j) => x j
    | .inr (.inr j) => y j

@[simp] theorem foldLift_center (K : ℕ) (c : ℂ) (x y : Fin K → ℂ) :
    foldLift K c x y (center K) = c := by
  change foldLift K c x y ((foldEquiv K) (.inl ())) = c
  simp [foldLift]
@[simp] theorem foldLift_pos (K : ℕ) (c : ℂ) (x y : Fin K → ℂ) (i : Fin K) :
    foldLift K c x y (pos K i) = x i := by
  change foldLift K c x y ((foldEquiv K) (.inr (.inl i))) = x i
  simp [foldLift]
@[simp] theorem foldLift_neg (K : ℕ) (c : ℂ) (x y : Fin K → ℂ) (i : Fin K) :
    foldLift K c x y (neg K i) = y i := by
  change foldLift K c x y ((foldEquiv K) (.inr (.inr i))) = y i
  simp [foldLift]

theorem fold_ext {K : ℕ} {u v : Fin (2 * K + 1) → ℂ}
    (hc : u (center K) = v (center K))
    (hp : ∀ i, u (pos K i) = v (pos K i))
    (hn : ∀ i, u (neg K i) = v (neg K i)) : u = v := by
  funext j
  obtain ⟨i, rfl⟩ := (foldEquiv K).surjective j
  rcases i with _ | (i | i)
  · exact hc
  · exact hp i
  · exact hn i

theorem foldLift_even (K : ℕ) (c : ℂ) (x : Fin K → ℂ) :
    foldLift K c x x ∈ evenCoefficientSubspace K := by
  rw [mem_evenCoefficientSubspace_iff]
  apply fold_ext <;> simp [reverseCoefficients]

theorem foldLift_odd (K : ℕ) (x : Fin K → ℂ) :
    foldLift K 0 x (-x) ∈ oddCoefficientSubspace K := by
  rw [mem_oddCoefficientSubspace_iff]
  apply fold_ext <;> simp [reverseCoefficients]

theorem moment_foldLift (K k : ℕ) (c : ℂ) (x y : Fin K → ℂ) :
    centeredMoment K k (foldLift K c x y) =
      (0 : ℂ)^k * c + (∑ i : Fin K, (i.val + 1 : ℂ)^k * x i) +
        ∑ i : Fin K, (-(i.val + 1 : ℂ))^k * y i := by
  unfold centeredMoment
  rw [sum_fold]
  simp

def rawEvenLift (K : ℕ) (x : Fin K → ℂ) : Fin (2 * K + 1) → ℂ :=
  foldLift K (-2 * ∑ i, x i / (i.val + 1 : ℂ)^2)
    (fun i => x i / (i.val + 1 : ℂ)^2) (fun i => x i / (i.val + 1 : ℂ)^2)

def rawOddLift (K : ℕ) (x : Fin K → ℂ) : Fin (2 * K + 1) → ℂ :=
  foldLift K 0 (fun i => x i / (i.val + 1 : ℂ)^2)
    (fun i => -(x i / (i.val + 1 : ℂ)^2))

theorem index_ne_zero {K : ℕ} (i : Fin K) : (i.val + 1 : ℂ) ≠ 0 := by
  exact_mod_cast (show i.val + 1 ≠ 0 by omega)

theorem zero_diagonal_rawEvenLift (K : ℕ) (x : Fin K → ℂ) :
    fixedSeedDiagonal 0 K (rawEvenLift K x) = foldLift K 0 x x := by
  apply fold_ext
  · simp [fixedSeedDiagonal_apply, fixedSeedDiagonalEntry, fixedSeedParameter, rawEvenLift]
  · intro i
    have hi := index_ne_zero i
    simp [fixedSeedDiagonal_apply, fixedSeedDiagonalEntry, fixedSeedParameter, rawEvenLift]
    field_simp
  · intro i
    have hi := index_ne_zero i
    simp [fixedSeedDiagonal_apply, fixedSeedDiagonalEntry, fixedSeedParameter, rawEvenLift]
    field_simp
    <;> ring

theorem zero_diagonal_rawOddLift (K : ℕ) (x : Fin K → ℂ) :
    fixedSeedDiagonal 0 K (rawOddLift K x) = foldLift K 0 x (-x) := by
  apply fold_ext
  · simp [fixedSeedDiagonal_apply, fixedSeedDiagonalEntry, fixedSeedParameter, rawOddLift]
  · intro i
    have hi := index_ne_zero i
    simp [fixedSeedDiagonal_apply, fixedSeedDiagonalEntry, fixedSeedParameter, rawOddLift]
    field_simp
  · intro i
    have hi := index_ne_zero i
    simp [fixedSeedDiagonal_apply, fixedSeedDiagonalEntry, fixedSeedParameter, rawOddLift]
    field_simp
    <;> ring

theorem rawEvenLift_moment_zero (K : ℕ) (x : Fin K → ℂ) :
    centeredMoment K 0 (rawEvenLift K x) = 0 := by
  rw [rawEvenLift, moment_foldLift]
  simp only [pow_zero, one_mul]
  ring

theorem rawEvenLift_moment_two (K : ℕ) (x : Fin K → ℂ) :
    centeredMoment K 2 (rawEvenLift K x) = 2 * ∑ i, x i := by
  rw [rawEvenLift, moment_foldLift]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add, neg_sq]
  have hsum : (∑ i : Fin K, (i.val + 1 : ℂ)^2 *
      (x i / (i.val + 1 : ℂ)^2)) = ∑ i, x i := by
    apply Finset.sum_congr rfl
    intro i _
    have hi := index_ne_zero i
    field_simp
  rw [hsum]
  ring

theorem rawEvenLift_moment_four (K : ℕ) (x : Fin K → ℂ) :
    centeredMoment K 4 (rawEvenLift K x) =
      2 * ∑ i, (i.val + 1 : ℂ)^2 * x i := by
  rw [rawEvenLift, moment_foldLift]
  have hn : ∀ a : ℂ, (-a)^4 = a^4 := by intro a; ring
  simp only [zero_pow (by decide : 4 ≠ 0), zero_mul, zero_add, hn]
  have hsum : (∑ i : Fin K, (i.val + 1 : ℂ)^4 *
      (x i / (i.val + 1 : ℂ)^2)) = ∑ i, (i.val + 1 : ℂ)^2 * x i := by
    apply Finset.sum_congr rfl
    intro i _
    have hi := index_ne_zero i
    field_simp
    <;> ring
  rw [hsum]
  ring

theorem rawOddLift_moment_one (K : ℕ) (x : Fin K → ℂ) :
    centeredMoment K 1 (rawOddLift K x) = 2 * ∑ i, x i / (i.val + 1 : ℂ) := by
  rw [rawOddLift, moment_foldLift]
  simp only [pow_one, zero_mul, zero_add, neg_mul_neg]
  have hsum : (∑ i : Fin K, (i.val + 1 : ℂ) *
      (x i / (i.val + 1 : ℂ)^2)) = ∑ i, x i / (i.val + 1 : ℂ) := by
    apply Finset.sum_congr rfl
    intro i _
    have hi := index_ne_zero i
    field_simp
  rw [hsum]
  ring

theorem rawOddLift_moment_three (K : ℕ) (x : Fin K → ℂ) :
    centeredMoment K 3 (rawOddLift K x) = 2 * ∑ i, (i.val + 1 : ℂ) * x i := by
  rw [rawOddLift, moment_foldLift]
  have hn : ∀ a : ℂ, (-a)^3 = -(a^3) := by intro a; ring
  simp only [zero_pow (by decide : 3 ≠ 0), zero_mul, zero_add,
    hn, neg_mul_neg]
  have hsum : (∑ i : Fin K, (i.val + 1 : ℂ)^3 *
      (x i / (i.val + 1 : ℂ)^2)) = ∑ i, (i.val + 1 : ℂ) * x i := by
    apply Finset.sum_congr rfl
    intro i _
    have hi := index_ne_zero i
    field_simp
    <;> ring
  rw [hsum]
  ring

theorem rawEvenLift_mem_iff (K : ℕ) (x : Fin K → ℂ) :
    rawEvenLift K x ∈ fixedEvenSeed K ↔
      (∑ i, x i = 0) ∧ (∑ i, (i.val + 1 : ℂ)^2 * x i = 0) := by
  rw [mem_fixedEvenSeed_iff, rawEvenLift_moment_zero,
    rawEvenLift_moment_two, rawEvenLift_moment_four]
  have hp : rawEvenLift K x ∈ evenCoefficientSubspace K := foldLift_even _ _ _
  simp [hp]

theorem rawOddLift_mem_iff (K : ℕ) (x : Fin K → ℂ) :
    rawOddLift K x ∈ fixedOddSeed K ↔
      (∑ i, x i / (i.val + 1 : ℂ) = 0) ∧ (∑ i, (i.val + 1 : ℂ) * x i = 0) := by
  rw [mem_fixedOddSeed_iff, rawOddLift_moment_one, rawOddLift_moment_three]
  have hp : rawOddLift K x ∈ oddCoefficientSubspace K := foldLift_odd _ _
  simp [hp]

theorem even_eq_fold {K : ℕ} (u : Fin (2 * K + 1) → ℂ)
    (hu : u ∈ evenCoefficientSubspace K) :
    u = foldLift K (u (center K)) (fun i => u (pos K i)) (fun i => u (pos K i)) := by
  apply fold_ext
  · simp
  · intro i; simp
  · intro i
    have h := congrFun ((mem_evenCoefficientSubspace_iff K u).mp hu) (pos K i)
    simpa [reverseCoefficients] using h

theorem odd_eq_fold {K : ℕ} (u : Fin (2 * K + 1) → ℂ)
    (hu : u ∈ oddCoefficientSubspace K) :
    u = foldLift K 0 (fun i => u (pos K i)) (fun i => -u (pos K i)) := by
  have h := (mem_oddCoefficientSubspace_iff K u).mp hu
  apply fold_ext
  · have hc := congrFun h (center K)
    have hc' : u (center K) = -u (center K) := by simpa [reverseCoefficients] using hc
    simpa using (CharZero.eq_neg_self_iff.mp hc')
  · intro i; simp
  · intro i
    have hi := congrFun h (pos K i)
    simpa [reverseCoefficients] using hi

def positiveCoordinates (K : ℕ) (u : Fin (2 * K + 1) → ℂ) : Fin K → ℂ :=
  fun i => (i.val + 1 : ℂ)^2 * u (pos K i)

@[simp] theorem positiveCoordinates_rawEvenLift (K : ℕ) (x : Fin K → ℂ) :
    positiveCoordinates K (rawEvenLift K x) = x := by
  funext i
  have hi := index_ne_zero i
  simp [positiveCoordinates, rawEvenLift, hi]
  field_simp

@[simp] theorem positiveCoordinates_rawOddLift (K : ℕ) (x : Fin K → ℂ) :
    positiveCoordinates K (rawOddLift K x) = x := by
  funext i
  have hi := index_ne_zero i
  simp [positiveCoordinates, rawOddLift, hi]
  field_simp

theorem rawEvenLift_positiveCoordinates {K : ℕ} (u : Fin (2 * K + 1) → ℂ)
    (hu : u ∈ fixedEvenSeed K) : rawEvenLift K (positiveCoordinates K u) = u := by
  have h := (mem_fixedEvenSeed_iff K u).mp hu
  have hf := even_eq_fold u h.1
  have h0 := h.2.1
  rw [hf, moment_foldLift] at h0
  simp only [pow_zero, one_mul] at h0
  apply fold_ext
  · simp only [rawEvenLift, foldLift_center]
    have hs : (∑ i, positiveCoordinates K u i / (i.val + 1 : ℂ)^2) =
        ∑ i : Fin K, u (pos K i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := index_ne_zero i
      simp [positiveCoordinates, hi]
    rw [hs]
    linear_combination -h0
  · intro i
    have hi := index_ne_zero i
    simp [rawEvenLift, positiveCoordinates, hi]
  · intro i
    have hi := index_ne_zero i
    have he := congrFun hf (neg K i)
    simpa [rawEvenLift, positiveCoordinates, hi] using he.symm

theorem rawOddLift_positiveCoordinates {K : ℕ} (u : Fin (2 * K + 1) → ℂ)
    (hu : u ∈ fixedOddSeed K) : rawOddLift K (positiveCoordinates K u) = u := by
  have h := (mem_fixedOddSeed_iff K u).mp hu
  have hf := odd_eq_fold u h.1
  apply fold_ext
  · have hc := congrFun hf (center K)
    simpa [rawOddLift] using hc.symm
  · intro i
    have hi := index_ne_zero i
    simp [rawOddLift, positiveCoordinates, hi]
  · intro i
    have hi := index_ne_zero i
    have he := congrFun hf (neg K i)
    simpa [rawOddLift, positiveCoordinates, hi] using he.symm

theorem mem_nativeLimitingEvenCarrier_iff (K : ℕ) (x : EuclideanSpace ℂ (Fin K)) :
    x ∈ nativeLimitingEvenCarrier K ↔
      (∑ i, x i = 0) ∧ (∑ i, (i.val + 1 : ℂ)^2 * x i = 0) := by
  constructor
  · intro hx
    constructor
    · have h := (Submodule.mem_orthogonal _ _).mp hx (nativeConstantVector K)
        (Submodule.subset_span (by simp))
      simpa [nativeConstantVector, PiLp.inner_apply] using h
    · have h := (Submodule.mem_orthogonal _ _).mp hx (nativeSquareVector K)
        (Submodule.subset_span (by simp))
      simpa [nativeSquareVector, PiLp.inner_apply, mul_comm] using h
  · rintro ⟨h0,h2⟩
    apply (Submodule.mem_orthogonal _ _).mpr
    intro v hv
    obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hv
    have hc : inner ℂ (nativeConstantVector K) x = 0 := by
      simpa [nativeConstantVector, PiLp.inner_apply] using h0
    have hd : inner ℂ (nativeSquareVector K) x = 0 := by
      simpa [nativeSquareVector, PiLp.inner_apply, mul_comm] using h2
    simp [inner_add_left, inner_smul_left, hc, hd]

theorem mem_nativeLimitingOddCarrier_iff (K : ℕ) (x : EuclideanSpace ℂ (Fin K)) :
    x ∈ nativeLimitingOddCarrier K ↔
      (∑ i, x i / (i.val + 1 : ℂ) = 0) ∧ (∑ i, (i.val + 1 : ℂ) * x i = 0) := by
  constructor
  · intro hx
    constructor
    · have h := (Submodule.mem_orthogonal _ _).mp hx (nativeReciprocalVector K)
        (Submodule.subset_span (by simp))
      simpa [nativeReciprocalVector, PiLp.inner_apply, div_eq_mul_inv, mul_comm] using h
    · have h := (Submodule.mem_orthogonal _ _).mp hx (nativeIndexVector K)
        (Submodule.subset_span (by simp))
      simpa [nativeIndexVector, PiLp.inner_apply, mul_comm] using h
  · rintro ⟨h0,h2⟩
    apply (Submodule.mem_orthogonal _ _).mpr
    intro v hv
    obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hv
    have hc : inner ℂ (nativeReciprocalVector K) x = 0 := by
      simpa [nativeReciprocalVector, PiLp.inner_apply, div_eq_mul_inv, mul_comm] using h0
    have hd : inner ℂ (nativeIndexVector K) x = 0 := by
      simpa [nativeIndexVector, PiLp.inner_apply, mul_comm] using h2
    simp [inner_add_left, inner_smul_left, hc, hd]

def evenZeroEquiv (K : ℕ) : fixedEvenSeed K ≃ₗ[ℂ] nativeLimitingEvenCarrier K where
  toFun u := ⟨WithLp.toLp 2 (positiveCoordinates K u), by
    apply (mem_nativeLimitingEvenCarrier_iff K _).mpr
    have hu : rawEvenLift K (positiveCoordinates K u) ∈ fixedEvenSeed K := by
      rw [rawEvenLift_positiveCoordinates _ u.property]
      exact u.property
    exact (rawEvenLift_mem_iff K _).mp hu⟩
  invFun x := ⟨rawEvenLift K x.val.ofLp,
    (rawEvenLift_mem_iff K _).mpr ((mem_nativeLimitingEvenCarrier_iff K x.val).mp x.property)⟩
  left_inv u := by
    apply Subtype.ext
    exact rawEvenLift_positiveCoordinates _ u.property
  right_inv x := by
    apply Subtype.ext
    exact congrArg (WithLp.toLp 2) (positiveCoordinates_rawEvenLift K x.val.ofLp)
  map_add' u v := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    simp [positiveCoordinates, mul_add]
  map_smul' c u := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    simp [positiveCoordinates]
    ring

def oddZeroEquiv (K : ℕ) : fixedOddSeed K ≃ₗ[ℂ] nativeLimitingOddCarrier K where
  toFun u := ⟨WithLp.toLp 2 (positiveCoordinates K u), by
    apply (mem_nativeLimitingOddCarrier_iff K _).mpr
    have hu : rawOddLift K (positiveCoordinates K u) ∈ fixedOddSeed K := by
      rw [rawOddLift_positiveCoordinates _ u.property]
      exact u.property
    exact (rawOddLift_mem_iff K _).mp hu⟩
  invFun x := ⟨rawOddLift K x.val.ofLp,
    (rawOddLift_mem_iff K _).mpr ((mem_nativeLimitingOddCarrier_iff K x.val).mp x.property)⟩
  left_inv u := by
    apply Subtype.ext
    exact rawOddLift_positiveCoordinates _ u.property
  right_inv x := by
    apply Subtype.ext
    exact congrArg (WithLp.toLp 2) (positiveCoordinates_rawOddLift K x.val.ofLp)
  map_add' u v := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    simp [positiveCoordinates, mul_add]
  map_smul' c u := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    simp [positiveCoordinates]
    ring

theorem inner_even_fold (K : ℕ) (x y : Fin K → ℂ) :
    inner ℂ (WithLp.toLp 2 (foldLift K 0 x x) : EuclideanSpace ℂ (Fin (2*K+1)))
      (WithLp.toLp 2 (foldLift K 0 y y)) =
        2 * inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin K)) (WithLp.toLp 2 y) := by
  simp only [PiLp.inner_apply]
  rw [sum_fold]
  simp
  ring

theorem inner_odd_fold (K : ℕ) (x y : Fin K → ℂ) :
    inner ℂ (WithLp.toLp 2 (foldLift K 0 x (-x)) : EuclideanSpace ℂ (Fin (2*K+1)))
      (WithLp.toLp 2 (foldLift K 0 y (-y))) =
        2 * inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin K)) (WithLp.toLp 2 y) := by
  simp only [PiLp.inner_apply]
  rw [sum_fold]
  simp
  ring

theorem zero_diagonal_even_seed (K : ℕ) (u : fixedEvenSeed K) :
    fixedSeedDiagonal 0 K u = foldLift K 0 (positiveCoordinates K u) (positiveCoordinates K u) := by
  conv_lhs => rw [← rawEvenLift_positiveCoordinates _ u.property]
  exact zero_diagonal_rawEvenLift K _

theorem zero_diagonal_odd_seed (K : ℕ) (u : fixedOddSeed K) :
    fixedSeedDiagonal 0 K u = foldLift K 0 (positiveCoordinates K u) (-positiveCoordinates K u) := by
  conv_lhs => rw [← rawOddLift_positiveCoordinates _ u.property]
  exact zero_diagonal_rawOddLift K _

theorem zero_even_gram (K : ℕ) (u v : fixedEvenSeed K) :
    inner ℂ (WithLp.toLp 2 (fixedSeedDiagonal 0 K u) : EuclideanSpace ℂ (Fin (2*K+1)))
      (WithLp.toLp 2 (fixedSeedDiagonal 0 K v)) =
        2 * inner ℂ ((evenZeroEquiv K u).val) ((evenZeroEquiv K v).val) := by
  rw [zero_diagonal_even_seed, zero_diagonal_even_seed]
  exact inner_even_fold K _ _

theorem zero_odd_gram (K : ℕ) (u v : fixedOddSeed K) :
    inner ℂ (WithLp.toLp 2 (fixedSeedDiagonal 0 K u) : EuclideanSpace ℂ (Fin (2*K+1)))
      (WithLp.toLp 2 (fixedSeedDiagonal 0 K v)) =
        2 * inner ℂ ((oddZeroEquiv K u).val) ((oddZeroEquiv K v).val) := by
  rw [zero_diagonal_odd_seed, zero_diagonal_odd_seed]
  exact inner_odd_fold K _ _

end Zeta23.OPICARound4.NativeZeroFrame
