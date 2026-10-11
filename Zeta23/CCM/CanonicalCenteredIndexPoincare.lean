import Zeta23.CCM.CanonicalCenteredIndexCoercivity

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate

/-!
# POST285 M73 (Step 115): centered-index Poincaré constant `1/4`

For a centered coefficient vector with `∑ z = 0`,

  `‖D z‖² = ∑ n² |z_n|² ≥ (1/4) ∑ |z_n|²`,

uniformly in `K`, improving the `C_K < 5` constant of
`CanonicalCenteredIndexCoercivity.lean` to `4`.

Proof (finite-dimensional, no Fourier analysis): put `w_n = n² - 1/4` (positive
for `n ≠ 0`).  The zero-sum condition gives `z_0 = -∑_{n≠0} z_n`, and weighted
Cauchy–Schwarz gives `|z_0|² ≤ (∑_{n≠0} 1/w_n) ∑_{n≠0} w_n |z_n|²`.  The weight
mass telescopes exactly:

  `∑_{0<|n|≤K} 1/(n² - 1/4) = 4 - 4/(2K+1)`,

so `∑ (n² - 1/4)|z_n|² ≥ (1/(2K+1)) ∑_{n≠0} (n² - 1/4)|z_n|² ≥ 0`, strictly
positive for `z ≠ 0`.

Scope.  The constant `1/4` is the uniform-in-`K` constant on the **whole**
zero-sum carrier; its optimality (approximation of the Dirichlet eigenfunction
`sin(t/2)`) is recorded as DERIVED/numerical evidence only and is not proved
here.  No sharpness is claimed for the narrower even legal carrier.
-/

/-- `∑_{0<|n|≤K} 1/(n² - 1/4)` over the centered grid. -/
def centeredHalfShiftMass (K : ℕ) : ℝ :=
  ∑ i : Fin (2 * K + 1),
    if centeredIndex K i = 0 then 0 else 1 / (((centeredIndex K i : ℤ) : ℝ) ^ 2 - 1 / 4)

private def latticeHalfShift (n : ℤ) : ℝ :=
  if n = 0 then 0 else 1 / ((n : ℝ) ^ 2 - 1 / 4)

private theorem latticeBox_succ_eq' (K : ℕ) :
    latticeBox (K + 1) =
      insert (-((K + 1 : ℕ) : ℤ)) (insert ((K + 1 : ℕ) : ℤ) (latticeBox K)) := by
  ext n
  simp only [mem_latticeBox, Finset.mem_insert]
  push_cast
  omega

private theorem latticeHalfShift_succ (K : ℕ) (n : ℤ) (hn : n = ((K + 1 : ℕ) : ℤ) ∨
    n = -((K + 1 : ℕ) : ℤ)) :
    latticeHalfShift n = 2 / (2 * (K : ℝ) + 1) - 2 / (2 * (K : ℝ) + 3) := by
  have hn0 : n ≠ 0 := by omega
  have hsq : ((n : ℝ)) ^ 2 = ((K : ℝ) + 1) ^ 2 := by
    rcases hn with h | h <;> subst h <;> push_cast <;> ring
  unfold latticeHalfShift
  rw [if_neg hn0, hsq]
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hb : 2 * (K : ℝ) + 1 ≠ 0 := by positivity
  have hc : 2 * (K : ℝ) + 3 ≠ 0 := by positivity
  have ha : ((K : ℝ) + 1) ^ 2 - 1 / 4 = (2 * (K : ℝ) + 1) * (2 * (K : ℝ) + 3) / 4 := by ring
  rw [ha, div_sub_div _ _ hb hc, one_div_div]
  congr 1
  ring

private theorem sum_latticeHalfShift (K : ℕ) :
    ∑ n ∈ latticeBox K, latticeHalfShift n = 4 - 4 / (2 * (K : ℝ) + 1) := by
  induction K with
  | zero =>
      have : latticeBox 0 = {0} := by
        ext n
        simp only [mem_latticeBox, Finset.mem_singleton]
        push_cast
        omega
      rw [this, Finset.sum_singleton]
      simp [latticeHalfShift]
  | succ K ih =>
      have hm1 : ((K + 1 : ℕ) : ℤ) ∉ latticeBox K := by
        rw [mem_latticeBox]; push_cast; omega
      have hm2 : -((K + 1 : ℕ) : ℤ) ∉ insert ((K + 1 : ℕ) : ℤ) (latticeBox K) := by
        rw [Finset.mem_insert, mem_latticeBox]; push_cast; omega
      rw [latticeBox_succ_eq', Finset.sum_insert hm2, Finset.sum_insert hm1, ih,
        latticeHalfShift_succ K _ (Or.inr rfl), latticeHalfShift_succ K _ (Or.inl rfl)]
      push_cast
      ring

/-- Exact telescoping mass `4 - 4/(2K+1)`. -/
theorem centeredHalfShiftMass_eq (K : ℕ) :
    centeredHalfShiftMass K = 4 - 4 / (2 * (K : ℝ) + 1) := by
  have hlat : centeredHalfShiftMass K = ∑ n ∈ latticeBox K, latticeHalfShift n := by
    unfold centeredHalfShiftMass
    exact sum_centeredIndex_eq_sum_latticeBox K latticeHalfShift
  rw [hlat, sum_latticeHalfShift]

/-- **M73 quantitative Poincaré inequality.**  If `∑ z = 0` then
`(1/4) ∑ |z_n|² + (1/(2K+1)) ∑_{n≠0} (n² - 1/4)|z_n|² ≤ ∑ n² |z_n|²`. -/
theorem quarter_sum_normSq_add_remainder_le {K : ℕ} (z : Fin (2 * K + 1) → ℂ)
    (h0 : ∑ i, z i = 0) :
    (1 / 4) * ∑ i, Complex.normSq (z i) +
        (1 / (2 * (K : ℝ) + 1)) *
          ∑ i ∈ (Finset.univ.erase (⟨K, by omega⟩ : Fin (2 * K + 1))),
            (((centeredIndex K i : ℤ) : ℝ) ^ 2 - 1 / 4) * Complex.normSq (z i) ≤
      ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (z i) := by
  classical
  set c : Fin (2 * K + 1) := ⟨K, by omega⟩ with hcdef
  have hc : centeredIndex K c = 0 := by simp [centeredIndex, c]
  set S := (Finset.univ : Finset (Fin (2 * K + 1))).erase c with hS
  have hne : ∀ i ∈ S, centeredIndex K i ≠ 0 := by
    intro i hi h
    exact Finset.ne_of_mem_erase hi (centeredIndex_injective K (h.trans hc.symm))
  have hsq1 : ∀ i ∈ S, (1 : ℝ) ≤ ((centeredIndex K i : ℤ) : ℝ) ^ 2 := by
    intro i hi
    have : (1 : ℤ) ≤ (centeredIndex K i) ^ 2 := by
      have := sq_pos_of_ne_zero (hne i hi)
      omega
    exact_mod_cast this
  have hw : ∀ i ∈ S, 0 < ((centeredIndex K i : ℤ) : ℝ) ^ 2 - 1 / 4 := by
    intro i hi; linarith [hsq1 i hi]
  have hsplit : ∀ g : Fin (2 * K + 1) → ℝ, ∑ i, g i = g c + ∑ i ∈ S, g i := by
    intro g
    rw [hS, Finset.add_sum_erase _ _ (Finset.mem_univ c)]
  have hzc : z c = -∑ i ∈ S, z i := by
    have h := h0
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), ← hS] at h
    linear_combination h
  set W : ℝ := ∑ i ∈ S, (((centeredIndex K i : ℤ) : ℝ) ^ 2 - 1 / 4) * Complex.normSq (z i)
    with hW
  have hmass : centeredHalfShiftMass K =
      ∑ i ∈ S, 1 / (((centeredIndex K i : ℤ) : ℝ) ^ 2 - 1 / 4) := by
    unfold centeredHalfShiftMass
    rw [hsplit, if_pos hc, zero_add]
    exact Finset.sum_congr rfl (fun i hi => if_neg (hne i hi))
  have hcs : Complex.normSq (z c) ≤ centeredHalfShiftMass K * W := by
    rw [hzc, Complex.normSq_neg, Complex.normSq_eq_norm_sq]
    have h1 : ‖∑ i ∈ S, z i‖ ≤ ∑ i ∈ S, ‖z i‖ := norm_sum_le _ _
    have h2 : (∑ i ∈ S, ‖z i‖) ^ 2 ≤
        (∑ i ∈ S, 1 / (((centeredIndex K i : ℤ) : ℝ) ^ 2 - 1 / 4)) * W := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro i hi; exact le_of_lt (one_div_pos.mpr (hw i hi))
      · intro i hi; exact mul_nonneg (hw i hi).le (Complex.normSq_nonneg _)
      · intro i hi
        have hwi := (hw i hi).ne'
        apply le_of_eq
        rw [Complex.normSq_eq_norm_sq, ← mul_assoc, one_div_mul_cancel hwi, one_mul]
    rw [hmass]
    calc ‖∑ i ∈ S, z i‖ ^ 2 ≤ (∑ i ∈ S, ‖z i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  rw [centeredHalfShiftMass_eq] at hcs
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i hi =>
    mul_nonneg (hw i hi).le (Complex.normSq_nonneg _)
  have hK : (0 : ℝ) < 2 * (K : ℝ) + 1 := by positivity
  -- rewrite both full sums through the centre/off-centre split
  have hfull : ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (z i) =
      (1 / 4) * ∑ i ∈ S, Complex.normSq (z i) + W := by
    rw [hsplit, hc, hW, Int.cast_zero, zero_pow two_ne_zero, zero_mul, zero_add,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hmass' : ∑ i, Complex.normSq (z i) = Complex.normSq (z c) + ∑ i ∈ S, Complex.normSq (z i) :=
    hsplit _
  rw [hfull, hmass']
  have hkey : (4 - 4 / (2 * (K : ℝ) + 1)) * W = 4 * W - 4 * (W / (2 * (K : ℝ) + 1)) := by
    ring
  rw [hkey] at hcs
  have hdiv : 1 / (2 * (K : ℝ) + 1) * W = W / (2 * (K : ℝ) + 1) := by ring
  rw [hdiv]
  linarith

/-- **M73 (Step 115):** `∑ |z_n|² ≤ 4 ∑ n² |z_n|²` whenever `∑ z = 0`. -/
theorem sum_normSq_le_four_mul {K : ℕ} (z : Fin (2 * K + 1) → ℂ) (h0 : ∑ i, z i = 0) :
    ∑ i, Complex.normSq (z i) ≤
      4 * ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (z i) := by
  have h := quarter_sum_normSq_add_remainder_le z h0
  have hrem : 0 ≤ (1 / (2 * (K : ℝ) + 1)) *
      ∑ i ∈ (Finset.univ.erase (⟨K, by omega⟩ : Fin (2 * K + 1))),
        (((centeredIndex K i : ℤ) : ℝ) ^ 2 - 1 / 4) * Complex.normSq (z i) := by
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg _ (Complex.normSq_nonneg _)
    have hc : centeredIndex K (⟨K, by omega⟩ : Fin (2 * K + 1)) = 0 := by simp [centeredIndex]
    have hne : centeredIndex K i ≠ 0 := fun h =>
      Finset.ne_of_mem_erase hi (centeredIndex_injective K (h.trans hc.symm))
    have : (1 : ℤ) ≤ (centeredIndex K i) ^ 2 := by
      have := sq_pos_of_ne_zero hne
      omega
    have : (1 : ℝ) ≤ ((centeredIndex K i : ℤ) : ℝ) ^ 2 := by exact_mod_cast this
    linarith
  linarith

/-- **M73 strict form:** a nonzero zero-sum `z` has `‖Dz‖² > ‖z‖²/4`. -/
theorem sum_normSq_lt_four_mul {K : ℕ} (z : Fin (2 * K + 1) → ℂ)
    (h0 : ∑ i, z i = 0) (hz : z ≠ 0) :
    ∑ i, Complex.normSq (z i) <
      4 * ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (z i) := by
  classical
  have h := quarter_sum_normSq_add_remainder_le z h0
  set c : Fin (2 * K + 1) := ⟨K, by omega⟩
  have hc : centeredIndex K c = 0 := by simp [centeredIndex, c]
  set S := (Finset.univ : Finset (Fin (2 * K + 1))).erase c with hS
  have hne : ∀ i ∈ S, centeredIndex K i ≠ 0 := by
    intro i hi h
    exact Finset.ne_of_mem_erase hi (centeredIndex_injective K (h.trans hc.symm))
  have hw : ∀ i ∈ S, 0 < ((centeredIndex K i : ℤ) : ℝ) ^ 2 - 1 / 4 := by
    intro i hi
    have : (1 : ℤ) ≤ (centeredIndex K i) ^ 2 := by
      have := sq_pos_of_ne_zero (hne i hi)
      omega
    have : (1 : ℝ) ≤ ((centeredIndex K i : ℤ) : ℝ) ^ 2 := by exact_mod_cast this
    linarith
  -- some off-centre coordinate is nonzero
  obtain ⟨j, hjS, hj⟩ : ∃ j ∈ S, z j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hz
    funext i
    by_cases hi : i = c
    · subst hi
      have h0' := h0
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), ← hS,
        Finset.sum_eq_zero hall, add_zero] at h0'
      exact h0'
    · exact hall i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  have hWpos : 0 < ∑ i ∈ S, (((centeredIndex K i : ℤ) : ℝ) ^ 2 - 1 / 4) *
      Complex.normSq (z i) :=
    Finset.sum_pos' (fun i hi => mul_nonneg (hw i hi).le (Complex.normSq_nonneg _))
      ⟨j, hjS, mul_pos (hw j hjS) (Complex.normSq_pos.mpr hj)⟩
  have hrem : 0 < (1 / (2 * (K : ℝ) + 1)) *
      ∑ i ∈ S, (((centeredIndex K i : ℤ) : ℝ) ^ 2 - 1 / 4) * Complex.normSq (z i) :=
    mul_pos (by positivity) hWpos
  linarith

/-- Euclidean form: `‖x‖² ≤ 4 ‖D x‖²` when the zeroth centered moment vanishes. -/
theorem norm_sq_le_four_mul_norm_index_sq (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (h0 : centeredMoment K 0 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) = 0) :
    ‖x‖ ^ 2 ≤ 4 * ‖euclideanIndexLinearMap K x‖ ^ 2 := by
  set u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x with hu
  have hsum : ∑ i, u i = 0 := by simpa [centeredMoment] using h0
  have hnorm : ‖x‖ ^ 2 = ∑ i, Complex.normSq (u i) := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.normSq_eq_norm_sq]
    rfl
  have hD : ‖euclideanIndexLinearMap K x‖ ^ 2 =
      ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (u i) := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    have hcoord : (euclideanIndexLinearMap K x) i = ((centeredIndex K i : ℤ) : ℂ) * u i := by
      change ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) (euclideanIndexLinearMap K x)) i = _
      rw [euclideanIndexLinearMap_coordinates]
      simp [indexMatrix, Matrix.mulVec_diagonal, u]
    rw [hcoord, norm_mul, mul_pow, Complex.normSq_eq_norm_sq (u i)]
    congr 1
    rw [Complex.norm_intCast, sq_abs]
  rw [hnorm, hD]
  exact sum_normSq_le_four_mul u hsum

/-- **M73 contact-gap upgrade.**  At an even eigenvector at the even ground value
with nonnegative parity gap `δ`, `δ ‖v‖² ≤ 4 |H(v)| |M₄(v)|` (was `C_K < 5`).
The carrier is the even boundary-flat sector, which lies inside the zero-sum
carrier; no parity-specific sharpness is claimed. -/
theorem parityGap_mul_norm_sq_le_four_mul_source_mul_momentFour
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig :
      parityCompressedCanonical .even L K v =
        (parityRayleighBottom .even L K : ℂ) • v)
    (hgap : 0 ≤ parityRayleighBottom .odd L K - parityRayleighBottom .even L K) :
    (parityRayleighBottom .odd L K - parityRayleighBottom .even L K) * ‖v‖ ^ 2 ≤
      4 * (‖explicitCanonicalSourceMoment L K v‖ *
          ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖) := by
  set δ := parityRayleighBottom .odd L K - parityRayleighBottom .even L K with hδ
  have hgapThm := parityGap_mul_evenIndex_norm_sq_le_re_star_source_mul_momentFour hL K hK v hveig
  rw [← hδ] at hgapThm
  have hflat := evenBoundaryFlatRawCoefficients_boundaryFlat K v
  have hcoer := norm_sq_le_four_mul_norm_index_sq K
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) hflat.1
  have hnormD : ‖euclideanEvenToOddIndexLinearMap K v‖ =
      ‖euclideanIndexLinearMap K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ := rfl
  have hnormv : ‖v‖ = ‖(v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ := rfl
  have hre : Complex.re
      (star (explicitCanonicalSourceMoment L K v) *
        centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)) ≤
      ‖explicitCanonicalSourceMoment L K v‖ *
        ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖ := by
    calc _ ≤ ‖star (explicitCanonicalSourceMoment L K v) *
            centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖ := Complex.re_le_norm _
      _ = _ := by rw [norm_mul, norm_star]
  rw [hnormv]
  rw [hnormD] at hgapThm
  calc δ * ‖(v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ ^ 2 ≤
        δ * (4 * ‖euclideanIndexLinearMap K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcoer hgap
    _ = 4 * (δ * ‖euclideanIndexLinearMap K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ ^ 2) := by
        ring
    _ ≤ 4 * (‖explicitCanonicalSourceMoment L K v‖ *
            ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖) :=
        mul_le_mul_of_nonneg_left (hgapThm.trans hre) (by norm_num)

end Zeta23.CCM

#print axioms Zeta23.CCM.centeredHalfShiftMass_eq
#print axioms Zeta23.CCM.quarter_sum_normSq_add_remainder_le
#print axioms Zeta23.CCM.sum_normSq_le_four_mul
#print axioms Zeta23.CCM.sum_normSq_lt_four_mul
#print axioms Zeta23.CCM.norm_sq_le_four_mul_norm_index_sq
#print axioms Zeta23.CCM.parityGap_mul_norm_sq_le_four_mul_source_mul_momentFour
