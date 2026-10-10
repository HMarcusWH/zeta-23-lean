import Zeta23.CCM.GlobalParityBottomSourceMoment
import Zeta23.CCM.SourceLatticeCoordinates
import Zeta23.CCM.QuadraticNormalSourceJets

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate

/-!
# POST284 follow-up M46: uniform centered-index coercivity (Steps 83, 89)

For a centered coefficient vector `z` on `[-K, K]` with `∑ z = 0`, put
`(Dz)_n = n z_n`.  With

`C_K := 1 + ∑_{0 < |n| ≤ K} 1/n² = 1 + 2 ∑_{n=1}^K 1/n²`,

* `‖z‖² ≤ C_K ‖Dz‖²` (discrete Poincaré inequality, no parity, contact, F04 or
  RH input);
* `C_K ≤ 5 - 4/(K+1) < 5`, and `C_K ≤ 2K+1` (so this supersedes the older
  `(2K+1)` index-mass bound of `ContactNinthJumpGapBound`);
* at an even eigenvector at the even ground value, combined with the existing
  parity-gap theorem `parityGap_mul_evenIndex_norm_sq_le_re_star_source_mul_momentFour`,
  a nonnegative odd–even gap `δ` gives `δ ‖v‖² ≤ C_K |H(v)| |M₄(v)|`.

The last item is a property of each actual ground eigenvector; it is not a
uniform sign theorem and does not exclude a contact.
-/

/-- `∑_{0 < |n| ≤ K} 1/n²` over the centered grid. -/
def centeredInverseSquareMass (K : ℕ) : ℝ :=
  ∑ i : Fin (2 * K + 1),
    if centeredIndex K i = 0 then 0 else 1 / ((centeredIndex K i : ℤ) : ℝ) ^ 2

/-- The coercivity constant `C_K = 1 + ∑_{0 < |n| ≤ K} 1/n²`. -/
def centeredCoercivityConstant (K : ℕ) : ℝ :=
  1 + centeredInverseSquareMass K

private def latticeInverseSquare (n : ℤ) : ℝ :=
  if n = 0 then 0 else 1 / (n : ℝ) ^ 2

private theorem latticeInverseSquare_nonneg (n : ℤ) : 0 ≤ latticeInverseSquare n := by
  unfold latticeInverseSquare
  split_ifs
  · exact le_rfl
  · positivity

theorem centeredInverseSquareMass_eq_lattice (K : ℕ) :
    centeredInverseSquareMass K = ∑ n ∈ latticeBox K, latticeInverseSquare n := by
  unfold centeredInverseSquareMass
  exact sum_centeredIndex_eq_sum_latticeBox K latticeInverseSquare

private theorem latticeBox_succ_eq (K : ℕ) :
    latticeBox (K + 1) = insert (-((K + 1 : ℕ) : ℤ)) (insert ((K + 1 : ℕ) : ℤ) (latticeBox K)) := by
  ext n
  simp only [mem_latticeBox, Finset.mem_insert]
  push_cast
  omega

private theorem sum_latticeBox_succ (K : ℕ) :
    ∑ n ∈ latticeBox (K + 1), latticeInverseSquare n =
      ∑ n ∈ latticeBox K, latticeInverseSquare n + 2 / ((K : ℝ) + 1) ^ 2 := by
  rw [latticeBox_succ_eq, Finset.sum_insert, Finset.sum_insert]
  · have h1 : latticeInverseSquare (-((K + 1 : ℕ) : ℤ)) = 1 / ((K : ℝ) + 1) ^ 2 := by
      unfold latticeInverseSquare
      rw [if_neg (by omega)]
      push_cast
      ring
    have h2 : latticeInverseSquare ((K + 1 : ℕ) : ℤ) = 1 / ((K : ℝ) + 1) ^ 2 := by
      unfold latticeInverseSquare
      rw [if_neg (by omega)]
      push_cast
      ring
    rw [h1, h2]
    ring
  · rw [mem_latticeBox]; omega
  · rw [Finset.mem_insert, mem_latticeBox]; omega

/-- Telescoping bound `∑_{0<|n|≤K} 1/n² ≤ 4 - 4/(K+1)`. -/
theorem centeredInverseSquareMass_le (K : ℕ) :
    centeredInverseSquareMass K ≤ 4 - 4 / ((K : ℝ) + 1) := by
  rw [centeredInverseSquareMass_eq_lattice]
  induction K with
  | zero =>
      have : latticeBox 0 = {0} := by
        ext n
        simp only [mem_latticeBox, Finset.mem_singleton]
        push_cast
        omega
      rw [this, Finset.sum_singleton]
      simp [latticeInverseSquare]
  | succ K ih =>
      rw [sum_latticeBox_succ]
      have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have hstep : 2 / ((K : ℝ) + 1) ^ 2 ≤ 4 / ((K : ℝ) + 1) - 4 / (((K + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        have e : 4 / ((K : ℝ) + 1) - 4 / ((K : ℝ) + 1 + 1) =
            4 / (((K : ℝ) + 1) * ((K : ℝ) + 2)) := by
          field_simp
          ring
        rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith

theorem centeredInverseSquareMass_nonneg (K : ℕ) : 0 ≤ centeredInverseSquareMass K := by
  rw [centeredInverseSquareMass_eq_lattice]
  exact Finset.sum_nonneg (fun n _ => latticeInverseSquare_nonneg n)

/-- **`C_K < 5`** uniformly in `K`. -/
theorem centeredCoercivityConstant_lt_five (K : ℕ) : centeredCoercivityConstant K < 5 := by
  have h := centeredInverseSquareMass_le K
  have hpos : 0 < 4 / ((K : ℝ) + 1) := by positivity
  unfold centeredCoercivityConstant
  linarith

theorem one_le_centeredCoercivityConstant (K : ℕ) : 1 ≤ centeredCoercivityConstant K := by
  unfold centeredCoercivityConstant
  linarith [centeredInverseSquareMass_nonneg K]

/-- Regression comparison: `C_K ≤ 2K + 1`, so the new bound is never worse than
the older index-mass constant. -/
theorem centeredCoercivityConstant_le_two_mul_add_one (K : ℕ) :
    centeredCoercivityConstant K ≤ 2 * K + 1 := by
  have h := centeredInverseSquareMass_le K
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h2 : 4 - 4 / ((K : ℝ) + 1) ≤ 2 * K := by
    have e : 4 - 4 / ((K : ℝ) + 1) = 4 * K / ((K : ℝ) + 1) := by
      field_simp
      ring
    have hKK : (0 : ℝ) ≤ K * (K - 1) := by
      rcases Nat.eq_zero_or_pos K with h0 | h0
      · subst h0; simp
      · have : (1 : ℝ) ≤ K := by exact_mod_cast h0
        nlinarith
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  unfold centeredCoercivityConstant
  linarith

/-- **M46 discrete Poincaré inequality.**  If `∑ z = 0` then
`∑ |z_n|² ≤ C_K ∑ n² |z_n|²`. -/
theorem sum_normSq_le_centeredCoercivityConstant_mul {K : ℕ} (z : Fin (2 * K + 1) → ℂ)
    (h0 : ∑ i, z i = 0) :
    ∑ i, Complex.normSq (z i) ≤
      centeredCoercivityConstant K *
        ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (z i) := by
  classical
  let c : Fin (2 * K + 1) := ⟨K, by omega⟩
  have hc : centeredIndex K c = 0 := by simp [centeredIndex, c]
  set S := (Finset.univ : Finset (Fin (2 * K + 1))).erase c with hS
  have hne : ∀ i ∈ S, centeredIndex K i ≠ 0 := by
    intro i hi h
    exact Finset.ne_of_mem_erase hi (centeredIndex_injective K (h.trans hc.symm))
  have hsplit : ∀ g : Fin (2 * K + 1) → ℝ, ∑ i, g i = g c + ∑ i ∈ S, g i := by
    intro g
    rw [hS, Finset.add_sum_erase _ _ (Finset.mem_univ c)]
  have hzc : z c = -∑ i ∈ S, z i := by
    have h := h0
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), ← hS] at h
    linear_combination h
  -- weights
  set W : ℝ := ∑ i ∈ S, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (z i) with hW
  have hmass : centeredInverseSquareMass K = ∑ i ∈ S, 1 / ((centeredIndex K i : ℤ) : ℝ) ^ 2 := by
    unfold centeredInverseSquareMass
    rw [hsplit, if_pos hc, zero_add]
    exact Finset.sum_congr rfl (fun i hi => if_neg (hne i hi))
  have hWfull : ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (z i) = W := by
    rw [hsplit, hc]
    simp [hW]
  -- the centre term by Cauchy–Schwarz
  have hcs : Complex.normSq (z c) ≤ centeredInverseSquareMass K * W := by
    rw [hzc, Complex.normSq_neg, Complex.normSq_eq_norm_sq]
    have h1 : ‖∑ i ∈ S, z i‖ ≤ ∑ i ∈ S, ‖z i‖ := norm_sum_le _ _
    have h2 : (∑ i ∈ S, ‖z i‖) ^ 2 ≤
        (∑ i ∈ S, 1 / ((centeredIndex K i : ℤ) : ℝ) ^ 2) *
          ∑ i ∈ S, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (z i) := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro i _; positivity
      · intro i _; exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
      · intro i hi
        have hci : ((centeredIndex K i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne i hi
        apply le_of_eq
        rw [Complex.normSq_eq_norm_sq]
        field_simp
    rw [hmass]
    calc ‖∑ i ∈ S, z i‖ ^ 2 ≤ (∑ i ∈ S, ‖z i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  -- the off-centre terms
  have hoff : ∑ i ∈ S, Complex.normSq (z i) ≤ W := by
    apply Finset.sum_le_sum
    intro i hi
    have h1 : (1 : ℝ) ≤ ((centeredIndex K i : ℤ) : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ (centeredIndex K i) ^ 2 := by
        have := sq_pos_of_ne_zero (hne i hi)
        omega
      exact_mod_cast this
    have h2 := Complex.normSq_nonneg (z i)
    nlinarith
  rw [hsplit (fun i => Complex.normSq (z i)), hWfull]
  unfold centeredCoercivityConstant
  linarith

/-- Strict form: a nonzero `z` with `∑ z = 0` has `‖Dz‖² > ‖z‖²/5`. -/
theorem sum_normSq_lt_five_mul {K : ℕ} (z : Fin (2 * K + 1) → ℂ)
    (h0 : ∑ i, z i = 0) (hz : z ≠ 0) :
    ∑ i, Complex.normSq (z i) <
      5 * ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (z i) := by
  have hle := sum_normSq_le_centeredCoercivityConstant_mul z h0
  have hpos : 0 < ∑ i, Complex.normSq (z i) := by
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  have hW : 0 < ∑ i, ((centeredIndex K i : ℤ) : ℝ) ^ 2 * Complex.normSq (z i) := by
    by_contra h
    push Not at h
    have hC0 : 0 ≤ centeredCoercivityConstant K := by
      linarith [one_le_centeredCoercivityConstant K]
    have := mul_nonpos_of_nonneg_of_nonpos hC0 h
    linarith
  have := centeredCoercivityConstant_lt_five K
  nlinarith

/-- Euclidean form: `‖x‖² ≤ C_K ‖D x‖²` when the zeroth centered moment vanishes. -/
theorem norm_sq_le_centeredCoercivityConstant_mul_norm_index_sq (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (h0 : centeredMoment K 0 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) = 0) :
    ‖x‖ ^ 2 ≤ centeredCoercivityConstant K * ‖euclideanIndexLinearMap K x‖ ^ 2 := by
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
  exact sum_normSq_le_centeredCoercivityConstant_mul u hsum

/-- **M46 contact-moment corollary.**  At an even eigenvector at the even ground
value with nonnegative odd–even parity gap `δ`,
`δ ‖v‖² ≤ C_K |H(v)| |M₄(v)|`, where `H` is the actual explicit canonical source
moment.  (Hypotheses are exactly those of the existing parity-gap theorem plus
`0 ≤ δ`.) -/
theorem parityGap_mul_norm_sq_le_coercivity_mul_source_mul_momentFour
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig :
      parityCompressedCanonical .even L K v =
        (parityRayleighBottom .even L K : ℂ) • v)
    (hgap : 0 ≤ parityRayleighBottom .odd L K - parityRayleighBottom .even L K) :
    (parityRayleighBottom .odd L K - parityRayleighBottom .even L K) * ‖v‖ ^ 2 ≤
      centeredCoercivityConstant K *
        (‖explicitCanonicalSourceMoment L K v‖ *
          ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖) := by
  set δ := parityRayleighBottom .odd L K - parityRayleighBottom .even L K with hδ
  have hgapThm := parityGap_mul_evenIndex_norm_sq_le_re_star_source_mul_momentFour hL K hK v hveig
  rw [← hδ] at hgapThm
  have hflat := evenBoundaryFlatRawCoefficients_boundaryFlat K v
  have hcoer := norm_sq_le_centeredCoercivityConstant_mul_norm_index_sq K
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
  have hC := one_le_centeredCoercivityConstant K
  rw [hnormv]
  rw [hnormD] at hgapThm
  calc δ * ‖(v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ ^ 2 ≤
        δ * (centeredCoercivityConstant K *
          ‖euclideanIndexLinearMap K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcoer hgap
    _ = centeredCoercivityConstant K *
          (δ * ‖euclideanIndexLinearMap K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ ^ 2) := by
        ring
    _ ≤ centeredCoercivityConstant K *
          (‖explicitCanonicalSourceMoment L K v‖ *
            ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖) :=
        mul_le_mul_of_nonneg_left (hgapThm.trans hre) (by linarith)

end Zeta23.CCM

#print axioms Zeta23.CCM.centeredInverseSquareMass_le
#print axioms Zeta23.CCM.centeredCoercivityConstant_lt_five
#print axioms Zeta23.CCM.centeredCoercivityConstant_le_two_mul_add_one
#print axioms Zeta23.CCM.sum_normSq_le_centeredCoercivityConstant_mul
#print axioms Zeta23.CCM.sum_normSq_lt_five_mul
#print axioms Zeta23.CCM.norm_sq_le_centeredCoercivityConstant_mul_norm_index_sq
#print axioms Zeta23.CCM.parityGap_mul_norm_sq_le_coercivity_mul_source_mul_momentFour
