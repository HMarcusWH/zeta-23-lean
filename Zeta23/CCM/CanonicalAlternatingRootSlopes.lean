import Zeta23.CCM.CanonicalShiftedSecular

noncomputable section

/-!
# M27 (Step 59): alternating root slopes of the canonical secular function

For `L > 0` and `K ≥ 2` let `A_L` (even compression) and `B_L` (odd
compression) be the canonical parity compressions, with eigenvalues
`a_1, …, a_m` and `b_1, …, b_n`, and let
`T_L(λ) = S_L(v_L(λ))`, `v_L(λ) = D⁻¹ (B_L - λ)⁻¹ g`, be the shifted secular
function, defined for real `λ` below the odd Rayleigh bottom (and set to `0`
above it, where it is never used).

* `one_sub_canonicalSecularFunction_eq`: below the odd floor,
  `1 - T_L(λ) = ∏ (a_i - λ) / ∏ (b_k - λ)`.  This is the #285/M26 determinant
  identity `det (A_L - λ) = det (B_L - λ) (1 - T_L(λ))` with both
  determinants expanded over the eigenvalues.
* `canonical_secular_hasDerivAt_root`: at every even eigenvalue `a_j` below the
  odd floor, `T_L` is differentiable with
  `T_L'(a_j) = ∏_{i ≠ j} (a_i - a_j) / ∏_k (b_k - a_j)`.
* `canonical_secular_root_slope_sign`: that slope is nonzero with sign
  `(-1)^{#{i : a_i < a_j}}`.  Numbering the roots increasingly
  (`a_(1) < a_(2) < …`, all simple by `canonical_finrank_eigenspace_le_one`),
  the slope at `a_(j)` has sign `(-1)^(j-1)`: `+, -, +, …`.

The proof uses only self-adjointness of `A_L`, `B_L`, coercivity of `B_L`
above its Rayleigh bottom (so `b_k > a_j`), and simplicity of the even roots
below the odd floor.  Scope: this is a statement about `T_L` as a function of
`λ` at fixed `L`.  It gives no sign for the aperture derivative `∂_L T_L`, no
monotonicity of `T_L` in `λ` away from the roots, and nothing about whether a
contact `T_L(0) = 1` occurs.  `D` is not assumed unitary and `A_L` is not the
scalar `𝓐_L`.
-/

namespace Zeta23.CCM

open Finset Module

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {T : E →ₗ[ℂ] E} {n : ℕ}

/-- For a symmetric `T`, `det (T - λ) = ∏ (a_i - λ)` over its eigenvalues. -/
theorem det_sub_smul_eq_prod_eigenvalues (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (lam : ℝ) :
    LinearMap.det (T - (lam : ℂ) • LinearMap.id) =
      ∏ i, (((hT.eigenvalues hn i) - lam : ℝ) : ℂ) := by
  set b := (hT.eigenvectorBasis hn).toBasis with hb
  rw [← LinearMap.det_toMatrix b, map_sub, map_smul, LinearMap.toMatrix_id,
    hT.toMatrix_eigenvectorBasis hn]
  have h : Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues hn) - (lam : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal fun i => (((hT.eigenvalues hn i) - lam : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [h, Matrix.det_diagonal]

/-- A Rayleigh lower bound bounds every eigenvalue from below. -/
theorem le_eigenvalues_of_coercive (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ}
    (hc : ∀ y, c * ‖y‖ ^ 2 ≤ (inner ℂ (T y) y).re) (i : Fin n) :
    c ≤ hT.eigenvalues hn i := by
  have h := hc (hT.eigenvectorBasis hn i)
  rw [hT.apply_eigenvectorBasis, inner_smul_left, (hT.eigenvectorBasis hn).orthonormal.1 i] at h
  simpa using h

/-- Two eigenbasis indices with the same eigenvalue `μ` force `dim E_μ ≥ 2`. -/
theorem eigenvalues_injOn_of_finrank_le_one (hT : T.IsSymmetric) (hn : finrank ℂ E = n)
    {i j : Fin n} (hij : hT.eigenvalues hn i = hT.eigenvalues hn j)
    (h1 : finrank ℂ (Module.End.eigenspace T (hT.eigenvalues hn j : ℂ)) ≤ 1) : i = j := by
  by_contra hne
  set V := Module.End.eigenspace T (hT.eigenvalues hn j : ℂ)
  have hmem : ∀ k, hT.eigenvalues hn k = hT.eigenvalues hn j → hT.eigenvectorBasis hn k ∈ V := by
    intro k hk
    rw [Module.End.mem_eigenspace_iff, hT.apply_eigenvectorBasis, hk]
    rfl
  have hli : LinearIndependent ℂ (fun k : ({i, j} : Finset (Fin n)) => hT.eigenvectorBasis hn k) :=
    (hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hle : Submodule.span ℂ (Set.range fun k : ({i, j} : Finset (Fin n)) =>
      hT.eigenvectorBasis hn k) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hmem _ hij
    · exact hmem _ rfl
  have h2 := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, Fintype.card_coe, Finset.card_pair hne] at h2
  omega

end Abstract

/-- Derivative of `∏ (a_i - λ) / ∏ (b_k - λ)` at a root `λ = a_j`. -/
theorem hasDerivAt_prod_sub_div_prod_sub {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) (j : Fin n)
    (hb : ∀ k, b k ≠ a j) :
    HasDerivAt (fun lam : ℝ => (∏ i, (a i - lam)) / ∏ k, (b k - lam))
      (-(∏ i ∈ univ.erase j, (a i - a j)) / ∏ k, (b k - a j)) (a j) := by
  have hN : HasDerivAt (fun lam : ℝ => ∏ i, (a i - lam))
      (∑ i, (∏ l ∈ univ.erase i, (a l - a j)) • (-1 : ℝ)) (a j) :=
    HasDerivAt.fun_finsetProd fun i _ => (hasDerivAt_id (a j)).const_sub (a i)
  have hD : HasDerivAt (fun lam : ℝ => ∏ k, (b k - lam))
      (∑ k, (∏ l ∈ univ.erase k, (b l - a j)) • (-1 : ℝ)) (a j) :=
    HasDerivAt.fun_finsetProd fun k _ => (hasDerivAt_id (a j)).const_sub (b k)
  have hD0 : ∏ k, (b k - a j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => sub_ne_zero.mpr (hb k)
  have hN0 : ∏ i, (a i - a j) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
  have hsum : ∑ i, (∏ l ∈ univ.erase i, (a l - a j)) • (-1 : ℝ) =
      -(∏ i ∈ univ.erase j, (a i - a j)) := by
    rw [Fintype.sum_eq_single j]
    · simp
    · intro i hi
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ j⟩) (sub_self _),
        zero_smul]
  have h := hN.div hD hD0
  rw [hN0, hsum] at h
  refine h.congr_deriv ?_
  rw [zero_mul, sub_zero, pow_two, ← div_div, mul_div_cancel_right₀ _ hD0]

/-- `(-1)^{#negatives} ∏ f = ∏ |f|`. -/
theorem neg_one_pow_card_neg_mul_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (-1) ^ #(s.filter fun i => f i < 0) * ∏ i ∈ s, f i = ∏ i ∈ s, |f i| := by
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun i => f i < 0),
    ← Finset.prod_filter_mul_prod_filter_not s (fun i => f i < 0) (f := fun i => |f i|)]
  have h1 : ∏ i ∈ s.filter (fun i => f i < 0), f i =
      (-1) ^ #(s.filter fun i => f i < 0) * ∏ i ∈ s.filter (fun i => f i < 0), |f i| := by
    rw [← Finset.prod_neg]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [abs_of_neg (Finset.mem_filter.mp hi).2, neg_neg]
  have h2 : ∏ i ∈ s.filter (fun i => ¬ f i < 0), f i =
      ∏ i ∈ s.filter (fun i => ¬ f i < 0), |f i| := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [abs_of_nonneg (not_lt.mp (Finset.mem_filter.mp hi).2)]
  rw [h1, h2, ← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_mul]

/-! ## Canonical alternating root slopes -/

section Canonical

variable {L : ℝ} {K : ℕ}

theorem evenCompressedCanonical_isSymmetric (L : ℝ) (K : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := euclideanEvenBoundaryFlatSubspace K)
      (evenCompressedCanonical L K) :=
  parityCompressedCanonical_isSymmetric .even L K

theorem oddCompressedCanonical_isSymmetric (L : ℝ) (K : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := euclideanOddBoundaryFlatSubspace K)
      (oddCompressedCanonical L K) :=
  parityCompressedCanonical_isSymmetric .odd L K

/-- Eigenvalues of the even compression `A_L` (Mathlib's decreasing order). -/
def canonicalEvenEigenvalues (L : ℝ) (K : ℕ) :
    Fin (finrank ℂ (euclideanEvenBoundaryFlatSubspace K)) → ℝ :=
  (evenCompressedCanonical_isSymmetric L K).eigenvalues rfl

/-- Eigenvalues of the odd compression `B_L`. -/
def canonicalOddEigenvalues (L : ℝ) (K : ℕ) :
    Fin (finrank ℂ (euclideanOddBoundaryFlatSubspace K)) → ℝ :=
  (oddCompressedCanonical_isSymmetric L K).eigenvalues rfl

/-- The secular function `T_L(λ) = S_L(v_L(λ))` below the odd floor, extended
by `0` above it. -/
def canonicalSecularFunction (L : ℝ) (K : ℕ) (hK : 2 ≤ K) (lam : ℝ) : ℂ :=
  if h : lam < parityRayleighBottom .odd L K then
    explicitCanonicalSourceMoment L K (canonicalShiftedRay L K hK h) else 0

theorem canonicalOddEigenvalues_ge (L : ℝ) (K : ℕ) (k) :
    parityRayleighBottom .odd L K ≤ canonicalOddEigenvalues L K k :=
  le_eigenvalues_of_coercive (oddCompressedCanonical_isSymmetric L K) rfl
    (oddCompressedCanonical_coercive L K) k

/-- **Step 58/59, spectral form:** below the odd floor
`1 - T_L(λ) = ∏ (a_i - λ) / ∏ (b_k - λ)` over the eigenvalues of `A_L` and `B_L`. -/
theorem one_sub_canonicalSecularFunction_eq (hL : 0 < L) (hK : 2 ≤ K) {lam : ℝ}
    (hlam : lam < parityRayleighBottom .odd L K) :
    1 - canonicalSecularFunction L K hK lam =
      (((∏ i, (canonicalEvenEigenvalues L K i - lam)) /
        ∏ k, (canonicalOddEigenvalues L K k - lam) : ℝ) : ℂ) := by
  have hA : LinearMap.det (evenShiftedCanonical L K lam) =
      ∏ i, ((canonicalEvenEigenvalues L K i - lam : ℝ) : ℂ) :=
    det_sub_smul_eq_prod_eigenvalues (evenCompressedCanonical_isSymmetric L K) rfl lam
  have hB : LinearMap.det (oddShiftedCanonical L K lam) =
      ∏ k, ((canonicalOddEigenvalues L K k - lam : ℝ) : ℂ) :=
    det_sub_smul_eq_prod_eigenvalues (oddCompressedCanonical_isSymmetric L K) rfl lam
  rw [canonicalSecularFunction, dif_pos hlam, ← canonical_shifted_det_div_eq hL hK hlam, hA, hB]
  push_cast
  rfl

/-- **M27 (Step 59), root slope.**  At an even eigenvalue `a_j` below the odd
floor, `T_L` is differentiable in `λ` with
`T_L'(a_j) = ∏_{i ≠ j} (a_i - a_j) / ∏_k (b_k - a_j)`. -/
theorem canonical_secular_hasDerivAt_root (hL : 0 < L) (hK : 2 ≤ K)
    (j : Fin (finrank ℂ (euclideanEvenBoundaryFlatSubspace K)))
    (hj : canonicalEvenEigenvalues L K j < parityRayleighBottom .odd L K) :
    HasDerivAt (canonicalSecularFunction L K hK)
      (((∏ i ∈ univ.erase j, (canonicalEvenEigenvalues L K i - canonicalEvenEigenvalues L K j)) /
        ∏ k, (canonicalOddEigenvalues L K k - canonicalEvenEigenvalues L K j) : ℝ) : ℂ)
      (canonicalEvenEigenvalues L K j) := by
  set a := canonicalEvenEigenvalues L K
  set b := canonicalOddEigenvalues L K
  have hb : ∀ k, b k ≠ a j := fun k =>
    ne_of_gt (lt_of_lt_of_le hj (canonicalOddEigenvalues_ge L K k))
  have hR := (hasDerivAt_prod_sub_div_prod_sub a b j hb).ofReal_comp.const_sub 1
  have hev : canonicalSecularFunction L K hK =ᶠ[nhds (a j)]
      fun lam => 1 - (((∏ i, (a i - lam)) / ∏ k, (b k - lam) : ℝ) : ℂ) := by
    filter_upwards [Iio_mem_nhds hj] with lam hlam
    rw [← one_sub_canonicalSecularFunction_eq hL hK hlam, sub_sub_cancel]
  refine (hR.congr_of_eventuallyEq hev).congr_deriv ?_
  push_cast
  ring

/-- **M27 (Step 59), alternating sign.**  At an even eigenvalue `a_j` below the
odd floor the slope is nonzero with sign `(-1)^{#{i : a_i < a_j}}`; ordered
increasingly, the roots below the odd floor alternate `+, -, +, …`. -/
theorem canonical_secular_root_slope_sign (hL : 0 < L) (hK : 2 ≤ K)
    (j : Fin (finrank ℂ (euclideanEvenBoundaryFlatSubspace K)))
    (hj : canonicalEvenEigenvalues L K j < parityRayleighBottom .odd L K) :
    0 < (-1) ^ #(univ.filter fun i => canonicalEvenEigenvalues L K i < canonicalEvenEigenvalues L K j) *
      ((∏ i ∈ univ.erase j, (canonicalEvenEigenvalues L K i - canonicalEvenEigenvalues L K j)) /
        ∏ k, (canonicalOddEigenvalues L K k - canonicalEvenEigenvalues L K j)) := by
  set a := canonicalEvenEigenvalues L K
  set b := canonicalOddEigenvalues L K
  have hD : 0 < ∏ k, (b k - a j) := Finset.prod_pos fun k _ =>
    sub_pos.mpr (lt_of_lt_of_le hj (canonicalOddEigenvalues_ge L K k))
  have hsimple : ∀ i, i ≠ j → a i ≠ a j := by
    intro i hij hai
    exact hij (eigenvalues_injOn_of_finrank_le_one (evenCompressedCanonical_isSymmetric L K)
      rfl hai (canonical_finrank_eigenspace_le_one hL hK hj))
  have hcard : (univ.filter fun i => a i < a j) =
      (univ.erase j).filter fun i => a i - a j < 0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true, sub_neg]
    constructor
    · intro h
      exact ⟨fun hij => by rw [hij] at h; exact lt_irrefl _ h, h⟩
    · exact fun h => h.2
  rw [hcard, ← mul_div_assoc, neg_one_pow_card_neg_mul_prod]
  refine div_pos (Finset.prod_pos fun i hi => ?_) hD
  exact abs_pos.mpr (sub_ne_zero.mpr (hsimple i (Finset.mem_erase.mp hi).1))

end Canonical

end Zeta23.CCM

#print axioms Zeta23.CCM.det_sub_smul_eq_prod_eigenvalues
#print axioms Zeta23.CCM.hasDerivAt_prod_sub_div_prod_sub
#print axioms Zeta23.CCM.le_eigenvalues_of_coercive
#print axioms Zeta23.CCM.eigenvalues_injOn_of_finrank_le_one
#print axioms Zeta23.CCM.neg_one_pow_card_neg_mul_prod
#print axioms Zeta23.CCM.one_sub_canonicalSecularFunction_eq
#print axioms Zeta23.CCM.canonical_secular_hasDerivAt_root
#print axioms Zeta23.CCM.canonical_secular_root_slope_sign
