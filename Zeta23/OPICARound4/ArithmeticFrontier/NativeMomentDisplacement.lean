import Zeta23.CCM.SourceNormalizationRepair
import Zeta23.CCM.ConstrainedCanonicalSector
import Zeta23.CCM.CanonicalSourceEnergyJets
import Zeta23.CCM.SourceMomentVandermondeFiltration
import Zeta23.OPICARound4.ArithmeticFrontier.MomentLeakage

/-!
# The native squared-index displacement: the ambient compressed commutator vanishes

Let `D = indexMatrix N` (centered Fourier indices `n`), `D₀ = D²` (the squared-index
geometry `diag(n²)`) and `A = canonicalSourceMatrix L N`, the full canonical source,
pole and diagonal corrections included. The existing theorem
`canonicalSourceMatrix_displacement` states `D A - A D = d 1ᵀ - 1 dᵀ` with
`d = displacementVector L N` (the divided-difference potential). From it:

* `(D₀ A - A D₀)ᵢⱼ = (nᵢ + nⱼ)(dᵢ - dⱼ)`, a rank-four matrix;
* `w* (D₀ A - A D₀) u = 0` whenever the centered moments `M₀` and `M₁` of `u` and
  `w` vanish (boundary flatness gives this; `M₂` is not needed);
* (NC) `Vᴴ (D₀ A - A D₀) V = 0` for every column map `V` whose columns are
  boundary-flat, hence on both actual pole-neutral parity carriers;
* composed with `MomentLeakage` (M51): under a leakage factorization
  `(1 - V Vᴴ) D₀ V = W Lᴴ`, the compressed commutator is exactly
  `(Vᴴ A W) Lᴴ - L (Vᴴ A W)ᴴ`.

The leakage itself is native geometry: `D₀` shifts centered moments by two, maps
the even slice (`M₄ = 0`) into the even boundary-flat sector and the odd slice
(`M₃ = M₅ = 0`) into the odd one. The native pole profiles satisfy
`(D₀ + β) r = c 1` (even) and `(D₀ + β) r = c' n` (odd) with `β = L²/(16π²)`, so
`D₀ u` stays pole-neutral on the slice. Leaving the slice is therefore exactly one
linear functional per parity: `M₆(u)` (even) or `M₇(u)` (odd), the rank-one
leakage. The explicit orthonormal factor `w ℓᴴ` is not constructed here.

These are exact identities. They give no sign of the native energy: a commutator
controls neither the diagonal nor the absolute energy.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open Matrix CCM

/-- The squared-index geometry `D₀ = diag(n²)` on the centered Fourier grid. -/
def squaredIndexMatrix (N : ℕ) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  indexMatrix N * indexMatrix N

theorem squaredIndexMatrix_eq_diagonal (N : ℕ) :
    squaredIndexMatrix N = diagonal fun i => ((centeredIndex N i : ℤ) : ℂ) ^ 2 := by
  unfold squaredIndexMatrix indexMatrix
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  ring

theorem squaredIndexMatrix_conjTranspose (N : ℕ) :
    (squaredIndexMatrix N)ᴴ = squaredIndexMatrix N := by
  rw [squaredIndexMatrix_eq_diagonal, diagonal_conjTranspose]
  congr 1
  funext i
  simp

/-- Entry formula: `(D₀ A - A D₀)ᵢⱼ = (nᵢ + nⱼ)(dᵢ - dⱼ)` for the full canonical source. -/
theorem squaredIndex_commutator_apply {L : ℝ} (hL : 0 < L) (N : ℕ) (i j : Fin (2 * N + 1)) :
    (squaredIndexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * squaredIndexMatrix N) i j =
      (((centeredIndex N i : ℤ) : ℂ) + ((centeredIndex N j : ℤ) : ℂ)) *
        (displacementVector L N i - displacementVector L N j) := by
  have hd := congrFun (congrFun (canonicalSourceMatrix_displacement hL N) i) j
  rw [Matrix.sub_apply, Matrix.sub_apply, indexMatrix, diagonal_mul, mul_diagonal,
    vecMulVec_apply, vecMulVec_apply] at hd
  rw [squaredIndexMatrix_eq_diagonal, Matrix.sub_apply, diagonal_mul, mul_diagonal]
  have hd' : ((centeredIndex N i : ℤ) : ℂ) * canonicalSourceMatrix L N i j -
      canonicalSourceMatrix L N i j * ((centeredIndex N j : ℤ) : ℂ) =
      displacementVector L N i - displacementVector L N j := by
    rw [hd]; ring
  linear_combination (((centeredIndex N i : ℤ) : ℂ) + ((centeredIndex N j : ℤ) : ℂ)) * hd'

/-- The commutator `D₀ A - A D₀` as an explicit rank-four combination. -/
theorem squaredIndex_commutator_eq {L : ℝ} (hL : 0 < L) (N : ℕ) :
    squaredIndexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * squaredIndexMatrix N =
      vecMulVec (fun i => ((centeredIndex N i : ℤ) : ℂ) * displacementVector L N i) (fun _ => 1) +
        vecMulVec (displacementVector L N) (fun j => ((centeredIndex N j : ℤ) : ℂ)) -
        vecMulVec (fun i => ((centeredIndex N i : ℤ) : ℂ)) (displacementVector L N) -
        vecMulVec (fun _ => 1) (fun j => ((centeredIndex N j : ℤ) : ℂ) * displacementVector L N j) := by
  ext i j
  rw [squaredIndex_commutator_apply hL]
  simp only [Matrix.sub_apply, Matrix.add_apply, vecMulVec_apply]
  ring

/-- `w* (a bᵀ) u = (w* a)(b u)`. -/
theorem star_dotProduct_vecMulVec_mulVec {n : Type*} [Fintype n] (w a b u : n → ℂ) :
    star w ⬝ᵥ (vecMulVec a b *ᵥ u) = (star w ⬝ᵥ a) * (b ⬝ᵥ u) := by
  simp only [dotProduct, mulVec, vecMulVec_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `1 ⬝ u = M₀(u)`. -/
theorem one_dotProduct_eq_centeredMoment_zero (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    (fun _ => (1 : ℂ)) ⬝ᵥ u = centeredMoment N 0 u := by
  simp [dotProduct, centeredMoment]

/-- `n ⬝ u = M₁(u)`. -/
theorem index_dotProduct_eq_centeredMoment_one (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    (fun j => ((centeredIndex N j : ℤ) : ℂ)) ⬝ᵥ u = centeredMoment N 1 u := by
  simp [dotProduct, centeredMoment]

/-- `w* 1 = conj M₀(w)`. -/
theorem star_dotProduct_one (N : ℕ) (w : Fin (2 * N + 1) → ℂ) :
    star w ⬝ᵥ (fun _ => (1 : ℂ)) = star (centeredMoment N 0 w) := by
  simp [dotProduct, centeredMoment, star_sum]

/-- `w* n = conj M₁(w)`; the indices are real. -/
theorem star_dotProduct_index (N : ℕ) (w : Fin (2 * N + 1) → ℂ) :
    star w ⬝ᵥ (fun j => ((centeredIndex N j : ℤ) : ℂ)) = star (centeredMoment N 1 w) := by
  simp [dotProduct, centeredMoment, star_sum, mul_comm]

/-- **Bilinear vanishing.** If `M₀` and `M₁` vanish on `u` and `w`, then
`w* (D₀ A - A D₀) u = 0` for the full canonical source. -/
theorem squaredIndex_commutator_form_eq_zero {L : ℝ} (hL : 0 < L) (N : ℕ)
    (u w : Fin (2 * N + 1) → ℂ)
    (hu0 : centeredMoment N 0 u = 0) (hu1 : centeredMoment N 1 u = 0)
    (hw0 : centeredMoment N 0 w = 0) (hw1 : centeredMoment N 1 w = 0) :
    star w ⬝ᵥ ((squaredIndexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * squaredIndexMatrix N) *ᵥ u) = 0 := by
  rw [squaredIndex_commutator_eq hL]
  simp only [sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add,
    star_dotProduct_vecMulVec_mulVec, one_dotProduct_eq_centeredMoment_zero,
    index_dotProduct_eq_centeredMoment_one, star_dotProduct_one, star_dotProduct_index,
    hu0, hu1, hw0, hw1, star_zero, mul_zero, zero_mul, sub_zero, add_zero]

/-- The bilinear vanishing on the boundary-flat sector. -/
theorem squaredIndex_commutator_form_eq_zero_of_boundaryFlat {L : ℝ} (hL : 0 < L) (N : ℕ)
    {u w : Fin (2 * N + 1) → ℂ} (hu : u ∈ boundaryFlatSubspace N)
    (hw : w ∈ boundaryFlatSubspace N) :
    star w ⬝ᵥ ((squaredIndexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * squaredIndexMatrix N) *ᵥ u) = 0 := by
  rw [mem_boundaryFlatSubspace_iff] at hu hw
  exact squaredIndex_commutator_form_eq_zero hL N u w hu.1 hu.2.1 hw.1 hw.2.1

/-- Entry formula for a compressed matrix: `(Vᴴ X V)ⱼₗ = colⱼ* X colₗ`. -/
theorem conjTranspose_mul_mul_apply {n k : Type*} [Fintype n] (V : Matrix n k ℂ)
    (X : Matrix n n ℂ) (j l : k) :
    (Vᴴ * X * V) j l = star (fun i => V i j) ⬝ᵥ (X *ᵥ fun i => V i l) := by
  simp only [mul_apply, conjTranspose_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **(NC) Native ambient-commutator cancellation.** For every column map whose
columns are boundary-flat, the compressed ambient commutator of the squared-index
geometry with the full canonical source vanishes. -/
theorem compressed_squaredIndex_commutator_eq_zero {L : ℝ} (hL : 0 < L) (N : ℕ) {k : Type*}
    [Fintype k] (V : Matrix (Fin (2 * N + 1)) k ℂ)
    (hV : ∀ j, (fun i => V i j) ∈ boundaryFlatSubspace N) :
    Vᴴ * (squaredIndexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * squaredIndexMatrix N) * V = 0 := by
  ext j l
  rw [conjTranspose_mul_mul_apply, Matrix.zero_apply]
  exact squaredIndex_commutator_form_eq_zero_of_boundaryFlat hL N (hV l) (hV j)

/-- **M51 on the native source.** With boundary-flat columns and a leakage
factorization `(1 - V Vᴴ) D₀ V = W Lᴴ`, the compressed commutator of the geometry
with the full canonical source is the pure leakage displacement
`(Vᴴ A W) Lᴴ - L (Vᴴ A W)ᴴ`. The factorization remains a hypothesis here. -/
theorem native_compressed_commutator_eq {L : ℝ} (hL : 0 < L) (N : ℕ) {k r : Type*}
    [Fintype k] [Fintype r] (V : Matrix (Fin (2 * N + 1)) k ℂ)
    (W : Matrix (Fin (2 * N + 1)) r ℂ) (Λ : Matrix k r ℂ)
    (hV : ∀ j, (fun i => V i j) ∈ boundaryFlatSubspace N)
    (hleak : (1 - V * Vᴴ) * squaredIndexMatrix N * V = W * Λᴴ) :
    (Vᴴ * squaredIndexMatrix N * V) * (Vᴴ * canonicalSourceMatrix L N * V) -
        (Vᴴ * canonicalSourceMatrix L N * V) * (Vᴴ * squaredIndexMatrix N * V) =
      (Vᴴ * canonicalSourceMatrix L N * W) * Λᴴ - Λ * (Vᴴ * canonicalSourceMatrix L N * W)ᴴ := by
  rw [compressed_commutator_eq V (squaredIndexMatrix N) (canonicalSourceMatrix L N) W Λ
    (squaredIndexMatrix_conjTranspose N) (canonicalSourceMatrix_isHermitian L N) hleak,
    compressed_squaredIndex_commutator_eq_zero hL N V hV, zero_add]

/-- `D₀` shifts every centered moment by two: `Mₖ(D₀ u) = Mₖ₊₂(u)`. -/
theorem centeredMoment_squaredIndex_mulVec (N k : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment N k (squaredIndexMatrix N *ᵥ u) = centeredMoment N (k + 2) u := by
  rw [squaredIndexMatrix_eq_diagonal]
  simp only [centeredMoment, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `D₀` preserves coefficient parity (it is the square of the parity flip `D`). -/
theorem squaredIndex_mulVec_mem_even (N : ℕ) {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ evenCoefficientSubspace N) :
    squaredIndexMatrix N *ᵥ u ∈ evenCoefficientSubspace N := by
  rw [mem_evenCoefficientSubspace_iff] at hu ⊢
  rw [squaredIndexMatrix, ← mulVec_mulVec, reverseCoefficients_indexMatrix_mulVec,
    reverseCoefficients_indexMatrix_mulVec, hu]
  simp [mulVec_neg]

/-- `D₀` preserves odd coefficient parity. -/
theorem squaredIndex_mulVec_mem_odd (N : ℕ) {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ oddCoefficientSubspace N) :
    squaredIndexMatrix N *ᵥ u ∈ oddCoefficientSubspace N := by
  rw [mem_oddCoefficientSubspace_iff] at hu ⊢
  rw [squaredIndexMatrix, ← mulVec_mulVec, reverseCoefficients_indexMatrix_mulVec,
    reverseCoefficients_indexMatrix_mulVec, hu]
  simp [mulVec_neg]

/-- **Even leakage geometry.** For an even boundary-flat vector with `M₄ = 0` (the
even slice condition), `D₀ u` is again even and boundary-flat, and its fourth
moment is `M₆(u)`. Leaving the even slice is measured only by `M₆(u)` and the
pole functional of `D₀ u`. -/
theorem squaredIndex_mulVec_even_leakage (N : ℕ) {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ evenBoundaryFlatSubspace N) (h4 : centeredMoment N 4 u = 0) :
    squaredIndexMatrix N *ᵥ u ∈ evenBoundaryFlatSubspace N ∧
      centeredMoment N 4 (squaredIndexMatrix N *ᵥ u) = centeredMoment N 6 u := by
  have hflat : u ∈ boundaryFlatSubspace N := (Submodule.mem_inf.mp hu).1
  have heven : u ∈ evenCoefficientSubspace N := (Submodule.mem_inf.mp hu).2
  rw [mem_boundaryFlatSubspace_iff] at hflat
  have h3 : centeredMoment N 3 u = 0 :=
    centeredMoment_odd_eq_zero_of_even heven (by decide)
  refine ⟨Submodule.mem_inf.mpr ⟨?_, squaredIndex_mulVec_mem_even N heven⟩,
    centeredMoment_squaredIndex_mulVec N 4 u⟩
  rw [mem_boundaryFlatSubspace_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [centeredMoment_squaredIndex_mulVec]; exact hflat.2.2
  · rw [centeredMoment_squaredIndex_mulVec]; exact h3
  · rw [centeredMoment_squaredIndex_mulVec]; exact h4

/-- **Odd leakage geometry.** For an odd boundary-flat vector with `M₃ = M₅ = 0` (the
odd slice conditions), `D₀ u` is odd and boundary-flat, its third moment vanishes
and its fifth moment is `M₇(u)`. Leaving the odd slice is measured only by `M₇(u)`
and the pole functional of `D₀ u`. -/
theorem squaredIndex_mulVec_odd_leakage (N : ℕ) {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ oddBoundaryFlatSubspace N) (h3 : centeredMoment N 3 u = 0)
    (h5 : centeredMoment N 5 u = 0) :
    squaredIndexMatrix N *ᵥ u ∈ oddBoundaryFlatSubspace N ∧
      centeredMoment N 3 (squaredIndexMatrix N *ᵥ u) = 0 ∧
      centeredMoment N 5 (squaredIndexMatrix N *ᵥ u) = centeredMoment N 7 u := by
  have hflat : u ∈ boundaryFlatSubspace N := (Submodule.mem_inf.mp hu).1
  have hodd : u ∈ oddCoefficientSubspace N := (Submodule.mem_inf.mp hu).2
  rw [mem_boundaryFlatSubspace_iff] at hflat
  have h4 : centeredMoment N 4 u = 0 :=
    centeredMoment_even_eq_zero_of_odd hodd (by decide)
  refine ⟨Submodule.mem_inf.mpr ⟨?_, squaredIndex_mulVec_mem_odd N hodd⟩, ?_,
    centeredMoment_squaredIndex_mulVec N 5 u⟩
  · rw [mem_boundaryFlatSubspace_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [centeredMoment_squaredIndex_mulVec]; exact hflat.2.2
    · rw [centeredMoment_squaredIndex_mulVec]; exact h3
    · rw [centeredMoment_squaredIndex_mulVec]; exact h4
  · rw [centeredMoment_squaredIndex_mulVec]; exact h5

/-- The native even pole profile `r(n) = L / (L² + 16π² n²)` satisfies
`n² r(n) = L/(16π²) - (L²/(16π²)) r(n)`, i.e. `(D₀ + β) r = (L/(16π²)) 1` with
`β = L²/(16π²)`. -/
theorem poleEvenProfile_mul_centeredIndex_sq {L : ℝ} (hL : 0 < L) (K : ℕ)
    (i : Fin (2 * K + 1)) :
    poleEvenProfile L K i * ((centeredIndex K i : ℤ) : ℂ) ^ 2 =
      ((L / (16 * Real.pi ^ 2) : ℝ) : ℂ) -
        ((L ^ 2 / (16 * Real.pi ^ 2) : ℝ) : ℂ) * poleEvenProfile L K i := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hd := ne_of_gt (poleProfileDenominator_pos hL (centeredIndex K i))
  have hr :
      poleEvenProfileReal (centeredIndex K i) L * ((centeredIndex K i : ℤ) : ℝ) ^ 2 =
        L / (16 * Real.pi ^ 2) -
          (L ^ 2 / (16 * Real.pi ^ 2)) * poleEvenProfileReal (centeredIndex K i) L := by
    unfold poleEvenProfileReal
    field_simp [hp, hd]
    unfold poleProfileDenominator
    ring
  unfold poleEvenProfile
  exact_mod_cast hr

/-- The native odd pole profile `r(n) = 4πn / (L² + 16π² n²)` satisfies
`n² r(n) = n/(4π) - (L²/(16π²)) r(n)`. -/
theorem poleOddProfile_mul_centeredIndex_sq {L : ℝ} (hL : 0 < L) (K : ℕ)
    (i : Fin (2 * K + 1)) :
    poleOddProfile L K i * ((centeredIndex K i : ℤ) : ℂ) ^ 2 =
      ((1 / (4 * Real.pi) : ℝ) : ℂ) * ((centeredIndex K i : ℤ) : ℂ) -
        ((L ^ 2 / (16 * Real.pi ^ 2) : ℝ) : ℂ) * poleOddProfile L K i := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hd := ne_of_gt (poleProfileDenominator_pos hL (centeredIndex K i))
  have hr :
      poleOddProfileReal (centeredIndex K i) L * ((centeredIndex K i : ℤ) : ℝ) ^ 2 =
        1 / (4 * Real.pi) * ((centeredIndex K i : ℤ) : ℝ) -
          (L ^ 2 / (16 * Real.pi ^ 2)) * poleOddProfileReal (centeredIndex K i) L := by
    unfold poleOddProfileReal
    field_simp [hp, hd]
    unfold poleProfileDenominator
    ring
  unfold poleOddProfile
  exact_mod_cast hr

/-- The even pole functional of `D₀ u` is `(L/(16π²)) M₀(u) - β · pole(u)`. -/
theorem poleEven_sum_squaredIndex_mulVec {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    ∑ i, poleEvenProfile L K i * (squaredIndexMatrix K *ᵥ u) i =
      ((L / (16 * Real.pi ^ 2) : ℝ) : ℂ) * centeredMoment K 0 u -
        ((L ^ 2 / (16 * Real.pi ^ 2) : ℝ) : ℂ) * ∑ i, poleEvenProfile L K i * u i := by
  rw [squaredIndexMatrix_eq_diagonal]
  simp only [mulVec_diagonal, centeredMoment, pow_zero, one_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := poleEvenProfile_mul_centeredIndex_sq hL K i
  linear_combination u i * h

/-- The odd pole functional of `D₀ u` is `(1/(4π)) M₁(u) - β · pole(u)`. -/
theorem poleOdd_sum_squaredIndex_mulVec {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    ∑ i, poleOddProfile L K i * (squaredIndexMatrix K *ᵥ u) i =
      ((1 / (4 * Real.pi) : ℝ) : ℂ) * centeredMoment K 1 u -
        ((L ^ 2 / (16 * Real.pi ^ 2) : ℝ) : ℂ) * ∑ i, poleOddProfile L K i * u i := by
  rw [squaredIndexMatrix_eq_diagonal]
  simp only [mulVec_diagonal, centeredMoment, pow_one, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := poleOddProfile_mul_centeredIndex_sq hL K i
  linear_combination u i * h

/-- **Rank-one even leakage.** On the even slice (even boundary-flat, pole-neutral,
`M₄ = 0`), `D₀ u` is even boundary-flat and pole-neutral, and it lies in the slice
exactly when `M₆(u) = 0`. Leaving the slice is one linear functional. -/
theorem squaredIndex_mulVec_even_slice_leakage {L : ℝ} (hL : 0 < L) (K : ℕ)
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ evenBoundaryFlatSubspace K)
    (hpole : ∑ i, poleEvenProfile L K i * u i = 0) (h4 : centeredMoment K 4 u = 0) :
    squaredIndexMatrix K *ᵥ u ∈ evenBoundaryFlatSubspace K ∧
      ∑ i, poleEvenProfile L K i * (squaredIndexMatrix K *ᵥ u) i = 0 ∧
      (centeredMoment K 4 (squaredIndexMatrix K *ᵥ u) = 0 ↔ centeredMoment K 6 u = 0) := by
  obtain ⟨hmem, h46⟩ := squaredIndex_mulVec_even_leakage K hu h4
  have hflat : u ∈ boundaryFlatSubspace K := (Submodule.mem_inf.mp hu).1
  rw [mem_boundaryFlatSubspace_iff] at hflat
  refine ⟨hmem, ?_, by rw [h46]⟩
  rw [poleEven_sum_squaredIndex_mulVec hL, hpole, hflat.1]
  ring

/-- **Rank-one odd leakage.** On the odd slice (odd boundary-flat, pole-neutral,
`M₃ = M₅ = 0`), `D₀ u` is odd boundary-flat and pole-neutral with `M₃ = 0`, and it
lies in the slice exactly when `M₇(u) = 0`. -/
theorem squaredIndex_mulVec_odd_slice_leakage {L : ℝ} (hL : 0 < L) (K : ℕ)
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ oddBoundaryFlatSubspace K)
    (hpole : ∑ i, poleOddProfile L K i * u i = 0) (h3 : centeredMoment K 3 u = 0)
    (h5 : centeredMoment K 5 u = 0) :
    squaredIndexMatrix K *ᵥ u ∈ oddBoundaryFlatSubspace K ∧
      ∑ i, poleOddProfile L K i * (squaredIndexMatrix K *ᵥ u) i = 0 ∧
      centeredMoment K 3 (squaredIndexMatrix K *ᵥ u) = 0 ∧
      (centeredMoment K 5 (squaredIndexMatrix K *ᵥ u) = 0 ↔ centeredMoment K 7 u = 0) := by
  obtain ⟨hmem, h3', h57⟩ := squaredIndex_mulVec_odd_leakage K hu h3 h5
  have hflat : u ∈ boundaryFlatSubspace K := (Submodule.mem_inf.mp hu).1
  rw [mem_boundaryFlatSubspace_iff] at hflat
  refine ⟨hmem, ?_, h3', by rw [h57]⟩
  rw [poleOdd_sum_squaredIndex_mulVec hL, hpole, hflat.2.1]
  ring

end Zeta23.OPICARound4.ArithmeticFrontier
