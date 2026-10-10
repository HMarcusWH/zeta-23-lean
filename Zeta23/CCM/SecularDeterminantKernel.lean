import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace Zeta23.CCM

open Matrix

/-!
# POST284 follow-up M20/M24/M26/M30: exact secular determinant and kernel

Abstract finite-dimensional algebra behind the rank-one parity intertwining
`B D - D A = g ⊗ h` (the repository's `B_L D - D A_L = g H_L`, with `H` the row
`h`).  Over any field, with `D` and `B` invertible, put

* `x = D⁻¹ B⁻¹ g`, `d = D⁻¹ g`, `T = h ⬝ x`.

Then (M20)

* `det A = det B · (1 - T)`;
* `A x = (1 - T) d` (constructive kernel vector at `T = 1`);
* every `z` with `A z = 0` equals `(h ⬝ z) x`; hence `ker A` is at most
  one-dimensional, and for `g ≠ 0`, `T = 1 ↔ ker A ≠ 0`.

(M26) The same statements hold for `A - λ`, `B - λ` at every `λ` with
`B - λ` invertible, because the intertwining is shift invariant.

(M24) A matched rank-one update `B' = B + t g ⊗ k`, `h' = h + t (k D)` keeps the
intertwining and gives `(1 - T') (1 + t γ) = 1 - T`, `γ = k ⬝ B⁻¹ g`.

(M30) An exact `2 × 2` instance with `T(h) = 1 + h³ / (12 + 3h³ - 4h⁶)` and
`A(h) = diag(-h³, 1)`: the rank-one relation, `T(0) = 1`, and a negative even
eigenvalue for `h > 0` all hold simultaneously.  Rank-one intertwining plus
cubic tangency therefore cannot by itself exclude a first crossing.

Scope: pure linear algebra.  Nothing here uses F04, the canonical operator,
the von Mangoldt weights, or RH; `T ≤ 1` is never asserted to imply `A ≽ 0`.
-/

section Abstract

variable {m : Type*} [Fintype m] [DecidableEq m] {𝕜 : Type*} [Field 𝕜]

/-- Rank-one determinant identity `det (1 - w ⊗ k) = 1 - k ⬝ w`. -/
theorem det_one_sub_vecMulVec (w k : m → 𝕜) :
    (1 - vecMulVec w k).det = 1 - k ⬝ᵥ w := by
  have hneg : -(vecMulVec w k) = replicateCol Unit (-w) * replicateRow Unit k := by
    rw [← vecMulVec_eq]
    ext i j
    simp [vecMulVec_apply]
  rw [sub_eq_add_neg, hneg, det_one_add_replicateCol_mul_replicateRow, dotProduct_neg,
    ← sub_eq_add_neg]

/-- Matrix determinant lemma in subtracted form. -/
theorem det_sub_vecMulVec {B : Matrix m m 𝕜} (hB : IsUnit B.det) (g k : m → 𝕜) :
    (B - vecMulVec g k).det = B.det * (1 - k ⬝ᵥ (B⁻¹ *ᵥ g)) := by
  have hfac : B - vecMulVec g k = B * (1 - vecMulVec (B⁻¹ *ᵥ g) k) := by
    rw [Matrix.mul_sub, Matrix.mul_one, mul_vecMulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
  rw [hfac, det_mul, det_one_sub_vecMulVec]

/-- The secular scalar `T = h ⬝ D⁻¹ B⁻¹ g`. -/
def secularScalar (B D : Matrix m m 𝕜) (g h : m → 𝕜) : 𝕜 :=
  h ⬝ᵥ (D⁻¹ *ᵥ (B⁻¹ *ᵥ g))

/-- The constructive secular vector `x = D⁻¹ B⁻¹ g`. -/
def secularVector (B D : Matrix m m 𝕜) (g : m → 𝕜) : m → 𝕜 :=
  D⁻¹ *ᵥ (B⁻¹ *ᵥ g)

variable {A B D : Matrix m m 𝕜} {g h : m → 𝕜}

omit [DecidableEq m] in
theorem mul_eq_of_rankOne (hrank : B * D - D * A = vecMulVec g h) :
    D * A = B * D - vecMulVec g h := by
  rw [← hrank, sub_sub_cancel]

/-- `D A D⁻¹ = B - g ⊗ (h D⁻¹)`. -/
theorem conj_eq_of_rankOne (hrank : B * D - D * A = vecMulVec g h) (hD : IsUnit D.det) :
    D * A * D⁻¹ = B - vecMulVec g (h ᵥ* D⁻¹) := by
  rw [mul_eq_of_rankOne hrank, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD,
    Matrix.mul_one, vecMulVec_mul]

/-- **M20 determinant identity:** `det A = det B · (1 - T)`. -/
theorem det_eq_mul_one_sub_secularScalar (hrank : B * D - D * A = vecMulVec g h)
    (hD : IsUnit D.det) (hB : IsUnit B.det) :
    A.det = B.det * (1 - secularScalar B D g h) := by
  have hDu : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr hD
  rw [← det_conj hDu A, conj_eq_of_rankOne hrank hD, det_sub_vecMulVec hB,
    ← Matrix.dotProduct_mulVec]
  rfl

omit [DecidableEq m] in
/-- `D (A v) = B (D v) - (h ⬝ v) g`. -/
theorem mulVec_mulVec_of_rankOne (hrank : B * D - D * A = vecMulVec g h) (v : m → 𝕜) :
    D *ᵥ (A *ᵥ v) = B *ᵥ (D *ᵥ v) - (h ⬝ᵥ v) • g := by
  rw [Matrix.mulVec_mulVec, mul_eq_of_rankOne hrank, Matrix.sub_mulVec, vecMulVec_mulVec,
    Matrix.mulVec_mulVec, op_smul_eq_smul]

private theorem inv_mulVec_cancel {M : Matrix m m 𝕜} (hM : IsUnit M.det) (v : m → 𝕜) :
    M⁻¹ *ᵥ (M *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]

private theorem mulVec_inv_cancel {M : Matrix m m 𝕜} (hM : IsUnit M.det) (v : m → 𝕜) :
    M *ᵥ (M⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]

/-- **M20 constructive kernel:** `A x = (1 - T) D⁻¹ g`. -/
theorem mulVec_secularVector (hrank : B * D - D * A = vecMulVec g h)
    (hD : IsUnit D.det) (hB : IsUnit B.det) :
    A *ᵥ secularVector B D g = (1 - secularScalar B D g h) • (D⁻¹ *ᵥ g) := by
  have h1 := mulVec_mulVec_of_rankOne hrank (secularVector B D g)
  rw [secularVector, mulVec_inv_cancel hD, mulVec_inv_cancel hB] at h1
  have h2 : D *ᵥ (A *ᵥ secularVector B D g) = (1 - secularScalar B D g h) • g := by
    rw [secularVector, h1, sub_smul, one_smul]
    rfl
  rw [← inv_mulVec_cancel hD (A *ᵥ secularVector B D g), h2, Matrix.mulVec_smul]

/-- **M20 kernel rigidity:** every even zero mode is `(h ⬝ z) x`. -/
theorem eq_smul_secularVector_of_mulVec_eq_zero (hrank : B * D - D * A = vecMulVec g h)
    (hD : IsUnit D.det) (hB : IsUnit B.det) {z : m → 𝕜} (hz : A *ᵥ z = 0) :
    z = (h ⬝ᵥ z) • secularVector B D g := by
  have h1 := mulVec_mulVec_of_rankOne hrank z
  rw [hz, Matrix.mulVec_zero] at h1
  have h2 : B *ᵥ (D *ᵥ z) = (h ⬝ᵥ z) • g := (sub_eq_zero.mp h1.symm)
  have h3 : D *ᵥ z = (h ⬝ᵥ z) • (B⁻¹ *ᵥ g) := by
    rw [← inv_mulVec_cancel hB (D *ᵥ z), h2, Matrix.mulVec_smul]
  conv_lhs => rw [← inv_mulVec_cancel hD z]
  rw [h3, Matrix.mulVec_smul]
  rfl

/-- **M20 contact criterion:** for `g ≠ 0`, `T = 1` iff `A` has a nonzero kernel vector. -/
theorem secularScalar_eq_one_iff (hrank : B * D - D * A = vecMulVec g h)
    (hD : IsUnit D.det) (hB : IsUnit B.det) (hg : g ≠ 0) :
    secularScalar B D g h = 1 ↔ ∃ z : m → 𝕜, z ≠ 0 ∧ A *ᵥ z = 0 := by
  have hd : D⁻¹ *ᵥ g ≠ 0 := by
    intro h0
    apply hg
    rw [← mulVec_inv_cancel hD g, h0, Matrix.mulVec_zero]
  have hx : secularVector B D g ≠ 0 := by
    intro h0
    apply hg
    have : B⁻¹ *ᵥ g = 0 := by
      rw [← mulVec_inv_cancel hD (B⁻¹ *ᵥ g)]
      change D *ᵥ secularVector B D g = 0
      rw [h0, Matrix.mulVec_zero]
    rw [← mulVec_inv_cancel hB g, this, Matrix.mulVec_zero]
  constructor
  · intro hT
    refine ⟨secularVector B D g, hx, ?_⟩
    rw [mulVec_secularVector hrank hD hB, hT, sub_self, zero_smul]
  · rintro ⟨z, hz0, hz⟩
    have hzeq := eq_smul_secularVector_of_mulVec_eq_zero hrank hD hB hz
    have hc : h ⬝ᵥ z ≠ 0 := by
      intro hc
      apply hz0
      rw [hzeq, hc, zero_smul]
    have hAz : A *ᵥ z = (h ⬝ᵥ z) • ((1 - secularScalar B D g h) • (D⁻¹ *ᵥ g)) := by
      conv_lhs => rw [hzeq]
      rw [Matrix.mulVec_smul, mulVec_secularVector hrank hD hB]
    rw [hz, smul_smul] at hAz
    have hmul : (h ⬝ᵥ z * (1 - secularScalar B D g h)) = 0 := by
      by_contra hne
      exact hd ((smul_eq_zero.mp hAz.symm).resolve_left hne)
    have := (mul_eq_zero.mp hmul).resolve_left hc
    exact (sub_eq_zero.mp this).symm

/-- The rank-one intertwining is invariant under a common spectral shift. -/
theorem rankOne_shift (hrank : B * D - D * A = vecMulVec g h) (μ : 𝕜) :
    (B - μ • 1) * D - D * (A - μ • 1) = vecMulVec g h := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, ← hrank]
  abel

/-- **M26 shifted secular equation:** for every `μ` with `B - μ` invertible,
`det (A - μ) = det (B - μ) · (1 - T(μ))` and `(A - μ) v(μ) = (1 - T(μ)) D⁻¹ g`. -/
theorem shifted_secular (hrank : B * D - D * A = vecMulVec g h) (hD : IsUnit D.det)
    (μ : 𝕜) (hBμ : IsUnit (B - μ • 1).det) :
    (A - μ • 1).det = (B - μ • 1).det * (1 - secularScalar (B - μ • 1) D g h) ∧
      (A - μ • 1) *ᵥ secularVector (B - μ • 1) D g =
        (1 - secularScalar (B - μ • 1) D g h) • (D⁻¹ *ᵥ g) :=
  ⟨det_eq_mul_one_sub_secularScalar (rankOne_shift hrank μ) hD hBμ,
    mulVec_secularVector (rankOne_shift hrank μ) hD hBμ⟩

/-- **M26 eigenspace rigidity:** below the odd spectrum every even eigenvector at
`μ` is a multiple of `v(μ)`; in particular the eigenspace is at most a line. -/
theorem shifted_eigenvector_eq_smul (hrank : B * D - D * A = vecMulVec g h)
    (hD : IsUnit D.det) (μ : 𝕜) (hBμ : IsUnit (B - μ • 1).det) {z : m → 𝕜}
    (hz : A *ᵥ z = μ • z) :
    z = (h ⬝ᵥ z) • secularVector (B - μ • 1) D g := by
  apply eq_smul_secularVector_of_mulVec_eq_zero (rankOne_shift hrank μ) hD hBμ
  rw [Matrix.sub_mulVec, hz, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]

/-- **M24 matched rank-one update (Sherman–Morrison form).**  With
`B' = B + t g ⊗ k` and `h' = h + t (k D)`, the intertwining persists and
`(1 - T') (1 + t γ) = 1 - T`, where `γ = k ⬝ B⁻¹ g`. -/
theorem matched_update (hrank : B * D - D * A = vecMulVec g h) (hD : IsUnit D.det)
    (hB : IsUnit B.det) (k : m → 𝕜) (t : 𝕜)
    (hB' : IsUnit (B + t • vecMulVec g k).det) :
    (B + t • vecMulVec g k) * D - D * A = vecMulVec g (h + t • (k ᵥ* D)) ∧
      (1 - secularScalar (B + t • vecMulVec g k) D g (h + t • (k ᵥ* D))) *
          (1 + t * (k ⬝ᵥ (B⁻¹ *ᵥ g))) =
        1 - secularScalar B D g h := by
  have hrank' : (B + t • vecMulVec g k) * D - D * A = vecMulVec g (h + t • (k ᵥ* D)) := by
    rw [Matrix.add_mul, Matrix.smul_mul, vecMulVec_mul, add_sub_right_comm, hrank]
    ext i j
    simp [vecMulVec_apply, mul_add, mul_left_comm]
  refine ⟨hrank', ?_⟩
  have hdet1 := det_eq_mul_one_sub_secularScalar hrank hD hB
  have hdet2 := det_eq_mul_one_sub_secularScalar hrank' hD hB'
  have hdetB' : (B + t • vecMulVec g k).det = B.det * (1 + t * (k ⬝ᵥ (B⁻¹ *ᵥ g))) := by
    have : B + t • vecMulVec g k = B - vecMulVec g (-(t • k)) := by
      ext i j
      simp [vecMulVec_apply]
    rw [this, det_sub_vecMulVec hB, neg_dotProduct, smul_dotProduct, smul_eq_mul, sub_neg_eq_add]
  rw [hdetB'] at hdet2
  have hBne : B.det ≠ 0 := hB.ne_zero
  have := hdet1.symm.trans hdet2
  rw [mul_assoc] at this
  have := mul_left_cancel₀ hBne this
  rw [this]
  ring

end Abstract

/-! ## M30: exact `2 × 2` crossing negative control -/

section Crossing

/-- Fixed (non-unitary) intertwiner `D = [[4,3],[3,2]]`, `det D = -1`. -/
def crossingD : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![4, 3], ![3, 2]]

/-- Odd generator `g = (1,1)`. -/
def crossingG : Fin 2 → ℝ := ![1, 1]

/-- Even block `A(h) = diag(-h³, 1)`. -/
def crossingA (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![-s ^ 3, 0], ![0, 1]]

/-- Odd block `B(h) = [[3, -2h³], [-2h³, 4 + h³]]`. -/
def crossingB (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![3, -2 * s ^ 3], ![-2 * s ^ 3, 4 + s ^ 3]]

/-- Source row `H(h) = (12 - 2h³, 6 - 4h³)`. -/
def crossingH (s : ℝ) : Fin 2 → ℝ := ![12 - 2 * s ^ 3, 6 - 4 * s ^ 3]

theorem crossing_rankOne (s : ℝ) :
    crossingB s * crossingD - crossingD * crossingA s = vecMulVec crossingG (crossingH s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossingB, crossingD, crossingA, crossingG, crossingH, vecMulVec_apply] <;> ring

theorem crossingD_det : crossingD.det = -1 := by
  rw [Matrix.det_fin_two]
  simp [crossingD]
  norm_num

theorem crossingA_det (s : ℝ) : (crossingA s).det = -s ^ 3 := by
  rw [Matrix.det_fin_two]
  simp [crossingA]

theorem crossingB_det (s : ℝ) : (crossingB s).det = 12 + 3 * s ^ 3 - 4 * s ^ 6 := by
  rw [Matrix.det_fin_two]
  simp [crossingB]
  ring

/-- **M30 exact secular scalar:** `(1 - T(h)) (12 + 3h³ - 4h⁶) = -h³` whenever
`det B(h) ≠ 0`; so `T(h) = 1 + h³ / (12 + 3h³ - 4h⁶)`, `T(0) = 1`, and
`T - 1` vanishes to third order at `h = 0`. -/
theorem crossing_secular (s : ℝ) (hs : 12 + 3 * s ^ 3 - 4 * s ^ 6 ≠ 0) :
    (1 - secularScalar (crossingB s) crossingD crossingG (crossingH s)) *
        (12 + 3 * s ^ 3 - 4 * s ^ 6) = -s ^ 3 := by
  have hD : IsUnit crossingD.det := by rw [crossingD_det]; norm_num
  have hB : IsUnit (crossingB s).det := by rw [crossingB_det]; exact Ne.isUnit hs
  have := det_eq_mul_one_sub_secularScalar (crossing_rankOne s) hD hB
  rw [crossingA_det, crossingB_det] at this
  linear_combination -this

/-- `B(0) = diag(3,4)` is positive definite (as a real quadratic form). -/
theorem crossingB_zero_posDef (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ (crossingB 0 *ᵥ v) := by
  have : v ⬝ᵥ (crossingB 0 *ᵥ v) = 3 * v 0 ^ 2 + 4 * v 1 ^ 2 := by
    simp [crossingB, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  rw [this]
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    positivity
  · positivity

/-- For every `h > 0` the even block has the negative direction `e₀`
(`⟪e₀, A(h) e₀⟫ = -h³ < 0`), while `A(0) ≽ 0`: the first crossing survives. -/
theorem crossingA_negative (s : ℝ) (hs : 0 < s) :
    (![1, 0] : Fin 2 → ℝ) ⬝ᵥ (crossingA s *ᵥ ![1, 0]) = -s ^ 3 ∧
      (![1, 0] : Fin 2 → ℝ) ⬝ᵥ (crossingA s *ᵥ ![1, 0]) < 0 := by
  have h : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ (crossingA s *ᵥ ![1, 0]) = -s ^ 3 := by
    simp [crossingA, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  exact ⟨h, by rw [h]; have := pow_pos hs 3; linarith⟩

theorem crossingA_zero_nonneg (v : Fin 2 → ℝ) :
    0 ≤ v ⬝ᵥ (crossingA 0 *ᵥ v) := by
  have : v ⬝ᵥ (crossingA 0 *ᵥ v) = v 1 ^ 2 := by
    simp [crossingA, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  rw [this]
  positivity

end Crossing

end Zeta23.CCM

#print axioms Zeta23.CCM.det_sub_vecMulVec
#print axioms Zeta23.CCM.det_eq_mul_one_sub_secularScalar
#print axioms Zeta23.CCM.mulVec_secularVector
#print axioms Zeta23.CCM.eq_smul_secularVector_of_mulVec_eq_zero
#print axioms Zeta23.CCM.secularScalar_eq_one_iff
#print axioms Zeta23.CCM.shifted_secular
#print axioms Zeta23.CCM.shifted_eigenvector_eq_smul
#print axioms Zeta23.CCM.matched_update
#print axioms Zeta23.CCM.crossing_rankOne
#print axioms Zeta23.CCM.crossing_secular
#print axioms Zeta23.CCM.crossingB_zero_posDef
#print axioms Zeta23.CCM.crossingA_negative
