import Zeta23.CCM.CanonicalSourceExcursion
import Zeta23.CCM.CanonicalCenteredIndexPoincare
import Zeta23.CCM.CanonicalSourceMomentAtoms
import Zeta23.CCM.SourceFourierConvolution
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate

/-!
# POST285 M75 (Steps 119–120): source Lipschitz bound, uniform negative interval,
and opposite-signed individual prime terms

For a centered coefficient vector `z` write `e(ω) = Re e_{Dz}(ω)` (`(Dz)_n = n z_n`,
`sourceEnergyRe`).

* **Entry Lipschitz bound.**  From the exact cosine-integral form of the source
  entry, `|S_nm(ω) - S_nm(ω')| ≤ (2 + 4π|m|) |ω - ω'|` whenever `|ω'| ≤ 1`.
* **Energy Lipschitz bound.**  `|e(ω) - e(ω')| ≤ M_K |ω - ω'| ‖z‖²` with
  `M_K = (2 + 4πK)(2K+1)K²` (`sourceLipschitzConstant`).
* **Step 119.**  For nonzero zero-sum `z` there is `ω₋ ∈ (0,1)` such that
  `e(ω) < -‖z‖²/(2π²)` for every `|ω - ω₋| ≤ η_K = 1/(2π² M_K)`; moreover
  `ω₋ > 2η_K` and `1 - ω₋ > (1/2 + 1/π²)/M_K` (from `e(0) = 0`, `e(1) ≥ ‖z‖²/2`).
* **Step 120.**  If `L ≥ π² M_K log 2`, Bertrand's postulate gives a prime
  `2 < p < e^L` whose sample `ω_p = 1 - log p / L` lies in that negative window, so
  the physical second-test prime term `-(Λ(p)(log p)²/√p) e(ω_p)` is strictly
  positive, while the `p = 2` term is strictly negative.

Scope.  These are statements about **individual** prime summands of the fixed-vector
test.  Nothing is said about the sign of the prime sum, of the full physical
second test, or of any contact-conditioned quantity; mixed individual prime signs
are an obstruction to termwise prime positivity, not an RH contradiction.
-/

/-! ## Lipschitz bounds -/

/-- `|centeredIndex N i| ≤ N`. -/
theorem abs_centeredIndex_le (N : ℕ) (i : Fin (2 * N + 1)) :
    |((centeredIndex N i : ℤ) : ℝ)| ≤ (N : ℝ) := by
  have h1 := i.2
  have habs : |centeredIndex N i| ≤ (N : ℤ) := by
    rw [abs_le]; simp only [centeredIndex]; omega
  rw [← Int.cast_abs]
  exact_mod_cast habs

/-- **Entry Lipschitz bound.** `|S_nm(ω) - S_nm(ω')| ≤ (2 + 4π|m|)|ω - ω'|` for
`|ω'| ≤ 1`. -/
theorem norm_sourceEntry_sub_le {ω ω' : ℝ} (hω' : |ω'| ≤ 1) (n m : ℤ) :
    ‖sourceEntry ω n m - sourceEntry ω' n m‖ ≤
      (2 + 4 * Real.pi * |(m : ℝ)|) * |ω - ω'| := by
  rw [sourceEntry_eq_cos_integral, sourceEntry_eq_cos_integral, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  have hpi := Real.pi_pos
  let f : ℝ → ℝ → ℝ := fun b t => Real.cos ((n : ℝ) * t + (m : ℝ) * (b - t))
  have hcont : ∀ b, Continuous (f b) := fun b => by fun_prop
  set a := 2 * Real.pi * ω with ha
  set a' := 2 * Real.pi * ω' with ha'
  show |1 / Real.pi * (∫ t in (0 : ℝ)..a, f a t) -
      1 / Real.pi * ∫ t in (0 : ℝ)..a', f a' t| ≤ _
  have hsplit : (∫ t in (0 : ℝ)..a, f a t) - ∫ t in (0 : ℝ)..a', f a' t =
      (∫ t in a'..a, f a t) + ∫ t in (0 : ℝ)..a', (f a t - f a' t) := by
    rw [intervalIntegral.integral_sub ((hcont a).intervalIntegrable _ _)
        ((hcont a').intervalIntegrable _ _),
      ← intervalIntegral.integral_add_adjacent_intervals
        ((hcont a).intervalIntegrable 0 a') ((hcont a).intervalIntegrable a' a)]
    ring
  have h1 : |∫ t in a'..a, f a t| ≤ 1 * |a - a'| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a') (b := a) (C := 1)
      (f := f a) (fun t _ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    rw [Real.norm_eq_abs] at this
    exact this
  have h2 : |∫ t in (0 : ℝ)..a', (f a t - f a' t)| ≤ (|(m : ℝ)| * |a - a'|) * |a' - 0| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := a')
      (C := |(m : ℝ)| * |a - a'|) (f := fun t => f a t - f a' t)
      (fun t _ => by
        rw [Real.norm_eq_abs]
        calc |f a t - f a' t| ≤
              |((n : ℝ) * t + (m : ℝ) * (a - t)) - ((n : ℝ) * t + (m : ℝ) * (a' - t))| :=
              Real.abs_cos_sub_cos_le _ _
          _ = |(m : ℝ)| * |a - a'| := by rw [← abs_mul]; congr 1; ring)
    rw [Real.norm_eq_abs] at this
    exact this
  have hΔ : |a - a'| = 2 * Real.pi * |ω - ω'| := by
    rw [ha, ha', ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have ha'abs : |a' - 0| = 2 * Real.pi * |ω'| := by
    rw [sub_zero, ha', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [← mul_sub, hsplit, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  have hm := abs_nonneg (m : ℝ)
  have hd := abs_nonneg (ω - ω')
  calc 1 / Real.pi * |(∫ t in a'..a, f a t) + ∫ t in (0 : ℝ)..a', (f a t - f a' t)| ≤
        1 / Real.pi * (1 * |a - a'| + (|(m : ℝ)| * |a - a'|) * |a' - 0|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = 2 * |ω - ω'| + 4 * Real.pi * |(m : ℝ)| * |ω - ω'| * |ω'| := by
        rw [hΔ, ha'abs]
        field_simp
        ring
    _ ≤ (2 + 4 * Real.pi * |(m : ℝ)|) * |ω - ω'| := by
        have : 4 * Real.pi * |(m : ℝ)| * |ω - ω'| * |ω'| ≤ 4 * Real.pi * |(m : ℝ)| * |ω - ω'| :=
          mul_le_of_le_one_right (by positivity) hω'
        linarith

/-- **Quadratic-form Lipschitz bound.**
`‖e_u(ω) - e_u(ω')‖ ≤ (2 + 4πN)|ω - ω'| (∑ |u_i|)²` for `|ω'| ≤ 1`. -/
theorem norm_quadraticForm_sourceMatrix_sub_le {ω ω' : ℝ} (hω' : |ω'| ≤ 1) (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    ‖quadraticForm (sourceMatrix ω N) u - quadraticForm (sourceMatrix ω' N) u‖ ≤
      (2 + 4 * Real.pi * N) * |ω - ω'| * (∑ i, ‖u i‖) ^ 2 := by
  have hpi := Real.pi_pos
  have hdiff : quadraticForm (sourceMatrix ω N) u - quadraticForm (sourceMatrix ω' N) u =
      ∑ i, ∑ j, conj (u i) * (sourceMatrix ω N i j - sourceMatrix ω' N i j) * u j := by
    unfold quadraticForm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hdiff]
  calc ‖∑ i, ∑ j, conj (u i) * (sourceMatrix ω N i j - sourceMatrix ω' N i j) * u j‖ ≤
        ∑ i, ∑ j, ‖conj (u i) * (sourceMatrix ω N i j - sourceMatrix ω' N i j) * u j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j, ‖u i‖ * ((2 + 4 * Real.pi * N) * |ω - ω'|) * ‖u j‖ := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        rw [norm_mul, norm_mul, Complex.norm_conj, sourceMatrix_apply, sourceMatrix_apply]
        have hentry := norm_sourceEntry_sub_le (ω := ω) hω' (centeredIndex N i)
          (centeredIndex N j)
        have hj := abs_centeredIndex_le N j
        have hentry' : ‖sourceEntry ω (centeredIndex N i) (centeredIndex N j) -
            sourceEntry ω' (centeredIndex N i) (centeredIndex N j)‖ ≤
            (2 + 4 * Real.pi * N) * |ω - ω'| := by
          refine hentry.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
          have := mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
          linarith
        gcongr
    _ = (2 + 4 * Real.pi * N) * |ω - ω'| * (∑ i, ‖u i‖) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        ring

/-- `(∑ |(Dz)_i|)² ≤ (2N+1) N² ‖z‖²`. -/
theorem sq_sum_norm_index_le (N : ℕ) (z : Fin (2 * N + 1) → ℂ) :
    (∑ i, ‖(indexMatrix N *ᵥ z) i‖) ^ 2 ≤
      (2 * N + 1) * N ^ 2 * ∑ i, Complex.normSq (z i) := by
  set u := indexMatrix N *ᵥ z with hu
  have hui : ∀ i, ‖u i‖ ≤ N * ‖z i‖ := by
    intro i
    have : u i = ((centeredIndex N i : ℤ) : ℂ) * z i := by
      simp [hu, indexMatrix, Matrix.mulVec_diagonal]
    rw [this, norm_mul, Complex.norm_intCast]
    exact mul_le_mul_of_nonneg_right (abs_centeredIndex_le N i) (norm_nonneg _)
  have hcs : (∑ i, ‖u i‖) ^ 2 ≤ ((2 * N + 1 : ℕ) : ℝ) * ∑ i, ‖u i‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (2 * N + 1))))
      (f := fun i => ‖u i‖)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have hsq : ∑ i, ‖u i‖ ^ 2 ≤ (N : ℝ) ^ 2 * ∑ i, Complex.normSq (z i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [Complex.normSq_eq_norm_sq]
    have := hui i
    have h0 := norm_nonneg (u i)
    nlinarith [norm_nonneg (z i)]
  calc (∑ i, ‖u i‖) ^ 2 ≤ ((2 * N + 1 : ℕ) : ℝ) * ((N : ℝ) ^ 2 * ∑ i, Complex.normSq (z i)) :=
        hcs.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
    _ = (2 * N + 1) * N ^ 2 * ∑ i, Complex.normSq (z i) := by push_cast; ring

/-- `M_N = (2 + 4πN)(2N+1)N²`. -/
def sourceLipschitzConstant (N : ℕ) : ℝ :=
  (2 + 4 * Real.pi * N) * (2 * N + 1) * N ^ 2

theorem sourceLipschitzConstant_pos {N : ℕ} (hN : N ≠ 0) : 0 < sourceLipschitzConstant N := by
  unfold sourceLipschitzConstant
  have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have := Real.pi_pos
  positivity

/-- **M75 energy Lipschitz bound.**
`|e(ω) - e(ω')| ≤ M_N |ω - ω'| ‖z‖²` for `|ω'| ≤ 1`. -/
theorem abs_sourceEnergyRe_index_sub_le {ω ω' : ℝ} (hω' : |ω'| ≤ 1) (N : ℕ)
    (z : Fin (2 * N + 1) → ℂ) :
    |sourceEnergyRe N (indexMatrix N *ᵥ z) ω - sourceEnergyRe N (indexMatrix N *ᵥ z) ω'| ≤
      sourceLipschitzConstant N * |ω - ω'| * ∑ i, Complex.normSq (z i) := by
  unfold sourceEnergyRe
  rw [← Complex.sub_re]
  have hpi := Real.pi_pos
  calc _ ≤ ‖quadraticForm (sourceMatrix ω N) (indexMatrix N *ᵥ z) -
        quadraticForm (sourceMatrix ω' N) (indexMatrix N *ᵥ z)‖ := Complex.abs_re_le_norm _
    _ ≤ (2 + 4 * Real.pi * N) * |ω - ω'| * (∑ i, ‖(indexMatrix N *ᵥ z) i‖) ^ 2 :=
        norm_quadraticForm_sourceMatrix_sub_le hω' N _
    _ ≤ (2 + 4 * Real.pi * N) * |ω - ω'| *
          ((2 * N + 1) * N ^ 2 * ∑ i, Complex.normSq (z i)) :=
        mul_le_mul_of_nonneg_left (sq_sum_norm_index_le N z) (by positivity)
    _ = _ := by unfold sourceLipschitzConstant; ring

/-! ## Endpoint values -/

/-- `e_u(1) = 2 ‖u‖²` (the source matrix at `ω = 1` is `2I`). -/
theorem sourceEnergyRe_one (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    sourceEnergyRe N u 1 = 2 * ∑ i, Complex.normSq (u i) := by
  unfold sourceEnergyRe quadraticForm
  rw [sourceMatrix_one]
  have hdiag : ∀ i, (∑ j, conj (u i) *
      ((2 : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)) i j * u j) =
      2 * (conj (u i) * u i) := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
      ring
    · intro j _ hji
      simp [Matrix.one_apply_ne (Ne.symm hji)]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp only [hdiag, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [mul_comm (conj (u i)), Complex.mul_conj, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- `e_{Dz}(1) = 2 ∑ n² |z_n|² ≥ ‖z‖²/2` for `∑ z = 0` (M73). -/
theorem sourceEnergyRe_index_one_ge (N : ℕ) (z : Fin (2 * N + 1) → ℂ)
    (hsum : ∑ i, z i = 0) :
    (∑ i, Complex.normSq (z i)) / 2 ≤ sourceEnergyRe N (indexMatrix N *ᵥ z) 1 := by
  rw [sourceEnergyRe_one]
  have hcoord : ∀ i, Complex.normSq ((indexMatrix N *ᵥ z) i) =
      ((centeredIndex N i : ℤ) : ℝ) ^ 2 * Complex.normSq (z i) := by
    intro i
    have : (indexMatrix N *ᵥ z) i = ((centeredIndex N i : ℤ) : ℂ) * z i := by
      simp [indexMatrix, Matrix.mulVec_diagonal]
    rw [this, Complex.normSq_mul, Complex.normSq_intCast, sq]
  simp only [hcoord]
  have := sum_normSq_le_four_mul z hsum
  linarith

/-- A nonzero zero-sum vector forces `N ≠ 0`. -/
theorem ne_zero_of_zeroSum {N : ℕ} {z : Fin (2 * N + 1) → ℂ} (hz : z ≠ 0)
    (hsum : ∑ i, z i = 0) : N ≠ 0 := by
  rintro rfl
  apply hz
  funext i
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst hi
  simpa using hsum

/-! ## Step 119: uniform negative interval -/

/-- `η_N = 1/(2π² M_N)`. -/
def sourceNegativeRadius (N : ℕ) : ℝ :=
  1 / (2 * Real.pi ^ 2 * sourceLipschitzConstant N)

/-- **M75 / Step 119.**  For nonzero zero-sum `z` there is `ω₋ ∈ (0,1)` with
`2η_N < ω₋`, `(1/2 + 1/π²)/M_N < 1 - ω₋`, and `e(ω) < -‖z‖²/(2π²)` whenever
`|ω - ω₋| ≤ η_N`.  In particular the closed window `[ω₋ - η_N, ω₋ + η_N]` lies in
`(0,1)`. -/
theorem exists_sourceNegativeWindow (N : ℕ) (z : Fin (2 * N + 1) → ℂ) (hz : z ≠ 0)
    (hsum : ∑ i, z i = 0) :
    ∃ ωneg ∈ Set.Ioo (0 : ℝ) 1,
      2 * sourceNegativeRadius N < ωneg ∧
      (1 / 2 + 1 / Real.pi ^ 2) / sourceLipschitzConstant N < 1 - ωneg ∧
      ∀ ω, |ω - ωneg| ≤ sourceNegativeRadius N →
        sourceEnergyRe N (indexMatrix N *ᵥ z) ω <
          -(∑ i, Complex.normSq (z i)) / (2 * Real.pi ^ 2) := by
  have hN := ne_zero_of_zeroSum hz hsum
  set M := sourceLipschitzConstant N with hMdef
  have hM : 0 < M := sourceLipschitzConstant_pos hN
  set c := ∑ i, Complex.normSq (z i) with hcdef
  have hc : 0 < c := sum_normSq_pos_of_ne_zero hz
  set e := sourceEnergyRe N (indexMatrix N *ᵥ z) with hedef
  have hpi2 : 0 < Real.pi ^ 2 := by have := Real.pi_pos; positivity
  obtain ⟨ωneg, hω, hneg⟩ := exists_sourceEnergyRe_lt_neg_of_zeroSum N z hz hsum
  have hωabs : |ωneg| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hω.1, hω.2]
  refine ⟨ωneg, hω, ?_, ?_, ?_⟩
  · -- distance from `ω = 0`, where `e = 0`
    have hlip := abs_sourceEnergyRe_index_sub_le (ω := ωneg) (ω' := 0) (by simp) N z
    rw [← hedef, ← hMdef, ← hcdef, hedef, sourceEnergyRe_zero, ← hedef, sub_zero, sub_zero,
      abs_of_pos hω.1] at hlip
    have h1 : c / Real.pi ^ 2 < M * ωneg * c := by
      have := neg_abs_le (e ωneg)
      have : -(c / Real.pi ^ 2) = -c / Real.pi ^ 2 := by ring
      linarith
    have h2 : 1 < Real.pi ^ 2 * M * ωneg := by
      rw [div_lt_iff₀ hpi2] at h1
      nlinarith
    unfold sourceNegativeRadius
    rw [← hMdef]
    have : 2 * (1 / (2 * Real.pi ^ 2 * M)) = 1 / (Real.pi ^ 2 * M) := by
      field_simp
    rw [this, div_lt_iff₀ (by positivity)]
    linarith
  · -- distance from `ω = 1`, where `e ≥ ‖z‖²/2`
    have hone := sourceEnergyRe_index_one_ge N z hsum
    rw [← hedef, ← hcdef] at hone
    have hlip := abs_sourceEnergyRe_index_sub_le (ω := 1) (ω' := ωneg) hωabs N z
    rw [← hedef, ← hMdef, ← hcdef, abs_of_pos (by linarith [hω.2] : (0 : ℝ) < 1 - ωneg)] at hlip
    have h1 : c * (1 / 2 + 1 / Real.pi ^ 2) < M * (1 - ωneg) * c := by
      have := le_abs_self (e 1 - e ωneg)
      have : -c / Real.pi ^ 2 = -(c * (1 / Real.pi ^ 2)) := by ring
      nlinarith
    rw [div_lt_iff₀ hM]
    nlinarith
  · intro ω hωw
    have hlip := abs_sourceEnergyRe_index_sub_le (ω := ω) (ω' := ωneg) hωabs N z
    rw [← hedef, ← hMdef, ← hcdef] at hlip
    have hη : M * |ω - ωneg| * c ≤ c / (2 * Real.pi ^ 2) := by
      have : M * |ω - ωneg| ≤ M * sourceNegativeRadius N := mul_le_mul_of_nonneg_left hωw hM.le
      have hMη : M * sourceNegativeRadius N = 1 / (2 * Real.pi ^ 2) := by
        unfold sourceNegativeRadius
        rw [← hMdef]
        field_simp
      calc M * |ω - ωneg| * c ≤ M * sourceNegativeRadius N * c :=
            mul_le_mul_of_nonneg_right this hc.le
        _ = c / (2 * Real.pi ^ 2) := by rw [hMη]; ring
    have := le_abs_self (e ω - e ωneg)
    have hsplit : -c / Real.pi ^ 2 + c / (2 * Real.pi ^ 2) = -c / (2 * Real.pi ^ 2) := by
      field_simp
      ring
    linarith

/-! ## Step 120: opposite-signed individual prime terms -/

/-- The physical second-test prime-power summand
`F_q = -(Λ(q)(log q)²/√q) e_{Dz}(1 - log q / L)` (exact von Mangoldt weight). -/
def physicalSecondPrimeTerm (N : ℕ) (z : Fin (2 * N + 1) → ℂ) (L : ℝ) (q : ℕ) : ℝ :=
  -(Λ q * Real.log q ^ 2 / Real.sqrt q) *
    sourceEnergyRe N (indexMatrix N *ᵥ z) (primeSourceCoordinate q L)

/-- For a prime `p` the coefficient is `(log p)³/√p > 0`. -/
theorem physicalSecondPrimeCoefficient_prime {p : ℕ} (hp : p.Prime) :
    Λ p * Real.log p ^ 2 / Real.sqrt p = Real.log p ^ 3 / Real.sqrt p ∧
      0 < Real.log p ^ 3 / Real.sqrt p := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  refine ⟨by ring, ?_⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have := Real.log_pos hp1
  have : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  positivity

/-- **M75 / Step 120.**  For nonzero zero-sum `z` and `L ≥ π² M_N log 2` there is a
prime `2 < p < e^L` whose sample lies in the Step 119 negative window, so its
physical second-test summand is strictly positive, while the `p = 2` summand is
strictly negative.  Individual summands only: no statement about the prime sum. -/
theorem exists_prime_physicalSecondPrimeTerm_pos_and_two_neg (N : ℕ)
    (z : Fin (2 * N + 1) → ℂ) (hz : z ≠ 0) (hsum : ∑ i, z i = 0) {L : ℝ}
    (hL : Real.pi ^ 2 * sourceLipschitzConstant N * Real.log 2 ≤ L) :
    ∃ p : ℕ, p.Prime ∧ 2 < p ∧ (p : ℝ) < Real.exp L ∧
      sourceEnergyRe N (indexMatrix N *ᵥ z) (primeSourceCoordinate p L) <
        -(∑ i, Complex.normSq (z i)) / (2 * Real.pi ^ 2) ∧
      0 < physicalSecondPrimeTerm N z L p ∧
      0 < sourceEnergyRe N (indexMatrix N *ᵥ z) (primeSourceCoordinate 2 L) ∧
      physicalSecondPrimeTerm N z L 2 < 0 := by
  have hN := ne_zero_of_zeroSum hz hsum
  set M := sourceLipschitzConstant N with hMdef
  have hM : 0 < M := sourceLipschitzConstant_pos hN
  set c := ∑ i, Complex.normSq (z i) with hcdef
  have hc : 0 < c := sum_normSq_pos_of_ne_zero hz
  set e := sourceEnergyRe N (indexMatrix N *ᵥ z) with hedef
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi2 : 9 < Real.pi ^ 2 := by nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `π² M ≥ 1`
  have hM1 : 1 ≤ M := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
    rw [hMdef]
    unfold sourceLipschitzConstant
    have h1 : (1 : ℝ) ≤ 2 + 4 * Real.pi * N := by nlinarith
    have h2 : (1 : ℝ) ≤ 2 * N + 1 := by linarith
    have h3 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have hLpos : 0 < L := by
    have : 0 < Real.pi ^ 2 * M * Real.log 2 := by positivity
    linarith
  obtain ⟨ωneg, hω, hlow, hhigh, hwin⟩ := exists_sourceNegativeWindow N z hz hsum
  rw [← hMdef] at hhigh
  rw [← hcdef, ← hedef] at hwin
  set η := sourceNegativeRadius N with hηdef
  have hη : η = 1 / (2 * Real.pi ^ 2 * M) := by rw [hηdef, hMdef]; rfl
  have hηpos : 0 < η := by rw [hη]; positivity
  -- `log 2 ≤ 2ηL`
  have h2ηL : Real.log 2 ≤ 2 * η * L := by
    rw [hη]
    have : 2 * (1 / (2 * Real.pi ^ 2 * M)) * L = L / (Real.pi ^ 2 * M) := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  -- lower logarithmic endpoint `A = L(1 - ω₋ - η) > log 2`
  set A := L * (1 - ωneg - η) with hA
  have hA2 : Real.log 2 < A := by
    have hgap : (1 / 2 + 1 / (2 * Real.pi ^ 2)) / M < 1 - ωneg - η := by
      have : (1 / 2 + 1 / (2 * Real.pi ^ 2)) / M = (1 / 2 + 1 / Real.pi ^ 2) / M - η := by
        rw [hη]; field_simp; ring
      rw [this]; linarith
    have hLM : Real.pi ^ 2 * Real.log 2 ≤ L / M := by
      rw [le_div_iff₀ hM]; linarith
    have hkey : Real.log 2 ≤ L * ((1 / 2 + 1 / (2 * Real.pi ^ 2)) / M) := by
      have : L * ((1 / 2 + 1 / (2 * Real.pi ^ 2)) / M) =
          (L / M) * (1 / 2 + 1 / (2 * Real.pi ^ 2)) := by ring
      rw [this]
      have hfac : 1 / 2 ≤ 1 / 2 + 1 / (2 * Real.pi ^ 2) := by
        have : 0 < 1 / (2 * Real.pi ^ 2) := by positivity
        linarith
      have hLM0 : 0 ≤ L / M := by positivity
      calc Real.log 2 ≤ Real.pi ^ 2 * Real.log 2 * (1 / 2) := by nlinarith
        _ ≤ (L / M) * (1 / 2 + 1 / (2 * Real.pi ^ 2)) := by
          apply mul_le_mul hLM hfac (by norm_num) hLM0
    calc Real.log 2 ≤ L * ((1 / 2 + 1 / (2 * Real.pi ^ 2)) / M) := hkey
      _ < L * (1 - ωneg - η) := mul_lt_mul_of_pos_left hgap hLpos
  -- Bertrand on `n = ⌊e^A⌋`
  set x := Real.exp A with hx
  have hx2 : 2 < x := by
    rw [hx, ← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_lt_exp.mpr hA2
  set n := ⌊x⌋₊ with hn
  have hn2 : 2 ≤ n := by
    rw [hn]; apply Nat.le_floor; push_cast; linarith
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hpx : x < p := by
    have := Nat.lt_floor_add_one x
    have : (n : ℝ) + 1 ≤ p := by exact_mod_cast hnp
    linarith
  have hp2x : (p : ℝ) ≤ 2 * x := by
    have h1 : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2n
    have h2 : (n : ℝ) ≤ x := Nat.floor_le (by positivity)
    linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp_lo : A < Real.log p := by
    rw [Real.lt_log_iff_exp_lt hp0]; exact hpx
  have hlogp_hi : Real.log p ≤ Real.log 2 + A := by
    rw [← Real.log_exp A, ← hx, ← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log hp0 hp2x
  -- the prime sample lies in the window
  have hwinp : |primeSourceCoordinate p L - ωneg| ≤ η := by
    unfold primeSourceCoordinate
    rw [abs_le]
    constructor
    · have : Real.log p / L ≤ 1 - ωneg + η := by
        rw [div_le_iff₀ hLpos]; nlinarith
      linarith
    · have : 1 - ωneg - η < Real.log p / L := by
        rw [lt_div_iff₀ hLpos]; linarith
      linarith
  have hep := hwin _ hwinp
  have hp2 : 2 < p := by
    have : (2 : ℝ) < p := by linarith
    exact_mod_cast this
  have hpL : (p : ℝ) < Real.exp L := by
    rw [← Real.exp_log hp0]
    apply Real.exp_lt_exp.mpr
    have : ωneg - η > 0 := by linarith
    nlinarith
  -- the `p = 2` sample is near `ω = 1`, where the energy is positive
  have he2 : 0 < e (primeSourceCoordinate 2 L) := by
    have hone := sourceEnergyRe_index_one_ge N z hsum
    rw [← hedef, ← hcdef] at hone
    have hlip := abs_sourceEnergyRe_index_sub_le (ω := primeSourceCoordinate 2 L) (ω' := 1)
      (by simp) N z
    rw [← hedef, ← hMdef, ← hcdef] at hlip
    have hd : |primeSourceCoordinate 2 L - 1| = Real.log 2 / L := by
      unfold primeSourceCoordinate
      rw [show 1 - Real.log ((2 : ℕ) : ℝ) / L - 1 = -(Real.log 2 / L) by push_cast; ring,
        abs_neg, abs_of_pos (by positivity)]
    rw [hd] at hlip
    have hML : M * (Real.log 2 / L) ≤ 1 / Real.pi ^ 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hLpos (by positivity)]
      linarith
    have hbound : M * (Real.log 2 / L) * c ≤ c / Real.pi ^ 2 := by
      calc M * (Real.log 2 / L) * c ≤ 1 / Real.pi ^ 2 * c :=
            mul_le_mul_of_nonneg_right hML hc.le
        _ = c / Real.pi ^ 2 := by ring
    have hpos : c / Real.pi ^ 2 < c / 2 := by
      apply div_lt_div_of_pos_left hc (by norm_num) (by linarith)
    have := neg_abs_le (e (primeSourceCoordinate 2 L) - e 1)
    linarith
  obtain ⟨-, hcoef⟩ := physicalSecondPrimeCoefficient_prime hp
  obtain ⟨-, hcoef2⟩ := physicalSecondPrimeCoefficient_prime Nat.prime_two
  have hcp := (physicalSecondPrimeCoefficient_prime hp).1
  have hc2 := (physicalSecondPrimeCoefficient_prime Nat.prime_two).1
  have hneg2 : -c / (2 * Real.pi ^ 2) < 0 := by
    have : 0 < c / (2 * Real.pi ^ 2) := by positivity
    rw [neg_div]; linarith
  refine ⟨p, hp, hp2, hpL, hep, ?_, he2, ?_⟩
  · unfold physicalSecondPrimeTerm
    rw [hcp, ← hedef]
    have : e (primeSourceCoordinate p L) < 0 := hep.trans hneg2
    nlinarith
  · unfold physicalSecondPrimeTerm
    rw [hc2, ← hedef]
    nlinarith

end Zeta23.CCM

#print axioms Zeta23.CCM.norm_sourceEntry_sub_le
#print axioms Zeta23.CCM.norm_quadraticForm_sourceMatrix_sub_le
#print axioms Zeta23.CCM.abs_sourceEnergyRe_index_sub_le
#print axioms Zeta23.CCM.sourceEnergyRe_one
#print axioms Zeta23.CCM.sourceEnergyRe_index_one_ge
#print axioms Zeta23.CCM.exists_sourceNegativeWindow
#print axioms Zeta23.CCM.physicalSecondPrimeCoefficient_prime
#print axioms Zeta23.CCM.exists_prime_physicalSecondPrimeTerm_pos_and_two_neg
