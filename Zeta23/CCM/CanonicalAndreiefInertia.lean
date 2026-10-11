import Zeta23.CCM.CanonicalSourceSpectralFlow
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section

/-!
# M71 (Steps 44, 109): Andréief interior inertia of the parity carriers

**Statement.**  For every source coordinate `0 < ω ≤ 1/2` and every `K ≥ 2`,
the elementary source form `sourceSesq ω K` restricted to the even
boundary-flat carrier on `[-K, K]` is nondegenerate with exact inertia
`(K/2, (K-1)/2, 0)`, and restricted to the odd carrier with exact inertia
`((K-1)/2, K/2, 0)` (`evenBoundaryFlat_source_exactInertia`,
`oddBoundaryFlat_source_exactInertia`).  This extends the half-aperture
theorems of `SourceParityExactInertia` to the whole interior `0 < ω < 1/2`.

**Proof route.**
1. *Andréief.*  For continuous bounded `f, g` and a finite measure `μ`,
   `det[∫ f_i g_j dμ] = (1/r!) ∫ det[f_m(x_i)] det[g_m(x_i)] dμ^r`
   (`det_integral_eq_integral_det_mul_prod`, `integral_det_mul_prod_eq`).
2. *Signed minors.*  With `f_k(t) = w(t) cos^k t`, `g_k(t) = f_k(a - t)` and
   `0 < a ≤ π`, both determinants are weighted Vandermonde determinants in
   `cos x_i` and `cos(a - x_i)`.  Since `cos` is strictly decreasing on
   `[0, π]`, every pair factor `(cos x_j - cos x_i)(cos(a-x_j) - cos(a-x_i))`
   is `≤ 0`, and `< 0` for distinct points.  Clamping to `[0, a]` makes the
   integrand sign-definite everywhere, and an open box of separated coordinates
   gives strict positivity: `(-1)^{r(r-1)/2} D_r > 0`
   (`andreiefSign_mul_det_gram_pos`).
3. *Jacobi.*  The Cramer vectors `w_k = ∑_{l ≤ k} adj(G_{k+1})_{l,k} e_l` are
   mutually orthogonal with `B(w_k, w_k) = D_k D_{k+1}`; alternating pivot signs
   give an explicit orthogonal positive/negative splitting
   (`jacobi_alternating_split`).
4. *Carrier Gram.*  The sesquilinear Fourier convolution formula
   (`sourceSesq_eq_convolution`) and the lattice character identities give
   `B(e_k, e_l) = π⁻¹ ∫_0^a w(t) cos^k t · w(a-t) cos^l(a-t) dt` on the even
   carrier (`w = (1 - cos)^2`) and minus the same with `w = sin · (1 - cos)` on
   the odd carrier, for the bases `e_k = evenCarrierMap m (cos^k)` and
   `oddCarrierMap m (cos^k)`, `k ≤ m = K - 2`.

**Scope firewall.**  This is a statement about the elementary
`sourceMatrix ω` on the parity boundary-flat carriers for `0 < ω ≤ 1/2`.  The
hypothesis `ω ≤ 1/2` (aperture `a ≤ π`) is used for the monotonicity of `cos`
and is not removable (on `(1/2, 1)` the inertia changes; see M72).  Nothing here
concerns the canonical `Pole - Arch - Prime` operator, its ground contacts, the
opposite-side sign (M76), or RH.
-/

namespace Zeta23.CCM

open MeasureTheory Matrix Finset Equiv Module
open scoped ComplexConjugate Interval

section Andreief

variable {r : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ]

/-- The evaluation matrix `A(x)_{m i} = f m (x i)`. -/
def evalMatrix (f : Fin r → ℝ → ℝ) (x : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun m i => f m (x i)

omit [IsFiniteMeasure μ] in
theorem continuous_det_evalMatrix {f : Fin r → ℝ → ℝ} (hf : ∀ m, Continuous (f m)) :
    Continuous fun x : Fin r → ℝ => (evalMatrix f x).det := by
  apply Continuous.matrix_det
  refine continuous_matrix fun m i => ?_
  exact (hf m).comp (continuous_apply i)

omit [IsFiniteMeasure μ] in
theorem abs_det_evalMatrix_le {f : Fin r → ℝ → ℝ} {C : ℝ} (hfC : ∀ m t, |f m t| ≤ C)
    (x : Fin r → ℝ) : |(evalMatrix f x).det| ≤ r.factorial * C ^ r := by
  rw [det_apply']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ σ : Perm (Fin r), |(Perm.sign σ : ℝ) * ∏ i, evalMatrix f x (σ i) i| ≤ C ^ r := by
    intro σ
    rw [abs_mul, Finset.abs_prod]
    have hs : |((Perm.sign σ : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
    rw [hs, one_mul]
    calc ∏ i, |evalMatrix f x (σ i) i| ≤ ∏ _i : Fin r, C :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hfC _ _
      _ = C ^ r := by simp
  calc ∑ σ : Perm (Fin r), |(Perm.sign σ : ℝ) * ∏ i, evalMatrix f x (σ i) i|
      ≤ ∑ _σ : Perm (Fin r), C ^ r := Finset.sum_le_sum fun σ _ => h σ
    _ = r.factorial * C ^ r := by
      simp [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- Continuous bounded functions are integrable for the finite product measure. -/
theorem integrable_pi_of_continuous_bound {F : (Fin r → ℝ) → ℝ} (hF : Continuous F)
    {B : ℝ} (hB : ∀ x, |F x| ≤ B) : Integrable F (Measure.pi fun _ : Fin r => μ) :=
  Integrable.of_bound hF.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hB x)

/-- **Andréief, first form.**  For continuous bounded `f, g`,
`det[∫ f_i g_j dμ] = ∫ det[f_m(x_i)] ∏_i g_i(x_i) dμ^r`. -/
theorem det_integral_eq_integral_det_mul_prod (f g : Fin r → ℝ → ℝ)
    (hf : ∀ m, Continuous (f m)) (hg : ∀ m, Continuous (g m)) {C : ℝ}
    (hfC : ∀ m t, |f m t| ≤ C) (hgC : ∀ m t, |g m t| ≤ C) :
    (Matrix.of fun i j => ∫ t, f i t * g j t ∂μ).det =
      ∫ x, (evalMatrix f x).det * ∏ i, g i (x i) ∂(Measure.pi fun _ : Fin r => μ) := by
  have hprod : ∀ σ : Perm (Fin r),
      ∏ i, (∫ t, f (σ i) t * g i t ∂μ) =
        ∫ x, ∏ i, (f (σ i) (x i) * g i (x i)) ∂(Measure.pi fun _ : Fin r => μ) := fun σ =>
    (integral_fintype_prod_eq_prod (fun i t => f (σ i) t * g i t)).symm
  have hint : ∀ σ : Perm (Fin r), Integrable
      (fun x : Fin r → ℝ => ((Perm.sign σ : ℤ) : ℝ) * ∏ i, (f (σ i) (x i) * g i (x i)))
      (Measure.pi fun _ : Fin r => μ) := by
    intro σ
    refine (integrable_pi_of_continuous_bound μ
      (F := fun x : Fin r → ℝ => ∏ i, (f (σ i) (x i) * g i (x i)))
      (continuous_finsetProd _ fun i _ =>
        ((hf (σ i)).comp (continuous_apply i)).mul ((hg i).comp (continuous_apply i)))
      (B := (C * C) ^ r) fun x => ?_).const_mul _
    rw [Finset.abs_prod]
    calc ∏ i, |f (σ i) (x i) * g i (x i)| ≤ ∏ _i : Fin r, C * C := by
          refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hfC _ _) (hgC _ _) (abs_nonneg _)
            ((abs_nonneg _).trans (hfC (σ i) 0))
      _ = (C * C) ^ r := by simp
  rw [det_apply']
  simp_rw [Matrix.of_apply, hprod, ← integral_const_mul]
  rw [← integral_finsetSum _ fun σ _ => hint σ]
  congr 1
  ext x
  rw [det_apply', Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]
  rfl

omit [IsFiniteMeasure μ] in
theorem det_evalMatrix_comp_perm (f : Fin r → ℝ → ℝ) (x : Fin r → ℝ) (τ : Perm (Fin r)) :
    (evalMatrix f (fun i => x (τ i))).det = (Perm.sign τ : ℝ) * (evalMatrix f x).det := by
  have h : evalMatrix f (fun i => x (τ i)) = (evalMatrix f x).submatrix id τ := by
    ext m i
    rfl
  rw [h, det_permute']

/-- **Andréief, symmetrized.**  `∫ det[f_m(x_i)] ∏ g_i(x_i) = (1/r!) ∫ det[f_m(x_i)] det[g_m(x_i)]`. -/
theorem integral_det_mul_prod_eq (f g : Fin r → ℝ → ℝ)
    (hf : ∀ m, Continuous (f m)) (hg : ∀ m, Continuous (g m)) {C : ℝ}
    (hfC : ∀ m t, |f m t| ≤ C) (hgC : ∀ m t, |g m t| ≤ C) :
    ∫ x, (evalMatrix f x).det * ∏ i, g i (x i) ∂(Measure.pi fun _ : Fin r => μ) =
      (r.factorial : ℝ)⁻¹ *
        ∫ x, (evalMatrix f x).det * (evalMatrix g x).det ∂(Measure.pi fun _ : Fin r => μ) := by
  set π : Measure (Fin r → ℝ) := Measure.pi fun _ : Fin r => μ with hπ
  have hcont : Continuous fun x : Fin r → ℝ => (evalMatrix f x).det :=
    continuous_det_evalMatrix hf
  have hgprod : ∀ τ : Perm (Fin r), Continuous fun x : Fin r → ℝ => ∏ i, g i (x (τ i)) :=
    fun τ => continuous_finsetProd _ fun i _ => (hg i).comp (continuous_apply (τ i))
  have hgbound : ∀ (τ : Perm (Fin r)) (x : Fin r → ℝ), |∏ i, g i (x (τ i))| ≤ |C| ^ r := by
    intro τ x
    rw [Finset.abs_prod]
    calc ∏ i, |g i (x (τ i))| ≤ ∏ _i : Fin r, |C| :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => (hgC _ _).trans (le_abs_self C)
      _ = |C| ^ r := by simp
  have hfbound : ∀ x, |(evalMatrix f x).det| ≤ r.factorial * |C| ^ r := fun x =>
    abs_det_evalMatrix_le (fun m t => (hfC m t).trans (le_abs_self C)) x
  -- change of variables `x ↦ x ∘ τ`
  have hcov : ∀ τ : Perm (Fin r),
      ∫ x, (evalMatrix f x).det * ∏ i, g i (x i) ∂π =
        ∫ x, (Perm.sign τ : ℝ) * ((evalMatrix f x).det * ∏ i, g i (x (τ i))) ∂π := by
    intro τ
    have hmp := measurePreserving_piCongrLeft (fun _ : Fin r => μ) τ.symm
    rw [← hmp.integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have happ : ∀ i, (MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℝ) τ.symm x) i = x (τ i) := by
      intro i
      have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin r => ℝ) τ.symm x (τ i)
      simpa using h
    dsimp only
    rw [show (MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℝ) τ.symm x) = fun i => x (τ i) from
      funext happ, det_evalMatrix_comp_perm]
    ring
  have hint : ∀ τ : Perm (Fin r), Integrable
      (fun x : Fin r → ℝ => (Perm.sign τ : ℝ) * ((evalMatrix f x).det * ∏ i, g i (x (τ i)))) π := by
    intro τ
    refine (integrable_pi_of_continuous_bound μ (hcont.mul (hgprod τ))
      (B := r.factorial * |C| ^ r * |C| ^ r) fun x => ?_).const_mul _
    rw [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hfbound x) (hgbound τ x) (abs_nonneg _)
      (mul_nonneg (by positivity) (by positivity))
  have hsum : (r.factorial : ℝ) * ∫ x, (evalMatrix f x).det * ∏ i, g i (x i) ∂π =
      ∫ x, (evalMatrix f x).det * (evalMatrix g x).det ∂π := by
    have hcard : (r.factorial : ℝ) = ∑ _τ : Perm (Fin r), (1 : ℝ) := by
      simp [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [hcard, Finset.sum_mul]
    simp_rw [one_mul]
    rw [Finset.sum_congr rfl fun τ _ => hcov τ, ← integral_finsetSum _ fun τ _ => hint τ]
    congr 1
    ext x
    have hre : ∀ τ : Perm (Fin r),
        (Perm.sign τ : ℝ) * ((evalMatrix f x).det * ∏ i, g i (x (τ i))) =
          (evalMatrix f x).det * ((Perm.sign τ : ℝ) * ∏ i, g i (x (τ i))) := fun τ => by ring
    rw [Finset.sum_congr rfl fun τ _ => hre τ, ← Finset.mul_sum,
      ← det_transpose (evalMatrix g x), det_apply' (evalMatrix g x)ᵀ]
    refine congrArg _ (Finset.sum_congr rfl fun τ _ => ?_)
    simp [evalMatrix, transpose_apply]
  rw [← hsum, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end Andreief

/-! ## Weighted Vandermonde determinants and their signs -/

section Signs

/-- Clamp to `[0, a]`. -/
def clampIcc (a t : ℝ) : ℝ := max 0 (min t a)

theorem continuous_clampIcc (a : ℝ) : Continuous (clampIcc a) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clampIcc_mem {a : ℝ} (ha : 0 ≤ a) (t : ℝ) : clampIcc a t ∈ Set.Icc 0 a :=
  ⟨le_max_left _ _, max_le ha (min_le_right _ _)⟩

theorem clampIcc_of_mem {a t : ℝ} (ht : t ∈ Set.Icc 0 a) : clampIcc a t = t := by
  unfold clampIcc
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- `det[w(x_i) v(x_i)^k] = ∏ w(x_i) · ∏_{i<j} (v(x_j) - v(x_i))`. -/
theorem det_evalMatrix_weight_pow {r : ℕ} (w v : ℝ → ℝ) (x : Fin r → ℝ) :
    (evalMatrix (fun k t => w t * v t ^ (k : ℕ)) x).det =
      (∏ i, w (x i)) * ∏ i : Fin r, ∏ j ∈ Ioi i, (v (x j) - v (x i)) := by
  have h : evalMatrix (fun k t => w t * v t ^ (k : ℕ)) x =
      (vandermonde fun i => v (x i))ᵀ * diagonal fun i => w (x i) := by
    ext k i
    simp [evalMatrix, vandermonde, mul_comm]
  rw [h, det_mul, det_transpose, det_diagonal, det_vandermonde, mul_comm]

/-- The sign of a pair factor for points of `[0, a]`, `a ≤ π`. -/
theorem cos_pair_mul_nonpos {a p q : ℝ} (ha : a ≤ Real.pi) (hp : p ∈ Set.Icc 0 a)
    (hq : q ∈ Set.Icc 0 a) :
    (Real.cos q - Real.cos p) * (Real.cos (a - q) - Real.cos (a - p)) ≤ 0 := by
  rcases lt_trichotomy p q with h | h | h
  · have h1 : Real.cos q < Real.cos p :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hp.1 (hq.2.trans ha) h
    have h2 : Real.cos (a - p) < Real.cos (a - q) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [hq.2]) (by linarith [hp.1]) (by linarith)
    nlinarith
  · subst h; simp
  · have h1 : Real.cos p < Real.cos q :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hq.1 (hp.2.trans ha) h
    have h2 : Real.cos (a - q) < Real.cos (a - p) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [hp.2]) (by linarith [hq.1]) (by linarith)
    nlinarith

theorem cos_pair_mul_neg {a p q : ℝ} (ha : a ≤ Real.pi) (hp : p ∈ Set.Icc 0 a)
    (hq : q ∈ Set.Icc 0 a) (hpq : p ≠ q) :
    (Real.cos q - Real.cos p) * (Real.cos (a - q) - Real.cos (a - p)) < 0 := by
  rcases lt_or_gt_of_ne hpq with h | h
  · have h1 : Real.cos q < Real.cos p :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hp.1 (hq.2.trans ha) h
    have h2 : Real.cos (a - p) < Real.cos (a - q) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [hq.2]) (by linarith [hp.1]) (by linarith)
    nlinarith
  · have h1 : Real.cos p < Real.cos q :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hq.1 (hp.2.trans ha) h
    have h2 : Real.cos (a - q) < Real.cos (a - p) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [hp.2]) (by linarith [hq.1]) (by linarith)
    nlinarith

/-- The Andréief sign `(-1)^{#pairs}`. -/
def andreiefSign (r : ℕ) : ℝ := (-1) ^ (∑ i : Fin r, #(Ioi i))

/-- Weighted cosine-power basis `w(c t) cos(c t)^k`, `c` the clamp to `[0,a]`. -/
def clampedLeft (a : ℝ) (w : ℝ → ℝ) (r : ℕ) : Fin r → ℝ → ℝ :=
  fun k t => w (clampIcc a t) * Real.cos (clampIcc a t) ^ (k : ℕ)

/-- Reflected basis `w(a - c t) cos(a - c t)^k`. -/
def clampedRight (a : ℝ) (w : ℝ → ℝ) (r : ℕ) : Fin r → ℝ → ℝ :=
  fun k t => w (a - clampIcc a t) * Real.cos (a - clampIcc a t) ^ (k : ℕ)

theorem det_clampedLeft_mul_det_clampedRight (a : ℝ) (w : ℝ → ℝ) {r : ℕ} (x : Fin r → ℝ) :
    andreiefSign r * ((evalMatrix (clampedLeft a w r) x).det *
        (evalMatrix (clampedRight a w r) x).det) =
      (∏ i, (w (clampIcc a (x i)) * w (a - clampIcc a (x i)))) *
        ∏ i : Fin r, ∏ j ∈ Ioi i,
          -((Real.cos (clampIcc a (x j)) - Real.cos (clampIcc a (x i))) *
            (Real.cos (a - clampIcc a (x j)) - Real.cos (a - clampIcc a (x i)))) := by
  have hL := det_evalMatrix_weight_pow (fun t => w (clampIcc a t))
    (fun t => Real.cos (clampIcc a t)) x
  have hR := det_evalMatrix_weight_pow (fun t => w (a - clampIcc a t))
    (fun t => Real.cos (a - clampIcc a t)) x
  unfold clampedLeft clampedRight
  rw [hL, hR]
  simp_rw [Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  unfold andreiefSign
  ring

theorem andreief_integrand_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ Real.pi) {w : ℝ → ℝ}
    (hw : ∀ t ∈ Set.Icc 0 a, 0 ≤ w t) {r : ℕ} (x : Fin r → ℝ) :
    0 ≤ andreiefSign r * ((evalMatrix (clampedLeft a w r) x).det *
        (evalMatrix (clampedRight a w r) x).det) := by
  rw [det_clampedLeft_mul_det_clampedRight]
  have hc : ∀ i, clampIcc a (x i) ∈ Set.Icc 0 a := fun i => clampIcc_mem ha0 _
  have hc' : ∀ i, a - clampIcc a (x i) ∈ Set.Icc 0 a := fun i =>
    ⟨by linarith [(hc i).2], by linarith [(hc i).1]⟩
  refine mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (hw _ (hc i)) (hw _ (hc' i)))
    (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => ?_)
  exact neg_nonneg.mpr (cos_pair_mul_nonpos ha (hc i) (hc j))

theorem andreief_integrand_pos {a : ℝ} (ha : a ≤ Real.pi) {w : ℝ → ℝ}
    (hw : ∀ t ∈ Set.Ioo 0 a, 0 < w t) {r : ℕ} {x : Fin r → ℝ}
    (hx : ∀ i, x i ∈ Set.Ioo 0 a) (hinj : Function.Injective x) :
    0 < andreiefSign r * ((evalMatrix (clampedLeft a w r) x).det *
        (evalMatrix (clampedRight a w r) x).det) := by
  rw [det_clampedLeft_mul_det_clampedRight]
  have hc : ∀ i, clampIcc a (x i) = x i := fun i =>
    clampIcc_of_mem (Set.Ioo_subset_Icc_self (hx i))
  simp_rw [hc]
  refine mul_pos (Finset.prod_pos fun i _ => mul_pos (hw _ (hx i)) (hw _ ?_))
    (Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_)
  · exact ⟨by linarith [(hx i).2], by linarith [(hx i).1]⟩
  · refine neg_pos.mpr (cos_pair_mul_neg ha (Set.Ioo_subset_Icc_self (hx i))
      (Set.Ioo_subset_Icc_self (hx j)) ?_)
    intro h
    have := hinj h
    rw [Finset.mem_Ioi] at hj
    exact hj.ne this

end Signs


/-! ## Signed leading minors -/

section MinorSign

open Set

theorem abs_andreiefSign (r : ℕ) : |andreiefSign r| = 1 := by
  unfold andreiefSign
  rw [abs_pow, abs_neg, abs_one, one_pow]

/-- **Andréief signed minor.**  For `0 < a ≤ π` and a continuous weight `w`,
nonnegative on `[0,a]` and positive on `(0,a)`, the `r × r` Gram matrix
`G_kl = ∫_0^a w(t) cos^k t · w(a-t) cos^l (a-t) dt` satisfies
`(-1)^{r(r-1)/2} det G > 0` (the sign is `andreiefSign r`). -/
theorem andreiefSign_mul_det_gram_pos {a : ℝ} (ha0 : 0 < a) (ha : a ≤ Real.pi) {w : ℝ → ℝ}
    (hwc : Continuous w) (hw : ∀ t ∈ Icc 0 a, 0 ≤ w t) (hw' : ∀ t ∈ Ioo 0 a, 0 < w t)
    (r : ℕ) :
    0 < andreiefSign r * (Matrix.of fun k l : Fin r =>
      ∫ t in Ioc 0 a, w t * Real.cos t ^ (k : ℕ) * (w (a - t) * Real.cos (a - t) ^ (l : ℕ))).det := by
  set μ : Measure ℝ := volume.restrict (Ioc 0 a) with hμ
  set F := clampedLeft a w r with hF
  set G := clampedRight a w r with hG
  have hentry : (Matrix.of fun k l : Fin r =>
      ∫ t in Ioc 0 a, w t * Real.cos t ^ (k : ℕ) * (w (a - t) * Real.cos (a - t) ^ (l : ℕ))) =
      Matrix.of fun k l => ∫ t, F k t * G l t ∂μ := by
    ext k l
    simp only [Matrix.of_apply]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have hc : clampIcc a t = t := clampIcc_of_mem (Ioc_subset_Icc_self ht)
    simp only [hF, hG, clampedLeft, clampedRight, hc]
  have hcl := continuous_clampIcc a
  have hFc : ∀ k, Continuous (F k) := fun k =>
    (hwc.comp hcl).mul ((Real.continuous_cos.comp hcl).pow _)
  have hGc : ∀ k, Continuous (G k) := fun k =>
    (hwc.comp (continuous_const.sub hcl)).mul
      ((Real.continuous_cos.comp (continuous_const.sub hcl)).pow _)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hwc.continuousOn (s := Icc 0 a))
  have hcos : ∀ (s : ℝ) (k : ℕ), |Real.cos s ^ k| ≤ 1 := fun s k => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one s)
  have hmem : ∀ t, clampIcc a t ∈ Icc 0 a := clampIcc_mem ha0.le
  have hmem' : ∀ t, a - clampIcc a t ∈ Icc 0 a := fun t =>
    ⟨by linarith [(hmem t).2], by linarith [(hmem t).1]⟩
  have hFb : ∀ k t, |F k t| ≤ M := fun k t => by
    simp only [hF, clampedLeft]
    rw [abs_mul]
    have h1 := hM _ (hmem t)
    rw [Real.norm_eq_abs] at h1
    calc |w (clampIcc a t)| * |Real.cos (clampIcc a t) ^ (k : ℕ)| ≤ M * 1 :=
          mul_le_mul h1 (hcos _ _) (abs_nonneg _) ((abs_nonneg _).trans h1)
      _ = M := mul_one M
  have hGb : ∀ k t, |G k t| ≤ M := fun k t => by
    simp only [hG, clampedRight]
    rw [abs_mul]
    have h1 := hM _ (hmem' t)
    rw [Real.norm_eq_abs] at h1
    calc |w (a - clampIcc a t)| * |Real.cos (a - clampIcc a t) ^ (k : ℕ)| ≤ M * 1 :=
          mul_le_mul h1 (hcos _ _) (abs_nonneg _) ((abs_nonneg _).trans h1)
      _ = M := mul_one M
  rw [hentry, det_integral_eq_integral_det_mul_prod μ F G hFc hGc hFb hGb,
    integral_det_mul_prod_eq μ F G hFc hGc hFb hGb, ← mul_assoc,
    mul_comm (andreiefSign r), mul_assoc, ← integral_const_mul]
  refine mul_pos (by positivity) ?_
  set H : (Fin r → ℝ) → ℝ := fun x =>
    andreiefSign r * ((evalMatrix F x).det * (evalMatrix G x).det) with hH
  have hHc : Continuous H :=
    continuous_const.mul ((continuous_det_evalMatrix hFc).mul (continuous_det_evalMatrix hGc))
  have hHb : ∀ x, |H x| ≤ r.factorial * M ^ r * (r.factorial * M ^ r) := fun x => by
    simp only [hH]
    rw [abs_mul, abs_andreiefSign, one_mul, abs_mul]
    exact mul_le_mul (abs_det_evalMatrix_le hFb x) (abs_det_evalMatrix_le hGb x)
      (abs_nonneg _) ((abs_nonneg _).trans (abs_det_evalMatrix_le hFb x))
  have hHint := integrable_pi_of_continuous_bound μ hHc hHb
  have hH0 : 0 ≤ H := fun x => andreief_integrand_nonneg ha0.le ha hw x
  rw [integral_pos_iff_support_of_nonneg hH0 hHint]
  -- an open box of separated coordinates
  set B : Set (Fin r → ℝ) := Set.pi univ fun i : Fin r =>
    Ioo (a * (i : ℕ) / r) (a * ((i : ℕ) + 1) / r) with hB
  have hr : ∀ i : Fin r, (0 : ℝ) < r := fun i => by
    have := i.2
    exact_mod_cast (Nat.zero_lt_of_lt this)
  have hBsupp : B ⊆ Function.support H := by
    intro x hx
    rw [Set.mem_univ_pi] at hx
    have hxi : ∀ i, x i ∈ Ioo 0 a := by
      intro i
      obtain ⟨h1, h2⟩ := hx i
      have hi : ((i : ℕ) : ℝ) + 1 ≤ r := by exact_mod_cast i.2
      have hr' := hr i
      constructor
      · refine lt_of_le_of_lt ?_ h1
        positivity
      · refine h2.trans_le ?_
        rw [div_le_iff₀ hr']
        nlinarith
    have hinj : Function.Injective x := by
      intro i j hij
      by_contra hne
      have hsep : ∀ i j : Fin r, i < j → x i < x j := by
        intro i j hlt
        have hr' := hr i
        have h1 := (hx i).2
        have h2 := (hx j).1
        have hle : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast hlt
        have : a * ((i : ℕ) + 1) / r ≤ a * (j : ℕ) / r := by
          apply div_le_div_of_nonneg_right _ hr'.le
          nlinarith
        linarith
      rcases lt_or_gt_of_ne hne with h | h
      · exact (hsep i j h).ne hij
      · exact (hsep j i h).ne hij.symm
    exact (andreief_integrand_pos ha hw' hxi hinj).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hBsupp)
  rw [hB, Measure.pi_pi]
  rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  have hr' := hr i
  rw [hμ, Measure.restrict_apply measurableSet_Ioo]
  have hsub : Ioo (a * (i : ℕ) / r) (a * ((i : ℕ) + 1) / r) ⊆ Ioc 0 a := by
    intro t ht
    have hi : ((i : ℕ) : ℝ) + 1 ≤ r := by exact_mod_cast i.2
    constructor
    · refine lt_of_le_of_lt ?_ ht.1
      positivity
    · refine (ht.2.trans_le ?_).le
      rw [div_le_iff₀ hr']
      nlinarith
  rw [Set.inter_eq_left.mpr hsub, Real.volume_Ioo]
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]
  apply div_lt_div_of_pos_right _ hr'
  nlinarith

end MinorSign


section Jacobi

variable {E : Type*} [AddCommGroup E] [Module ℂ E] (Bl : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ)

/-- Leading `r × r` block of a real `ℕ`-indexed Gram array. -/
def leadGram (g : ℕ → ℕ → ℝ) (r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => g i j

/-- Leading principal minor `D_r`. -/
def leadMinor (g : ℕ → ℕ → ℝ) (r : ℕ) : ℝ := (leadGram g r).det

/-- Cramer coefficients: the last column of the adjugate of the leading
`(k+1) × (k+1)` block. -/
def cramerCoeff (g : ℕ → ℕ → ℝ) (k : ℕ) (l : Fin (k + 1)) : ℝ :=
  adjugate (leadGram g (k + 1)) l (Fin.last k)

/-- The Cramer vector `w_k = ∑_{l ≤ k} adj(G_{k+1})_{l,k} e_l`. -/
def cramerVec (g : ℕ → ℕ → ℝ) (e : ℕ → E) (k : ℕ) : E :=
  ∑ l : Fin (k + 1), ((cramerCoeff g k l : ℝ) : ℂ) • e l

theorem sum_gram_mul_cramerCoeff (g : ℕ → ℕ → ℝ) (k : ℕ) (i : Fin (k + 1)) :
    ∑ l : Fin (k + 1), g i l * cramerCoeff g k l =
      if i = Fin.last k then leadMinor g (k + 1) else 0 := by
  have h : (leadGram g (k + 1) * adjugate (leadGram g (k + 1))) i (Fin.last k) =
      ((leadGram g (k + 1)).det • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) i (Fin.last k) := by
    rw [mul_adjugate]
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  rw [show (∑ l : Fin (k + 1), g i l * cramerCoeff g k l) =
      ∑ j, leadGram g (k + 1) i j * adjugate (leadGram g (k + 1)) j (Fin.last k) from rfl, h,
    leadMinor]
  split_ifs <;> simp

theorem cramerCoeff_last (g : ℕ → ℕ → ℝ) (k : ℕ) :
    cramerCoeff g k (Fin.last k) = leadMinor g k := by
  unfold cramerCoeff
  rw [adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  have hsub : (leadGram g (k + 1)).submatrix Fin.castSucc Fin.castSucc = leadGram g k := by
    ext i j
    simp [leadGram]
  rw [hsub, leadMinor, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem sesq_sum_smul_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → E) (y : E) :
    Bl (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, conj (c i) * Bl (v i) y := by
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

theorem sesq_sum_smul_right {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → E) (x : E) :
    Bl x (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * Bl x (v i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]

variable {Bl} {g : ℕ → ℕ → ℝ} {e : ℕ → E} {n : ℕ}

theorem sesq_e_cramerVec (hg : ∀ i j, i < n → j < n → Bl (e i) (e j) = (g i j : ℂ))
    {k : ℕ} (hk : k < n) (i : ℕ) (hi : i ≤ k) :
    Bl (e i) (cramerVec g e k) = if i = k then (leadMinor g (k + 1) : ℂ) else 0 := by
  unfold cramerVec
  rw [sesq_sum_smul_right]
  rw [Finset.sum_congr rfl fun (l : Fin (k + 1)) _ => by
    rw [hg i l (by omega) (by have := l.2; omega)] ]
  have h := sum_gram_mul_cramerCoeff g k ⟨i, by omega⟩
  have hcast : ∑ l : Fin (k + 1), ((cramerCoeff g k l : ℝ) : ℂ) * (g i l : ℂ) =
      ((∑ l : Fin (k + 1), g i l * cramerCoeff g k l : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [hcast]
  rw [h]
  have hiff : (⟨i, by omega⟩ : Fin (k + 1)) = Fin.last k ↔ i = k := by
    rw [Fin.ext_iff, Fin.val_last]
  by_cases hik : i = k
  · rw [if_pos (hiff.mpr hik), if_pos hik]
  · rw [if_neg (fun h => hik (hiff.mp h)), if_neg hik, Complex.ofReal_zero]

theorem sesq_cramerVec_e (hg : ∀ i j, i < n → j < n → Bl (e i) (e j) = (g i j : ℂ))
    (hsym : ∀ i j, i < n → j < n → g i j = g j i) {k : ℕ} (hk : k < n) (i : ℕ) (hi : i ≤ k) :
    Bl (cramerVec g e k) (e i) = if i = k then (leadMinor g (k + 1) : ℂ) else 0 := by
  unfold cramerVec
  rw [sesq_sum_smul_left]
  rw [Finset.sum_congr rfl fun (l : Fin (k + 1)) _ => by
    rw [hg l i (by have := l.2; omega) (by omega), Complex.conj_ofReal] ]
  have h := sum_gram_mul_cramerCoeff g k ⟨i, by omega⟩
  have hcast : ∑ l : Fin (k + 1), ((cramerCoeff g k l : ℝ) : ℂ) * (g l i : ℂ) =
      ((∑ l : Fin (k + 1), g i l * cramerCoeff g k l : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun l _ => by
      rw [hsym l i (by have := l.2; omega) (by omega)]; ring
  rw [hcast]
  rw [h]
  have hiff : (⟨i, by omega⟩ : Fin (k + 1)) = Fin.last k ↔ i = k := by
    rw [Fin.ext_iff, Fin.val_last]
  by_cases hik : i = k
  · rw [if_pos (hiff.mpr hik), if_pos hik]
  · rw [if_neg (fun h => hik (hiff.mp h)), if_neg hik, Complex.ofReal_zero]

theorem sesq_cramerVec_of_lt (hg : ∀ i j, i < n → j < n → Bl (e i) (e j) = (g i j : ℂ))
    {j k : ℕ} (hk : k < n) (hjk : j < k) : Bl (cramerVec g e j) (cramerVec g e k) = 0 := by
  rw [show cramerVec g e j = ∑ l : Fin (j + 1), ((cramerCoeff g j l : ℝ) : ℂ) • e l from rfl,
    sesq_sum_smul_left]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hl := l.2
  rw [sesq_e_cramerVec hg hk l (by omega), if_neg (by omega), mul_zero]

theorem sesq_cramerVec_of_gt (hg : ∀ i j, i < n → j < n → Bl (e i) (e j) = (g i j : ℂ))
    (hsym : ∀ i j, i < n → j < n → g i j = g j i) {j k : ℕ} (hj : j < n) (hjk : k < j) :
    Bl (cramerVec g e j) (cramerVec g e k) = 0 := by
  rw [show cramerVec g e k = ∑ l : Fin (k + 1), ((cramerCoeff g k l : ℝ) : ℂ) • e l from rfl,
    sesq_sum_smul_right]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hl := l.2
  rw [sesq_cramerVec_e hg hsym hj l (by omega), if_neg (by omega), mul_zero]

theorem sesq_cramerVec_self (hg : ∀ i j, i < n → j < n → Bl (e i) (e j) = (g i j : ℂ))
    {k : ℕ} (hk : k < n) :
    Bl (cramerVec g e k) (cramerVec g e k) = ((leadMinor g k * leadMinor g (k + 1) : ℝ) : ℂ) := by
  rw [show cramerVec g e k = ∑ l : Fin (k + 1), ((cramerCoeff g k l : ℝ) : ℂ) • e l from rfl]
  rw [sesq_sum_smul_left, ← show cramerVec g e k =
      ∑ l : Fin (k + 1), ((cramerCoeff g k l : ℝ) : ℂ) • e l from rfl]
  rw [Fintype.sum_eq_single (Fin.last k)]
  · rw [sesq_e_cramerVec hg hk _ (by simp), Fin.val_last, if_pos rfl, Complex.conj_ofReal,
      cramerCoeff_last]
    push_cast
    ring
  · intro l hl
    have hlt : (l : ℕ) < k := by
      have := l.2
      have : (l : ℕ) ≠ k := fun h => hl (Fin.ext (by rw [h, Fin.val_last]))
      omega
    rw [sesq_e_cramerVec hg hk l hlt.le, if_neg hlt.ne, mul_zero]

/-! ### Orthogonal families -/

theorem sesq_pos_of_orthFamily {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) (r : ι → ℝ)
    (horth : ∀ i j, i ≠ j → Bl (v i) (v j) = 0) (hdiag : ∀ i, Bl (v i) (v i) = (r i : ℂ))
    (hr : ∀ i, 0 < r i) :
    ∀ x ∈ Submodule.span ℂ (Set.range v), x ≠ 0 → 0 < (Bl x x).re := by
  intro x hx hne
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  have hval : Bl (∑ i, c i • v i) (∑ i, c i • v i) =
      ∑ i, ((Complex.normSq (c i) * r i : ℝ) : ℂ) := by
    rw [sesq_sum_smul_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sesq_sum_smul_right, Fintype.sum_eq_single i
      (fun j hj => by rw [horth i j (Ne.symm hj), mul_zero]), hdiag]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [hval, Complex.re_sum]
  simp_rw [Complex.ofReal_re]
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by simp [h])
  exact Finset.sum_pos' (fun j _ => mul_nonneg (Complex.normSq_nonneg _) (hr j).le)
    ⟨i, Finset.mem_univ _, mul_pos (Complex.normSq_pos.mpr hi) (hr i)⟩

theorem linearIndependent_of_orthFamily {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E)
    (r : ι → ℝ) (horth : ∀ i j, i ≠ j → Bl (v i) (v j) = 0)
    (hdiag : ∀ i, Bl (v i) (v i) = (r i : ℂ)) (hr : ∀ i, r i ≠ 0) :
    LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (Bl (v i)) hc
  rw [sesq_sum_smul_right, map_zero, Fintype.sum_eq_single i
    (fun j hj => by rw [horth i j (Ne.symm hj), mul_zero]), hdiag] at h
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact absurd (Complex.ofReal_eq_zero.mp h) (hr i)

theorem sesq_eq_zero_of_spans {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → E) (u : κ → E)
    (h : ∀ i j, Bl (v i) (u j) = 0) :
    ∀ x ∈ Submodule.span ℂ (Set.range v), ∀ y ∈ Submodule.span ℂ (Set.range u), Bl x y = 0 := by
  intro x hx y hy
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
  rw [sesq_sum_smul_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [sesq_sum_smul_right, Finset.sum_eq_zero fun j _ => by rw [h, mul_zero], mul_zero]

/-! ### Jacobi splitting with alternating pivots -/

/-- **Jacobi splitting, alternating pivots.**  Let `e_0, …, e_{n-1}` lie in an
`n`-dimensional subspace `V` with real symmetric Gram array `g` for the
sesquilinear form `B`.  If the pivot products `D_k D_{k+1}` of the leading
minors have sign `(-1)^k` for every `k < n`, then the even Cramer vectors span
a positive definite subspace of dimension `⌈n/2⌉`, the odd ones a negative
definite subspace of dimension `⌊n/2⌋`, the two are `B`-orthogonal, and
together they span `V`. -/
theorem jacobi_alternating_split [FiniteDimensional ℂ E]
    (hg : ∀ i j, i < n → j < n → Bl (e i) (e j) = (g i j : ℂ))
    (hsym : ∀ i j, i < n → j < n → g i j = g j i)
    (hsign : ∀ k < n, 0 < (-1) ^ k * (leadMinor g k * leadMinor g (k + 1)))
    (V : Submodule ℂ E) (hV : finrank ℂ V = n) (he : ∀ k < n, e k ∈ V) :
    ∃ P N : Submodule ℂ E, P ⊔ N = V ∧ finrank ℂ P = (n + 1) / 2 ∧ finrank ℂ N = n / 2 ∧
      (∀ p ∈ P, ∀ q ∈ N, Bl p q = 0 ∧ Bl q p = 0) ∧
      (∀ p ∈ P, p ≠ 0 → 0 < (Bl p p).re) ∧ (∀ q ∈ N, q ≠ 0 → (Bl q q).re < 0) := by
  set vP : Fin ((n + 1) / 2) → E := fun j => cramerVec g e (2 * j) with hvP
  set vN : Fin (n / 2) → E := fun j => cramerVec g e (2 * j + 1) with hvN
  set rP : Fin ((n + 1) / 2) → ℝ := fun j =>
    leadMinor g (2 * j) * leadMinor g (2 * j + 1) with hrP
  set rN : Fin (n / 2) → ℝ := fun j =>
    -(leadMinor g (2 * j + 1) * leadMinor g (2 * j + 1 + 1)) with hrN
  have hrPpos : ∀ j, 0 < rP j := by
    intro j
    have hj := j.2
    have h := hsign (2 * j) (by omega)
    rwa [pow_mul, neg_one_sq, one_pow, one_mul] at h
  have hrNpos : ∀ j, 0 < rN j := by
    intro j
    have hj := j.2
    have h := hsign (2 * j + 1) (by omega)
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul] at h
    exact h
  have hgk : ∀ j k : ℕ, j < n → k < n → j ≠ k →
      Bl (cramerVec g e j) (cramerVec g e k) = 0 := by
    intro j k hj hk hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact sesq_cramerVec_of_lt hg hk h
    · exact sesq_cramerVec_of_gt hg hsym hj h
  have horthP : ∀ i j, i ≠ j → Bl (vP i) (vP j) = 0 := fun i j hij =>
    hgk _ _ (by have := i.2; omega) (by have := j.2; omega)
      (fun h => hij (Fin.ext (by omega)))
  have horthN : ∀ i j, i ≠ j → Bl (vN i) (vN j) = 0 := fun i j hij =>
    hgk _ _ (by have := i.2; omega) (by have := j.2; omega)
      (fun h => hij (Fin.ext (by omega)))
  have hdiagP : ∀ i, Bl (vP i) (vP i) = (rP i : ℂ) := fun i =>
    sesq_cramerVec_self hg (by have := i.2; omega)
  have hdiagN' : ∀ i, (-Bl) (vN i) (vN i) = (rN i : ℂ) := fun i => by
    rw [LinearMap.neg_apply, LinearMap.neg_apply,
      sesq_cramerVec_self hg (by have := i.2; omega), hrN]
    push_cast
    ring
  have horthN' : ∀ i j, i ≠ j → (-Bl) (vN i) (vN j) = 0 := fun i j hij => by
    rw [LinearMap.neg_apply, LinearMap.neg_apply, horthN i j hij, neg_zero]
  set P := Submodule.span ℂ (Set.range vP) with hP
  set N := Submodule.span ℂ (Set.range vN) with hN
  have hpos : ∀ p ∈ P, p ≠ 0 → 0 < (Bl p p).re :=
    sesq_pos_of_orthFamily vP rP horthP hdiagP hrPpos
  have hneg : ∀ q ∈ N, q ≠ 0 → (Bl q q).re < 0 := by
    intro q hq hne
    have h := sesq_pos_of_orthFamily (Bl := -Bl) vN rN horthN' hdiagN' hrNpos q hq hne
    rw [LinearMap.neg_apply, LinearMap.neg_apply, Complex.neg_re] at h
    linarith
  have horth : ∀ p ∈ P, ∀ q ∈ N, Bl p q = 0 ∧ Bl q p = 0 := by
    intro p hp q hq
    constructor
    · exact sesq_eq_zero_of_spans vP vN
        (fun i j => hgk _ _ (by have := i.2; omega) (by have := j.2; omega) (by omega)) p hp q hq
    · exact sesq_eq_zero_of_spans vN vP
        (fun i j => hgk _ _ (by have := i.2; omega) (by have := j.2; omega) (by omega)) q hq p hp
  have hPdim : finrank ℂ P = (n + 1) / 2 := by
    rw [hP, finrank_span_eq_card (linearIndependent_of_orthFamily vP rP horthP hdiagP
      fun i => (hrPpos i).ne'), Fintype.card_fin]
  have hNdim : finrank ℂ N = n / 2 := by
    have hli := linearIndependent_of_orthFamily (Bl := -Bl) vN rN horthN' hdiagN'
      fun i => (hrNpos i).ne'
    rw [hN, finrank_span_eq_card hli, Fintype.card_fin]
  have hmemV : ∀ k < n, cramerVec g e k ∈ V := by
    intro k hk
    unfold cramerVec
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (he l (by omega))
  have hle : P ⊔ N ≤ V := by
    apply sup_le
    · rw [hP, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hmemV _ (by have := j.2; omega)
    · rw [hN, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hmemV _ (by have := j.2; omega)
  have hinf : P ⊓ N = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hne
    have h1 := hpos x hx.1 hne
    have h2 := hneg x hx.2 hne
    linarith
  have hsupdim : finrank ℂ ↥(P ⊔ N) = n := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P N
    rw [hinf, finrank_bot, add_zero, hPdim, hNdim] at h
    omega
  refine ⟨P, N, ?_, hPdim, hNdim, horth, hpos, hneg⟩
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hsupdim, hV])

end Jacobi


/-! ## Sesquilinear Fourier convolution -/

theorem sum_conj_cos_mul_eq_profiles₂ (N : ℕ) (u v : Fin (2 * N + 1) → ℂ) (a t : ℝ) :
    ∑ i, ∑ j, conj (u i) *
        (Real.cos ((centeredIndex N i : ℝ) * t +
          (centeredIndex N j : ℝ) * (a - t)) : ℂ) * v j =
      conj (sourceCosProfile N u t) * sourceCosProfile N v (a - t) -
        conj (sourceSinProfile N u t) * sourceSinProfile N v (a - t) := by
  unfold sourceCosProfile sourceSinProfile
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.cos_add]
  push_cast
  ring

/-- **Sesquilinear Fourier convolution representation of the elementary
source form.** -/
theorem sourceSesq_eq_convolution (ω : ℝ) (N : ℕ) (u v : Fin (2 * N + 1) → ℂ) :
    sourceSesq ω N u v =
      ((1 / Real.pi : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..(2 * Real.pi * ω),
          (conj (sourceCosProfile N u t) * sourceCosProfile N v (2 * Real.pi * ω - t) -
            conj (sourceSinProfile N u t) * sourceSinProfile N v (2 * Real.pi * ω - t)) := by
  set a : ℝ := 2 * Real.pi * ω with ha
  have hentry : ∀ i j : Fin (2 * N + 1),
      sourceMatrix ω N i j =
        ((1 / Real.pi : ℝ) : ℂ) * ∫ t in (0 : ℝ)..a,
          (Real.cos ((centeredIndex N i : ℝ) * t +
            (centeredIndex N j : ℝ) * (a - t)) : ℂ) := by
    intro i j
    rw [sourceMatrix_apply, sourceEntry_eq_cos_integral, ← ha, Complex.ofReal_mul,
      intervalIntegral.integral_ofReal]
  have hcont : ∀ i j : Fin (2 * N + 1), Continuous fun t : ℝ =>
      conj (u i) * (Real.cos ((centeredIndex N i : ℝ) * t +
        (centeredIndex N j : ℝ) * (a - t)) : ℂ) * v j := by
    intro i j
    fun_prop
  have hterm : ∀ i j : Fin (2 * N + 1),
      conj (u i) * sourceMatrix ω N i j * v j =
        ((1 / Real.pi : ℝ) : ℂ) * ∫ t in (0 : ℝ)..a,
          conj (u i) * (Real.cos ((centeredIndex N i : ℝ) * t +
            (centeredIndex N j : ℝ) * (a - t)) : ℂ) * v j := by
    intro i j
    rw [hentry, intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
    ring
  let g : Fin (2 * N + 1) → Fin (2 * N + 1) → ℝ → ℂ := fun i j t =>
    conj (u i) * (Real.cos ((centeredIndex N i : ℝ) * t +
      (centeredIndex N j : ℝ) * (a - t)) : ℂ) * v j
  have hsum : ∀ i, ∑ j, (∫ t in (0 : ℝ)..a, g i j t) =
      ∫ t in (0 : ℝ)..a, ∑ j, g i j t := fun i =>
    (intervalIntegral.integral_finsetSum
      (fun j _ => (hcont i j).intervalIntegrable _ _)).symm
  have hsum2 : ∑ i, (∫ t in (0 : ℝ)..a, ∑ j, g i j t) =
      ∫ t in (0 : ℝ)..a, ∑ i, ∑ j, g i j t :=
    (intervalIntegral.integral_finsetSum
      (fun i _ => (continuous_finsetSum _ (fun j _ => hcont i j)).intervalIntegrable _ _)).symm
  unfold sourceSesq
  calc ∑ i, ∑ j, conj (u i) * sourceMatrix ω N i j * v j
      = ∑ i, ∑ j, ((1 / Real.pi : ℝ) : ℂ) * ∫ t in (0 : ℝ)..a, g i j t := by
        simp only [hterm, g]
    _ = ((1 / Real.pi : ℝ) : ℂ) * ∑ i, ∑ j, ∫ t in (0 : ℝ)..a, g i j t := by
        simp only [Finset.mul_sum]
    _ = ((1 / Real.pi : ℝ) : ℂ) * ∫ t in (0 : ℝ)..a, ∑ i, ∑ j, g i j t := by
        rw [Finset.sum_congr rfl (fun i _ => hsum i), hsum2]
    _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr
        intro t _
        exact sum_conj_cos_mul_eq_profiles₂ N u v a t

/-! ## Lattice characters -/

/-- The cosine character `n ↦ cos(n t)`. -/
def cosChar (t : ℝ) : ℤ → ℂ := fun n => (Real.cos (n * t) : ℂ)

/-- The sine character `n ↦ sin(n t)`. -/
def sinChar (t : ℝ) : ℤ → ℂ := fun n => (Real.sin (n * t) : ℂ)

private theorem ofReal_add_div_two (x y : ℝ) : ((x : ℂ) + (y : ℂ)) / 2 = (((x + y) / 2 : ℝ) : ℂ) := by
  push_cast; ring

private theorem ofReal_sub_div_two (x y : ℝ) : ((x : ℂ) - (y : ℂ)) / 2 = (((x - y) / 2 : ℝ) : ℂ) := by
  push_cast; ring

theorem latticeCos_cosChar (t : ℝ) :
    latticeCos (cosChar t) = (Real.cos t : ℂ) • cosChar t := by
  funext n
  simp only [latticeCos, cosChar, Pi.smul_apply, smul_eq_mul]
  rw [ofReal_add_div_two, ← Complex.ofReal_mul]
  congr 1
  push_cast
  rw [show ((n : ℝ) - 1) * t = n * t - t by ring, show ((n : ℝ) + 1) * t = n * t + t by ring,
    Real.cos_sub, Real.cos_add]
  ring

theorem latticeSin_cosChar (t : ℝ) :
    latticeSin (cosChar t) = (Real.sin t : ℂ) • sinChar t := by
  funext n
  simp only [latticeSin, cosChar, sinChar, Pi.smul_apply, smul_eq_mul]
  rw [ofReal_sub_div_two, ← Complex.ofReal_mul]
  congr 1
  push_cast
  rw [show ((n : ℝ) - 1) * t = n * t - t by ring, show ((n : ℝ) + 1) * t = n * t + t by ring,
    Real.cos_sub, Real.cos_add]
  ring

theorem latticeCos_sinChar (t : ℝ) :
    latticeCos (sinChar t) = (Real.cos t : ℂ) • sinChar t := by
  funext n
  simp only [latticeCos, sinChar, Pi.smul_apply, smul_eq_mul]
  rw [ofReal_add_div_two, ← Complex.ofReal_mul]
  congr 1
  push_cast
  rw [show ((n : ℝ) - 1) * t = n * t - t by ring, show ((n : ℝ) + 1) * t = n * t + t by ring,
    Real.sin_sub, Real.sin_add]
  ring

theorem latticeSin_sinChar (t : ℝ) :
    latticeSin (sinChar t) = (-(Real.sin t : ℂ)) • cosChar t := by
  funext n
  simp only [latticeSin, sinChar, cosChar, Pi.smul_apply, smul_eq_mul]
  rw [ofReal_sub_div_two, ← Complex.ofReal_neg, ← Complex.ofReal_mul]
  congr 1
  push_cast
  rw [show ((n : ℝ) - 1) * t = n * t - t by ring, show ((n : ℝ) + 1) * t = n * t + t by ring,
    Real.sin_sub, Real.sin_add]
  ring

theorem latticeOneSubCos_cosChar (t : ℝ) :
    latticeOneSubCos (cosChar t) = ((1 - Real.cos t : ℝ) : ℂ) • cosChar t := by
  funext n
  have h := congrFun (latticeCos_cosChar t) n
  simp only [latticeOneSubCos, Pi.smul_apply, smul_eq_mul] at h ⊢
  rw [h]
  push_cast
  ring

theorem latticeOneSubCos_sinChar (t : ℝ) :
    latticeOneSubCos (sinChar t) = ((1 - Real.cos t : ℝ) : ℂ) • sinChar t := by
  funext n
  have h := congrFun (latticeCos_sinChar t) n
  simp only [latticeOneSubCos, Pi.smul_apply, smul_eq_mul] at h ⊢
  rw [h]
  push_cast
  ring

theorem latticePair_smul_left (N : ℕ) (c : ℂ) (p f : ℤ → ℂ) :
    latticePair N (c • p) f = c * latticePair N p f := by
  unfold latticePair
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem latticePair_mono {M N : ℕ} (h : M ≤ N) (p : ℤ → ℂ) {f : ℤ → ℂ}
    (hf : LatticeSupported M f) : latticePair N p f = latticePair M p f := by
  unfold latticePair
  exact sum_latticeBox_eq_of_vanish h _ fun n hn => by rw [hf n hn, mul_zero]

theorem sourceCosProfile_ofLattice (N : ℕ) (f : ℤ → ℂ) (t : ℝ) :
    sourceCosProfile N (ofLattice N f) t = latticePair N (cosChar t) f := by
  unfold sourceCosProfile latticePair cosChar
  rw [← sum_centeredIndex_eq_sum_latticeBox N (fun n => (Real.cos (n * t) : ℂ) * f n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofLattice_apply, mul_comm]

theorem sourceSinProfile_ofLattice (N : ℕ) (f : ℤ → ℂ) (t : ℝ) :
    sourceSinProfile N (ofLattice N f) t = latticePair N (sinChar t) f := by
  unfold sourceSinProfile latticePair sinChar
  rw [← sum_centeredIndex_eq_sum_latticeBox N (fun n => (Real.sin (n * t) : ℂ) * f n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofLattice_apply, mul_comm]

/-! ## The cosine-power basis -/

/-- Lattice coefficients of `cos^k t`. -/
def cosPowLattice : ℕ → ℤ → ℂ
  | 0 => fun n => if n = 0 then 1 else 0
  | k + 1 => latticeCos (cosPowLattice k)

theorem cosPowLattice_supported : ∀ k, LatticeSupported k (cosPowLattice k)
  | 0 => by
    intro n hn
    rw [mem_latticeBox] at hn
    simp only [cosPowLattice]
    rw [if_neg (by omega)]
  | k + 1 => (cosPowLattice_supported k).latticeCos

theorem cosPowLattice_symmetric : ∀ k, LatticeSymmetric (cosPowLattice k)
  | 0 => by
    intro n
    simp only [cosPowLattice, neg_eq_zero]
  | k + 1 => (cosPowLattice_symmetric k).latticeCos

theorem latticePair_cosChar_cosPowLattice (t : ℝ) :
    ∀ k, latticePair k (cosChar t) (cosPowLattice k) = (Real.cos t ^ k : ℝ)
  | 0 => by
    unfold latticePair
    rw [show latticeBox 0 = {0} by decide]
    simp [cosPowLattice, cosChar]
  | k + 1 => by
    rw [cosPowLattice, latticePair_latticeCos (cosPowLattice_supported k), latticeCos_cosChar,
      latticePair_smul_left, latticePair_mono (Nat.le_succ k) _ (cosPowLattice_supported k),
      latticePair_cosChar_cosPowLattice t k]
    push_cast
    ring

theorem latticePair_sinChar_cosPowLattice (t : ℝ) :
    ∀ k, latticePair k (sinChar t) (cosPowLattice k) = 0
  | 0 => by
    unfold latticePair
    rw [show latticeBox 0 = {0} by decide]
    simp [cosPowLattice, sinChar]
  | k + 1 => by
    rw [cosPowLattice, latticePair_latticeCos (cosPowLattice_supported k), latticeCos_sinChar,
      latticePair_smul_left, latticePair_mono (Nat.le_succ k) _ (cosPowLattice_supported k),
      latticePair_sinChar_cosPowLattice t k, mul_zero]


/-! ## Carrier profiles in the cosine-power basis -/

theorem evenCarrier_cosProfile {m k : ℕ} (hk : k ≤ m) (t : ℝ) :
    sourceCosProfile (m + 2) (evenCarrierMap m (cosPowLattice k)) t =
      (((1 - Real.cos t) ^ 2 * Real.cos t ^ k : ℝ) : ℂ) := by
  have hq : LatticeSupported m (cosPowLattice k) := (cosPowLattice_supported k).mono hk
  have hq1 : LatticeSupported (m + 1) (latticeOneSubCos (cosPowLattice k)) := hq.oneSubCos
  rw [evenCarrierMap, sourceCosProfile_ofLattice]
  change latticePair (m + 1 + 1) (cosChar t)
    (latticeOneSubCos (latticeOneSubCos (cosPowLattice k))) = _
  rw [latticePair_oneSubCos hq1, latticeOneSubCos_cosChar, latticePair_smul_left,
    latticePair_mono (Nat.le_succ (m + 1)) _ hq1, latticePair_oneSubCos hq,
    latticeOneSubCos_cosChar, latticePair_smul_left,
    latticePair_mono (by omega : k ≤ m + 1) _ (cosPowLattice_supported k),
    latticePair_cosChar_cosPowLattice]
  push_cast
  ring

theorem evenCarrier_sinProfile {m k : ℕ} (hk : k ≤ m) (t : ℝ) :
    sourceSinProfile (m + 2) (evenCarrierMap m (cosPowLattice k)) t = 0 := by
  have hq : LatticeSupported m (cosPowLattice k) := (cosPowLattice_supported k).mono hk
  have hq1 : LatticeSupported (m + 1) (latticeOneSubCos (cosPowLattice k)) := hq.oneSubCos
  rw [evenCarrierMap, sourceSinProfile_ofLattice]
  change latticePair (m + 1 + 1) (sinChar t)
    (latticeOneSubCos (latticeOneSubCos (cosPowLattice k))) = _
  rw [latticePair_oneSubCos hq1, latticeOneSubCos_sinChar, latticePair_smul_left,
    latticePair_mono (Nat.le_succ (m + 1)) _ hq1, latticePair_oneSubCos hq,
    latticeOneSubCos_sinChar, latticePair_smul_left,
    latticePair_mono (by omega : k ≤ m + 1) _ (cosPowLattice_supported k),
    latticePair_sinChar_cosPowLattice, mul_zero, mul_zero]

theorem oddCarrier_cosProfile {m k : ℕ} (hk : k ≤ m) (t : ℝ) :
    sourceCosProfile (m + 2) (oddCarrierMap m (cosPowLattice k)) t = 0 := by
  have hq : LatticeSupported m (cosPowLattice k) := (cosPowLattice_supported k).mono hk
  have hq1 : LatticeSupported (m + 1) (latticeOneSubCos (cosPowLattice k)) := hq.oneSubCos
  rw [oddCarrierMap, sourceCosProfile_ofLattice]
  change latticePair (m + 1 + 1) (cosChar t)
    (latticeSin (latticeOneSubCos (cosPowLattice k))) = _
  rw [latticePair_latticeSin hq1, latticeSin_cosChar, latticePair_smul_left,
    latticePair_mono (Nat.le_succ (m + 1)) _ hq1, latticePair_oneSubCos hq,
    latticeOneSubCos_sinChar, latticePair_smul_left,
    latticePair_mono (by omega : k ≤ m + 1) _ (cosPowLattice_supported k),
    latticePair_sinChar_cosPowLattice, mul_zero, mul_zero, neg_zero]

theorem oddCarrier_sinProfile {m k : ℕ} (hk : k ≤ m) (t : ℝ) :
    sourceSinProfile (m + 2) (oddCarrierMap m (cosPowLattice k)) t =
      ((Real.sin t * (1 - Real.cos t) * Real.cos t ^ k : ℝ) : ℂ) := by
  have hq : LatticeSupported m (cosPowLattice k) := (cosPowLattice_supported k).mono hk
  have hq1 : LatticeSupported (m + 1) (latticeOneSubCos (cosPowLattice k)) := hq.oneSubCos
  rw [oddCarrierMap, sourceSinProfile_ofLattice]
  change latticePair (m + 1 + 1) (sinChar t)
    (latticeSin (latticeOneSubCos (cosPowLattice k))) = _
  rw [latticePair_latticeSin hq1, latticeSin_sinChar, latticePair_smul_left,
    latticePair_mono (Nat.le_succ (m + 1)) _ hq1, latticePair_oneSubCos hq,
    latticeOneSubCos_cosChar, latticePair_smul_left,
    latticePair_mono (by omega : k ≤ m + 1) _ (cosPowLattice_supported k),
    latticePair_cosChar_cosPowLattice]
  push_cast
  ring

/-! ## Gram arrays of the carrier bases -/

/-- The bundled sesquilinear elementary source form. -/
def sourceSesqLin (ω : ℝ) (N : ℕ) :
    (Fin (2 * N + 1) → ℂ) →ₗ⋆[ℂ] (Fin (2 * N + 1) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (sourceSesq ω N) (sourceSesq_add_left ω N)
    (fun c u v => by rw [sourceSesq_smul_left, smul_eq_mul]) (sourceSesq_add_right ω N)
    (fun c u v => by rw [sourceSesq_smul_right, smul_eq_mul]; rfl)

theorem sourceSesqLin_apply (ω : ℝ) (N : ℕ) (u v : Fin (2 * N + 1) → ℂ) :
    sourceSesqLin ω N u v = sourceSesq ω N u v := rfl

/-- Even Andréief weight `(1 - cos t)^2`. -/
def evenAndreiefWeight (t : ℝ) : ℝ := (1 - Real.cos t) ^ 2

/-- Odd Andréief weight `sin t (1 - cos t)`. -/
def oddAndreiefWeight (t : ℝ) : ℝ := Real.sin t * (1 - Real.cos t)

/-- Real Andréief Gram array `∫_0^a w(t) cos^k t · w(a-t) cos^l(a-t) dt`. -/
def andreiefGram (w : ℝ → ℝ) (a : ℝ) (k l : ℕ) : ℝ :=
  ∫ t in Set.Ioc 0 a, w t * Real.cos t ^ k * (w (a - t) * Real.cos (a - t) ^ l)

theorem sourceSesq_evenCarrier_cosPow {ω : ℝ} (hω : 0 ≤ ω) {m k l : ℕ} (hk : k ≤ m)
    (hl : l ≤ m) :
    sourceSesq ω (m + 2) (evenCarrierMap m (cosPowLattice k))
        (evenCarrierMap m (cosPowLattice l)) =
      (((1 / Real.pi) * andreiefGram evenAndreiefWeight (2 * Real.pi * ω) k l : ℝ) : ℂ) := by
  have ha : 0 ≤ 2 * Real.pi * ω := by positivity
  rw [sourceSesq_eq_convolution]
  simp_rw [evenCarrier_cosProfile hk, evenCarrier_cosProfile hl, evenCarrier_sinProfile hk,
    evenCarrier_sinProfile hl, Complex.conj_ofReal, mul_zero, sub_zero, ← Complex.ofReal_mul]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_of_le ha,
    ← Complex.ofReal_mul]
  rfl

theorem sourceSesq_oddCarrier_cosPow {ω : ℝ} (hω : 0 ≤ ω) {m k l : ℕ} (hk : k ≤ m)
    (hl : l ≤ m) :
    sourceSesq ω (m + 2) (oddCarrierMap m (cosPowLattice k))
        (oddCarrierMap m (cosPowLattice l)) =
      -(((1 / Real.pi) * andreiefGram oddAndreiefWeight (2 * Real.pi * ω) k l : ℝ) : ℂ) := by
  have ha : 0 ≤ 2 * Real.pi * ω := by positivity
  rw [sourceSesq_eq_convolution]
  simp_rw [oddCarrier_cosProfile hk, oddCarrier_cosProfile hl, oddCarrier_sinProfile hk,
    oddCarrier_sinProfile hl, Complex.conj_ofReal, mul_zero, zero_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_of_le ha,
    ← Complex.ofReal_mul]
  congr 1
  rw [integral_neg, mul_neg]
  rfl

/-! ## Pivot signs -/

theorem andreiefSign_succ (k : ℕ) : andreiefSign (k + 1) = (-1) ^ k * andreiefSign k := by
  unfold andreiefSign
  rw [Fin.sum_univ_castSucc, ← pow_add]
  congr 1
  have h1 : ∀ i : Fin k, #(Ioi (Fin.castSucc i)) = #(Ioi i) + 1 := by
    intro i
    rw [Fin.card_Ioi, Fin.card_Ioi, Fin.val_castSucc]
    have := i.2
    omega
  have h2 : #(Ioi (Fin.last k)) = 0 := by
    rw [Fin.card_Ioi, Fin.val_last]
    omega
  rw [Finset.sum_congr rfl fun i _ => h1 i, h2, Finset.sum_add_distrib]
  simp
  ring

theorem andreiefSign_mul_self (r : ℕ) : andreiefSign r * andreiefSign r = 1 := by
  unfold andreiefSign
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

theorem leadMinor_smul (c : ℝ) (G : ℕ → ℕ → ℝ) (r : ℕ) :
    leadMinor (fun i j => c * G i j) r = c ^ r * leadMinor G r := by
  unfold leadMinor
  have h : leadGram (fun i j => c * G i j) r = c • leadGram G r := by
    ext i j
    simp [leadGram]
  rw [h, det_smul, Fintype.card_fin]

/-- Alternating pivots from Andréief signed minors, after a positive rescaling. -/
theorem pivot_sign_of_andreief {c : ℝ} (hc : 0 < c) (G : ℕ → ℕ → ℝ)
    (hG : ∀ r, 0 < andreiefSign r * leadMinor G r) (k : ℕ) :
    0 < (-1) ^ k * (leadMinor (fun i j => c * G i j) k *
      leadMinor (fun i j => c * G i j) (k + 1)) := by
  rw [leadMinor_smul, leadMinor_smul]
  have e1 := hG k
  have e2 := hG (k + 1)
  rw [andreiefSign_succ] at e2
  have hsq := andreiefSign_mul_self k
  have key : (-1) ^ k * (leadMinor G k * leadMinor G (k + 1)) =
      (andreiefSign k * leadMinor G k) *
        ((-1) ^ k * andreiefSign k * leadMinor G (k + 1)) := by
    linear_combination (-((-1) ^ k * leadMinor G k * leadMinor G (k + 1))) * hsq
  have hpos : 0 < (-1) ^ k * (leadMinor G k * leadMinor G (k + 1)) := by
    rw [key]
    exact mul_pos e1 e2
  have hck : 0 < c ^ k * c ^ (k + 1) := by positivity
  calc (0 : ℝ) < c ^ k * c ^ (k + 1) * ((-1) ^ k * (leadMinor G k * leadMinor G (k + 1))) :=
        mul_pos hck hpos
    _ = (-1) ^ k * (c ^ k * leadMinor G k * (c ^ (k + 1) * leadMinor G (k + 1))) := by ring

/-! ## Weights -/

theorem one_sub_cos_pos_of_mem {a t : ℝ} (ha : a ≤ Real.pi) (ht : t ∈ Set.Ioo 0 a) :
    0 < 1 - Real.cos t := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (ht.2.le.trans ha) ht.1
  rw [Real.cos_zero] at h
  linarith

theorem continuous_evenAndreiefWeight : Continuous evenAndreiefWeight :=
  (continuous_const.sub Real.continuous_cos).pow 2

theorem continuous_oddAndreiefWeight : Continuous oddAndreiefWeight :=
  Real.continuous_sin.mul (continuous_const.sub Real.continuous_cos)

theorem evenAndreiefWeight_nonneg (t : ℝ) : 0 ≤ evenAndreiefWeight t := sq_nonneg _

theorem evenAndreiefWeight_pos {a t : ℝ} (ha : a ≤ Real.pi) (ht : t ∈ Set.Ioo 0 a) :
    0 < evenAndreiefWeight t := pow_pos (one_sub_cos_pos_of_mem ha ht) 2

theorem oddAndreiefWeight_nonneg {a t : ℝ} (ha : a ≤ Real.pi) (ht : t ∈ Set.Icc 0 a) :
    0 ≤ oddAndreiefWeight t :=
  mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (ht.2.trans ha))
    (sub_nonneg.mpr (Real.cos_le_one t))

theorem oddAndreiefWeight_pos {a t : ℝ} (ha : a ≤ Real.pi) (ht : t ∈ Set.Ioo 0 a) :
    0 < oddAndreiefWeight t :=
  mul_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans_le ha)) (one_sub_cos_pos_of_mem ha ht)

/-! ## Exact interior inertia -/

/-- **M71, even carrier (Steps 44, 109).**  For every source coordinate
`0 < ω ≤ 1/2` and every `K ≥ 2`, the elementary source form on
`evenBoundaryFlatSubspace K` is nondegenerate and has exact inertia
`(K/2, (K-1)/2, 0) = (⌈d/2⌉, ⌊d/2⌋, 0)` with `d = K - 1`: an explicit
orthogonal positive/negative splitting of these dimensions exists, and these are
the maximal dimensions of positive and negative definite subspaces. -/
theorem evenBoundaryFlat_source_exactInertia {ω : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2)
    (K : ℕ) (hK : 2 ≤ K) :
    ∃ P Nn : Submodule ℂ (Fin (2 * K + 1) → ℂ),
      P ⊔ Nn = evenBoundaryFlatSubspace K ∧
      finrank ℂ P = K / 2 ∧ finrank ℂ Nn = (K - 1) / 2 ∧
      (∀ u ∈ P, ∀ v ∈ Nn, sourceSesq ω K u v = 0 ∧ sourceSesq ω K v u = 0) ∧
      (∀ u ∈ P, u ≠ 0 → 0 < (quadraticForm (sourceMatrix ω K) u).re) ∧
      (∀ u ∈ Nn, u ≠ 0 → (quadraticForm (sourceMatrix ω K) u).re < 0) ∧
      (∀ v ∈ evenBoundaryFlatSubspace K,
        (∀ w ∈ evenBoundaryFlatSubspace K, sourceSesq ω K v w = 0) → v = 0) ∧
      (∀ W : Submodule ℂ (Fin (2 * K + 1) → ℂ), W ≤ evenBoundaryFlatSubspace K →
        (∀ w ∈ W, w ≠ 0 → 0 < (quadraticForm (sourceMatrix ω K) w).re) →
          finrank ℂ W ≤ K / 2) ∧
      (∀ W : Submodule ℂ (Fin (2 * K + 1) → ℂ), W ≤ evenBoundaryFlatSubspace K →
        (∀ w ∈ W, w ≠ 0 → (quadraticForm (sourceMatrix ω K) w).re < 0) →
          finrank ℂ W ≤ (K - 1) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 2 := ⟨K - 2, by omega⟩
  have ha0 : 0 < 2 * Real.pi * ω := by positivity
  have hapi : 2 * Real.pi * ω ≤ Real.pi := by nlinarith [Real.pi_pos]
  set G := andreiefGram evenAndreiefWeight (2 * Real.pi * ω) with hG
  set e : ℕ → (Fin (2 * (m + 2) + 1) → ℂ) := fun k => evenCarrierMap m (cosPowLattice k)
    with he
  have hgram : ∀ i j, i < m + 1 → j < m + 1 →
      sourceSesqLin ω (m + 2) (e i) (e j) = (((1 / Real.pi) * G i j : ℝ) : ℂ) :=
    fun i j hi hj => sourceSesq_evenCarrier_cosPow hω0.le (by omega) (by omega)
  have hsym : ∀ i j, i < m + 1 → j < m + 1 →
      (1 / Real.pi) * G i j = (1 / Real.pi) * G j i := by
    intro i j hi hj
    have h := sourceSesq_conj_symm ω (m + 2) (e i) (e j)
    rw [show sourceSesq ω (m + 2) (e i) (e j) = _ from hgram i j hi hj,
      show sourceSesq ω (m + 2) (e j) (e i) = _ from hgram j i hj hi,
      Complex.conj_ofReal] at h
    exact Complex.ofReal_injective h
  have hsign : ∀ k < m + 1, 0 < (-1) ^ k *
      (leadMinor (fun i j => (1 / Real.pi) * G i j) k *
        leadMinor (fun i j => (1 / Real.pi) * G i j) (k + 1)) := fun k _ =>
    pivot_sign_of_andreief (one_div_pos.mpr Real.pi_pos) G
      (fun r => andreiefSign_mul_det_gram_pos ha0 hapi continuous_evenAndreiefWeight
        (fun t _ => evenAndreiefWeight_nonneg t) (fun t ht => evenAndreiefWeight_pos hapi ht) r) k
  have hV : finrank ℂ (evenBoundaryFlatSubspace (m + 2)) = m + 1 := by
    rw [finrank_evenBoundaryFlatSubspace (m + 2) (by omega)]
    omega
  have hmem : ∀ k < m + 1, e k ∈ evenBoundaryFlatSubspace (m + 2) := fun k hk =>
    evenCarrierMap_mem ((cosPowLattice_supported k).mono (by omega)) (cosPowLattice_symmetric k)
  obtain ⟨P, N, hsup, hP, hN, horth, hpos, hneg⟩ :=
    jacobi_alternating_split (Bl := sourceSesqLin ω (m + 2)) hgram hsym hsign _ hV hmem
  have hinert := exactInertia_of_orthogonal_split (sourceSesq ω (m + 2))
    (fun x y z => sourceSesq_add_left _ _ x y z) _ _ _ hsup horth hpos hneg
  refine ⟨P, N, hsup, by omega, by omega, horth, hpos, hneg,
    hinert.1, ?_, ?_⟩
  · intro W hW hWpos
    have := hinert.2.1 W hW hWpos
    rw [hP] at this
    omega
  · intro W hW hWneg
    have := hinert.2.2 W hW hWneg
    rw [hN] at this
    omega

/-- **M71, odd carrier (Steps 44, 109).**  For every `0 < ω ≤ 1/2` and every
`K ≥ 2`, the elementary source form on `oddBoundaryFlatSubspace K` is
nondegenerate with exact inertia `((K-1)/2, K/2, 0) = (⌊d/2⌋, ⌈d/2⌉, 0)`,
`d = K - 1`. -/
theorem oddBoundaryFlat_source_exactInertia {ω : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2)
    (K : ℕ) (hK : 2 ≤ K) :
    ∃ P Nn : Submodule ℂ (Fin (2 * K + 1) → ℂ),
      P ⊔ Nn = oddBoundaryFlatSubspace K ∧
      finrank ℂ P = (K - 1) / 2 ∧ finrank ℂ Nn = K / 2 ∧
      (∀ u ∈ P, ∀ v ∈ Nn, sourceSesq ω K u v = 0 ∧ sourceSesq ω K v u = 0) ∧
      (∀ u ∈ P, u ≠ 0 → 0 < (quadraticForm (sourceMatrix ω K) u).re) ∧
      (∀ u ∈ Nn, u ≠ 0 → (quadraticForm (sourceMatrix ω K) u).re < 0) ∧
      (∀ v ∈ oddBoundaryFlatSubspace K,
        (∀ w ∈ oddBoundaryFlatSubspace K, sourceSesq ω K v w = 0) → v = 0) ∧
      (∀ W : Submodule ℂ (Fin (2 * K + 1) → ℂ), W ≤ oddBoundaryFlatSubspace K →
        (∀ w ∈ W, w ≠ 0 → 0 < (quadraticForm (sourceMatrix ω K) w).re) →
          finrank ℂ W ≤ (K - 1) / 2) ∧
      (∀ W : Submodule ℂ (Fin (2 * K + 1) → ℂ), W ≤ oddBoundaryFlatSubspace K →
        (∀ w ∈ W, w ≠ 0 → (quadraticForm (sourceMatrix ω K) w).re < 0) →
          finrank ℂ W ≤ K / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 2 := ⟨K - 2, by omega⟩
  have ha0 : 0 < 2 * Real.pi * ω := by positivity
  have hapi : 2 * Real.pi * ω ≤ Real.pi := by nlinarith [Real.pi_pos]
  set G := andreiefGram oddAndreiefWeight (2 * Real.pi * ω) with hG
  set e : ℕ → (Fin (2 * (m + 2) + 1) → ℂ) := fun k => oddCarrierMap m (cosPowLattice k)
    with he
  have hgram0 : ∀ i j, i < m + 1 → j < m + 1 →
      sourceSesq ω (m + 2) (e i) (e j) = -(((1 / Real.pi) * G i j : ℝ) : ℂ) :=
    fun i j hi hj => sourceSesq_oddCarrier_cosPow hω0.le (by omega) (by omega)
  have hgram : ∀ i j, i < m + 1 → j < m + 1 →
      (-sourceSesqLin ω (m + 2)) (e i) (e j) = (((1 / Real.pi) * G i j : ℝ) : ℂ) := by
    intro i j hi hj
    rw [LinearMap.neg_apply, LinearMap.neg_apply, sourceSesqLin_apply, hgram0 i j hi hj, neg_neg]
  have hsym : ∀ i j, i < m + 1 → j < m + 1 →
      (1 / Real.pi) * G i j = (1 / Real.pi) * G j i := by
    intro i j hi hj
    have h := sourceSesq_conj_symm ω (m + 2) (e i) (e j)
    rw [hgram0 i j hi hj, hgram0 j i hj hi, map_neg, Complex.conj_ofReal, neg_inj] at h
    exact Complex.ofReal_injective h
  have hsign : ∀ k < m + 1, 0 < (-1) ^ k *
      (leadMinor (fun i j => (1 / Real.pi) * G i j) k *
        leadMinor (fun i j => (1 / Real.pi) * G i j) (k + 1)) := fun k _ =>
    pivot_sign_of_andreief (one_div_pos.mpr Real.pi_pos) G
      (fun r => andreiefSign_mul_det_gram_pos ha0 hapi continuous_oddAndreiefWeight
        (fun t ht => oddAndreiefWeight_nonneg hapi ht)
        (fun t ht => oddAndreiefWeight_pos hapi ht) r) k
  have hV : finrank ℂ (oddBoundaryFlatSubspace (m + 2)) = m + 1 := by
    rw [finrank_oddBoundaryFlatSubspace (m + 2) (by omega)]
    omega
  have hmem : ∀ k < m + 1, e k ∈ oddBoundaryFlatSubspace (m + 2) := fun k hk =>
    oddCarrierMap_mem ((cosPowLattice_supported k).mono (by omega)) (cosPowLattice_symmetric k)
  obtain ⟨Pm, Nm, hsup, hP, hN, horth, hpos, hneg⟩ :=
    jacobi_alternating_split (Bl := -sourceSesqLin ω (m + 2)) hgram hsym hsign _ hV hmem
  -- for the source form itself the roles swap
  have horth' : ∀ u ∈ Nm, ∀ v ∈ Pm, sourceSesq ω (m + 2) u v = 0 ∧ sourceSesq ω (m + 2) v u = 0 := by
    intro u hu v hv
    obtain ⟨h1, h2⟩ := horth v hv u hu
    rw [LinearMap.neg_apply, LinearMap.neg_apply, neg_eq_zero] at h1 h2
    exact ⟨h2, h1⟩
  have hpos' : ∀ u ∈ Nm, u ≠ 0 → 0 < (sourceSesq ω (m + 2) u u).re := by
    intro u hu hne
    have h := hneg u hu hne
    rw [LinearMap.neg_apply, LinearMap.neg_apply, Complex.neg_re] at h
    exact neg_lt_zero.mp h
  have hneg' : ∀ u ∈ Pm, u ≠ 0 → (sourceSesq ω (m + 2) u u).re < 0 := by
    intro u hu hne
    have h := hpos u hu hne
    rw [LinearMap.neg_apply, LinearMap.neg_apply, Complex.neg_re] at h
    exact neg_pos.mp h
  have hsup' : Nm ⊔ Pm = oddBoundaryFlatSubspace (m + 2) := by rw [sup_comm]; exact hsup
  have hinert := exactInertia_of_orthogonal_split (sourceSesq ω (m + 2))
    (fun x y z => sourceSesq_add_left _ _ x y z) _ _ _ hsup' horth' hpos' hneg'
  refine ⟨Nm, Pm, hsup', by omega, by omega, horth', hpos', hneg',
    hinert.1, ?_, ?_⟩
  · intro W hW hWpos
    have := hinert.2.1 W hW hWpos
    rw [hN] at this
    omega
  · intro W hW hWneg
    have := hinert.2.2 W hW hWneg
    rw [hP] at this
    omega

/-- Corollary: for `K ≥ 3` and `0 < ω ≤ 1/2` both parity carriers are strictly
indefinite for the elementary source form. -/
theorem parityBoundaryFlat_source_indefinite {ω : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2)
    (K : ℕ) (hK : 3 ≤ K) :
    (∃ u ∈ evenBoundaryFlatSubspace K, 0 < (quadraticForm (sourceMatrix ω K) u).re) ∧
    (∃ u ∈ evenBoundaryFlatSubspace K, (quadraticForm (sourceMatrix ω K) u).re < 0) ∧
    (∃ u ∈ oddBoundaryFlatSubspace K, 0 < (quadraticForm (sourceMatrix ω K) u).re) ∧
    (∃ u ∈ oddBoundaryFlatSubspace K, (quadraticForm (sourceMatrix ω K) u).re < 0) := by
  have hex : ∀ (W : Submodule ℂ (Fin (2 * K + 1) → ℂ)), 0 < finrank ℂ W →
      ∃ w ∈ W, w ≠ 0 := by
    intro W hW
    obtain ⟨w, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.mp hW)
    exact ⟨w, hw.1, hw.2⟩
  obtain ⟨Pe, Ne, hsupe, hPe, hNe, -, hpose, hnege, -⟩ :=
    evenBoundaryFlat_source_exactInertia hω0 hω K (by omega)
  obtain ⟨Po, No, hsupo, hPo, hNo, -, hposo, hnego, -⟩ :=
    oddBoundaryFlat_source_exactInertia hω0 hω K (by omega)
  obtain ⟨a, ha, ha0⟩ := hex Pe (by rw [hPe]; omega)
  obtain ⟨b, hb, hb0⟩ := hex Ne (by rw [hNe]; omega)
  obtain ⟨c, hc, hc0⟩ := hex Po (by rw [hPo]; omega)
  obtain ⟨d, hd, hd0⟩ := hex No (by rw [hNo]; omega)
  exact ⟨⟨a, hsupe ▸ Submodule.mem_sup_left ha, hpose a ha ha0⟩,
    ⟨b, hsupe ▸ Submodule.mem_sup_right hb, hnege b hb hb0⟩,
    ⟨c, hsupo ▸ Submodule.mem_sup_left hc, hposo c hc hc0⟩,
    ⟨d, hsupo ▸ Submodule.mem_sup_right hd, hnego d hd hd0⟩⟩


end Zeta23.CCM

#print axioms Zeta23.CCM.det_integral_eq_integral_det_mul_prod
#print axioms Zeta23.CCM.integral_det_mul_prod_eq
#print axioms Zeta23.CCM.andreiefSign_mul_det_gram_pos
#print axioms Zeta23.CCM.jacobi_alternating_split
#print axioms Zeta23.CCM.sourceSesq_eq_convolution
#print axioms Zeta23.CCM.sourceSesq_evenCarrier_cosPow
#print axioms Zeta23.CCM.sourceSesq_oddCarrier_cosPow
#print axioms Zeta23.CCM.evenBoundaryFlat_source_exactInertia
#print axioms Zeta23.CCM.oddBoundaryFlat_source_exactInertia
#print axioms Zeta23.CCM.parityBoundaryFlat_source_indefinite
