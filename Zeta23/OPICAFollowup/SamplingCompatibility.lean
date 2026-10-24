import Zeta23.OPICAFollowup.ForcedEuler

/-!
The native multi-zero sampling compatibility law (R2-S2). For actual zeros ρ_i (ζ(ρ_i) = 0,
0 < Re ρ_i < 1) with profiles h_i = `zeroProfile` ρ_i and κ_i = ρ_i(1 - ρ_i), the pairings are
linear in the first argument:

  N_ij = ∫_0^∞ h_i conj h_j,  Q_ij = ∫_0^∞ x² h_i' conj h_j',  b_i = Σ_{n ≥ 1} h_i(n) - 1/2.

- Pairing the forced Euler equation (S1.4) of h_i with conj h_j cell by cell telescopes as in
  `ForcedEuler`, now with a cellwise smooth (not C¹) second factor. The outer boundary term
  (N+1)² h_i'((N+1)-) conj h_j(N+1) is O(N^-2) and tends to 0. The continuum term has integral
  1/2 (Stage 9 self-duality) and the atoms give the absolutely convergent sum conj S_j. This gives
  Q_ij = κ_i (N_ij + conj b_j), and Hermitian symmetry gives Q_ij = conj κ_j (N_ij + b_i).
- N and Q are integral Gram matrices, hence positive semidefinite. Q - N/4 is positive
  semidefinite because its quadratic form at c is ∫ |ψ'|² for the log unitary of the finite
  combination Σ conj(c_i) h_i (positive form identity S1.5).
- The undivided identity (κ_i - conj κ_j) N_ij = conj κ_j b_i - κ_i conj b_j is kept in general.
  The divided-difference form is stated only when κ_i ≠ conj κ_j.
- `finite_countercontrol` is the paper's auxiliary finite-dimensional control
  h_i = κ_i (A - κ_i I)^(-1) g: the same identities and Gram positivity hold with nonreal κ_i, so
  they do not by themselves force real parameters. It is not a zeta system.
-/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology ComplexConjugate ComplexOrder

namespace Zeta23.OPICAFollowup

section PiecewiseParts

/-- Integration by parts on one cell [n, n+1] (n ≥ 1) against a function smooth on the cell. -/
lemma cell_parts_branch (ρ : ℂ) {n : ℕ} (hn : 1 ≤ n) {φ φ' : ℝ → ℂ}
    (hφ : ∀ x ∈ Icc (n : ℝ) (n + 1), HasDerivAt φ (φ' x) x) (hφ' : ContinuousOn φ' (Icc (n : ℝ) (n + 1))) :
    ∫ x in (n : ℝ)..(n + 1), (x : ℂ) ^ 2 * srhoCellDeriv ρ n x * φ' x =
      ((((n : ℝ) + 1 : ℝ) : ℂ) ^ 2 * srhoCellDeriv ρ n ((n : ℝ) + 1) * φ ((n : ℝ) + 1) -
        ((n : ℝ) : ℂ) ^ 2 * srhoCellDeriv ρ n n * φ n) +
      spectralKappa ρ * ∫ x in (n : ℝ)..(n + 1), srhoCell ρ n x * φ x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ n + 1 := by linarith
  have hmem : ∀ x ∈ uIcc (n : ℝ) (n + 1), x ∈ Icc (n : ℝ) (n + 1) := fun x hx => by
    rwa [uIcc_of_le hle] at hx
  have hpos : ∀ x ∈ uIcc (n : ℝ) (n + 1), 0 < x := fun x hx => lt_of_lt_of_le hn0 (hmem x hx).1
  have hu : ∀ x ∈ uIcc (n : ℝ) (n + 1), HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * srhoCellDeriv ρ n y)
      (-spectralKappa ρ * srhoCell ρ n x) x := fun x hx => hasDerivAt_sq_mul_srhoCellDeriv ρ n (hpos x hx)
  have hv : ∀ x ∈ uIcc (n : ℝ) (n + 1), HasDerivAt φ (φ' x) x := fun x hx => hφ x (hmem x hx)
  have hcellc : ContinuousOn (fun x => -spectralKappa ρ * srhoCell ρ n x) (uIcc (n : ℝ) (n + 1)) :=
    fun x hx => ((hasDerivAt_srhoCell ρ n (hpos x hx)).continuousAt.const_mul _).continuousWithinAt
  have hφ'' : ContinuousOn φ' (uIcc (n : ℝ) (n + 1)) := by rwa [uIcc_of_le hle]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hcellc.intervalIntegrable) hφ''.intervalIntegrable
  have e1 : (∫ x in (n : ℝ)..(n + 1), (x : ℂ) ^ 2 * srhoCellDeriv ρ n x * φ' x) =
      ∫ x in (n : ℝ)..(n + 1), ((x : ℂ) ^ 2 * srhoCellDeriv ρ n x) * φ' x := rfl
  rw [e1, hparts]
  have e2 : (∫ x in (n : ℝ)..(n + 1), -spectralKappa ρ * srhoCell ρ n x * φ x) =
      -spectralKappa ρ * ∫ x in (n : ℝ)..(n + 1), srhoCell ρ n x * φ x := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  rw [e2]; push_cast; ring

/-- One cell [n, n+1], n ≥ 1, of ∫ x² h' w for w the derivative of a cellwise smooth v. -/
lemma euler_cell_branch (ρ : ℂ) {n : ℕ} (hn : 1 ≤ n) {v w vb wb : ℝ → ℂ}
    (hvb : ∀ x ∈ Icc (n : ℝ) (n + 1), HasDerivAt vb (wb x) x) (hwb : ContinuousOn wb (Icc (n : ℝ) (n + 1)))
    (hv : EqOn v vb (Icc (n : ℝ) (n + 1))) (hw : EqOn w wb (Ioo (n : ℝ) (n + 1))) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * w x) volume n (n + 1) ∧
    ∫ x in (n : ℝ)..(n + 1), (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * w x =
      ((((n : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv ρ n ((n : ℝ) + 1) / normalizationBrho ρ) *
          v ((n : ℝ) + 1) -
        ((n : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv ρ n n / normalizationBrho ρ) * v n) +
      spectralKappa ρ * ∫ x in (n : ℝ)..(n + 1), (zeroProfile ρ x - 1) * v x := by
  have hle : (n : ℝ) ≤ n + 1 := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem : ∀ x ∈ uIcc (n : ℝ) (n + 1), x ∈ Icc (n : ℝ) (n + 1) := fun x hx => by
    rwa [uIcc_of_le hle] at hx
  have heqIoo : EqOn (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * w x)
      (fun x : ℝ => -(1 / normalizationBrho ρ) * ((x : ℂ) ^ 2 * srhoCellDeriv ρ n x * wb x))
      (Ioo (n : ℝ) (n + 1)) := fun x hx => by
    simp only [zeroProfileDeriv_eq_cell ρ (Ioo_subset_Ico_self hx), hw hx]; ring
  have hcont : ContinuousOn (fun x : ℝ => -(1 / normalizationBrho ρ) * ((x : ℂ) ^ 2 * srhoCellDeriv ρ n x * wb x))
      (uIcc (n : ℝ) (n + 1)) := by
    rw [uIcc_of_le hle]
    refine continuousOn_const.mul ((((Complex.continuous_ofReal.pow 2).continuousOn).mul ?_).mul hwb)
    exact (continuousOn_srhoCellDeriv ρ n).mono fun x hx => lt_of_lt_of_le hn0 hx.1
  refine ⟨intervalIntegrable_congr_Ioo hle heqIoo hcont.intervalIntegrable, ?_⟩
  have hparts := cell_parts_branch ρ hn hvb hwb
  have e2 : (∫ x in (n : ℝ)..(n + 1), (zeroProfile ρ x - 1) * v x) =
      ∫ x in (n : ℝ)..(n + 1), -(1 / normalizationBrho ρ) * (srhoCell ρ n x * vb x) :=
    intervalIntegral.integral_congr fun x hx => by
      simp only [zeroProfile_eq_cell_closed ρ (hmem x hx), hv (hmem x hx)]; ring
  rw [intervalIntegral_congr_Ioo hle heqIoo, intervalIntegral.integral_const_mul, hparts, e2,
    intervalIntegral.integral_const_mul, hv ⟨le_refl _, hle⟩, hv ⟨hle, le_refl _⟩]
  ring

/-- Telescoped ∫_0^(N+1) x² h' w for a continuous, cellwise smooth v with cell derivative w. -/
lemma euler_parts_branch {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) {v w : ℝ → ℂ}
    (hvc : Continuous v) (vb wb : ℕ → ℝ → ℂ)
    (hvb : ∀ n : ℕ, ∀ x ∈ Icc (n : ℝ) (n + 1), HasDerivAt (vb n) (wb n x) x)
    (hwb : ∀ n : ℕ, ContinuousOn (wb n) (Icc (n : ℝ) (n + 1)))
    (hv : ∀ n : ℕ, EqOn v (vb n) (Icc (n : ℝ) (n + 1)))
    (hw : ∀ n : ℕ, EqOn w (wb n) (Ioo (n : ℝ) (n + 1))) (N : ℕ) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * w x) volume 0 ((N : ℝ) + 1) ∧
    ∫ x in (0 : ℝ)..((N : ℝ) + 1), (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * w x =
      spectralKappa ρ * ((∫ x in (0 : ℝ)..((N : ℝ) + 1), (zeroProfile ρ x - 1) * v x) +
        ∑ m ∈ Finset.range N, v (m + 1)) +
      (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv ρ N ((N : ℝ) + 1) / normalizationBrho ρ) *
        v ((N : ℝ) + 1) := by
  induction N with
  | zero =>
    have hz : EqOn (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * w x) (fun _ => (0 : ℂ))
        (Ioo (0 : ℝ) 1) := fun x hx => by
      have hx' : x ∈ Ico ((0 : ℕ) : ℝ) ((0 : ℕ) + 1) := by simpa using Ioo_subset_Ico_self hx
      simp only [zeroProfileDeriv_eq_cell ρ hx', srhoCellDeriv_zero, zero_div, neg_zero, mul_zero,
        zero_mul]
    have hone : (∫ x in (0 : ℝ)..1, (zeroProfile ρ x - 1) * v x) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun x hx => ?_]
      · simp
      · rw [uIcc_of_le zero_le_one] at hx
        simp only [zeroProfile_eq_one ρ (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩), sub_self, zero_mul]
    simp only [CharP.cast_eq_zero, zero_add, Finset.range_zero, Finset.sum_empty, add_zero,
      srhoCellDeriv_zero, zero_div, neg_zero, mul_zero, zero_mul]
    refine ⟨intervalIntegrable_congr_Ioo zero_le_one hz intervalIntegrable_const, ?_⟩
    rw [intervalIntegral_congr_Ioo zero_le_one hz, hone]; simp
  | succ N ih =>
    obtain ⟨hI, hE⟩ := ih
    have hc : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    have hvb' := hvb (N + 1); have hwb' := hwb (N + 1); have hv' := hv (N + 1); have hw' := hw (N + 1)
    rw [hc] at hvb' hwb' hv' hw'
    obtain ⟨hI1, hE1⟩ := euler_cell_branch ρ (n := N + 1) (by omega)
      (by rw [hc]; exact hvb') (by rw [hc]; exact hwb') (by rw [hc]; exact hv') (by rw [hc]; exact hw')
    rw [hc] at hI1 hE1
    have hc2 : ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 1 + 1 := by push_cast; ring
    rw [hc2]
    have hhv : ∀ a b : ℝ, IntervalIntegrable (fun x => (zeroProfile ρ x - 1) * v x) volume a b :=
      fun a b => (((continuous_zeroProfile ρ).sub continuous_const).mul hvc).intervalIntegrable a b
    refine ⟨hI.trans hI1, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hI hI1, hE, hE1,
      ← intervalIntegral.integral_add_adjacent_intervals (hhv 0 ((N : ℝ) + 1)) (hhv ((N : ℝ) + 1) ((N : ℝ) + 1 + 1)),
      Finset.sum_range_succ]
    have hj := zeroProfile_deriv_jump h0 h1 hh N
    have hNc : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    have hj' : ((N + 1 : ℕ) : ℂ) ^ 2 * (-(srhoCellDeriv ρ (N + 1) (N + 1 : ℕ) / normalizationBrho ρ) -
        -(srhoCellDeriv ρ N (N + 1 : ℕ) / normalizationBrho ρ)) = -spectralKappa ρ := by
      rw [hj]; field_simp
    have hcast : (((N : ℝ) + 1 : ℝ) : ℂ) = ((N + 1 : ℕ) : ℂ) := by push_cast; ring
    have hcastR : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, hcastR] at *
    simp only [Nat.cast_add, Nat.cast_one] at hj'
    push_cast at *
    linear_combination (-(v ((N : ℝ) + 1))) * hj'

end PiecewiseParts

section Gram

/-- N(ρ, σ) = ∫_0^∞ h_ρ conj h_σ, linear in the first argument. -/
def profileGram (ρ σ : ℂ) : ℂ := ∫ x in Ioi (0 : ℝ), zeroProfile ρ x * conj (zeroProfile σ x)

/-- Q(ρ, σ) = ∫_0^∞ x² h_ρ' conj h_σ', linear in the first argument. -/
def profileFormGram (ρ σ : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * deriv (zeroProfile ρ) x * conj (deriv (zeroProfile σ) x)

/-- The sample S_ρ = Σ_{n ≥ 1} h_ρ(n). -/
def profileSample (ρ : ℂ) : ℂ := ∑' n : ℕ, zeroProfile ρ (n + 1)

/-- The sample defect S_ρ - 1/2 (the paper's b_i in S2). -/
def profileSampleDefect (ρ : ℂ) : ℂ := profileSample ρ - 1 / 2

lemma deriv_zeroProfile_ae (ρ : ℂ) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), deriv (zeroProfile ρ) x = zeroProfileDeriv ρ x := by
  have hnull : (volume : Measure ℝ) (Set.range (fun n : ℕ => (n : ℝ))) = 0 :=
    (Set.countable_range _).measure_zero _
  refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hx0
  exact deriv_zeroProfile_eq hx0 hx

lemma summable_zeroProfile_nat {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    Summable (fun n : ℕ => zeroProfile ρ (n + 1)) := by
  obtain ⟨K, hK0, hK⟩ := zeroProfile_norm_le hz h0 h1
  have hs : Summable (fun n : ℕ => K * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left K
  refine Summable.of_norm_bounded hs fun n => (hK _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hK0
  rw [one_div]
  refine inv_anti₀ (by positivity) ?_
  push_cast; nlinarith

lemma memLp_two_star {f : ℝ → ℂ} {μ : Measure ℝ} (hf : MemLp f 2 μ) :
    MemLp (fun x => conj (f x)) 2 μ := hf.star

lemma integrable_mul_conj {f g : ℝ → ℂ} {μ : Measure ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => f x * conj (g x)) μ := by
  have : ENNReal.HolderTriple 2 2 1 := ⟨by norm_num [ENNReal.inv_two_add_inv_two]⟩
  exact hf.integrable_mul hg.star

lemma integrableOn_gramN {ρ σ : ℂ} (hzρ : riemannZeta ρ = 0) (h0ρ : 0 < ρ.re) (h1ρ : ρ.re < 1)
    (hzσ : riemannZeta σ = 0) (h0σ : 0 < σ.re) (h1σ : σ.re < 1) :
    IntegrableOn (fun x => zeroProfile ρ x * conj (zeroProfile σ x)) (Ioi 0) :=
  integrable_mul_conj ((memLp_two_zeroProfile hzρ h0ρ h1ρ).restrict _)
    ((memLp_two_zeroProfile hzσ h0σ h1σ).restrict _)

lemma integrableOn_gramQ {ρ σ : ℂ} (hzρ : riemannZeta ρ = 0) (h0ρ : 0 < ρ.re) (h1ρ : ρ.re < 1)
    (hzσ : riemannZeta σ = 0) (h0σ : 0 < σ.re) (h1σ : σ.re < 1) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ 2 * deriv (zeroProfile ρ) x * conj (deriv (zeroProfile σ) x))
      (Ioi 0) := by
  refine (integrable_mul_conj (memLp_two_mul_deriv_zeroProfile hzρ h0ρ h1ρ)
    (memLp_two_mul_deriv_zeroProfile hzσ h0σ h1σ)).congr (Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_ofReal]; ring

/-- (N+1)² h'((N+1)-) is bounded. -/
lemma left_deriv_sq_bound {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ C : ℝ, ∀ N : ℕ, ‖(((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 *
      -(srhoCellDeriv ρ N ((N : ℝ) + 1) / normalizationBrho ρ)‖ ≤ C := by
  have hh := zero_ne_half hz
  obtain ⟨C, hC0, hC⟩ := zeroProfileDeriv_bound hz h0 h1
  refine ⟨C + ‖spectralKappa ρ‖, fun N => ?_⟩
  have hx1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hx0 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hj := zeroProfile_deriv_jump h0 h1 hh N
  have hcR : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [hcR] at hj
  have hD : zeroProfileDeriv ρ ((N : ℝ) + 1) =
      -(srhoCellDeriv ρ (N + 1) ((N : ℝ) + 1) / normalizationBrho ρ) :=
    zeroProfileDeriv_eq_cell ρ (n := N + 1) ⟨by rw [hcR], by rw [hcR]; linarith⟩
  have hNc : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have hcC : (((N : ℝ) + 1 : ℝ) : ℂ) = ((N + 1 : ℕ) : ℂ) := by push_cast; ring
  have hval : (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv ρ N ((N : ℝ) + 1) / normalizationBrho ρ) =
      (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * zeroProfileDeriv ρ ((N : ℝ) + 1) + spectralKappa ρ := by
    rw [hD, hcC]
    have : -(srhoCellDeriv ρ N ((N : ℝ) + 1) / normalizationBrho ρ) =
        -(srhoCellDeriv ρ (N + 1) ((N : ℝ) + 1) / normalizationBrho ρ) +
          spectralKappa ρ / ((N + 1 : ℕ) : ℂ) ^ 2 := by linear_combination -hj
    rw [this]; field_simp
  rw [hval]
  suffices hs : ‖(((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * zeroProfileDeriv ρ ((N : ℝ) + 1)‖ ≤ C by
    linarith [norm_add_le ((((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * zeroProfileDeriv ρ ((N : ℝ) + 1)) (spectralKappa ρ)]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have hmin : min 1 (((N : ℝ) + 1) ^ (-2 : ℝ)) = ((N : ℝ) + 1) ^ (-2 : ℝ) :=
    min_eq_right (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num))
  calc ((N : ℝ) + 1) ^ 2 * ‖zeroProfileDeriv ρ ((N : ℝ) + 1)‖
      ≤ ((N : ℝ) + 1) ^ 2 * (C * ((N : ℝ) + 1) ^ (-2 : ℝ)) := by
        rw [← hmin]; exact mul_le_mul_of_nonneg_left (hC _ hx0) (by positivity)
    _ = C := by
        rw [Real.rpow_neg hx0.le, Real.rpow_two]; field_simp

lemma tendsto_zeroProfile_nat {σ : ℂ} (hz : riemannZeta σ = 0) (h0 : 0 < σ.re) (h1 : σ.re < 1) :
    Tendsto (fun N : ℕ => zeroProfile σ ((N : ℝ) + 1)) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := zeroProfile_norm_le hz h0 h1
  have hlim : Tendsto (fun N : ℕ => K * (1 + ((N : ℝ) + 1) ^ 2)⁻¹) atTop (𝓝 (K * 0)) := by
    refine (tendsto_inv_atTop_zero.comp ?_).const_mul K
    refine tendsto_atTop_add_const_left _ _ ?_
    exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  rw [mul_zero] at hlim
  exact squeeze_zero_norm (fun N => hK _) hlim

/-- The pairing of (S1.4) for h_ρ with conj h_σ on [0, N+1], with its explicit boundary term. -/
lemma gram_finite {ρ σ : ℂ} (h0ρ : 0 < ρ.re) (h1ρ : ρ.re < 1) (hhρ : ρ ≠ 1 / 2) (N : ℕ) :
    ∫ x in (0 : ℝ)..((N : ℝ) + 1), (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * conj (zeroProfileDeriv σ x) =
      spectralKappa ρ * ((∫ x in (0 : ℝ)..((N : ℝ) + 1), (zeroProfile ρ x - 1) * conj (zeroProfile σ x)) +
        ∑ m ∈ Finset.range N, conj (zeroProfile σ (m + 1))) +
      (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv ρ N ((N : ℝ) + 1) / normalizationBrho ρ) *
        conj (zeroProfile σ ((N : ℝ) + 1)) := by
  refine (euler_parts_branch h0ρ h1ρ hhρ (v := fun x => conj (zeroProfile σ x))
    (w := fun x => conj (zeroProfileDeriv σ x))
    (Complex.continuous_conj.comp (continuous_zeroProfile σ))
    (fun n x => conj (1 - srhoCell σ n x / normalizationBrho σ))
    (fun n x => conj (-(srhoCellDeriv σ n x / normalizationBrho σ))) ?_ ?_ ?_ ?_ N).2
  · intro n x hx
    have := (hasDerivAt_zeroProfile_branch σ n hx.1).star
    simpa using this
  · intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [srhoCellDeriv_zero, zero_div, neg_zero, map_zero]; exact continuousOn_const
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      exact Complex.continuous_conj.comp_continuousOn
        (((continuousOn_srhoCellDeriv σ n).mono fun x hx => lt_of_lt_of_le hn0 hx.1).div_const _).neg
  · intro n x hx
    simp only [zeroProfile_eq_cell_closed σ hx]
  · intro n x hx
    simp only [zeroProfileDeriv_eq_cell σ (Ioo_subset_Ico_self hx)]

lemma gram_boundary_tendsto {ρ σ : ℂ} (hzρ : riemannZeta ρ = 0) (h0ρ : 0 < ρ.re) (h1ρ : ρ.re < 1)
    (hzσ : riemannZeta σ = 0) (h0σ : 0 < σ.re) (h1σ : σ.re < 1) :
    Tendsto (fun N : ℕ => (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 *
      -(srhoCellDeriv ρ N ((N : ℝ) + 1) / normalizationBrho ρ) * conj (zeroProfile σ ((N : ℝ) + 1)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := left_deriv_sq_bound hzρ h0ρ h1ρ
  have h := (tendsto_zeroProfile_nat hzσ h0σ h1σ).norm
  rw [norm_zero] at h
  refine squeeze_zero_norm (fun N => ?_) (by simpa using h.const_mul C)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right (hC N) (norm_nonneg _)

/-- The Gram identity Q(ρ, σ) = κ_ρ (N(ρ, σ) + conj b_σ) for actual zeros. -/
theorem gram_identity {ρ σ : ℂ} (hzρ : riemannZeta ρ = 0) (h0ρ : 0 < ρ.re) (h1ρ : ρ.re < 1)
    (hzσ : riemannZeta σ = 0) (h0σ : 0 < σ.re) (h1σ : σ.re < 1) :
    profileFormGram ρ σ = spectralKappa ρ * (profileGram ρ σ + conj (profileSampleDefect σ)) := by
  have hhρ := zero_ne_half hzρ
  have hQI := integrableOn_gramQ hzρ h0ρ h1ρ hzσ h0σ h1σ
  have hae : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      (x : ℂ) ^ 2 * deriv (zeroProfile ρ) x * conj (deriv (zeroProfile σ) x) =
        (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * conj (zeroProfileDeriv σ x) := by
    filter_upwards [deriv_zeroProfile_ae ρ, deriv_zeroProfile_ae σ] with x h1 h2
    rw [h1, h2]
  have hQI' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * conj (zeroProfileDeriv σ x))
      (Ioi 0) := hQI.congr_fun_ae hae
  have hQ : profileFormGram ρ σ =
      ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * conj (zeroProfileDeriv σ x) :=
    integral_congr_ae hae
  have hb : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hL := intervalIntegral_tendsto_integral_Ioi 0 hQI' hb
  have hNI := integrableOn_gramN hzρ h0ρ h1ρ hzσ h0σ h1σ
  have hcI : IntegrableOn (fun x => conj (zeroProfile σ x)) (Ioi 0) :=
    (memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr
      (integrable_zeroProfile hzσ h0σ h1σ)).star).integrableOn
  have hAI : IntegrableOn (fun x => (zeroProfile ρ x - 1) * conj (zeroProfile σ x)) (Ioi 0) :=
    (hNI.sub hcI).congr_fun (fun x _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  have hA := intervalIntegral_tendsto_integral_Ioi 0 hAI hb
  have hS : HasSum (fun n : ℕ => conj (zeroProfile σ (n + 1))) (conj (profileSample σ)) :=
    Complex.hasSum_conj'.mpr (summable_zeroProfile_nat hzσ h0σ h1σ).hasSum
  have hB := gram_boundary_tendsto hzρ h0ρ h1ρ hzσ h0σ h1σ
  have hR := ((hA.add hS.tendsto_sum_nat).const_mul (spectralKappa ρ)).add hB
  rw [add_zero] at hR
  have hlimit := tendsto_nhds_unique (hL.congr fun N => gram_finite h0ρ h1ρ hhρ N) hR
  have hsplit : (∫ x in Ioi (0 : ℝ), (zeroProfile ρ x - 1) * conj (zeroProfile σ x)) =
      profileGram ρ σ - 1 / 2 := by
    have hhalf : (∫ x in Ioi (0 : ℝ), conj (zeroProfile σ x)) = 1 / 2 := by
      rw [integral_conj, integral_Ioi_zeroProfile hzσ h0σ h1σ, map_div₀, map_one]
      exact congrArg _ (Complex.conj_ofNat 2)
    rw [profileGram, ← hhalf, ← integral_sub hNI hcI]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [hQ, hlimit, hsplit, profileSampleDefect]
  simp only [map_sub, map_div₀, map_one, map_ofNat]
  ring

end Gram

section Positivity

variable {ι : Type*} [Fintype ι]

/-- The quadratic form of an integral Gram matrix (linear in the first argument). -/
lemma gram_quadratic {μ : Measure ℝ} (f : ι → ℝ → ℂ)
    (hf : ∀ i j, Integrable (fun a => f i a * conj (f j a)) μ) (c : ι → ℂ) :
    ∑ i, conj (c i) * ∑ j, (∫ a, f i a * conj (f j a) ∂μ) * c j =
      ((∫ a, ‖∑ i, conj (c i) * f i a‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hpt : ∀ a, (((‖∑ i, conj (c i) * f i a‖ ^ 2 : ℝ)) : ℂ) =
      ∑ i, ∑ j, conj (c i) * (f i a * conj (f j a)) * c j := by
    intro a
    push_cast
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, Complex.conj_conj]; ring
  rw [← integral_complex_ofReal]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((hf i j).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((hf i j).const_mul _).mul_const _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_const_mul]; ring

lemma posSemidef_gram {μ : Measure ℝ} (f : ι → ℝ → ℂ)
    (hf : ∀ i j, Integrable (fun a => f i a * conj (f j a)) μ) :
    (Matrix.of fun i j => ∫ a, f i a * conj (f j a) ∂μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_def, ← integral_conj, map_mul,
      Complex.conj_conj]
    exact integral_congr_ae (Eventually.of_forall fun a => mul_comm _ _)
  · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_def]
    rw [gram_quadratic f hf c]
    exact Complex.zero_le_real.mpr (integral_nonneg fun a => sq_nonneg _)

end Positivity

section Roots

/-- Finite linear combinations stay in the log form domain. -/
lemma logFormDomain_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) {h h' : ι → ℝ → ℂ}
    (hD : ∀ i, LogFormDomain (h i) (h' i)) :
    LogFormDomain (fun x => ∑ i, c i * h i x) (fun x => ∑ i, c i * h' i x) := by
  have hII : ∀ a b : ℝ, 0 < a → 0 < b → ∀ i, IntervalIntegrable (fun x => c i * h' i x) volume a b :=
    fun a b ha hb i => ((hD i).intervalIntegrable a b ha hb).const_mul (c i)
  refine ⟨fun a b ha hb => ?_, fun a b ha hb => ?_, ?_, ?_, ?_⟩
  · rw [intervalIntegral.integral_finsetSum fun i _ => hII a b ha hb i, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, ← (hD i).integral_eq a b ha hb]; ring
  · exact intervalIntegrable_iff.mpr (integrable_finsetSum _ fun i _ =>
      intervalIntegrable_iff.mp (hII a b ha hb i))
  · exact Finset.measurable_sum _ fun i _ => measurable_const.mul (hD i).measurable_deriv
  · exact memLp_finsetSum _ fun i _ => (hD i).memLp.const_mul (c i)
  · have := memLp_finsetSum (μ := volume.restrict (Ioi 0)) (p := 2) Finset.univ
      fun i _ => (hD i).memLp_mul_deriv.const_mul (c i)
    convert this using 1; ext x; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

lemma profileGram_conj (ρ σ : ℂ) : conj (profileGram σ ρ) = profileGram ρ σ := by
  rw [profileGram, profileGram, ← integral_conj]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only [map_mul, Complex.conj_conj]; ring)

lemma profileFormGram_conj (ρ σ : ℂ) : conj (profileFormGram σ ρ) = profileFormGram ρ σ := by
  rw [profileFormGram, profileFormGram, ← integral_conj]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    simp only [map_mul, map_pow, Complex.conj_conj, Complex.conj_ofReal]; ring)

lemma profileGram_self (ρ : ℂ) :
    profileGram ρ ρ = ((∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 : ℝ) : ℂ) := by
  rw [profileGram, ← integral_complex_ofReal]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    simp only; push_cast; rw [Complex.mul_conj'])

lemma integral_norm_sq_pos {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    0 < ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 := by
  have hI : IntegrableOn (fun x => ‖zeroProfile ρ x‖ ^ 2) (Ioi 0) :=
    ((memLp_two_zeroProfile hz h0 h1).restrict (Ioi 0)).integrable_norm_pow (p := 2) two_ne_zero
  have h1' : (∫ x in Ioc (0 : ℝ) 1, ‖zeroProfile ρ x‖ ^ 2) = 1 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (1 : ℝ)) fun x hx => by
      simp only [zeroProfile_eq_one ρ (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩), norm_one, one_pow]]
    simp
  have hle := setIntegral_mono_set hI (Eventually.of_forall fun x => sq_nonneg ‖zeroProfile ρ x‖)
    (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0).eventuallyLE
  linarith

/-- R2-S2 (S2.1): for any family of actual zeros, all sample sums and integrals converge, the
finite-cell pairing of (S1.4) with conj h_j has the explicit boundary term, which tends to 0, and
Q_ij = κ_i (N_ij + conj b_j) = conj κ_j (N_ij + b_i), with the pairings linear in the first
argument: N_ij = ∫_0^∞ h_i conj h_j, Q_ij = ∫_0^∞ x² h_i' conj h_j', b_i = Σ_{n ≥ 1} h_i(n) - 1/2. -/
theorem native_sampling_gram_identity {ι : Type*} (ρ : ι → ℂ) (hz : ∀ i, riemannZeta (ρ i) = 0)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) :
    (∀ i, Summable (fun n : ℕ => zeroProfile (ρ i) (n + 1))) ∧
    (∀ i j, IntegrableOn (fun x => zeroProfile (ρ i) x * conj (zeroProfile (ρ j) x)) (Ioi 0)) ∧
    (∀ i j, IntegrableOn (fun x : ℝ => (x : ℂ) ^ 2 * deriv (zeroProfile (ρ i)) x *
      conj (deriv (zeroProfile (ρ j)) x)) (Ioi 0)) ∧
    (∀ i, ∫ x in Ioi (0 : ℝ), zeroProfile (ρ i) x = 1 / 2) ∧
    (∀ i j (N : ℕ), ∫ x in (0 : ℝ)..((N : ℝ) + 1),
      (x : ℂ) ^ 2 * zeroProfileDeriv (ρ i) x * conj (zeroProfileDeriv (ρ j) x) =
        spectralKappa (ρ i) * ((∫ x in (0 : ℝ)..((N : ℝ) + 1),
          (zeroProfile (ρ i) x - 1) * conj (zeroProfile (ρ j) x)) +
            ∑ m ∈ Finset.range N, conj (zeroProfile (ρ j) (m + 1))) +
        (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv (ρ i) N ((N : ℝ) + 1) / normalizationBrho (ρ i)) *
          conj (zeroProfile (ρ j) ((N : ℝ) + 1))) ∧
    (∀ i j, Tendsto (fun N : ℕ => (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 *
      -(srhoCellDeriv (ρ i) N ((N : ℝ) + 1) / normalizationBrho (ρ i)) *
        conj (zeroProfile (ρ j) ((N : ℝ) + 1))) atTop (𝓝 0)) ∧
    (∀ i j, profileFormGram (ρ i) (ρ j) =
      spectralKappa (ρ i) * (profileGram (ρ i) (ρ j) + conj (profileSampleDefect (ρ j)))) ∧
    (∀ i j, profileFormGram (ρ i) (ρ j) =
      conj (spectralKappa (ρ j)) * (profileGram (ρ i) (ρ j) + profileSampleDefect (ρ i))) := by
  refine ⟨fun i => summable_zeroProfile_nat (hz i) (h0 i) (h1 i),
    fun i j => integrableOn_gramN (hz i) (h0 i) (h1 i) (hz j) (h0 j) (h1 j),
    fun i j => integrableOn_gramQ (hz i) (h0 i) (h1 i) (hz j) (h0 j) (h1 j),
    fun i => integral_Ioi_zeroProfile (hz i) (h0 i) (h1 i),
    fun i j N => gram_finite (h0 i) (h1 i) (zero_ne_half (hz i)) N,
    fun i j => gram_boundary_tendsto (hz i) (h0 i) (h1 i) (hz j) (h0 j) (h1 j),
    fun i j => gram_identity (hz i) (h0 i) (h1 i) (hz j) (h0 j) (h1 j), fun i j => ?_⟩
  rw [← profileFormGram_conj, gram_identity (hz j) (h0 j) (h1 j) (hz i) (h0 i) (h1 i), map_mul, map_add,
    Complex.conj_conj, profileGram_conj]

/-- R2-S2: for any finite family of actual zeros, N, Q and Q - N/4 are positive semidefinite
Hermitian matrices; the undivided identity (κ_i - conj κ_j) N_ij = conj κ_j b_i - κ_i conj b_j holds
always (in particular at conjugate coincidence); the divided-difference identity
N_ij/(κ_i conj κ_j) = (M_i - conj M_j)/(κ_i - conj κ_j), M = b/κ, holds when the denominator is
nonzero; and Im M_i / Im κ_i = N_ii/|κ_i|² > 0 when Im κ_i ≠ 0. -/
theorem native_sampling_form_positive {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (hz : ∀ i, riemannZeta (ρ i) = 0) (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) :
    (Matrix.of fun i j => profileGram (ρ i) (ρ j)).PosSemidef ∧
    (Matrix.of fun i j => profileFormGram (ρ i) (ρ j)).PosSemidef ∧
    (Matrix.of fun i j => profileFormGram (ρ i) (ρ j) - profileGram (ρ i) (ρ j) / 4).PosSemidef ∧
    (∀ i j, (spectralKappa (ρ i) - conj (spectralKappa (ρ j))) * profileGram (ρ i) (ρ j) =
      conj (spectralKappa (ρ j)) * profileSampleDefect (ρ i) -
        spectralKappa (ρ i) * conj (profileSampleDefect (ρ j))) ∧
    (∀ i j, spectralKappa (ρ i) - conj (spectralKappa (ρ j)) ≠ 0 →
      profileGram (ρ i) (ρ j) / (spectralKappa (ρ i) * conj (spectralKappa (ρ j))) =
        (profileSampleDefect (ρ i) / spectralKappa (ρ i) -
          conj (profileSampleDefect (ρ j) / spectralKappa (ρ j))) /
            (spectralKappa (ρ i) - conj (spectralKappa (ρ j)))) ∧
    (∀ i, (spectralKappa (ρ i)).im ≠ 0 →
      (profileSampleDefect (ρ i) / spectralKappa (ρ i)).im / (spectralKappa (ρ i)).im =
        (∫ x in Ioi (0 : ℝ), ‖zeroProfile (ρ i) x‖ ^ 2) / ‖spectralKappa (ρ i)‖ ^ 2 ∧
      0 < ∫ x in Ioi (0 : ℝ), ‖zeroProfile (ρ i) x‖ ^ 2) := by
  obtain ⟨-, -, -, -, -, -, hG1, hG2⟩ := native_sampling_gram_identity ρ hz h0 h1
  have hk : ∀ i, spectralKappa (ρ i) ≠ 0 := fun i => by
    obtain ⟨hρ0, hρ1⟩ := strip_ne (h0 i) (h1 i)
    exact mul_ne_zero hρ0 (sub_ne_zero.mpr (Ne.symm hρ1))
  have hU : ∀ i j, (spectralKappa (ρ i) - conj (spectralKappa (ρ j))) * profileGram (ρ i) (ρ j) =
      conj (spectralKappa (ρ j)) * profileSampleDefect (ρ i) -
        spectralKappa (ρ i) * conj (profileSampleDefect (ρ j)) := fun i j => by
    linear_combination hG2 i j - hG1 i j
  -- Gram presentations
  set μ := volume.restrict (Ioi (0 : ℝ))
  have hNint : ∀ i j, Integrable (fun a => zeroProfile (ρ i) a * conj (zeroProfile (ρ j) a)) μ :=
    fun i j => integrableOn_gramN (hz i) (h0 i) (h1 i) (hz j) (h0 j) (h1 j)
  set f : ι → ℝ → ℂ := fun i x => (x : ℂ) * deriv (zeroProfile (ρ i)) x with hf
  have hQf : ∀ i j, profileFormGram (ρ i) (ρ j) = ∫ a, f i a * conj (f j a) ∂μ := fun i j => by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hf, map_mul, Complex.conj_ofReal]; ring
  have hQint : ∀ i j, Integrable (fun a => f i a * conj (f j a)) μ := fun i j =>
    integrable_mul_conj (memLp_two_mul_deriv_zeroProfile (hz i) (h0 i) (h1 i))
      (memLp_two_mul_deriv_zeroProfile (hz j) (h0 j) (h1 j))
  have hNpsd : (Matrix.of fun i j => profileGram (ρ i) (ρ j)).PosSemidef :=
    posSemidef_gram (μ := μ) (fun i => zeroProfile (ρ i)) hNint
  have hQeq : (Matrix.of fun i j => profileFormGram (ρ i) (ρ j)) =
      Matrix.of fun i j => ∫ a, f i a * conj (f j a) ∂μ := by
    ext i j; simp only [Matrix.of_apply, hQf]
  have hQpsd : (Matrix.of fun i j => profileFormGram (ρ i) (ρ j)).PosSemidef := by
    rw [hQeq]; exact posSemidef_gram f hQint
  refine ⟨hNpsd, hQpsd, ?_, hU, fun i j hd => ?_, fun i hi => ?_⟩
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => ?_
    · have h1' := hNpsd.1; have h2' := hQpsd.1
      ext i j
      have e1 := congrFun (congrFun h1' i) j
      have e2 := congrFun (congrFun h2' i) j
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply] at e1 e2 ⊢
      rw [star_sub, star_div₀, e1, e2, star_ofNat]
    · -- quadratic form = ∫ |ψ'|² for the combination H = Σ conj(c_i) h_i
      set H : ℝ → ℂ := fun x => ∑ i, conj (c i) * zeroProfile (ρ i) x
      set H' : ℝ → ℂ := fun x => ∑ i, conj (c i) * zeroProfileDeriv (ρ i) x
      have hD : LogFormDomain H H' :=
        logFormDomain_sum (fun i => conj (c i)) fun i => zeroProfile_mem_logFormDomain (hz i) (h0 i) (h1 i)
      have hform := (log_unitary_form_identity H H' hD).2.2.2.2.1
      have hqN := gram_quadratic (μ := μ) (fun i => zeroProfile (ρ i)) hNint c
      have hqQ := gram_quadratic f hQint c
      have hlog : (∫ a, ‖∑ i, conj (c i) * f i a‖ ^ 2 ∂μ) = logForm H' := by
        rw [logForm]
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_all_iff.mpr fun i => deriv_zeroProfile_ae (ρ i)]
          with x hx hd
        have hx0 : (0 : ℝ) < x := hx
        have : ∑ i, conj (c i) * f i x = (x : ℂ) * H' x := by
          simp only [hf, H', hd, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, mul_pow]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_def]
      have hsplit : ∑ i, conj (c i) * ∑ j, (profileFormGram (ρ i) (ρ j) - profileGram (ρ i) (ρ j) / 4) * c j =
          (∑ i, conj (c i) * ∑ j, (∫ a, f i a * conj (f j a) ∂μ) * c j) -
            (∑ i, conj (c i) * ∑ j, (∫ a, zeroProfile (ρ i) a * conj (zeroProfile (ρ j) a) ∂μ) * c j) / 4 := by
        simp only [hQf, profileGram, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hsplit, hqN, hqQ, hlog, hform]
      have : (((∫ t, ‖logUnitaryDeriv H H' t‖ ^ 2) + 1 / 4 * ∫ x in Ioi 0, ‖H x‖ ^ 2 : ℝ) : ℂ) -
          ((∫ a, ‖∑ i, conj (c i) * zeroProfile (ρ i) a‖ ^ 2 ∂μ : ℝ) : ℂ) / 4 =
          ((∫ t, ‖logUnitaryDeriv H H' t‖ ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [this]
      exact Complex.zero_le_real.mpr (integral_nonneg fun t => sq_nonneg _)
  · have hki := hk i; have hkj : conj (spectralKappa (ρ j)) ≠ 0 := (map_ne_zero _).mpr (hk j)
    rw [div_eq_div_iff (mul_ne_zero hki hkj) hd, map_div₀]
    have e : (profileSampleDefect (ρ i) / spectralKappa (ρ i) -
        conj (profileSampleDefect (ρ j)) / conj (spectralKappa (ρ j))) *
          (spectralKappa (ρ i) * conj (spectralKappa (ρ j))) =
        conj (spectralKappa (ρ j)) * profileSampleDefect (ρ i) -
          spectralKappa (ρ i) * conj (profileSampleDefect (ρ j)) := by
      field_simp
    rw [e]; linear_combination hU i j
  · refine ⟨?_, integral_norm_sq_pos (hz i) (h0 i) (h1 i)⟩
    have key := congrArg Complex.im (hU i i)
    rw [profileGram_self] at key
    set κ := spectralKappa (ρ i)
    set b := profileSampleDefect (ρ i)
    set n := ∫ x in Ioi (0 : ℝ), ‖zeroProfile (ρ i) x‖ ^ 2
    simp only [Complex.mul_im, Complex.sub_im, Complex.sub_re, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im] at key
    have hn2 : ‖κ‖ ^ 2 = Complex.normSq κ := (Complex.normSq_eq_norm_sq κ).symm
    have hpos : 0 < Complex.normSq κ := Complex.normSq_pos.mpr (hk i)
    have hk2 : κ.im * n = κ.re * b.im - κ.im * b.re := by ring_nf at key; linarith
    rw [Complex.div_im, hn2, show b.im * κ.re / Complex.normSq κ - b.re * κ.im / Complex.normSq κ =
      κ.im * n / Complex.normSq κ by rw [hk2]; ring]
    field_simp

end Roots

section Countercontrol

/-- The weighted finite Gram matrix Σ_k w_k f_i(k) conj f_j(k) is positive semidefinite. -/
lemma posSemidef_finite_gram {ι m : Type*} [Fintype ι] [Fintype m] (w : m → ℝ) (hw : ∀ k, 0 ≤ w k)
    (f : ι → m → ℂ) :
    (Matrix.of fun i j => ∑ k, (w k : ℂ) * f i k * conj (f j k)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_def, map_sum, map_mul,
      Complex.conj_ofReal, Complex.conj_conj]
    exact Finset.sum_congr rfl fun k _ => by ring
  · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_def]
    have hk : ∀ k, (((w k * ‖∑ i, conj (c i) * f i k‖ ^ 2 : ℝ)) : ℂ) =
        ∑ i, ∑ j, conj (c i) * ((w k : ℂ) * f i k * conj (f j k)) * c j := by
      intro k
      push_cast
      rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul, Complex.conj_conj]; ring
    have e : ∑ i, conj (c i) * ∑ j, (∑ k, (w k : ℂ) * f i k * conj (f j k)) * c j =
        ((∑ k, w k * ‖∑ i, conj (c i) * f i k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      simp_rw [hk]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    exact Complex.zero_le_real.mpr (Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (sq_nonneg _))

/-- The paper's auxiliary finite-dimensional control vector h = κ (A - κ I)^(-1) g for the real
diagonal matrix A = diag a and the real vector g. -/
def controlVector {m : Type*} (a g : m → ℝ) (κ : ℂ) (k : m) : ℂ := κ * g k / (a k - κ)

lemma controlVector_forced {m : Type*} (a g : m → ℝ) {κ : ℂ} (hκ : κ.im ≠ 0) (k : m) :
    (a k : ℂ) * controlVector a g κ k = κ * (controlVector a g κ k + g k) := by
  have hd : (a k : ℂ) - κ ≠ 0 := fun h => hκ (by
    have := congrArg Complex.im h
    simpa using this.symm)
  rw [controlVector]
  field_simp
  ring

/-- R2-S2 falsification control (auxiliary, not a zeta system): for a positive real diagonal A,
a real vector g and nonreal parameters κ_i, the vectors h_i = κ_i (A - κ_i I)^(-1) g with
b_i = g* h_i, N_ij = ⟨h_i, h_j⟩ and Q_ij = ⟨A h_i, h_j⟩ (linear in the first argument) satisfy the
same identities (S2.1)-(S2.3) with positive semidefinite N and Q. Positivity and the displayed
identities therefore do not force real parameters. -/
theorem finite_countercontrol {ι m : Type*} [Fintype ι] [Fintype m] (a g : m → ℝ)
    (ha : ∀ k, 0 < a k) (κ : ι → ℂ) (hκ : ∀ i, (κ i).im ≠ 0) :
    (Matrix.of fun i j => ∑ k, controlVector a g (κ i) k * conj (controlVector a g (κ j) k)).PosSemidef ∧
    (Matrix.of fun i j =>
      ∑ k, (a k : ℂ) * controlVector a g (κ i) k * conj (controlVector a g (κ j) k)).PosSemidef ∧
    (∀ i j, ∑ k, (a k : ℂ) * controlVector a g (κ i) k * conj (controlVector a g (κ j) k) =
      κ i * (∑ k, controlVector a g (κ i) k * conj (controlVector a g (κ j) k) +
        conj (∑ k, (g k : ℂ) * controlVector a g (κ j) k))) ∧
    (∀ i j, ∑ k, (a k : ℂ) * controlVector a g (κ i) k * conj (controlVector a g (κ j) k) =
      conj (κ j) * (∑ k, controlVector a g (κ i) k * conj (controlVector a g (κ j) k) +
        ∑ k, (g k : ℂ) * controlVector a g (κ i) k)) ∧
    (∀ i j, (κ i - conj (κ j)) * ∑ k, controlVector a g (κ i) k * conj (controlVector a g (κ j) k) =
      conj (κ j) * (∑ k, (g k : ℂ) * controlVector a g (κ i) k) -
        κ i * conj (∑ k, (g k : ℂ) * controlVector a g (κ j) k)) ∧
    (∀ i j, κ i - conj (κ j) ≠ 0 →
      (∑ k, controlVector a g (κ i) k * conj (controlVector a g (κ j) k)) / (κ i * conj (κ j)) =
        ((∑ k, (g k : ℂ) * controlVector a g (κ i) k) / κ i -
          conj ((∑ k, (g k : ℂ) * controlVector a g (κ j) k) / κ j)) / (κ i - conj (κ j))) := by
  set h : ι → m → ℂ := fun i k => controlVector a g (κ i) k with hh
  set N : ι → ι → ℂ := fun i j => ∑ k, h i k * conj (h j k) with hN
  set b : ι → ℂ := fun i => ∑ k, (g k : ℂ) * h i k with hb
  have hk : ∀ i, κ i ≠ 0 := fun i h0 => hκ i (by simp [h0])
  have h1 : ∀ i j, ∑ k, (a k : ℂ) * h i k * conj (h j k) = κ i * (N i j + conj (b j)) := fun i j => by
    simp only [hN, hb, map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [controlVector_forced a g (hκ i) k]; ring
  have h2 : ∀ i j, ∑ k, (a k : ℂ) * h i k * conj (h j k) = conj (κ j) * (N i j + b i) := fun i j => by
    simp only [hN, hb, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e := congrArg conj (controlVector_forced a g (hκ j) k)
    simp only [map_mul, map_add, Complex.conj_ofReal] at e
    calc (a k : ℂ) * h i k * conj (h j k) = h i k * ((a k : ℂ) * conj (controlVector a g (κ j) k)) := by
          simp only [hh]; ring
      _ = _ := by rw [e]; simp only [hh]; ring
  have hU : ∀ i j, (κ i - conj (κ j)) * N i j = conj (κ j) * b i - κ i * conj (b j) := fun i j => by
    linear_combination h2 i j - h1 i j
  refine ⟨?_, posSemidef_finite_gram a (fun k => (ha k).le) h, h1, h2, hU, fun i j hd => ?_⟩
  · have := posSemidef_finite_gram (fun _ : m => (1 : ℝ)) (fun _ => zero_le_one) h
    simpa only [Complex.ofReal_one, one_mul] using this
  · have hki := hk i
    have hkj : conj (κ j) ≠ 0 := (map_ne_zero _).mpr (hk j)
    rw [div_eq_div_iff (mul_ne_zero hki hkj) hd, map_div₀]
    have e : (b i / κ i - conj (b j) / conj (κ j)) * (κ i * conj (κ j)) =
        conj (κ j) * b i - κ i * conj (b j) := by field_simp
    rw [e]; linear_combination hU i j

end Countercontrol

end Zeta23.OPICAFollowup
