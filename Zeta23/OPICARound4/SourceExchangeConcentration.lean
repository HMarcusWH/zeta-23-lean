import Zeta23.OPICARound4.NativeSourceBudget
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
namespace Zeta23.OPICARound4
open CCM MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate Interval

/-- The actual finite Fourier polynomial at unit aperture. -/
def sourceFiniteFourier (K : ℕ) (u : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ → ℂ :=
  localizedFiniteFunction 1 K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) u)

@[fun_prop] theorem sourceFiniteFourier_continuous (K : ℕ)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) : Continuous (sourceFiniteFourier K u) := by
  unfold sourceFiniteFourier
  fun_prop

/-- Symmetric and antisymmetric overlap energies. These are finite
compressions of exchange channels, with overlap counted with multiplicity. -/
def sourceExchangePlus (K : ℕ) (ω : ℝ)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  (1 / 2) * ∫ t in (0 : ℝ)..ω,
    ‖sourceFiniteFourier K u (t + (1 - ω)) + sourceFiniteFourier K u t‖ ^ 2

def sourceExchangeMinus (K : ℕ) (ω : ℝ)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  (1 / 2) * ∫ t in (0 : ℝ)..ω,
    ‖sourceFiniteFourier K u (t + (1 - ω)) - sourceFiniteFourier K u t‖ ^ 2

def sourceConcentration (K : ℕ) (ω : ℝ)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  (∫ t in (0 : ℝ)..ω, ‖sourceFiniteFourier K u (t + (1 - ω))‖ ^ 2) +
    ∫ t in (0 : ℝ)..ω, ‖sourceFiniteFourier K u t‖ ^ 2

def sourceExchangeMixed (K : ℕ) (ω : ℝ)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℂ :=
  ∫ t in (0 : ℝ)..ω,
    conj (sourceFiniteFourier K h t) * sourceFiniteFourier K u (t + (1 - ω)) +
      conj (sourceFiniteFourier K h (t + (1 - ω))) * sourceFiniteFourier K u t

theorem sourceConcentration_eq_plus_add_minus (K : ℕ) (ω : ℝ)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceConcentration K ω u = sourceExchangePlus K ω u + sourceExchangeMinus K ω u := by
  have hc1 : Continuous (fun t : ℝ => ‖sourceFiniteFourier K u (t + (1 - ω))‖ ^ 2) := by fun_prop
  have hc2 : Continuous (fun t : ℝ => ‖sourceFiniteFourier K u t‖ ^ 2) := by fun_prop
  have hcp : Continuous (fun t : ℝ =>
    ‖sourceFiniteFourier K u (t + (1 - ω)) + sourceFiniteFourier K u t‖ ^ 2) := by fun_prop
  have hcm : Continuous (fun t : ℝ =>
    ‖sourceFiniteFourier K u (t + (1 - ω)) - sourceFiniteFourier K u t‖ ^ 2) := by fun_prop
  unfold sourceConcentration sourceExchangePlus sourceExchangeMinus
  rw [← intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    ← mul_add, ← intervalIntegral.integral_add (hcp.intervalIntegrable _ _) (hcm.intervalIntegrable _ _),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  ring

theorem sourceExchange_nonneg (K : ℕ) {ω : ℝ} (hω : 0 ≤ ω)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    0 ≤ sourceExchangePlus K ω u ∧ 0 ≤ sourceExchangeMinus K ω u := by
  constructor
  · exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hω (fun _ _ => sq_nonneg _))
  · exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hω (fun _ _ => sq_nonneg _))

theorem sourceConcentration_nonneg (K : ℕ) {ω : ℝ} (hω : 0 ≤ ω)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) : 0 ≤ sourceConcentration K ω u := by
  rw [sourceConcentration_eq_plus_add_minus]
  exact add_nonneg (sourceExchange_nonneg K hω u).1 (sourceExchange_nonneg K hω u).2

/-- On the full source interval each endpoint interval costs at most I.
Their overlap is deliberately counted twice. -/
theorem sourceConcentration_le_two_norm_sq (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceConcentration K ω u ≤ 2 * ‖u‖ ^ 2 := by
  have h1 := localizedFiniteFunction_unit_shifted_energy_le_norm_sq K u
    (sub_nonneg.mpr hω1) (show 1 - ω ≤ 1 by linarith)
  have h2 := localizedFiniteFunction_unit_initial_energy_le_norm_sq K u
    (sub_nonneg.mpr hω1) (show 1 - ω ≤ 1 by linarith)
  have he : 1 - (1 - ω) = ω := by ring
  rw [he] at h1 h2
  exact (add_le_add h1 h2).trans_eq (by ring)

/-- Below half aperture the two energy intervals are disjoint. -/
theorem sourceConcentration_le_norm_sq_of_half (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hhalf : ω ≤ 1 / 2)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceConcentration K ω u ≤ ‖u‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => ‖sourceFiniteFourier K u t‖ ^ 2
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hgap : ω ≤ 1 - ω := by linarith
  have hd : 1 - ω ≤ 1 := by linarith
  have hshift := intervalIntegral.integral_comp_add_right
    (f := f) (a := (0 : ℝ)) (b := ω) (1 - ω)
  have he : ω + (1 - ω) = 1 := by ring
  rw [zero_add, he] at hshift
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (0 : ℝ) ω)
    (hc.intervalIntegrable (μ := volume) ω (1 - ω))
  have hj := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (0 : ℝ) (1 - ω))
    (hc.intervalIntegrable (μ := volume) (1 - ω) 1)
  have hn : 0 ≤ ∫ t in ω..(1 - ω), f t :=
    intervalIntegral.integral_nonneg hgap (fun _ _ => sq_nonneg _)
  have htotal : (∫ t in (0 : ℝ)..1, f t) = ‖u‖ ^ 2 :=
    localizedFiniteFunction_unit_energy_eq_norm_sq K u
  unfold sourceConcentration
  change (∫ t in (0 : ℝ)..ω, f (t + (1 - ω))) + (∫ t in (0 : ℝ)..ω, f t) ≤ _
  rw [hshift]
  linarith

/-- The symmetrized unit Fourier overlap is exactly the native source energy. -/
theorem sourceExchangeMixed_self_eq_native (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceExchangeMixed K ω u u = sourceContract K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) u) ω := by
  rw [sourceContract_eq_localizedWeilCorrelation_unit K _ ω hω0 hω1,
    localizedWeilCorrelation,
    weilTest_localizedFiniteVector_pos K _ (sub_nonneg.mpr hω1) (by linarith : 1 - ω ≤ 1),
    weilTest_localizedFiniteVector_neg K _ (sub_nonneg.mpr hω1) (by linarith : 1 - ω ≤ 1)]
  have he : 1 - (1 - ω) = ω := by ring
  rw [he]
  have h1 : Continuous (fun t : ℝ =>
    sourceFiniteFourier K u (t + (1 - ω)) * conj (sourceFiniteFourier K u t)) := by fun_prop
  have h2 : Continuous (fun t : ℝ =>
    sourceFiniteFourier K u t * conj (sourceFiniteFourier K u (t + (1 - ω)))) := by fun_prop
  change sourceExchangeMixed K ω u u =
    (∫ t in (0 : ℝ)..ω, sourceFiniteFourier K u (t + (1 - ω)) * conj (sourceFiniteFourier K u t)) +
      ∫ t in (0 : ℝ)..ω, sourceFiniteFourier K u t * conj (sourceFiniteFourier K u (t + (1 - ω)))
  rw [← intervalIntegral.integral_add (h1.intervalIntegrable (μ := volume) _ _)
    (h2.intervalIntegrable (μ := volume) _ _)]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [sourceExchangeMixed, sourceFiniteFourier]
  ring

/-- Exact exchange-channel difference, with native S and no projection claim. -/
theorem native_source_energy_eq_exchange_difference (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (sourceMatrix ω K) u =
      sourceExchangePlus K ω u - sourceExchangeMinus K ω u := by
  have hs := congrArg Complex.re (sourceExchangeMixed_self_eq_native K hω0 hω1 u)
  have hc : Continuous (fun t : ℝ =>
    conj (sourceFiniteFourier K u t) * sourceFiniteFourier K u (t + (1 - ω)) +
      conj (sourceFiniteFourier K u (t + (1 - ω))) * sourceFiniteFourier K u t) := by fun_prop
  change RCLike.re (∫ t in (0 : ℝ)..ω,
    conj (sourceFiniteFourier K u t) * sourceFiniteFourier K u (t + (1 - ω)) +
      conj (sourceFiniteFourier K u (t + (1 - ω))) * sourceFiniteFourier K u t) = _ at hs
  have hre := (intervalIntegral.intervalIntegral_re
    (hc.intervalIntegrable (μ := volume) (0 : ℝ) ω)).trans hs
  change (∫ t in (0 : ℝ)..ω, _) = matrixRealEnergy (sourceMatrix ω K) u at hre
  rw [← hre]
  have hp : Continuous (fun t : ℝ =>
    ‖sourceFiniteFourier K u (t + (1 - ω)) + sourceFiniteFourier K u t‖ ^ 2) := by fun_prop
  have hm : Continuous (fun t : ℝ =>
    ‖sourceFiniteFourier K u (t + (1 - ω)) - sourceFiniteFourier K u t‖ ^ 2) := by fun_prop
  unfold sourceExchangePlus sourceExchangeMinus
  rw [← mul_sub, ← intervalIntegral.integral_sub (hp.intervalIntegrable _ _) (hm.intervalIntegrable _ _),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  have hreal : RCLike.re (star (sourceFiniteFourier K u t) * sourceFiniteFourier K u (t + (1 - ω))) =
      RCLike.re (star (sourceFiniteFourier K u (t + (1 - ω))) * sourceFiniteFourier K u t) := by
    change (conj (sourceFiniteFourier K u t) * sourceFiniteFourier K u (t + (1 - ω))).re =
      (conj (sourceFiniteFourier K u (t + (1 - ω))) * sourceFiniteFourier K u t).re
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simp only [RCLike.inner_apply, starRingEnd_apply, map_add]
  rw [hreal]
  ring

private theorem continuous_interval_inner_norm_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f g : ℝ → E) (hf : Continuous f) (hg : Continuous g)
    {ω : ℝ} (hω : 0 ≤ ω) :
    ‖∫ t in (0 : ℝ)..ω, inner ℂ (f t) (g t)‖ ^ 2 ≤
      (∫ t in (0 : ℝ)..ω, ‖f t‖ ^ 2) * (∫ t in (0 : ℝ)..ω, ‖g t‖ ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) ω)
  have mem2 (v : ℝ → E) (hv : Continuous v) : MemLp v 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hω).mp
      ((hv.norm.pow 2).intervalIntegrable (μ := volume) (0 : ℝ) ω)
  have hf2 := mem2 f hf
  have hg2 := mem2 g hg
  have hn (v : ℝ → E) (hv : MemLp v 2 μ) :
      ‖hv.toLp v‖ ^ 2 = ∫ t in (0 : ℝ)..ω, ‖v t‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (hv.toLp v), L2.inner_def,
      ← integral_re (L2.integrable_inner (𝕜 := ℂ) (hv.toLp v) (hv.toLp v)),
      intervalIntegral.integral_of_le hω]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with t ht
    rw [ht, inner_self_eq_norm_sq]
  have hi : inner ℂ (hf2.toLp f) (hg2.toLp g) =
      ∫ t in (0 : ℝ)..ω, inner ℂ (f t) (g t) := by
    rw [L2.inner_def, intervalIntegral.integral_of_le hω]
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp, hg2.coeFn_toLp] with t ht hu
    rw [ht, hu]
  have hc := norm_inner_le_norm (𝕜 := ℂ) (hf2.toLp f) (hg2.toLp g)
  have hc2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hc
  rw [mul_pow, hn f hf2, hn g hg2, hi] at hc2
  exact hc2

/-- Paired L² Cauchy--Schwarz uses the same two overlap intervals for both
vectors. Their possible overlap is retained in each concentration cost. -/
theorem sourceExchangeMixed_norm_sq_le (K : ℕ) {ω : ℝ} (hω : 0 ≤ ω)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖sourceExchangeMixed K ω h u‖ ^ 2 ≤
      sourceConcentration K ω h * sourceConcentration K ω u := by
  let f : ℝ → EuclideanSpace ℂ (Fin 2) := fun t =>
    WithLp.toLp 2 ![sourceFiniteFourier K h t, sourceFiniteFourier K h (t + (1 - ω))]
  let g : ℝ → EuclideanSpace ℂ (Fin 2) := fun t =>
    WithLp.toLp 2 ![sourceFiniteFourier K u (t + (1 - ω)), sourceFiniteFourier K u t]
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hi : (∫ t in (0 : ℝ)..ω, inner ℂ (f t) (g t)) = sourceExchangeMixed K ω h u := by
    unfold sourceExchangeMixed
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, f, g,
      Matrix.cons_val_zero, Matrix.cons_val_one, Complex.star_def]
    ring
  have hn1 : (∫ t in (0 : ℝ)..ω, ‖f t‖ ^ 2) = sourceConcentration K ω h := by
    have hp (t : ℝ) : ‖f t‖ ^ 2 = ‖sourceFiniteFourier K h t‖ ^ 2 +
        ‖sourceFiniteFourier K h (t + (1 - ω))‖ ^ 2 := by
      simp [f, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    simp_rw [hp]
    rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun t : ℝ => ‖sourceFiniteFourier K h t‖ ^ 2)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => ‖sourceFiniteFourier K h (t + (1 - ω))‖ ^ 2)).intervalIntegrable _ _)]
    exact add_comm _ _
  have hn2 : (∫ t in (0 : ℝ)..ω, ‖g t‖ ^ 2) = sourceConcentration K ω u := by
    have hp (t : ℝ) : ‖g t‖ ^ 2 = ‖sourceFiniteFourier K u (t + (1 - ω))‖ ^ 2 +
        ‖sourceFiniteFourier K u t‖ ^ 2 := by
      simp [g, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    simp_rw [hp]
    exact intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun t : ℝ => ‖sourceFiniteFourier K u (t + (1 - ω))‖ ^ 2)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => ‖sourceFiniteFourier K u t‖ ^ 2)).intervalIntegrable _ _)
  simpa only [hi, hn1, hn2] using continuous_interval_inner_norm_sq_le f g hf hg hω

theorem sourceFiniteFourier_eq_sum_exp (K : ℕ)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) (t : ℝ) :
    sourceFiniteFourier K u t = ∑ i, u i *
      Complex.exp (Complex.I * ((2 * Real.pi * (centeredIndex K i : ℝ) * t : ℝ) : ℂ)) := by
  simp [sourceFiniteFourier, localizedFiniteFunction, localizedMode]

/-- Exact native mixed exchange identity. It uses the inherited basis Weil
correlation, preserving both shifted orientations and all complex cross terms. -/
theorem sourceExchangeMixed_eq_native (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceExchangeMixed K ω h u = sourceAtomPairing K h u ω := by
  have hy0 : 0 ≤ 1 - ω := sub_nonneg.mpr hω1
  have hy1 : 1 - ω ≤ 1 := by linarith
  have he : 1 - (1 - ω) = ω := by ring
  have hb (i j : Fin (2 * K + 1)) :
      (∫ t in (0 : ℝ)..ω,
        conj (localizedMode 1 (centeredIndex K i) t) *
            localizedMode 1 (centeredIndex K j) (t + (1 - ω)) +
          conj (localizedMode 1 (centeredIndex K i) (t + (1 - ω))) *
            localizedMode 1 (centeredIndex K j) t) =
        sourceEntry ω (centeredIndex K i) (centeredIndex K j) := by
    have hc := localizedWeilCorrelation_basis_eq_qBasis
      (centeredIndex K i) (centeredIndex K j) (by norm_num : (0 : ℝ) < 1) hy0 hy1
    rw [localizedWeilCorrelation, weilTest_localizedZeroExtendedMode_pos _ _ hy0 hy1,
      weilTest_localizedZeroExtendedMode_neg _ _ hy0 hy1, he] at hc
    have hi1 : Continuous (fun t : ℝ => localizedMode 1 (centeredIndex K j) (t + (1 - ω)) *
      conj (localizedMode 1 (centeredIndex K i) t)) := by fun_prop
    have hi2 : Continuous (fun t : ℝ => localizedMode 1 (centeredIndex K j) t *
      conj (localizedMode 1 (centeredIndex K i) (t + (1 - ω)))) := by fun_prop
    rw [← intervalIntegral.integral_add (hi1.intervalIntegrable (μ := volume) _ _)
      (hi2.intervalIntegrable (μ := volume) _ _)] at hc
    have hs := sourceEntry_one_sub_eq_qBasis (centeredIndex K i) (centeredIndex K j) (1 - ω) 1
    rw [div_one, he] at hs
    rw [← hs] at hc
    calc
      _ = (∫ t in (0 : ℝ)..ω,
        localizedMode 1 (centeredIndex K j) (t + (1 - ω)) * conj (localizedMode 1 (centeredIndex K i) t) +
          localizedMode 1 (centeredIndex K j) t * conj (localizedMode 1 (centeredIndex K i) (t + (1 - ω)))) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        ring
      _ = _ := hc
  have hp (t : ℝ) :
      conj (sourceFiniteFourier K h t) * sourceFiniteFourier K u (t + (1 - ω)) +
        conj (sourceFiniteFourier K h (t + (1 - ω))) * sourceFiniteFourier K u t =
      ∑ i, ∑ j, (conj (h i) * u j) *
        (conj (localizedMode 1 (centeredIndex K i) t) * localizedMode 1 (centeredIndex K j) (t + (1 - ω)) +
          conj (localizedMode 1 (centeredIndex K i) (t + (1 - ω))) * localizedMode 1 (centeredIndex K j) t) := by
    simp only [sourceFiniteFourier, localizedFiniteFunction, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
    ring
  unfold sourceExchangeMixed
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_const_mul, hb, sourceEntry_eq_ofReal]
      change _ = (sourceEntryReal ω (centeredIndex K i) (centeredIndex K j) : ℂ) *
        (star (h i) * u j)
      rw [Complex.star_def]
      ring
    · intro j _
      exact (by fun_prop : Continuous (fun t : ℝ => (conj (h i) * u j) *
        (conj (localizedMode 1 (centeredIndex K i) t) * localizedMode 1 (centeredIndex K j) (t + (1 - ω)) +
          conj (localizedMode 1 (centeredIndex K i) (t + (1 - ω))) * localizedMode 1 (centeredIndex K j) t))).intervalIntegrable _ _
  · intro i _
    exact (by fun_prop : Continuous (fun t : ℝ => ∑ j, (conj (h i) * u j) *
      (conj (localizedMode 1 (centeredIndex K i) t) * localizedMode 1 (centeredIndex K j) (t + (1 - ω)) +
        conj (localizedMode 1 (centeredIndex K i) (t + (1 - ω))) * localizedMode 1 (centeredIndex K j) t))).intervalIntegrable _ _

/-- Full complex Cauchy--Schwarz for the actual atom, with both native
concentrations. No individual matrix-entry or dimension estimate is used. -/
theorem native_source_mixed_concentration_bound (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖sourceAtomPairing K h u ω‖ ≤
      Real.sqrt (sourceConcentration K ω h * sourceConcentration K ω u) := by
  rw [← sourceExchangeMixed_eq_native K hω0 hω1 h u]
  exact Real.le_sqrt_of_sq_le (sourceExchangeMixed_norm_sq_le K hω0 h u)

private theorem native_source_square_concentration_of_cost (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (c : ℝ) (hc : 0 ≤ c)
    (hcost : ∀ v : EuclideanSpace ℂ (Fin (2 * K + 1)),
      sourceConcentration K ω v ≤ c * ‖v‖ ^ 2)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖(sourceMatrix ω K).toEuclideanLin u‖ ^ 2 ≤ c * sourceConcentration K ω u := by
  let v := (sourceMatrix ω K).toEuclideanLin u
  have hsq : (‖v‖ ^ 2) ^ 2 ≤ sourceConcentration K ω v * sourceConcentration K ω u := by
    have h := sourceExchangeMixed_norm_sq_le K hω0 v u
    rw [sourceExchangeMixed_eq_native K hω0 hω1, sourceAtomPairing_eq_physical_inner] at h
    change ‖inner ℂ v v‖ ^ 2 ≤ _ at h
    simpa [inner_self_eq_norm_sq_to_K, norm_pow] using h
  have hC := sourceConcentration_nonneg K hω0 u
  have hbound := hsq.trans (mul_le_mul_of_nonneg_right (hcost v) hC)
  change ‖v‖ ^ 2 ≤ c * sourceConcentration K ω u
  by_cases hv : ‖v‖ = 0
  · simpa [hv] using mul_nonneg hc hC
  · have hp : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv))
    apply (mul_le_mul_iff_left₀ hp).mp
    convert hbound using 1 <;> ring

/-- Actual S²≤2C on the full source interval. The coefficient two prices
the overlap counted with multiplicity. -/
theorem native_source_square_concentration_full (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖(sourceMatrix ω K).toEuclideanLin u‖ ^ 2 ≤ 2 * sourceConcentration K ω u :=
  native_source_square_concentration_of_cost K hω0 hω1 2 (by norm_num)
    (sourceConcentration_le_two_norm_sq K hω0 hω1) u

/-- Actual S²≤C on the half interval, where the two energy windows are disjoint. -/
theorem native_source_square_concentration_half (K : ℕ) {ω : ℝ}
    (hω0 : 0 ≤ ω) (hhalf : ω ≤ 1 / 2)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖(sourceMatrix ω K).toEuclideanLin u‖ ^ 2 ≤ sourceConcentration K ω u := by
  simpa only [one_mul] using native_source_square_concentration_of_cost K hω0
    (show ω ≤ 1 by linarith) 1 (by norm_num)
    (by intro v; simpa only [one_mul] using sourceConcentration_le_norm_sq_of_half K hω0 hhalf v) u

end Zeta23.OPICARound4
