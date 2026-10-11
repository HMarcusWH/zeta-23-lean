import Zeta23.CCM.CanonicalRegularizedEnergyIdentity
import Zeta23.CCM.ProductionWeightedTestCalculus
import Zeta23.CCM.FirstCrossingProductionCurvatureBridge
import Zeta23.CCM.CanonicalSourceSpectralFlow
import Zeta23.CCM.CanonicalCompressedSeamJets
import Zeta23.CCM.RegularFirstBadRieszEnergy
import Zeta23.CCM.CanonicalApertureContinuity
import Zeta23.CCM.ProductionPhysicalFunctionalCongruence
import Zeta23.CCM.CanonicalCompressedApertureC2
import Zeta23.CCM.MixedSourceDerivativeTransport

noncomputable section

/-!
# M65: prime-free F04 derivative authority

For `0 < L < log 2` no prime power lies below `e^L`, so the canonical even
energy `E_z(L) = Re⟪A_L z, z⟫` is the regularized pole/archimedean integral
with the exact `wCorrection` and no prime terms (M05/M64 real form).  This
module differentiates that integral under the moving aperture (Leibniz with a
moving upper limit, `t ρ(t)` regularized), checks the endpoint cancellation
through `wCorrection' = e^{-L/2} ρ(L)`, and proves all three fields of
`ProductionContactF04DerivativeAuthority L K` on that window:

* `E'_z(L)` is the physical value of the first-derivative test;
* `E''_z(L) + (2/L) E'_z(L)` is the physical value of the second-derivative test
  (the boundary term vanishes because `e'_z(0) = 0` on boundary-flat vectors);
* `Re⟪z, A'_L w⟫` is the physical value of the mixed test, by symmetric
  polarization on both sides.

`D` is not used.  The global F04 interface (all `L`, across prime seams) stays
OPEN.
-/


namespace Zeta23.CCM

open MeasureTheory Set Filter Topology
open scoped Interval ArithmeticFunction ComplexConjugate

/-- A function with `‖f x - f x₀‖ ≤ C ‖x - x₀‖²` near `x₀` has derivative `0`. -/
theorem hasDerivAt_zero_of_sq_bound {f : ℝ → ℝ} {x₀ C : ℝ}
    (h : ∀ᶠ x in 𝓝 x₀, |f x - f x₀| ≤ C * (x - x₀) ^ 2) :
    HasDerivAt f 0 x₀ := by
  rw [hasDerivAt_iff_isLittleO]
  simp only [smul_zero, sub_zero]
  have hO : (fun x => f x - f x₀) =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [h] with x hx
    rw [Real.norm_eq_abs, norm_pow, norm_norm, Real.norm_eq_abs, sq_abs]
    exact hx
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x₀ one_lt_two)

/-- **Leibniz rule with a moving upper limit.**  If `x ↦ F x t` has derivative
`F' x t` bounded by `B` for `x` near `L₀` and `t ∈ (0, L₀ + δ)`, the slices are
continuous on `(0, L₀ + δ)` and `F L₀` is integrable on `[0, L₀]`, then
`x ↦ ∫₀ˣ F x t dt` has derivative `F L₀ L₀ + ∫₀^{L₀} F' L₀ t dt` at `L₀`.
The integrand may be unbounded near `t = 0`; only the derivative is bounded. -/
theorem hasDerivAt_integral_moving_upper
    {F F' : ℝ → ℝ → ℝ} {L₀ δ B : ℝ} (hL₀ : 0 < L₀) (hδ : 0 < δ) (hδL : δ < L₀)
    (hdiff : ∀ x ∈ Ioo (L₀ - δ) (L₀ + δ), ∀ t ∈ Ioo 0 (L₀ + δ),
      HasDerivAt (fun y => F y t) (F' x t) x)
    (hbound : ∀ x ∈ Ioo (L₀ - δ) (L₀ + δ), ∀ t ∈ Ioo 0 (L₀ + δ), |F' x t| ≤ B)
    (hcontF : ∀ x ∈ Ioo (L₀ - δ) (L₀ + δ), ContinuousOn (F x) (Ioo 0 (L₀ + δ)))
    (hcontF' : ContinuousOn (F' L₀) (Ioo 0 (L₀ + δ)))
    (hint : IntervalIntegrable (F L₀) volume 0 L₀) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, F x t)
      (F L₀ L₀ + ∫ t in (0 : ℝ)..L₀, F' L₀ t) L₀ := by
  set s := Ioo (L₀ - δ) (L₀ + δ) with hs_def
  set U := Ioo (0 : ℝ) (L₀ + δ) with hU_def
  have hL₀s : L₀ ∈ s := ⟨by linarith, by linarith⟩
  have hs : s ∈ 𝓝 L₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hL₀U : L₀ ∈ U := ⟨hL₀, by linarith⟩
  have hIoc : Ioc (0 : ℝ) L₀ ⊆ U := fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hbound L₀ hL₀s L₀ hL₀U)
  -- Lipschitz bound in the parameter
  have hlip : ∀ x ∈ s, ∀ t ∈ U, |F x t - F L₀ t| ≤ B * |x - L₀| := by
    intro x hx t ht
    have := (convex_Ioo (L₀ - δ) (L₀ + δ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y => F y t) (f' := fun y => F' y t)
      (fun y hy => (hdiff y hy t ht).hasDerivWithinAt)
      (fun y hy => by rw [Real.norm_eq_abs]; exact hbound y hy t ht) hL₀s hx
    simpa [Real.norm_eq_abs] using this
  -- integrability of nearby slices on `[0, L₀]`
  have hmeas : ∀ x ∈ s, AEStronglyMeasurable (F x) (volume.restrict (Ι (0 : ℝ) L₀)) := by
    intro x hx
    rw [uIoc_of_le hL₀.le]
    exact ((hcontF x hx).mono hIoc).aestronglyMeasurable measurableSet_Ioc
  have hintx : ∀ x ∈ s, IntervalIntegrable (F x) volume 0 L₀ := by
    intro x hx
    have hdiffint : IntervalIntegrable (fun t => F x t - F L₀ t) volume 0 L₀ := by
      refine (intervalIntegrable_const (c := B * |x - L₀|)).mono_fun'
        ((hmeas x hx).sub (hmeas L₀ hL₀s)) ?_
      rw [uIoc_of_le hL₀.le]
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
      show ‖F x t - F L₀ t‖ ≤ B * |x - L₀|
      rw [Real.norm_eq_abs]
      exact hlip x hx t (hIoc ht)
    have := hdiffint.add hint
    simpa using this
  have hsubU : ∀ x ∈ s, uIcc L₀ x ⊆ U := by
    intro x hx t ht
    rcases le_total L₀ x with h | h
    · rw [uIcc_of_le h] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2, hx.2]⟩
    · rw [uIcc_of_ge h] at ht
      exact ⟨by linarith [ht.1, hx.1], by linarith [ht.2]⟩
  have hintU : ∀ x ∈ s, ∀ y ∈ s, IntervalIntegrable (F y) volume L₀ x := fun x hx y hy =>
    ((hcontF y hy).mono (hsubU x hx)).intervalIntegrable
  -- the three pieces
  obtain ⟨-, h1⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := L₀) (F := F) (F' := F') (x₀ := L₀) (bound := fun _ => B)
    hs (Filter.eventually_of_mem hs hmeas) hint
    (by rw [uIoc_of_le hL₀.le]; exact (hcontF'.mono hIoc).aestronglyMeasurable measurableSet_Ioc)
    (Eventually.of_forall fun t ht x hx => by
      rw [uIoc_of_le hL₀.le] at ht
      rw [Real.norm_eq_abs]; exact hbound x hx t (hIoc ht))
    intervalIntegrable_const
    (Eventually.of_forall fun t ht x hx => by
      rw [uIoc_of_le hL₀.le] at ht
      exact hdiff x hx t (hIoc ht))
  have hUopen : IsOpen U := isOpen_Ioo
  have h2 : HasDerivAt (fun x => ∫ t in L₀..x, F L₀ t) (F L₀ L₀) L₀ :=
    intervalIntegral.integral_hasDerivAt_right (by simp)
      ((hcontF L₀ hL₀s).stronglyMeasurableAtFilter hUopen L₀ hL₀U)
      ((hcontF L₀ hL₀s).continuousAt (hUopen.mem_nhds hL₀U))
  set R : ℝ → ℝ := fun x => ∫ t in L₀..x, (F x t - F L₀ t) with hR
  have h3 : HasDerivAt R 0 L₀ := by
    apply hasDerivAt_zero_of_sq_bound (C := B)
    filter_upwards [hs] with x hx
    have hR0 : R L₀ = 0 := by simp [hR]
    rw [hR0, sub_zero]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := L₀) (b := x) (C := B * |x - L₀|) (f := fun t => F x t - F L₀ t)
      (fun t ht => by
        rw [Real.norm_eq_abs]
        exact hlip x hx t (hsubU x hx (uIoc_subset_uIcc ht)))
    rw [Real.norm_eq_abs] at this
    calc |R x| ≤ B * |x - L₀| * |x - L₀| := this
      _ = B * (x - L₀) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
  have hsum := (h1.add h2).add h3
  have heq : (fun x => ∫ t in (0 : ℝ)..x, F x t) =ᶠ[𝓝 L₀]
      fun x => ((∫ t in (0 : ℝ)..L₀, F x t) + ∫ t in L₀..x, F L₀ t) + R x := by
    filter_upwards [hs] with x hx
    rw [← intervalIntegral.integral_add_adjacent_intervals (hintx x hx) (hintU x hx x hx)]
    simp only [hR]
    rw [intervalIntegral.integral_sub (hintU x hx x hx) (hintU x hx L₀ hL₀s)]
    ring
  have := hsum.congr_of_eventuallyEq heq
  rw [show F L₀ L₀ + ∫ t in (0 : ℝ)..L₀, F' L₀ t =
    (∫ t in (0 : ℝ)..L₀, F' L₀ t) + F L₀ L₀ + 0 by ring]
  exact this

/-- The elementary source quadratic form is real: it is the real source energy. -/
theorem quadraticForm_sourceMatrix_equiv_eq_ofReal (ω : ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    quadraticForm (sourceMatrix ω K) ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) =
      (sourceAtomRealEnergy K x ω : ℂ) := by
  set u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  have h := sourceSesq_conj_symm ω K u u
  rw [sourceSesq_self] at h
  apply Complex.ext
  · simp [sourceAtomRealEnergy, matrixRealEnergy, u]
  · rw [Complex.ofReal_im]
    exact Complex.conj_eq_iff_im.mp h

/-- **M05, real form.** The canonical real energy of any vector, with
`e(ω) = sourceAtomRealEnergy K x ω` and the exact von Mangoldt weights. -/
theorem matrixRealEnergy_canonical_eq_regularized (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) {L : ℝ} (hL : 0 < L) :
    matrixRealEnergy (canonicalSourceMatrix L K) x =
      (∫ t in (0 : ℝ)..L, sourceAtomRealEnergy K x (1 - t / L) * completeSourcePoleWeight t) -
        ((∫ t in (0 : ℝ)..L, (sourceAtomRealEnergy K x (1 - t / L) -
            sourceAtomRealEnergy K x 1 * Real.exp (-t / 2)) * archDensity t) +
          sourceAtomRealEnergy K x 1 * wCorrection L) -
        ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          (Λ q / Real.sqrt q) * sourceAtomRealEnergy K x (1 - Real.log q / L) := by
  unfold matrixRealEnergy
  rw [quadraticForm_canonicalSourceMatrix_eq_regularizedEnergy K _ hL]
  simp only [quadraticForm_sourceMatrix_equiv_eq_ofReal, primeSourceWeight]
  have h1 : (∫ t in (0 : ℝ)..L, ((sourceAtomRealEnergy K x (1 - t / L) : ℝ) : ℂ) *
      (completeSourcePoleWeight t : ℂ)) =
      ((∫ t in (0 : ℝ)..L, sourceAtomRealEnergy K x (1 - t / L) *
        completeSourcePoleWeight t : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr fun t _ => by push_cast; ring
  have h2 : (∫ t in (0 : ℝ)..L, (((sourceAtomRealEnergy K x (1 - t / L) : ℝ) : ℂ) -
      ((sourceAtomRealEnergy K x 1 : ℝ) : ℂ) * (Real.exp (-t / 2) : ℂ)) * (archDensity t : ℂ)) =
      ((∫ t in (0 : ℝ)..L, (sourceAtomRealEnergy K x (1 - t / L) -
          sourceAtomRealEnergy K x 1 * Real.exp (-t / 2)) * archDensity t : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr fun t _ => by push_cast; ring
  rw [h1, h2]
  have h3 : ∀ q : ℕ, ((Λ q / Real.sqrt q : ℝ) : ℂ) *
      ((sourceAtomRealEnergy K x (1 - Real.log q / L) : ℝ) : ℂ) =
      (((Λ q / Real.sqrt q) * sourceAtomRealEnergy K x (1 - Real.log q / L) : ℝ) : ℂ) := by
    intro q; push_cast; ring
  simp only [h3, ← Complex.ofReal_sum, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    ← Complex.ofReal_sub, Complex.ofReal_re]

/-- Below `log 2` there are no prime-power samples. -/
theorem Icc_two_floor_exp_eq_empty {L : ℝ} (hL2 : L < Real.log 2) :
    Finset.Icc 2 ⌊Real.exp L⌋₊ = ∅ := by
  have hexp : Real.exp L < 2 := by
    calc Real.exp L < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hL2
      _ = 2 := Real.exp_log (by norm_num)
  have hfl : ⌊Real.exp L⌋₊ < 2 := (Nat.floor_lt (Real.exp_pos L).le).mpr (by exact_mod_cast hexp)
  exact Finset.Icc_eq_empty (by omega)

/-- `archDensity` is continuous on the open positive half-line. -/
theorem continuousOn_archDensity : ContinuousOn archDensity (Ioi 0) := by
  unfold archDensity
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  have : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.mpr (by linarith [mem_Ioi.mp hx])
  linarith

/-- `wCorrection' = e^{-L/2} ρ(L)` on the positive half-line. -/
theorem hasDerivAt_wCorrection {L : ℝ} (hL : 0 < L) :
    HasDerivAt wCorrection (Real.exp (-L / 2) * archDensity L) L := by
  have he : 1 < Real.exp L := Real.one_lt_exp_iff.mpr hL
  have hd : Real.exp L - 1 ≠ 0 := by linarith
  have hq : HasDerivAt (fun s => (Real.exp s + 1) / (Real.exp s - 1))
      ((Real.exp L * (Real.exp L - 1) - (Real.exp L + 1) * Real.exp L) /
        (Real.exp L - 1) ^ 2) L :=
    ((Real.hasDerivAt_exp L).add_const 1).div ((Real.hasDerivAt_exp L).sub_const 1) hd
  have hpos : (Real.exp L + 1) / (Real.exp L - 1) ≠ 0 := by
    apply div_ne_zero (by linarith) hd
  have hlog := hq.log hpos
  have hfun : wCorrection = fun s =>
      (1 / 2) * (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) +
        -(1 / 2) * Real.log ((Real.exp s + 1) / (Real.exp s - 1)) := by
    funext s
    unfold wCorrection
    ring
  have hw := (hlog.const_mul (-(1 / 2 : ℝ))).const_add
    ((1 / 2) * (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)))
  rw [hfun]
  refine hw.congr_deriv ?_
  symm
  unfold archDensity
  rw [← mul_div_assoc, ← Real.exp_add, show -L / 2 + L / 2 = 0 by ring, Real.exp_zero,
    Real.exp_neg]
  set E := Real.exp L
  have hE0 : E ≠ 0 := (Real.exp_pos L).ne'
  have hE1 : E - 1 ≠ 0 := hd
  have hE2 : E + 1 ≠ 0 := by positivity
  have hE3 : E - E⁻¹ ≠ 0 := by
    have : E⁻¹ < 1 := inv_lt_one_of_one_lt₀ he
    linarith
  have hE4 : E ^ 2 - 1 ≠ 0 := by
    have : 1 < E ^ 2 := one_lt_pow₀ he two_ne_zero
    linarith
  have hE5 : -1 + E ^ 2 ≠ 0 := by rw [add_comm, ← sub_eq_add_neg]; exact hE4
  field_simp
  ring


/-! ## Bounds and coordinates -/

theorem exists_abs_bound_Icc {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ y ∈ Icc a b, |f y| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
  have := hC y hy
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem hasDerivAt_one_sub_div_param (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 - t / y) (t / x ^ 2) x := by
  have h := ((hasDerivAt_inv hx).const_mul t).const_sub 1
  have hfun : (fun y : ℝ => 1 - t * y⁻¹) = fun y => 1 - t / y := by
    funext y; rw [div_eq_mul_inv]
  rw [hfun] at h
  refine h.congr_deriv ?_
  field_simp

@[fun_prop] theorem continuous_completeSourcePoleWeight : Continuous completeSourcePoleWeight := by
  unfold completeSourcePoleWeight; fun_prop

theorem continuous_sourceAtomRealEnergy (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    Continuous (sourceAtomRealEnergy K x) :=
  (contDiff_sourceAtomRealEnergy K x).continuous

/-- Window facts for the Leibniz applications with `δ = L₀/2`. -/
theorem window_coord {L₀ x t : ℝ} (hL₀ : 0 < L₀) (hx : x ∈ Ioo (L₀ - L₀ / 2) (L₀ + L₀ / 2))
    (ht : t ∈ Ioo 0 (L₀ + L₀ / 2)) :
    0 < x ∧ 1 - t / x ∈ Icc (-2 : ℝ) 1 ∧ t / x ^ 2 ≤ 6 / L₀ ∧ 1 / x ^ 2 ≤ 4 / L₀ ^ 2 ∧
      t ∈ Icc 0 (2 * L₀) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨ht1, ht2⟩ := ht
  have hxpos : 0 < x := by linarith
  have hxL : L₀ / 2 < x := by linarith
  refine ⟨hxpos, ⟨?_, ?_⟩, ?_, ?_, ⟨ht1.le, by linarith⟩⟩
  · have : t / x ≤ 3 := by
      rw [div_le_iff₀ hxpos]; linarith
    linarith
  · have : 0 ≤ t / x := div_nonneg ht1.le hxpos.le
    linarith
  · have hx2' : (L₀ / 2) ^ 2 ≤ x ^ 2 := by nlinarith
    calc t / x ^ 2 ≤ (3 * L₀ / 2) / (L₀ / 2) ^ 2 := by
          apply div_le_div₀ (by positivity) (by linarith) (by positivity) hx2'
      _ = 6 / L₀ := by field_simp; ring
  · have hx2' : (L₀ / 2) ^ 2 ≤ x ^ 2 := by nlinarith
    calc 1 / x ^ 2 ≤ 1 / (L₀ / 2) ^ 2 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hx2'
      _ = 4 / L₀ ^ 2 := by field_simp; ring

/-! ## Pole channel -/

section Channels

variable (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))

/-- **Pole channel derivative.** -/
theorem hasDerivAt_poleChannel {L₀ : ℝ} (hL₀ : 0 < L₀) :
    HasDerivAt
      (fun L => ∫ t in (0 : ℝ)..L, sourceAtomRealEnergy K x (1 - t / L) *
        completeSourcePoleWeight t)
      (∫ t in (0 : ℝ)..L₀, sourceAtomRealEnergyDerivative K x (1 - t / L₀) * (t / L₀ ^ 2) *
        completeSourcePoleWeight t) L₀ := by
  obtain ⟨C1, hC1, hC1b⟩ := exists_abs_bound_Icc
    (continuous_sourceAtomRealEnergyDerivative K x) (-2) 1
  obtain ⟨CW, hCW, hCWb⟩ := exists_abs_bound_Icc continuous_completeSourcePoleWeight 0 (2 * L₀)
  have h := hasDerivAt_integral_moving_upper (L₀ := L₀) (δ := L₀ / 2)
    (B := C1 * (6 / L₀) * CW)
    (F := fun y t => sourceAtomRealEnergy K x (1 - t / y) * completeSourcePoleWeight t)
    (F' := fun y t => sourceAtomRealEnergyDerivative K x (1 - t / y) * (t / y ^ 2) *
      completeSourcePoleWeight t)
    hL₀ (by positivity) (by linarith)
    (fun y hy t ht => by
      have hy0 := (window_coord hL₀ hy ht).1.ne'
      exact ((hasDerivAt_sourceAtomRealEnergy_transport K x (1 - t / y)).comp y
        (hasDerivAt_one_sub_div_param t hy0)).mul_const _)
    (fun y hy t ht => by
      obtain ⟨-, hω, hq, -, htI⟩ := window_coord hL₀ hy ht
      have ht0 : 0 ≤ t / y ^ 2 := div_nonneg ht.1.le (sq_nonneg _)
      rw [abs_mul, abs_mul, abs_of_nonneg ht0]
      exact mul_le_mul (mul_le_mul (hC1b _ hω) hq ht0 hC1) (hCWb _ htI) (abs_nonneg _)
        (by positivity))
    (fun y hy => by
      have hy0 : y ≠ 0 := by linarith [hy.1]
      exact (by fun_prop (disch := exact hy0) :
        Continuous fun t => sourceAtomRealEnergy K x (1 - t / y) *
          completeSourcePoleWeight t).continuousOn)
    ((by fun_prop (disch := exact hL₀.ne') :
        Continuous fun t => sourceAtomRealEnergyDerivative K x (1 - t / L₀) * (t / L₀ ^ 2) *
          completeSourcePoleWeight t).continuousOn)
    ((by fun_prop (disch := exact hL₀.ne') :
        Continuous fun t => sourceAtomRealEnergy K x (1 - t / L₀) *
          completeSourcePoleWeight t).intervalIntegrable _ _)
  refine h.congr_deriv ?_
  simp [div_self hL₀.ne']

/-! ## Archimedean channel -/

/-- `t ρ(t)` is bounded on `(0, T]`. -/
theorem abs_mul_archDensity_le {T C : ℝ} (hC : ∀ y ∈ Icc 0 T, |regularizedArchScale y| ≤ C)
    {t : ℝ} (ht : t ∈ Ioc 0 T) : |t * archDensity t| ≤ C := by
  rw [← regularizedArchScale_eq_mul_archDensity ht.1.ne']
  exact hC t ⟨ht.1.le, ht.2⟩

/-- **Archimedean channel derivative.**  The integrand is unbounded only through
`ρ(t) ~ 1/(2t)`; its parameter derivative carries a factor `t` and is bounded. -/
theorem hasDerivAt_archChannel {L₀ : ℝ} (hL₀ : 0 < L₀) :
    HasDerivAt
      (fun L => ∫ t in (0 : ℝ)..L, (sourceAtomRealEnergy K x (1 - t / L) -
        sourceAtomRealEnergy K x 1 * Real.exp (-t / 2)) * archDensity t)
      (-(sourceAtomRealEnergy K x 1 * Real.exp (-L₀ / 2) * archDensity L₀) +
        ∫ t in (0 : ℝ)..L₀, sourceAtomRealEnergyDerivative K x (1 - t / L₀) * (t / L₀ ^ 2) *
          archDensity t) L₀ := by
  obtain ⟨C1, hC1, hC1b⟩ := exists_abs_bound_Icc
    (continuous_sourceAtomRealEnergyDerivative K x) (-2) 1
  obtain ⟨CR, hCR, hCRb⟩ := exists_abs_bound_Icc continuous_regularizedArchScale 0 (2 * L₀)
  have hρ : ContinuousOn archDensity (Ioo 0 (L₀ + L₀ / 2)) :=
    continuousOn_archDensity.mono fun t ht => ht.1
  -- integrability of the base slice through a linear bound on the numerator
  have hint : IntervalIntegrable (fun t => (sourceAtomRealEnergy K x (1 - t / L₀) -
      sourceAtomRealEnergy K x 1 * Real.exp (-t / 2)) * archDensity t) volume 0 L₀ := by
    set N : ℝ → ℝ := fun t => sourceAtomRealEnergy K x (1 - t / L₀) -
      sourceAtomRealEnergy K x 1 * Real.exp (-t / 2) with hN
    set M := C1 / L₀ + |sourceAtomRealEnergy K x 1| / 2
    have hNd : ∀ t, HasDerivAt N (sourceAtomRealEnergyDerivative K x (1 - t / L₀) * (-(1 / L₀)) -
        sourceAtomRealEnergy K x 1 * (Real.exp (-t / 2) * (-1 / 2))) t := by
      intro t
      have h1 := (hasDerivAt_sourceAtomRealEnergy_transport K x (1 - t / L₀)).comp t
        (((hasDerivAt_id t).div_const L₀).const_sub 1)
      have h2 := ((((hasDerivAt_id t).neg).div_const 2).exp).const_mul
        (sourceAtomRealEnergy K x 1)
      refine (h1.sub h2).congr_deriv ?_
      simp only [Pi.neg_apply, id_eq]
    have hNb : ∀ t ∈ Icc (0 : ℝ) L₀, ‖sourceAtomRealEnergyDerivative K x (1 - t / L₀) *
        (-(1 / L₀)) - sourceAtomRealEnergy K x 1 * (Real.exp (-t / 2) * (-1 / 2))‖ ≤ M := by
      intro t ht
      have hω : 1 - t / L₀ ∈ Icc (-2 : ℝ) 1 := by
        have h0 : 0 ≤ t / L₀ := div_nonneg ht.1 hL₀.le
        have h1 : t / L₀ ≤ 1 := (div_le_one hL₀).mpr ht.2
        constructor <;> linarith
      have hexp : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
      rw [Real.norm_eq_abs]
      calc _ ≤ |sourceAtomRealEnergyDerivative K x (1 - t / L₀) * (-(1 / L₀))| +
            |sourceAtomRealEnergy K x 1 * (Real.exp (-t / 2) * (-1 / 2))| := abs_sub _ _
        _ ≤ C1 / L₀ + |sourceAtomRealEnergy K x 1| / 2 := by
          rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / L₀),
            abs_of_pos (Real.exp_pos _), abs_div, abs_neg, abs_one, abs_two]
          have := hC1b _ hω
          have hm1 : |sourceAtomRealEnergyDerivative K x (1 - t / L₀)| * (1 / L₀) ≤ C1 / L₀ := by
            rw [mul_one_div]; exact div_le_div_of_nonneg_right this hL₀.le
          have hm2 : |sourceAtomRealEnergy K x 1| * (Real.exp (-t / 2) * (1 / 2)) ≤
              |sourceAtomRealEnergy K x 1| / 2 := by
            have : Real.exp (-t / 2) * (1 / 2) ≤ 1 / 2 := by linarith
            calc _ ≤ |sourceAtomRealEnergy K x 1| * (1 / 2) :=
                  mul_le_mul_of_nonneg_left this (abs_nonneg _)
              _ = _ := by ring
          linarith
    have hNlin : ∀ t ∈ Icc (0 : ℝ) L₀, |N t| ≤ M * t := by
      intro t ht
      have := (convex_Icc (0 : ℝ) L₀).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun y _ => (hNd y).hasDerivWithinAt) hNb ⟨le_refl 0, hL₀.le⟩ ht
      have hN0 : N 0 = 0 := by simp [hN]
      rw [hN0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at this
      exact this
    have hM : 0 ≤ M := by positivity
    refine (intervalIntegrable_const (c := M * CR)).mono_fun' ?_ ?_
    · rw [uIoc_of_le hL₀.le]
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact ((by fun_prop (disch := exact hL₀.ne') : Continuous N).continuousOn).mul
        (continuousOn_archDensity.mono fun t ht => ht.1)
    · rw [uIoc_of_le hL₀.le]
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
      show ‖N t * archDensity t‖ ≤ M * CR
      have htI : t ∈ Icc (0 : ℝ) L₀ := ⟨ht.1.le, ht.2⟩
      have hρpos : 0 < archDensity t := archDensity_pos_of_pos ht.1
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρpos]
      have hR := abs_mul_archDensity_le (T := 2 * L₀) hCRb (t := t) ⟨ht.1, by linarith [ht.2]⟩
      rw [abs_mul, abs_of_pos ht.1, abs_of_pos hρpos] at hR
      calc |N t| * archDensity t ≤ M * t * archDensity t :=
            mul_le_mul_of_nonneg_right (hNlin t htI) hρpos.le
        _ = M * (t * archDensity t) := by ring
        _ ≤ M * CR := mul_le_mul_of_nonneg_left hR hM
  have h := hasDerivAt_integral_moving_upper (L₀ := L₀) (δ := L₀ / 2)
    (B := C1 * (4 / L₀ ^ 2) * CR)
    (F := fun y t => (sourceAtomRealEnergy K x (1 - t / y) -
      sourceAtomRealEnergy K x 1 * Real.exp (-t / 2)) * archDensity t)
    (F' := fun y t => sourceAtomRealEnergyDerivative K x (1 - t / y) * (t / y ^ 2) *
      archDensity t)
    hL₀ (by positivity) (by linarith)
    (fun y hy t ht => by
      have hy0 := (window_coord hL₀ hy ht).1.ne'
      have := (((hasDerivAt_sourceAtomRealEnergy_transport K x (1 - t / y)).comp y
        (hasDerivAt_one_sub_div_param t hy0)).sub_const
          (sourceAtomRealEnergy K x 1 * Real.exp (-t / 2))).mul_const (archDensity t)
      exact this)
    (fun y hy t ht => by
      obtain ⟨hy0, hω, -, hq, htI⟩ := window_coord hL₀ hy ht
      have hρpos : 0 < archDensity t := archDensity_pos_of_pos ht.1
      have hR := abs_mul_archDensity_le (T := 2 * L₀) hCRb (t := t) ⟨ht.1, htI.2⟩
      have heq : sourceAtomRealEnergyDerivative K x (1 - t / y) * (t / y ^ 2) * archDensity t =
          sourceAtomRealEnergyDerivative K x (1 - t / y) * (1 / y ^ 2) * (t * archDensity t) := by
        field_simp
      rw [heq, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1 / y ^ 2)]
      exact mul_le_mul (mul_le_mul (hC1b _ hω) hq (by positivity) hC1) hR (abs_nonneg _)
        (by positivity))
    (fun y hy => by
      have hy0 : y ≠ 0 := by linarith [hy.1]
      exact ((by fun_prop (disch := exact hy0) :
        Continuous fun t => sourceAtomRealEnergy K x (1 - t / y) -
          sourceAtomRealEnergy K x 1 * Real.exp (-t / 2)).continuousOn).mul hρ)
    (((by fun_prop (disch := exact hL₀.ne') :
        Continuous fun t => sourceAtomRealEnergyDerivative K x (1 - t / L₀) *
          (t / L₀ ^ 2)).continuousOn).mul hρ)
    hint
  refine h.congr_deriv ?_
  simp only [div_self hL₀.ne', sub_self, sourceAtomRealEnergy_zero, zero_sub]
  ring

end Channels

/-! ## Regular channel form of the prime-free physical value -/

/-- Regular pole density `t W(t)`. -/
def poleScale (t : ℝ) : ℝ := t * completeSourcePoleWeight t

@[fun_prop] theorem continuous_poleScale : Continuous poleScale := by
  unfold poleScale; fun_prop

/-- Below `log 2` the physical value has no prime terms. -/
theorem productionArithmeticRealValue_eq_channels_of_lt_log_two {L : ℝ}
    (hL2 : L < Real.log 2) (f : ℝ → ℝ) :
    productionArithmeticRealValue L f =
      (∫ t in (0 : ℝ)..L, f t * completeSourcePoleWeight t) -
        ∫ t in (0 : ℝ)..L, f t * archDensity t := by
  unfold productionArithmeticRealValue productionArithmeticComplexValue
    dictionaryCompletePhysicalRHS
  rw [Icc_two_floor_exp_eq_empty hL2, Finset.sum_empty, sub_zero, Complex.sub_re]
  have hpole : Complex.re (∫ t in (0 : ℝ)..L, (f t : ℂ) * (completeSourcePoleWeight t : ℂ)) =
      ∫ t in (0 : ℝ)..L, f t * completeSourcePoleWeight t := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_re] using
      congrArg Complex.re (intervalIntegral.integral_ofReal
        (f := fun t : ℝ => f t * completeSourcePoleWeight t) (a := (0 : ℝ)) (b := L))
  have harch : Complex.re (∫ t in (0 : ℝ)..L, (f t : ℂ) * (archDensity t : ℂ)) =
      ∫ t in (0 : ℝ)..L, f t * archDensity t := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_re] using
      congrArg Complex.re (intervalIntegral.integral_ofReal
        (f := fun t : ℝ => f t * archDensity t) (a := (0 : ℝ)) (b := L))
  rw [hpole, harch]

/-- A test vanishing linearly at `0` has a regular channel form: `t ρ(t)` is the
continuous `regularizedArchScale`. -/
theorem productionArithmeticRealValue_mul_id_eq {L : ℝ} (hL : 0 < L)
    (hL2 : L < Real.log 2) (h : ℝ → ℝ) :
    productionArithmeticRealValue L (fun t => t * h t) =
      (∫ t in (0 : ℝ)..L, h t * poleScale t) -
        ∫ t in (0 : ℝ)..L, h t * regularizedArchScale t := by
  rw [productionArithmeticRealValue_eq_channels_of_lt_log_two hL2]
  congr 1
  · exact intervalIntegral.integral_congr fun t _ => by unfold poleScale; ring
  · refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hL.le] at ht
    rw [regularizedArchScale_eq_mul_archDensity ht.1.ne']
    ring

theorem productionArithmeticRealValue_clamp_mul_id {L : ℝ} (hL : 0 < L)
    (hL2 : L < Real.log 2) {f : ℝ → ℝ} (h : ℝ → ℝ) (hfh : ∀ t, f t = t * h t) :
    productionArithmeticRealValue L (productionPhysicalClamp L f) =
      (∫ t in (0 : ℝ)..L, h t * poleScale t) -
        ∫ t in (0 : ℝ)..L, h t * regularizedArchScale t := by
  rw [productionArithmeticRealValue_congr_on_Icc hL (g := fun t => t * h t)
    (fun t ht => by rw [productionPhysicalClamp_eq ht, hfh])]
  exact productionArithmeticRealValue_mul_id_eq hL hL2 h

/-! ## Mixed source derivative polarization -/

theorem sourceEntryDerivative_symm (ω : ℝ) (n m : ℤ) :
    sourceEntryDerivative ω n m = sourceEntryDerivative ω m n := by
  unfold sourceEntryDerivative
  by_cases h : n = m
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    have h1 : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr h
    have h2 : ((m - n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (Ne.symm h)
    rw [div_eq_div_iff h1 h2]
    push_cast
    ring

theorem sourceAtomPairingDerivative_swap (K : ℕ) (x y : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) :
    sourceAtomPairingDerivative K y x ω = conj (sourceAtomPairingDerivative K x y ω) := by
  unfold sourceAtomPairingDerivative
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sourceEntryDerivative_symm ω (centeredIndex K j)]
  rw [Complex.real_smul, Complex.real_smul, map_mul, map_mul, Complex.conj_ofReal]
  simp only [Complex.star_def, RCLike.conj_conj]
  ring

theorem sourceAtomPairingDerivative_polarization (K : ℕ)
    (x y : EuclideanSpace ℂ (Fin (2 * K + 1))) (ω : ℝ) :
    sourceAtomPairingDerivative K (x + y) (x + y) ω -
        sourceAtomPairingDerivative K (x - y) (x - y) ω =
      2 * sourceAtomPairingDerivative K x y ω + 2 * sourceAtomPairingDerivative K y x ω := by
  unfold sourceAtomPairingDerivative
  simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply, star_add, star_sub,
    ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.real_smul]
  ring

/-- Real polarization of the mixed source derivative through the real energy
derivative. -/
theorem sourceAtomPairingDerivative_re_polarization (K : ℕ)
    (x y : EuclideanSpace ℂ (Fin (2 * K + 1))) (ω : ℝ) :
    Complex.re (sourceAtomPairingDerivative K x y ω) =
      (sourceAtomRealEnergyDerivative K (x + y) ω -
        sourceAtomRealEnergyDerivative K (x - y) ω) / 4 := by
  rw [← sourceAtomPairingDerivative_self_re_eq_realEnergyDerivative,
    ← sourceAtomPairingDerivative_self_re_eq_realEnergyDerivative, ← Complex.sub_re,
    sourceAtomPairingDerivative_polarization, sourceAtomPairingDerivative_swap K x y]
  simp [Complex.mul_re]
  ring

/-! ## F04 below `log 2` -/

section F04

variable (K : ℕ)

/-- `e₁` channel against a continuous density `V`. -/
def primeFreeFirstChannel (x : EuclideanSpace ℂ (Fin (2 * K + 1))) (L : ℝ) (V : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..L, sourceAtomRealEnergyDerivative K x (1 - t / L) * (1 / L ^ 2) * V t

/-- `e₂` channel against a continuous density `V`. -/
def primeFreeSecondChannel (x : EuclideanSpace ℂ (Fin (2 * K + 1))) (L : ℝ) (V : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..L, sourceAtomRealEnergySecondDerivative K x (1 - t / L) * (t / L ^ 4) * V t

/-- Mixed channel against a continuous density `V`. -/
def primeFreeMixedChannel (x y : EuclideanSpace ℂ (Fin (2 * K + 1))) (L : ℝ) (V : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..L, Complex.re (sourceAtomPairingDerivative K x y (1 - t / L)) *
    (1 / L ^ 2) * V t

theorem hasDerivAt_inv_sq {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-2 / x ^ 3) x := by
  have h := (hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx)
  have hfun : (fun y : ℝ => y ^ 2)⁻¹ = fun y => 1 / y ^ 2 := by
    funext y; rw [Pi.inv_apply, one_div]
  rw [hfun] at h
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **Second-order Leibniz step.**  The boundary term vanishes because
`e₁(0) = 0` on boundary-flat vectors. -/
theorem hasDerivAt_primeFreeFirstChannel (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {V : ℝ → ℝ} (hV : Continuous V) {L₀ : ℝ} (hL₀ : 0 < L₀)
    (h0 : sourceAtomRealEnergyDerivative K x 0 = 0) :
    HasDerivAt (fun L => primeFreeFirstChannel K x L V)
      (primeFreeSecondChannel K x L₀ V - 2 / L₀ * primeFreeFirstChannel K x L₀ V) L₀ := by
  obtain ⟨C1, hC1, hC1b⟩ := exists_abs_bound_Icc
    (continuous_sourceAtomRealEnergyDerivative K x) (-2) 1
  obtain ⟨C2, hC2, hC2b⟩ := exists_abs_bound_Icc
    (continuous_sourceAtomRealEnergySecondDerivative K x) (-2) 1
  obtain ⟨CV, hCV, hCVb⟩ := exists_abs_bound_Icc hV 0 (2 * L₀)
  have h := hasDerivAt_integral_moving_upper (L₀ := L₀) (δ := L₀ / 2)
    (B := (C2 * (6 / L₀) * (4 / L₀ ^ 2) + C1 * (16 / L₀ ^ 3)) * CV)
    (F := fun y t => sourceAtomRealEnergyDerivative K x (1 - t / y) * (1 / y ^ 2) * V t)
    (F' := fun y t => (sourceAtomRealEnergySecondDerivative K x (1 - t / y) * (t / y ^ 2) *
      (1 / y ^ 2) + sourceAtomRealEnergyDerivative K x (1 - t / y) * (-2 / y ^ 3)) * V t)
    hL₀ (by positivity) (by linarith)
    (fun y hy t ht => by
      have hy0 := (window_coord hL₀ hy ht).1.ne'
      exact (((hasDerivAt_sourceAtomRealEnergyDerivative_transport K x (1 - t / y)).comp y
        (hasDerivAt_one_sub_div_param t hy0)).mul (hasDerivAt_inv_sq hy0)).mul_const (V t))
    (fun y hy t ht => by
      obtain ⟨hypos, hω, hq, hq2, htI⟩ := window_coord hL₀ hy ht
      have hyL : L₀ / 2 < y := by linarith [hy.1]
      have hcube : 2 / y ^ 3 ≤ 16 / L₀ ^ 3 := by
        have h3 : (L₀ / 2) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by positivity) hyL.le 3
        calc 2 / y ^ 3 ≤ 2 / (L₀ / 2) ^ 3 :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) h3
          _ = 16 / L₀ ^ 3 := by field_simp; ring
      have ht0 : 0 ≤ t / y ^ 2 := div_nonneg ht.1.le (sq_nonneg _)
      have hA : |sourceAtomRealEnergySecondDerivative K x (1 - t / y) * (t / y ^ 2) *
          (1 / y ^ 2)| ≤ C2 * (6 / L₀) * (4 / L₀ ^ 2) := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_pos (by positivity : 0 < 1 / y ^ 2)]
        exact mul_le_mul (mul_le_mul (hC2b _ hω) hq ht0 hC2) hq2 (by positivity)
          (by positivity)
      have hB : |sourceAtomRealEnergyDerivative K x (1 - t / y) * (-2 / y ^ 3)| ≤
          C1 * (16 / L₀ ^ 3) := by
        rw [abs_mul, neg_div, abs_neg, abs_of_pos (by positivity : 0 < 2 / y ^ 3)]
        exact mul_le_mul (hC1b _ hω) hcube (by positivity) hC1
      rw [abs_mul]
      exact mul_le_mul ((abs_add_le _ _).trans (add_le_add hA hB)) (hCVb _ htI)
        (abs_nonneg _) (by positivity))
    (fun y hy => by
      exact (by fun_prop : Continuous fun t =>
        sourceAtomRealEnergyDerivative K x (1 - t / y) * (1 / y ^ 2) * V t).continuousOn)
    ((by fun_prop : Continuous fun t =>
        (sourceAtomRealEnergySecondDerivative K x (1 - t / L₀) * (t / L₀ ^ 2) *
          (1 / L₀ ^ 2) + sourceAtomRealEnergyDerivative K x (1 - t / L₀) *
            (-2 / L₀ ^ 3)) * V t).continuousOn)
    ((by fun_prop : Continuous fun t =>
        sourceAtomRealEnergyDerivative K x (1 - t / L₀) * (1 / L₀ ^ 2) * V t).intervalIntegrable
          _ _)
  refine h.congr_deriv ?_
  have hF0 : sourceAtomRealEnergyDerivative K x (1 - L₀ / L₀) * (1 / L₀ ^ 2) * V L₀ = 0 := by
    rw [div_self hL₀.ne', sub_self, h0]; ring
  unfold primeFreeSecondChannel primeFreeFirstChannel
  rw [hF0, zero_add, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun t => sourceAtomRealEnergySecondDerivative K x
        (1 - t / L₀) * (t / L₀ ^ 4) * V t).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => 2 / L₀ * (sourceAtomRealEnergyDerivative K x
        (1 - t / L₀) * (1 / L₀ ^ 2) * V t)).intervalIntegrable _ _)]
  exact intervalIntegral.integral_congr fun t _ => by field_simp; ring

/-- The fixed even energy below `log 2`, in regularized form without prime terms. -/
theorem productionContactFixedEnergy_even_eq_regularized {L : ℝ} (hL : 0 < L)
    (hL2 : L < Real.log 2) (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFixedEnergy .even L K z =
      (∫ t in (0 : ℝ)..L, sourceAtomRealEnergy K (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (1 - t / L) * completeSourcePoleWeight t) -
        ((∫ t in (0 : ℝ)..L, (sourceAtomRealEnergy K (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
            (1 - t / L) - sourceAtomRealEnergy K (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 1 *
              Real.exp (-t / 2)) * archDensity t) +
          sourceAtomRealEnergy K (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 1 * wCorrection L) := by
  have h := parityCanonicalSourceEnergy_eq_matrixRealEnergy .even L K z
  unfold parityCanonicalSourceEnergy at h
  unfold productionContactFixedEnergy
  rw [h, matrixRealEnergy_canonical_eq_regularized K _ hL, Icc_two_floor_exp_eq_empty hL2,
    Finset.sum_empty, sub_zero]

/-- **First variation below `log 2`** in regular channel form. -/
theorem productionContactFirstVariation_even_eq_channels {L : ℝ} (hL : 0 < L)
    (hL2 : L < Real.log 2) (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFirstVariation .even L K z =
      primeFreeFirstChannel K z L poleScale -
        primeFreeFirstChannel K z L regularizedArchScale := by
  have hP := hasDerivAt_poleChannel K (z : EuclideanSpace ℂ (Fin (2 * K + 1))) hL
  have hG := hasDerivAt_archChannel K (z : EuclideanSpace ℂ (Fin (2 * K + 1))) hL
  have hw := (hasDerivAt_wCorrection hL).const_mul
    (sourceAtomRealEnergy K (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 1)
  have hE := (hP.sub (hG.add hw)).congr_of_eventuallyEq
    (f₁ := fun s => productionContactFixedEnergy .even s K z) (by
      filter_upwards [Ioo_mem_nhds hL hL2] with s hs
      exact productionContactFixedEnergy_even_eq_regularized K hs.1 hs.2 z)
  unfold productionContactFirstVariation
  rw [hE.deriv]
  unfold primeFreeFirstChannel poleScale
  have harch : (∫ t in (0 : ℝ)..L, sourceAtomRealEnergyDerivative K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - t / L) * (t / L ^ 2) * archDensity t) =
      ∫ t in (0 : ℝ)..L, sourceAtomRealEnergyDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - t / L) * (1 / L ^ 2) *
          regularizedArchScale t := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hL.le] at ht
    rw [regularizedArchScale_eq_mul_archDensity ht.1.ne']
    ring
  have hpole : (∫ t in (0 : ℝ)..L, sourceAtomRealEnergyDerivative K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - t / L) * (t / L ^ 2) *
        completeSourcePoleWeight t) =
      ∫ t in (0 : ℝ)..L, sourceAtomRealEnergyDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - t / L) * (1 / L ^ 2) *
          (t * completeSourcePoleWeight t) :=
    intervalIntegral.integral_congr fun t _ => by ring
  rw [← harch, ← hpole]
  ring

theorem productionFirstDerivativePhysicalValue_eq_channels {L : ℝ} (hL : 0 < L)
    (hL2 : L < Real.log 2) (z : euclideanEvenBoundaryFlatSubspace K) :
    productionArithmeticRealValue L (productionFirstDerivativePhysicalTest L K z) =
      primeFreeFirstChannel K z L poleScale -
        primeFreeFirstChannel K z L regularizedArchScale := by
  unfold productionFirstDerivativePhysicalTest
  rw [productionArithmeticRealValue_clamp_mul_id hL hL2
    (fun t => sourceAtomRealEnergyDerivative K (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (1 - t / L) * (1 / L ^ 2))
    (fun t => by unfold productionFirstDerivativePhysicalRaw; ring)]
  rfl

theorem productionSecondDerivativePhysicalValue_eq_channels {L : ℝ} (hL : 0 < L)
    (hL2 : L < Real.log 2) (z : euclideanEvenBoundaryFlatSubspace K) :
    productionArithmeticRealValue L (productionSecondDerivativePhysicalTest L K z) =
      primeFreeSecondChannel K z L poleScale -
        primeFreeSecondChannel K z L regularizedArchScale := by
  unfold productionSecondDerivativePhysicalTest
  rw [productionArithmeticRealValue_clamp_mul_id hL hL2
    (fun t => sourceAtomRealEnergySecondDerivative K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - t / L) * (t / L ^ 4))
    (fun t => by unfold productionSecondDerivativePhysicalRaw; ring)]
  rfl

theorem productionMixedDerivativePhysicalValue_eq_channels {L : ℝ} (hL : 0 < L)
    (hL2 : L < Real.log 2) (z w : euclideanEvenBoundaryFlatSubspace K) :
    productionArithmeticRealValue L (productionMixedDerivativePhysicalTest L K z w) =
      primeFreeMixedChannel K z w L poleScale -
        primeFreeMixedChannel K z w L regularizedArchScale := by
  unfold productionMixedDerivativePhysicalTest
  rw [productionArithmeticRealValue_clamp_mul_id hL hL2
    (fun t => Complex.re (sourceAtomPairingDerivative K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (w : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (1 - t / L)) * (1 / L ^ 2))
    (fun t => by unfold productionMixedDerivativePhysicalRaw; ring)]
  rfl

theorem primeFreeMixedChannel_polarization (x y : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {L : ℝ} {V : ℝ → ℝ} (hV : Continuous V) :
    primeFreeMixedChannel K x y L V =
      (primeFreeFirstChannel K (x + y) L V - primeFreeFirstChannel K (x - y) L V) / 4 := by
  unfold primeFreeMixedChannel primeFreeFirstChannel
  rw [← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun t => sourceAtomRealEnergyDerivative K (x + y)
        (1 - t / L) * (1 / L ^ 2) * V t).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => sourceAtomRealEnergyDerivative K (x - y)
        (1 - t / L) * (1 / L ^ 2) * V t).intervalIntegrable _ _),
    ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [sourceAtomPairingDerivative_re_polarization]
  ring

/-- Symmetric polarization of the compressed aperture derivative. -/
theorem re_inner_canonicalEvenApertureFirst_polarization {L : ℝ} (hL : 0 < L)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    Complex.re (inner ℂ z (canonicalEvenApertureFirst L K w)) =
      (productionContactFirstVariation .even L K (z + w) -
        productionContactFirstVariation .even L K (z - w)) / 4 := by
  rw [canonicalEven_firstVariation_eq_inner hL, canonicalEven_firstVariation_eq_inner hL]
  have hs := canonicalEvenApertureFirst_isSymmetric hL K
  have h1 : inner ℂ (canonicalEvenApertureFirst L K w) z =
      conj (inner ℂ z (canonicalEvenApertureFirst L K w)) :=
    (inner_conj_symm (canonicalEvenApertureFirst L K w) z).symm
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right]
  rw [hs z w, h1]
  simp only [Complex.add_re, Complex.sub_re, Complex.conj_re]
  ring

/-- **M65: prime-free F04 derivative authority.**  For `0 < L < log 2` there are no
prime samples, and the three F04 identities hold unconditionally: the first
variation, the Euler-corrected fixed second variation, and the mixed aperture
derivative all equal their production physical values. -/
theorem productionContactF04DerivativeAuthority_of_lt_log_two {L : ℝ} (hL : 0 < L)
    (hL2 : L < Real.log 2) :
    ProductionContactF04DerivativeAuthority L K where
  first z := by
    rw [productionContactFirstVariation_even_eq_channels K hL hL2,
      productionFirstDerivativePhysicalValue_eq_channels K hL hL2]
  fixedSecondEuler z := by
    have h0 := sourceAtomRealEnergyDerivative_zero_of_boundaryFlat K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (evenBoundaryFlatRawCoefficients_boundaryFlat K z)
    have hd : HasDerivAt (fun s => primeFreeFirstChannel K z s poleScale -
        primeFreeFirstChannel K z s regularizedArchScale) _ L :=
      (hasDerivAt_primeFreeFirstChannel K _ continuous_poleScale hL h0).sub
        (hasDerivAt_primeFreeFirstChannel K _ continuous_regularizedArchScale hL h0)
    have hev : (fun s => productionContactFirstVariation .even s K z) =ᶠ[𝓝 L]
        fun s => primeFreeFirstChannel K z s poleScale -
          primeFreeFirstChannel K z s regularizedArchScale := by
      filter_upwards [Ioo_mem_nhds hL hL2] with s hs
      exact productionContactFirstVariation_even_eq_channels K hs.1 hs.2 z
    unfold productionContactFixedSecondVariation
    rw [hev.deriv_eq, hd.deriv, productionContactFirstVariation_even_eq_channels K hL hL2,
      productionSecondDerivativePhysicalValue_eq_channels K hL hL2]
    ring
  mixed z w := by
    rw [re_inner_canonicalEvenApertureFirst_polarization K hL,
      productionContactFirstVariation_even_eq_channels K hL hL2,
      productionContactFirstVariation_even_eq_channels K hL hL2,
      productionMixedDerivativePhysicalValue_eq_channels K hL hL2,
      primeFreeMixedChannel_polarization K _ _ continuous_poleScale,
      primeFreeMixedChannel_polarization K _ _ continuous_regularizedArchScale]
    simp only [Submodule.coe_add, Submodule.coe_sub]
    ring

end F04

/-- Below `log 2` the Euler-corrected second pairing equals the production
saturation gap with no F04 hypothesis. -/
theorem canonicalSecondPairing_euler_eq_productionSaturationGap_of_lt_log_two
    {L : ℝ} (hL : 0 < L) (hL2 : L < Real.log 2) (K : ℕ) (hK : 2 ≤ K)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    productionContactSaturationGap L K z w =
      canonicalContactSecondPairing L K z w +
        2 * productionContactFirstVariation .even L K z / L :=
  canonicalSecondPairing_euler_eq_productionSaturationGap hL K hK z w
    (productionContactF04DerivativeAuthority_of_lt_log_two K hL hL2)

end Zeta23.CCM

#print axioms Zeta23.CCM.hasDerivAt_integral_moving_upper
#print axioms Zeta23.CCM.matrixRealEnergy_canonical_eq_regularized
#print axioms Zeta23.CCM.hasDerivAt_wCorrection
#print axioms Zeta23.CCM.hasDerivAt_poleChannel
#print axioms Zeta23.CCM.hasDerivAt_archChannel
#print axioms Zeta23.CCM.productionArithmeticRealValue_eq_channels_of_lt_log_two
#print axioms Zeta23.CCM.sourceAtomPairingDerivative_re_polarization
#print axioms Zeta23.CCM.hasDerivAt_primeFreeFirstChannel
#print axioms Zeta23.CCM.productionContactFirstVariation_even_eq_channels
#print axioms Zeta23.CCM.re_inner_canonicalEvenApertureFirst_polarization
#print axioms Zeta23.CCM.productionContactF04DerivativeAuthority_of_lt_log_two
#print axioms Zeta23.CCM.canonicalSecondPairing_euler_eq_productionSaturationGap_of_lt_log_two
