import Zeta23.CCM.FinitePhysicalNormalization
import Zeta23.CCM.CanonicalPoleNeutralPublicAPI
import Zeta23.CCM.NativeDetectorSchur
import Zeta23.CCM.DetectorRetainedSchurState
import Zeta23.CCM.OriginalDetectorPaddedFiniteH1Rate
import Zeta23.ExceptionalZero.BoundaryFlatFiniteWeil
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The actual normalized-mode physical realization, its adjoint, and its legal H1 bound. -/

noncomputable section
open Set Complex MeasureTheory Matrix
open scoped Topology ComplexConjugate

namespace Zeta23.CCM

abbrev CanonicalPhysicalL2 := Lp ℂ 2 (volume : Measure ℝ)

theorem finitePhysicalSynthesis_add (L : ℝ) (K : ℕ)
    (u v : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    finitePhysicalSynthesis L K (u + v) =
      finitePhysicalSynthesis L K u + finitePhysicalSynthesis L K v := by
  funext x
  change (∑ i, (u i + v i) * localizedZeroExtendedMode L (centeredIndex K i) x) = _
  simp only [add_mul, Finset.sum_add_distrib]
  rfl

theorem finitePhysicalSynthesis_sub (L : ℝ) (K : ℕ)
    (u v : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    finitePhysicalSynthesis L K (u - v) =
      finitePhysicalSynthesis L K u - finitePhysicalSynthesis L K v := by
  funext x
  change (∑ i, (u i - v i) * localizedZeroExtendedMode L (centeredIndex K i) x) = _
  simp only [sub_mul, Finset.sum_sub_distrib]
  rfl

def canonicalPhysicalValue (L : ℝ) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) : CanonicalPhysicalL2 :=
  (localizedFiniteVector_memLp_two L K ((EuclideanSpace.equiv _ ℂ) v)).toLp
    (finitePhysicalSynthesis L K v)

theorem canonicalPhysicalValue_ae (L : ℝ) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    canonicalPhysicalValue L K v =ᵐ[volume] finitePhysicalSynthesis L K v :=
  MemLp.coeFn_toLp _

private theorem norm_sq_toLp_eq_integral {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have he : inner ℂ (hf.toLp f) (hf.toLp f) = ∫ x : ℝ, ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), he, integral_complex_ofReal]
  rfl

theorem canonicalPhysicalValue_norm {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖canonicalPhysicalValue L K v‖ = ‖v‖ := by
  have he := norm_sq_toLp_eq_integral
    (localizedFiniteVector_memLp_two L K ((EuclideanSpace.equiv _ ℂ) v))
  change ‖canonicalPhysicalValue L K v‖ ^ 2 = ∫ x : ℝ, ‖finitePhysicalSynthesis L K v x‖ ^ 2 at he
  rw [finitePhysicalSynthesis_energy hL K v] at he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

def canonicalPhysicalIsometry {L : ℝ} (hL : 0 < L) (K : ℕ) :
    EuclideanSpace ℂ (Fin (2 * K + 1)) →ₗᵢ[ℂ] CanonicalPhysicalL2 where
  toFun := canonicalPhysicalValue L K
  map_add' u v := by
    apply Lp.ext
    filter_upwards [canonicalPhysicalValue_ae L K (u + v), canonicalPhysicalValue_ae L K u,
      canonicalPhysicalValue_ae L K v, Lp.coeFn_add (canonicalPhysicalValue L K u)
        (canonicalPhysicalValue L K v)] with x huv hu hv hadd
    rw [huv, hadd]
    change finitePhysicalSynthesis L K (u + v) x =
      canonicalPhysicalValue L K u x + canonicalPhysicalValue L K v x
    rw [hu, hv]
    exact congrFun (finitePhysicalSynthesis_add L K u v) x
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [canonicalPhysicalValue_ae L K (c • v), canonicalPhysicalValue_ae L K v,
      Lp.coeFn_smul c (canonicalPhysicalValue L K v)] with x hcv hv hsmul
    simp only [RingHom.id_apply]
    rw [hcv, hsmul]
    change finitePhysicalSynthesis L K (c • v) x = c • canonicalPhysicalValue L K v x
    rw [hv]
    exact congrFun (finitePhysicalSynthesis_smul L K c v) x
  norm_map' := canonicalPhysicalValue_norm hL K

theorem canonicalPhysicalIsometry_ae {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    canonicalPhysicalIsometry hL K v =ᵐ[volume] finitePhysicalSynthesis L K v :=
  canonicalPhysicalValue_ae L K v

def canonicalPhysicalProjection {L : ℝ} (hL : 0 < L) (K : ℕ) :
    CanonicalPhysicalL2 →L[ℂ] EuclideanSpace ℂ (Fin (2 * K + 1)) :=
  (canonicalPhysicalIsometry hL K).toContinuousLinearMap.adjoint

theorem canonicalPhysicalProjection_synthesis {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    canonicalPhysicalProjection hL K (canonicalPhysicalIsometry hL K v) = v :=
  congrArg (fun A => A v) (canonicalPhysicalIsometry hL K).adjoint_comp_self

theorem canonicalPhysicalProjection_inner {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) (g : CanonicalPhysicalL2) :
    inner ℂ v (canonicalPhysicalProjection hL K g) =
      ∫ x : ℝ, conj (finitePhysicalSynthesis L K v x) * g x := by
  rw [canonicalPhysicalProjection, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [canonicalPhysicalIsometry_ae hL K v] with x hx
  change inner ℂ (canonicalPhysicalIsometry hL K v x) (g x) = _
  rw [hx]
  simp only [RCLike.inner_apply, mul_comm]

theorem canonicalPhysicalIsometry_centeredZeroExtend {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hNM : N ≤ M) (v : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    canonicalPhysicalIsometry hL M (euclideanCenteredZeroExtend hNM v) =
      canonicalPhysicalIsometry hL N v := by
  apply Lp.ext
  filter_upwards [canonicalPhysicalIsometry_ae hL M (euclideanCenteredZeroExtend hNM v),
    canonicalPhysicalIsometry_ae hL N v] with x hM hN
  rw [hM, hN]
  change localizedFiniteVector L M ((EuclideanSpace.equiv _ ℂ)
      (euclideanCenteredZeroExtend hNM v)) x =
    localizedFiniteVector L N ((EuclideanSpace.equiv _ ℂ) v) x
  rw [euclideanCenteredZeroExtend_coordinates, localizedFiniteVector_centeredZeroExtend]

def canonicalNativeCoefficientInclusion (σ : ReversalParity) (L : ℝ) (K : ℕ) :
    nativePoleNeutralParitySpace σ L K →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (2 * K + 1)) := by
  cases σ
  · exact (euclideanEvenBoundaryFlatSubspace K).subtypeₗᵢ.comp
      (poleNeutralEvenSubspace L K).subtypeₗᵢ
  · exact (euclideanOddBoundaryFlatSubspace K).subtypeₗᵢ.comp
      (poleNeutralOddSubspace L K).subtypeₗᵢ

def canonicalNativePhysicalIsometry (σ : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    nativePoleNeutralParitySpace σ L K →ₗᵢ[ℂ] CanonicalPhysicalL2 :=
  (canonicalPhysicalIsometry hL K).comp (canonicalNativeCoefficientInclusion σ L K)

def canonicalNativePhysicalProjection (σ : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    CanonicalPhysicalL2 →L[ℂ] nativePoleNeutralParitySpace σ L K :=
  (canonicalNativePhysicalIsometry σ hL K).toContinuousLinearMap.adjoint

theorem canonicalNativePhysicalIsometry_centeredZeroExtend (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) {N M : ℕ} (hNM : N ≤ M)
    (v : nativePoleNeutralParitySpace σ L N) :
    canonicalNativePhysicalIsometry σ hL M (nativePoleNeutralParityCenteredZeroExtend σ L hNM v) =
      canonicalNativePhysicalIsometry σ hL N v := by
  have hc : canonicalNativeCoefficientInclusion σ L M
      (nativePoleNeutralParityCenteredZeroExtend σ L hNM v) =
      euclideanCenteredZeroExtend hNM (canonicalNativeCoefficientInclusion σ L N v) := by
    cases σ <;> rfl
  change canonicalPhysicalIsometry hL M (canonicalNativeCoefficientInclusion σ L M
    (nativePoleNeutralParityCenteredZeroExtend σ L hNM v)) =
      canonicalPhysicalIsometry hL N (canonicalNativeCoefficientInclusion σ L N v)
  rw [hc, canonicalPhysicalIsometry_centeredZeroExtend hL hNM]

theorem canonicalNativePhysicalIsometry_predecessor (σ : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL)
    (v : nativePoleNeutralParitySpace σ L (s.cutoff - 1)) :
    canonicalNativePhysicalIsometry σ hL Kd (nativeDetectorPredecessorEmbedding σ s v) =
      canonicalNativePhysicalIsometry σ hL (s.cutoff - 1) v :=
  canonicalNativePhysicalIsometry_centeredZeroExtend σ hL _ v

theorem canonicalNativePhysicalProjection_synthesis (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (v : nativePoleNeutralParitySpace σ L K) :
    canonicalNativePhysicalProjection σ hL K (canonicalNativePhysicalIsometry σ hL K v) = v :=
  congrArg (fun A => A v) (canonicalNativePhysicalIsometry σ hL K).adjoint_comp_self

theorem canonicalNativePhysicalIsometry_ae (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (v : nativePoleNeutralParitySpace σ L K) :
    canonicalNativePhysicalIsometry σ hL K v =ᵐ[volume]
      finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v) :=
  canonicalPhysicalIsometry_ae hL K _

theorem canonicalNativePhysicalProjection_inner (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (v : nativePoleNeutralParitySpace σ L K)
    (g : CanonicalPhysicalL2) :
    inner ℂ v (canonicalNativePhysicalProjection σ hL K g) =
      ∫ x : ℝ, conj (finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v) x) * g x := by
  rw [canonicalNativePhysicalProjection, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [canonicalNativePhysicalIsometry_ae σ hL K v] with x hx
  change inner ℂ (canonicalNativePhysicalIsometry σ hL K v x) (g x) = _
  rw [hx]
  simp only [RCLike.inner_apply, mul_comm]

theorem canonicalNativePhysicalProjection_orthogonal (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (v : nativePoleNeutralParitySpace σ L K)
    (g : CanonicalPhysicalL2) :
    inner ℂ (canonicalNativePhysicalIsometry σ hL K v)
      (g - canonicalNativePhysicalIsometry σ hL K (canonicalNativePhysicalProjection σ hL K g)) = 0 := by
  rw [inner_sub_right, (canonicalNativePhysicalIsometry σ hL K).inner_map_map]
  exact sub_eq_zero.mpr
    ((canonicalNativePhysicalIsometry σ hL K).toContinuousLinearMap.adjoint_inner_right v g).symm

theorem canonicalNativePhysicalProjection_norm_le (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (g : CanonicalPhysicalL2) :
    ‖canonicalNativePhysicalProjection σ hL K g‖ ≤ ‖g‖ := by
  let v := canonicalNativePhysicalProjection σ hL K g
  have hi : inner ℂ v v = inner ℂ (canonicalNativePhysicalIsometry σ hL K v) g :=
    (canonicalNativePhysicalIsometry σ hL K).toContinuousLinearMap.adjoint_inner_right v g
  have he : ‖v‖ ^ 2 ≤ ‖v‖ * ‖g‖ := by
    calc
      _ = (inner ℂ v v).re := norm_sq_eq_re_inner (𝕜 := ℂ) v
      _ = (inner ℂ (canonicalNativePhysicalIsometry σ hL K v) g).re := congrArg Complex.re hi
      _ ≤ ‖canonicalNativePhysicalIsometry σ hL K v‖ * ‖g‖ := by
        simpa only [RCLike.re_eq_complex_re] using
          re_inner_le_norm (𝕜 := ℂ) (canonicalNativePhysicalIsometry σ hL K v) g
      _ = _ := by rw [(canonicalNativePhysicalIsometry σ hL K).norm_map]
  by_cases hz : ‖v‖ = 0
  · change ‖v‖ ≤ ‖g‖
    rw [hz]
    exact norm_nonneg g
  · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hz)
    change ‖v‖ ≤ ‖g‖
    nlinarith

def canonicalPhysicalDerivativeCoefficients (L : ℝ) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) : EuclideanSpace ℂ (Fin (2 * K + 1)) :=
  WithLp.toLp 2 (fun i => v i * localizedFrequency L (centeredIndex K i))

theorem canonicalPhysicalSynthesis_deriv {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) (hv : v ∈ euclideanBoundaryFlatSubspace K) :
    deriv (finitePhysicalSynthesis L K v) =
      finitePhysicalSynthesis L K (canonicalPhysicalDerivativeCoefficients L K v) := by
  unfold finitePhysicalSynthesis
  rw [deriv_localizedFiniteVector_eq_indicator_firstJet K _ hL
    ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat K v).mp hv),
    localizedFiniteVector_eq_indicator]
  congr 1

theorem canonicalPhysicalDerivativeCoefficients_norm_sq_le {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖canonicalPhysicalDerivativeCoefficients L K v‖ ^ 2 ≤
      (2 * Real.pi * K / L) ^ 2 * ‖v‖ ^ 2 := by
  have hb : 0 ≤ 2 * Real.pi / L := by positivity
  have hi (i : Fin (2 * K + 1)) : |((centeredIndex K i : ℤ) : ℝ)| ≤ (K : ℝ) := by
    have hn : |centeredIndex K i| ≤ (K : ℤ) := by
      rw [abs_le]
      simp only [centeredIndex]
      constructor <;> omega
    rw [← Int.cast_abs]
    exact_mod_cast hn
  have hf (i : Fin (2 * K + 1)) :
      ‖localizedFrequency L (centeredIndex K i)‖ ≤ 2 * Real.pi * K / L := by
    have hn : ‖(centeredIndex K i : ℂ)‖ = |((centeredIndex K i : ℤ) : ℝ)| := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    simp only [localizedFrequency, localizedBaseFrequency, norm_mul, norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb, hn]
    simpa only [div_mul_eq_mul_div, mul_assoc] using mul_le_mul_of_nonneg_left (hi i) hb
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change ‖v i * localizedFrequency L (centeredIndex K i)‖ ^ 2 ≤ _
  rw [norm_mul, mul_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf i) 2)
    (sq_nonneg ‖v i‖)).trans_eq (mul_comm _ _)

theorem canonicalPhysicalSynthesis_H1_bound {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) (hv : v ∈ euclideanBoundaryFlatSubspace K) :
    originalDetectorPhysicalH1Error (finitePhysicalSynthesis L K v) 0 ≤
      Real.sqrt (1 + (2 * Real.pi * K / L) ^ 2) * ‖v‖ := by
  unfold originalDetectorPhysicalH1Error
  simp only [Pi.zero_apply, sub_zero]
  rw [finitePhysicalSynthesis_energy hL, canonicalPhysicalSynthesis_deriv hL K v hv,
    finitePhysicalSynthesis_energy hL]
  calc
    _ ≤ Real.sqrt ((1 + (2 * Real.pi * K / L) ^ 2) * ‖v‖ ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [canonicalPhysicalDerivativeCoefficients_norm_sq_le hL K v])
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg v)]


private theorem ft_add_smul {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (c z : ℂ) :
    Zeta23.paperFT (f + c • g) z = Zeta23.paperFT f z + c * Zeta23.paperFT g z := by
  have hp : Continuous (fun x : ℝ => Complex.exp (Complex.I * z * (x : ℂ))) := by fun_prop
  have hi : Integrable (fun x => f x * Complex.exp (I * z * (x : ℂ))) volume :=
    (hf.mul hp).integrable_of_hasCompactSupport hfc.mul_right
  have hj : Integrable (fun x => g x * Complex.exp (I * z * (x : ℂ))) volume :=
    (hg.mul hp).integrable_of_hasCompactSupport hgc.mul_right
  have he : (fun x => (f + c • g) x * Complex.exp (Complex.I * z * (x : ℂ))) =
      fun x => f x * Complex.exp (Complex.I * z * (x : ℂ)) +
        c * (g x * Complex.exp (Complex.I * z * (x : ℂ))) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold Zeta23.paperFT
  rw [he, integral_add hi (hj.const_mul c), integral_const_mul]

private theorem W_polar {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Zeta23.zetaZeroConfig.W f g =
      (1 / 4 : ℂ) * ((Zeta23.zetaZeroConfig.W (f + (1 : ℂ) • g) (f + (1 : ℂ) • g) -
        Zeta23.zetaZeroConfig.W (f + (-1 : ℂ) • g) (f + (-1 : ℂ) • g)) +
        (I * Zeta23.zetaZeroConfig.W (f + I • g) (f + I • g) -
          I * Zeta23.zetaZeroConfig.W (f + (-I) • g) (f + (-I) • g))) := by
  have hc (c : ℂ) : HasCompactSupport (f + c • g) := by
    apply hfc.add
    have he : c • g = (fun _ : ℝ => c) * g := by funext x; rfl
    rw [he]
    exact hgc.mul_left
  have hs (c : ℂ) : HasSum (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand (f + c • g) (f + c • g) ρ)
      (Zeta23.zetaZeroConfig.W (f + c • g) (f + c • g)) :=
    (Zeta23.ExceptionalZero.zeta_Wsummand_summable
      (hf.add (hg.const_smul c)) (hf.add (hg.const_smul c)).continuous (hc c) (hc c)).hasSum
  have ht := (((hs 1).sub (hs (-1))).add
    (((hs I).mul_left I).sub ((hs (-I)).mul_left I))).mul_left (1 / 4 : ℂ)
  have he : (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (1 / 4 : ℂ) *
        ((Zeta23.zetaZeroConfig.Wsummand (f + (1 : ℂ) • g) (f + (1 : ℂ) • g) ρ -
          Zeta23.zetaZeroConfig.Wsummand (f + (-1 : ℂ) • g) (f + (-1 : ℂ) • g) ρ) +
          (I * Zeta23.zetaZeroConfig.Wsummand (f + I • g) (f + I • g) ρ -
            I * Zeta23.zetaZeroConfig.Wsummand (f + (-I) • g) (f + (-I) • g) ρ))) =
      fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f g ρ := by
    funext ρ
    unfold Zeta23.ZeroConfig.Wsummand
    simp only [ft_add_smul hf.continuous hg.continuous hfc hgc, map_add, map_mul,
      Complex.conj_I, map_neg, map_one]
    ring_nf
    simp only [I_sq]
    ring
  change HasSum (fun ρ => _) _ at ht
  rw [he] at ht
  exact ht.tsum_eq


theorem canonicalNativeCoefficientInclusion_eq_ambient (σ : ReversalParity) (L : ℝ) (K : ℕ)
    (v : nativePoleNeutralParitySpace σ L K) :
    canonicalNativeCoefficientInclusion σ L K v = nativePoleNeutralParityAmbient σ L K v := by
  cases σ <;> rfl

theorem canonicalNativePhysicalSynthesis_H1_bound (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (v : nativePoleNeutralParitySpace σ L K) :
    originalDetectorPhysicalH1Error
      (finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v)) 0 ≤
      Real.sqrt (1 + (2 * Real.pi * K / L) ^ 2) * ‖v‖ := by
  have he := canonicalPhysicalSynthesis_H1_bound hL K (nativePoleNeutralParityAmbient σ L K v)
    (nativePoleNeutralParityAmbient_legal σ L K v)
  rw [nativePoleNeutralParityAmbient_norm] at he
  simpa only [canonicalNativeCoefficientInclusion_eq_ambient] using he

/-- The mixed dictionary uses the Weil form's linear-first convention. -/
theorem canonicalPhysicalSynthesis_mixed_Weil {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u v : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hu : u ∈ euclideanBoundaryFlatSubspace K) (hv : v ∈ euclideanBoundaryFlatSubspace K) :
    Zeta23.zetaZeroConfig.W (finitePhysicalSynthesis L K u) (finitePhysicalSynthesis L K v) =
      inner ℂ v ((canonicalSourceMatrix L K).toEuclideanLin u) := by
  have hC (w : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (hw : w ∈ euclideanBoundaryFlatSubspace K) : ContDiff ℝ 2 (finitePhysicalSynthesis L K w) :=
    contDiff_localizedFiniteVector_of_boundaryFlat K _ hL
      ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat K w).mp hw)
  have hS (w : EuclideanSpace ℂ (Fin (2 * K + 1))) :
      HasCompactSupport (finitePhysicalSynthesis L K w) := localizedFiniteVector_hasCompactSupport L K _
  have hdiag (c : ℂ) :
      Zeta23.zetaZeroConfig.W (finitePhysicalSynthesis L K u + c • finitePhysicalSynthesis L K v)
        (finitePhysicalSynthesis L K u + c • finitePhysicalSynthesis L K v) =
      inner ℂ (u + c • v) ((canonicalSourceMatrix L K).toEuclideanLin (u + c • v)) := by
    rw [← finitePhysicalSynthesis_smul, ← finitePhysicalSynthesis_add]
    exact (Zeta23.ExceptionalZero.zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm
      K _ hL ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat K (u + c • v)).mp
        ((euclideanBoundaryFlatSubspace K).add_mem hu ((euclideanBoundaryFlatSubspace K).smul_mem c hv)))).trans
      (quadraticForm_eq_inner_toEuclideanLin _ (u + c • v))
  have hp := W_polar (hC u hu) (hC v hv) (hS u) (hS v)
  rw [hdiag 1, hdiag (-1), hdiag I, hdiag (-I)] at hp
  refine hp.trans ?_
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    map_one, map_neg, Complex.conj_I, RingHom.id_apply]
  ring_nf
  simp only [I_sq]
  ring

theorem canonicalNativePhysical_mixed_compression (σ : ReversalParity) (L : ℝ) (K : ℕ)
    (u v : nativePoleNeutralParitySpace σ L K) :
    inner ℂ v (nativePoleNeutralParityCanonical σ L K u) =
      inner ℂ (nativePoleNeutralParityAmbient σ L K v)
        ((canonicalSourceMatrix L K).toEuclideanLin (nativePoleNeutralParityAmbient σ L K u)) := by
  cases σ
  · calc
      _ = inner ℂ v.val (evenCompressedCanonical L K u.val) :=
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
          (𝕜 := ℂ) (E := euclideanEvenBoundaryFlatSubspace K)
          (K := poleNeutralEvenSubspace L K) v (evenCompressedCanonical L K u.val)
      _ = _ :=
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
          (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin (2*K+1)))
          (K := euclideanEvenBoundaryFlatSubspace K) v.val
          ((canonicalSourceMatrix L K).toEuclideanLin u.val.val)
  · calc
      _ = inner ℂ v.val (oddCompressedCanonical L K u.val) :=
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
          (𝕜 := ℂ) (E := euclideanOddBoundaryFlatSubspace K)
          (K := poleNeutralOddSubspace L K) v (oddCompressedCanonical L K u.val)
      _ = _ :=
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
          (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin (2*K+1)))
          (K := euclideanOddBoundaryFlatSubspace K) v.val
          ((canonicalSourceMatrix L K).toEuclideanLin u.val.val)

theorem canonicalNativePhysicalSynthesis_mixed_Weil (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u v : nativePoleNeutralParitySpace σ L K) :
    Zeta23.zetaZeroConfig.W
      (finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K u))
      (finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v)) =
      inner ℂ v (nativePoleNeutralParityCanonical σ L K u) := by
  simp only [canonicalNativeCoefficientInclusion_eq_ambient]
  exact (canonicalPhysicalSynthesis_mixed_Weil hL K _ _
    (nativePoleNeutralParityAmbient_legal σ L K u)
    (nativePoleNeutralParityAmbient_legal σ L K v)).trans
      (canonicalNativePhysical_mixed_compression σ L K u v).symm

/-- The first possible predecessor is the actual zero native space. -/
theorem canonicalNativePhysicalProjection_firstCutoff_zero (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (g : CanonicalPhysicalL2) :
    canonicalNativePhysicalProjection σ hL 2 g = 0 := by
  have hd : Module.finrank ℂ (nativePoleNeutralParitySpace σ L 2) = 0 := by
    simpa using finrank_nativePoleNeutralParitySpace σ hL 2 (by omega)
  letI : Subsingleton (nativePoleNeutralParitySpace σ L 2) := Module.finrank_zero_iff.mp hd
  exact Subsingleton.elim _ _

end Zeta23.CCM

#print axioms Zeta23.CCM.finitePhysicalSynthesis_add
#print axioms Zeta23.CCM.finitePhysicalSynthesis_sub
#print axioms Zeta23.CCM.canonicalPhysicalValue_ae
#print axioms Zeta23.CCM.canonicalPhysicalValue_norm
#print axioms Zeta23.CCM.canonicalPhysicalIsometry_ae
#print axioms Zeta23.CCM.canonicalPhysicalProjection_synthesis
#print axioms Zeta23.CCM.canonicalPhysicalProjection_inner
#print axioms Zeta23.CCM.canonicalPhysicalIsometry_centeredZeroExtend
#print axioms Zeta23.CCM.canonicalNativePhysicalIsometry_centeredZeroExtend
#print axioms Zeta23.CCM.canonicalNativePhysicalIsometry_predecessor
#print axioms Zeta23.CCM.canonicalNativePhysicalProjection_synthesis
#print axioms Zeta23.CCM.canonicalNativePhysicalIsometry_ae
#print axioms Zeta23.CCM.canonicalNativePhysicalProjection_inner
#print axioms Zeta23.CCM.canonicalNativePhysicalProjection_orthogonal
#print axioms Zeta23.CCM.canonicalNativePhysicalProjection_norm_le
#print axioms Zeta23.CCM.canonicalPhysicalSynthesis_deriv
#print axioms Zeta23.CCM.canonicalPhysicalDerivativeCoefficients_norm_sq_le
#print axioms Zeta23.CCM.canonicalPhysicalSynthesis_H1_bound
#print axioms Zeta23.CCM.canonicalNativeCoefficientInclusion_eq_ambient
#print axioms Zeta23.CCM.canonicalNativePhysicalSynthesis_H1_bound
#print axioms Zeta23.CCM.canonicalPhysicalSynthesis_mixed_Weil
#print axioms Zeta23.CCM.canonicalNativePhysical_mixed_compression
#print axioms Zeta23.CCM.canonicalNativePhysicalSynthesis_mixed_Weil
#print axioms Zeta23.CCM.canonicalNativePhysicalProjection_firstCutoff_zero

