import Zeta23.ExceptionalZero.WeilLiteratureBridge
import Zeta23.WeilEF.ZeroSummability

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex MeasureTheory Real Set
open scoped BigOperators ComplexConjugate

/-!
# WCONT-A: quantitative common-support continuity of the genuine zeta Weil form

The load-bearing estimate is asymmetric, matching the repository's exact
`ZeroConfig.W` convention and W2-A regularity surface:

* the first argument is `C²`, so its paper Fourier transform receives
  `(1 + ‖γ‖²)⁻¹` decay;
* the second argument is only continuous and compactly supported, so only the
  zeroth-order Fourier bound is used;
* the closed critical strip gives `|Im γ_ρ| ≤ 1/2` uniformly;
* the existing inverse-square zero mass supplies one family-independent
  summable majorant.

No RH assumption, approximation index, source normalization, or finite-matrix
identification enters this file.
-/

/-- The fixed inverse-square mass of the concrete zeta zero configuration. -/
def zetaInvSqZeroMass : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) /
      (1 + Complex.normSq (gammaOf ρ))

/-- The inverse-square zeta-zero weight used by WCONT-A is summable
unconditionally. -/
theorem zeta_invSqZeroWeight_summable :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) /
        (1 + Complex.normSq (gammaOf ρ))) := by
  simpa [zetaZeroConfig] using
    (Zeta23.WeilEF.zero_sum_inv_sq zetaSeam)

/-- The fixed inverse-square zeta-zero mass is nonnegative. -/
theorem zetaInvSqZeroMass_nonneg : 0 ≤ zetaInvSqZeroMass := by
  unfold zetaInvSqZeroMass
  exact tsum_nonneg fun ρ =>
    div_nonneg (Nat.cast_nonneg _)
      (by
        nlinarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))] :
        0 ≤ 1 + Complex.normSq (gammaOf (ρ : ℂ)))

/-- Pointwise common-support majorant for one genuine zeta Weil summand.

The first Fourier leg receives the global `(1 + normSq γ)⁻¹` estimate, while
the conjugated second leg uses only the zeroth-order estimate. -/
theorem norm_zeta_Wsummand_le_commonSupport
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hg : Continuous g)
    (hfsupp : ∀ x, f x ≠ 0 → |x| ≤ Λ)
    (hgsupp : ∀ x, g x ≠ 0 → |x| ≤ Λ)
    (ρ : zetaZeroConfig.carrier) :
    ‖zetaZeroConfig.Wsummand f g ρ‖ ≤
      (Real.exp Λ *
          ((∫ x, ‖f x‖) + ∫ x, ‖deriv (deriv f) x‖) *
          (∫ x, ‖g x‖)) *
        ((zetaZeroConfig.mult ρ : ℝ) /
          (1 + Complex.normSq (gammaOf ρ))) := by
  have hstrip : 0 ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ 1 :=
    zetaZeroConfig.strip _ ρ.2
  have him : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 :=
    Zeta23.WeilEF.abs_gammaOf_im_le hstrip
  have himc :
      |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
    simpa using him
  have hfc : HasCompactSupport f :=
    hasCompactSupport_of_support_subset_abs hfsupp
  have hgc : HasCompactSupport g :=
    hasCompactSupport_of_support_subset_abs hgsupp
  have hgi : Integrable g :=
    hg.integrable_of_hasCompactSupport hgc
  have hF0 : 0 ≤ ∫ x, ‖f x‖ := integral_nonneg fun _ => norm_nonneg _
  have hF2 : 0 ≤ ∫ x, ‖deriv (deriv f) x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hG0 : 0 ≤ ∫ x, ‖g x‖ := integral_nonneg fun _ => norm_nonneg _
  have hden : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
    nlinarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
  have hfWeighted :=
    norm_paperFT_mul_one_add_normSq_le hf hfsupp (gammaOf (ρ : ℂ))
  have hfDiv :
      ‖paperFT f (gammaOf (ρ : ℂ))‖ ≤
        Real.exp (|(gammaOf (ρ : ℂ)).im| * Λ) *
            ((∫ x, ‖f x‖) + ∫ x, ‖deriv (deriv f) x‖) /
          (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
    rw [le_div_iff₀ hden]
    exact hfWeighted
  have hmul :
      |(gammaOf (ρ : ℂ)).im| * Λ ≤ Λ / 2 := by
    have := mul_le_mul_of_nonneg_right him hΛ
    nlinarith
  have hexpf :
      Real.exp (|(gammaOf (ρ : ℂ)).im| * Λ) ≤ Real.exp (Λ / 2) :=
    Real.exp_le_exp.mpr hmul
  have hfFinal :
      ‖paperFT f (gammaOf (ρ : ℂ))‖ ≤
        Real.exp (Λ / 2) *
            ((∫ x, ‖f x‖) + ∫ x, ‖deriv (deriv f) x‖) /
          (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
    calc
      ‖paperFT f (gammaOf (ρ : ℂ))‖
          ≤ Real.exp (|(gammaOf (ρ : ℂ)).im| * Λ) *
              ((∫ x, ‖f x‖) + ∫ x, ‖deriv (deriv f) x‖) /
            (1 + Complex.normSq (gammaOf (ρ : ℂ))) := hfDiv
      _ ≤ Real.exp (Λ / 2) *
              ((∫ x, ‖f x‖) + ∫ x, ‖deriv (deriv f) x‖) /
            (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
        gcongr
  have hg0 :=
    norm_paperFT_le hgi hgsupp
      ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))
  have hmulc :
      |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| * Λ ≤ Λ / 2 := by
    have := mul_le_mul_of_nonneg_right himc hΛ
    nlinarith
  have hexpg :
      Real.exp
          (|((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| * Λ) ≤
        Real.exp (Λ / 2) :=
    Real.exp_le_exp.mpr hmulc
  have hgFinal :
      ‖paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ ≤
        Real.exp (Λ / 2) * ∫ x, ‖g x‖ := by
    calc
      ‖paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖
          ≤ Real.exp
              (|((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| * Λ) *
              ∫ x, ‖g x‖ := hg0
      _ ≤ Real.exp (Λ / 2) * ∫ x, ‖g x‖ := by
        gcongr
  have hexp :
      Real.exp (Λ / 2) * Real.exp (Λ / 2) = Real.exp Λ := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ‖zetaZeroConfig.Wsummand f g ρ‖
        = (zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT f (gammaOf (ρ : ℂ))‖ *
            ‖paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ := by
          simp [ZeroConfig.Wsummand]
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
          (Real.exp (Λ / 2) *
              ((∫ x, ‖f x‖) + ∫ x, ‖deriv (deriv f) x‖) /
            (1 + Complex.normSq (gammaOf (ρ : ℂ)))) *
          (Real.exp (Λ / 2) * ∫ x, ‖g x‖) := by
        gcongr
    _ = (Real.exp Λ *
          ((∫ x, ‖f x‖) + ∫ x, ‖deriv (deriv f) x‖) *
          (∫ x, ‖g x‖)) *
        ((zetaZeroConfig.mult ρ : ℝ) /
          (1 + Complex.normSq (gammaOf ρ))) := by
        rw [← hexp]
        ring

/-- **WCONT-A, production bilinear bound.**  On a fixed common support envelope,
the genuine zeta Weil form is bounded by one fixed inverse-square zero mass.

This is a static quantitative estimate, not a family dominated-convergence
statement. -/
theorem zeta_W_norm_le_commonSupport
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hg : Continuous g)
    (hfsupp : ∀ x, f x ≠ 0 → |x| ≤ Λ)
    (hgsupp : ∀ x, g x ≠ 0 → |x| ≤ Λ) :
    ‖zetaZeroConfig.W f g‖ ≤
      Real.exp Λ * zetaInvSqZeroMass *
        ((∫ x, ‖f x‖) + ∫ x, ‖deriv (deriv f) x‖) *
        (∫ x, ‖g x‖) := by
  let C : ℝ :=
    Real.exp Λ *
      ((∫ x, ‖f x‖) + ∫ x, ‖deriv (deriv f) x‖) *
      (∫ x, ‖g x‖)
  have hmajor :
      HasSum
        (fun ρ : zetaZeroConfig.carrier =>
          C * ((zetaZeroConfig.mult ρ : ℝ) /
            (1 + Complex.normSq (gammaOf ρ))))
        (C * zetaInvSqZeroMass) := by
    simpa [zetaInvSqZeroMass] using
      zeta_invSqZeroWeight_summable.hasSum.mul_left C
  unfold ZeroConfig.W
  calc
    ‖∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand f g ρ‖
        ≤ C * zetaInvSqZeroMass := by
          apply tsum_of_norm_bounded hmajor
          intro ρ
          simpa [C] using
            norm_zeta_Wsummand_le_commonSupport
              hΛ hf hg hfsupp hgsupp ρ
    _ = Real.exp Λ * zetaInvSqZeroMass *
        ((∫ x, ‖f x‖) + ∫ x, ‖deriv (deriv f) x‖) *
        (∫ x, ‖g x‖) := by
      simp [C]
      ring

/-- Pointwise algebra behind the diagonal perturbation identity. -/
theorem zeta_Wsummand_self_sub_self_eq_cross
    {p h : ℝ → ℂ}
    (hp : ContDiff ℝ 2 p)
    (hh : ContDiff ℝ 2 h)
    (hpc : HasCompactSupport p)
    (hhc : HasCompactSupport h)
    (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand p p ρ -
        zetaZeroConfig.Wsummand h h ρ =
      zetaZeroConfig.Wsummand (p - h) p ρ +
        zetaZeroConfig.Wsummand h (p - h) ρ := by
  unfold ZeroConfig.Wsummand
  rw [paperFT_sub hp.continuous hh.continuous hpc hhc,
    paperFT_sub hp.continuous hh.continuous hpc hhc]
  simp only [map_sub]
  ring

/-- Summability-safe exact diagonal cross-term identity.

All four relevant zero-side series are certified summable before subtraction
and addition are transported through their `HasSum` witnesses. -/
theorem zeta_W_self_sub_self_eq_cross
    {p h : ℝ → ℂ}
    (hp : ContDiff ℝ 2 p)
    (hh : ContDiff ℝ 2 h)
    (hpc : HasCompactSupport p)
    (hhc : HasCompactSupport h) :
    zetaZeroConfig.W p p - zetaZeroConfig.W h h =
      zetaZeroConfig.W (p - h) p +
        zetaZeroConfig.W h (p - h) := by
  have he : ContDiff ℝ 2 (p - h) := hp.sub hh
  have hec : HasCompactSupport (p - h) := hpc.sub hhc
  have hpp :=
    zeta_Wsummand_summable hp hp.continuous hpc hpc
  have hhh :=
    zeta_Wsummand_summable hh hh.continuous hhc hhc
  have hep :=
    zeta_Wsummand_summable he hp.continuous hec hpc
  have hhe :=
    zeta_Wsummand_summable hh he.continuous hhc hec
  have hlhs := hpp.hasSum.sub hhh.hasSum
  have hrhs := hep.hasSum.add hhe.hasSum
  unfold ZeroConfig.W
  calc
    (∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand p p ρ) -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaZeroConfig.Wsummand h h ρ =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.Wsummand p p ρ -
          zetaZeroConfig.Wsummand h h ρ) := hlhs.tsum_eq.symm
    _ =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.Wsummand (p - h) p ρ +
          zetaZeroConfig.Wsummand h (p - h) ρ) := by
        refine tsum_congr fun ρ => ?_
        exact zeta_Wsummand_self_sub_self_eq_cross hp hh hpc hhc ρ
    _ =
      (∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand (p - h) p ρ) +
      ∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand h (p - h) ρ := hrhs.tsum_eq

/-- **WCONT-A diagonal cash-out.**  The self-form perturbation is controlled by
the `L¹ + second-derivative L¹` size of the error in the first cross term and
by the error's `L¹` size in the second cross term. -/
theorem zeta_W_self_sub_self_norm_le_commonSupport
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {p h : ℝ → ℂ}
    (hp : ContDiff ℝ 2 p)
    (hh : ContDiff ℝ 2 h)
    (hpsupp : ∀ x, p x ≠ 0 → |x| ≤ Λ)
    (hhsupp : ∀ x, h x ≠ 0 → |x| ≤ Λ) :
    ‖zetaZeroConfig.W p p - zetaZeroConfig.W h h‖ ≤
      Real.exp Λ * zetaInvSqZeroMass *
        (((∫ x, ‖(p - h) x‖) +
            ∫ x, ‖deriv (deriv (p - h)) x‖) *
            (∫ x, ‖p x‖) +
          ((∫ x, ‖h x‖) +
            ∫ x, ‖deriv (deriv h) x‖) *
            (∫ x, ‖(p - h) x‖)) := by
  have hpc : HasCompactSupport p :=
    hasCompactSupport_of_support_subset_abs hpsupp
  have hhc : HasCompactSupport h :=
    hasCompactSupport_of_support_subset_abs hhsupp
  have he : ContDiff ℝ 2 (p - h) := hp.sub hh
  have hesupp : ∀ x, (p - h) x ≠ 0 → |x| ≤ Λ := by
    intro x hx
    by_cases hpx : p x = 0
    · have hhx : h x ≠ 0 := by
        intro hhx
        apply hx
        simp [hpx, hhx]
      exact hhsupp x hhx
    · exact hpsupp x hpx
  have he_p :=
    zeta_W_norm_le_commonSupport
      hΛ he hp.continuous hesupp hpsupp
  have hh_e :=
    zeta_W_norm_le_commonSupport
      hΛ hh he.continuous hhsupp hesupp
  rw [zeta_W_self_sub_self_eq_cross hp hh hpc hhc]
  calc
    ‖zetaZeroConfig.W (p - h) p +
        zetaZeroConfig.W h (p - h)‖
        ≤ ‖zetaZeroConfig.W (p - h) p‖ +
          ‖zetaZeroConfig.W h (p - h)‖ := norm_add_le _ _
    _ ≤
      (Real.exp Λ * zetaInvSqZeroMass *
          ((∫ x, ‖(p - h) x‖) +
            ∫ x, ‖deriv (deriv (p - h)) x‖) *
          (∫ x, ‖p x‖)) +
      (Real.exp Λ * zetaInvSqZeroMass *
          ((∫ x, ‖h x‖) +
            ∫ x, ‖deriv (deriv h) x‖) *
          (∫ x, ‖(p - h) x‖)) :=
        add_le_add he_p hh_e
    _ =
      Real.exp Λ * zetaInvSqZeroMass *
        (((∫ x, ‖(p - h) x‖) +
            ∫ x, ‖deriv (deriv (p - h)) x‖) *
            (∫ x, ‖p x‖) +
          ((∫ x, ‖h x‖) +
            ∫ x, ‖deriv (deriv h) x‖) *
            (∫ x, ‖(p - h) x‖)) := by
      ring

end Zeta23.ExceptionalZero
