import Zeta23.ExceptionalZero.TwoTranslateNegativity
import Zeta23.ExceptionalZero.WeilLiteratureBridge

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Matrix MeasureTheory
open scoped BigOperators ComplexConjugate

/-!
# W0: contract the negative two-translate matrix to one physical Weil test

The X3 layer already supplies an admissible compact C² test `k`, an aperture `t`,
and a strict negative direction for the complete two-translate Weil matrix.  W2-A
supplies the pairwise zero-side summability certificates that make the corresponding
finite sesquilinear contraction legal at the level of `ZeroConfig.W`.

The repository convention is load-bearing: `W` is linear in its first argument and
conjugate-linear in its second.  Therefore a matrix coefficient vector `(a,b)`
corresponds to the physical function

`conj(a) * k + conj(b) * translateRight k t`.

For the existing phase witness `(‖C‖,-C)`, this is exactly
`‖C‖ * k - conj(C) * translateRight k t`.
-/

/-- Physical two-translate combination matching the repository's matrix coefficient
convention. -/
def twoTranslateCombination
    (k : ℝ → ℂ) (t : ℝ) (a b : ℂ) : ℝ → ℂ :=
  fun x =>
    (starRingEnd ℂ) a * k x +
      (starRingEnd ℂ) b * translateRight k t x

/-- The physical test attached to the existing division-free phase witness. -/
def twoTranslatePhaseTest
    (Z : ZeroConfig) (k : ℝ → ℂ) (t : ℝ) : ℝ → ℂ :=
  let C := weilRelativeCorrelation Z k t
  twoTranslateCombination k t (‖C‖ : ℂ) (-C)

/-- A two-translate combination preserves C² regularity. -/
theorem twoTranslateCombination_contDiff
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (t : ℝ) (a b : ℂ) :
    ContDiff ℝ 2 (twoTranslateCombination k t a b) := by
  unfold twoTranslateCombination
  exact
    (contDiff_const.mul hk).add
      (contDiff_const.mul (contDiff_translateRight hk t))

/-- A two-translate combination preserves compact support. -/
theorem twoTranslateCombination_hasCompactSupport
    {k : ℝ → ℂ} (hkc : HasCompactSupport k)
    (t : ℝ) (a b : ℂ) :
    HasCompactSupport (twoTranslateCombination k t a b) := by
  unfold twoTranslateCombination
  exact
    hkc.mul_left.add
      (hasCompactSupport_translateRight hkc t).mul_left

/-- The phase test is C² whenever the base test is C². -/
theorem twoTranslatePhaseTest_contDiff
    (Z : ZeroConfig) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (t : ℝ) :
    ContDiff ℝ 2 (twoTranslatePhaseTest Z k t) := by
  unfold twoTranslatePhaseTest
  exact twoTranslateCombination_contDiff hk t _ _

/-- The phase test is compactly supported whenever the base test is. -/
theorem twoTranslatePhaseTest_hasCompactSupport
    (Z : ZeroConfig) {k : ℝ → ℂ}
    (hkc : HasCompactSupport k) (t : ℝ) :
    HasCompactSupport (twoTranslatePhaseTest Z k t) := by
  unfold twoTranslatePhaseTest
  exact twoTranslateCombination_hasCompactSupport hkc t _ _

/-- Paper Fourier transform of the exact two-translate combination.  Integrability is
proved before using linearity of the Bochner integral. -/
theorem paperFT_twoTranslateCombination
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k)
    (t : ℝ) (a b z : ℂ) :
    paperFT (twoTranslateCombination k t a b) z =
      (starRingEnd ℂ) a * paperFT k z +
        (starRingEnd ℂ) b * paperFT (translateRight k t) z := by
  have hkt : ContDiff ℝ 2 (translateRight k t) :=
    contDiff_translateRight hk t
  have hkct : HasCompactSupport (translateRight k t) :=
    hasCompactSupport_translateRight hkc t
  have hphase : Continuous (fun x : ℝ => Complex.exp (I * z * (x : ℂ))) := by
    fun_prop
  have hik : Integrable (fun x : ℝ => k x * Complex.exp (I * z * (x : ℂ))) :=
    (hk.continuous.mul hphase).integrable_of_hasCompactSupport hkc.mul_right
  have hit : Integrable
      (fun x : ℝ => translateRight k t x * Complex.exp (I * z * (x : ℂ))) :=
    (hkt.continuous.mul hphase).integrable_of_hasCompactSupport hkct.mul_right
  unfold paperFT twoTranslateCombination
  have hfun :
      (fun x : ℝ =>
        ((starRingEnd ℂ) a * k x +
            (starRingEnd ℂ) b * translateRight k t x) *
          Complex.exp (I * z * (x : ℂ))) =
      (fun x : ℝ =>
        (starRingEnd ℂ) a *
            (k x * Complex.exp (I * z * (x : ℂ))) +
          (starRingEnd ℂ) b *
            (translateRight k t x * Complex.exp (I * z * (x : ℂ)))) := by
    funext x
    ring
  rw [hfun, integral_add (hik.const_mul _) (hit.const_mul _),
    integral_const_mul_C, integral_const_mul_C]

/-- W2-A gives all four pairwise summability certificates required by the
two-translate contraction. -/
theorem zeta_twoTranslate_Wsummand_summable_package
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k)
    (t : ℝ) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand k k ρ) ∧
    Summable (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand k (translateRight k t) ρ) ∧
    Summable (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand (translateRight k t) k ρ) ∧
    Summable (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand
        (translateRight k t) (translateRight k t) ρ) := by
  have hkt : ContDiff ℝ 2 (translateRight k t) :=
    contDiff_translateRight hk t
  have hkct : HasCompactSupport (translateRight k t) :=
    hasCompactSupport_translateRight hkc t
  exact ⟨
    zeta_Wsummand_summable hk hk.continuous hkc hkc,
    zeta_Wsummand_summable hk hkt.continuous hkc hkct,
    zeta_Wsummand_summable hkt hk.continuous hkct hkc,
    zeta_Wsummand_summable hkt hkt.continuous hkct hkct⟩

/-- Pointwise zero-side expansion of the two-translate combination. -/
theorem zeta_Wsummand_twoTranslateCombination
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k)
    (t : ℝ) (a b : ℂ)
    (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand
        (twoTranslateCombination k t a b)
        (twoTranslateCombination k t a b) ρ =
      (starRingEnd ℂ) a * a * zetaZeroConfig.Wsummand k k ρ +
      (starRingEnd ℂ) a * b *
        zetaZeroConfig.Wsummand k (translateRight k t) ρ +
      (starRingEnd ℂ) b * a *
        zetaZeroConfig.Wsummand (translateRight k t) k ρ +
      (starRingEnd ℂ) b * b *
        zetaZeroConfig.Wsummand
          (translateRight k t) (translateRight k t) ρ := by
  unfold ZeroConfig.Wsummand
  rw [paperFT_twoTranslateCombination hk hkc,
    paperFT_twoTranslateCombination hk hkc]
  simp only [map_add, map_mul, map_neg, map_ofReal, map_natCast,
    Complex.conj_conj]
  ring

/-- Summability-safe finite sesquilinear expansion of the genuine zeta Weil form
on the two-translate sector. -/
theorem zeta_W_twoTranslateCombination_expansion
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k)
    (t : ℝ) (a b : ℂ) :
    zetaZeroConfig.W
        (twoTranslateCombination k t a b)
        (twoTranslateCombination k t a b) =
      (starRingEnd ℂ) a * a * zetaZeroConfig.W k k +
      (starRingEnd ℂ) a * b *
        zetaZeroConfig.W k (translateRight k t) +
      (starRingEnd ℂ) b * a *
        zetaZeroConfig.W (translateRight k t) k +
      (starRingEnd ℂ) b * b *
        zetaZeroConfig.W
          (translateRight k t) (translateRight k t) := by
  obtain ⟨h11, h12, h21, h22⟩ :=
    zeta_twoTranslate_Wsummand_summable_package hk hkc t
  let c11 : ℂ := (starRingEnd ℂ) a * a
  let c12 : ℂ := (starRingEnd ℂ) a * b
  let c21 : ℂ := (starRingEnd ℂ) b * a
  let c22 : ℂ := (starRingEnd ℂ) b * b
  have hs11 := h11.hasSum.mul_left c11
  have hs12 := h12.hasSum.mul_left c12
  have hs21 := h21.hasSum.mul_left c21
  have hs22 := h22.hasSum.mul_left c22
  have hsum := ((hs11.add hs12).add hs21).add hs22
  unfold ZeroConfig.W
  calc
    (∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand
          (twoTranslateCombination k t a b)
          (twoTranslateCombination k t a b) ρ) =
      ∑' ρ : zetaZeroConfig.carrier,
        (c11 * zetaZeroConfig.Wsummand k k ρ +
          c12 * zetaZeroConfig.Wsummand k (translateRight k t) ρ +
          c21 * zetaZeroConfig.Wsummand (translateRight k t) k ρ +
          c22 * zetaZeroConfig.Wsummand
            (translateRight k t) (translateRight k t) ρ) := by
        refine tsum_congr fun ρ => ?_
        simpa [c11, c12, c21, c22] using
          zeta_Wsummand_twoTranslateCombination hk hkc t a b ρ
    _ =
      c11 * (∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand k k ρ) +
      c12 * (∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand k (translateRight k t) ρ) +
      c21 * (∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand (translateRight k t) k ρ) +
      c22 * (∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand
          (translateRight k t) (translateRight k t) ρ) := hsum.tsum_eq
    _ =
      (starRingEnd ℂ) a * a * (∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand k k ρ) +
      (starRingEnd ℂ) a * b * (∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand k (translateRight k t) ρ) +
      (starRingEnd ℂ) b * a * (∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand (translateRight k t) k ρ) +
      (starRingEnd ℂ) b * b * (∑' ρ : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand
          (translateRight k t) (translateRight k t) ρ) := by
        rfl

/-- The genuine zeta Weil value of the physical two-translate combination is
exactly the quadratic value of the existing Hermitian two-translate matrix. -/
theorem zeta_W_twoTranslateCombination_eq_matrixQuadratic
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k)
    (t : ℝ) (a b : ℂ) :
    zetaZeroConfig.W
        (twoTranslateCombination k t a b)
        (twoTranslateCombination k t a b) =
      star (![a, b]) ⬝ᵥ
        (twoTranslateWeilMatrix zetaZeroConfig k t *ᵥ ![a, b]) := by
  rw [zeta_W_twoTranslateCombination_expansion hk hkc]
  rw [W_f_translateRight_eq_star_relativeCorrelation,
    W_translateRight_self]
  simp [twoTranslateWeilMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The phase test realizes the already-proved matrix phase witness exactly. -/
theorem zeta_W_twoTranslatePhaseTest_eq_phaseWitness
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k)
    (t : ℝ) :
    zetaZeroConfig.W
        (twoTranslatePhaseTest zetaZeroConfig k t)
        (twoTranslatePhaseTest zetaZeroConfig k t) =
      star (twoTranslatePhaseWitness
        (weilRelativeCorrelation zetaZeroConfig k t)) ⬝ᵥ
        (twoTranslateWeilMatrix zetaZeroConfig k t *ᵥ
          twoTranslatePhaseWitness
            (weilRelativeCorrelation zetaZeroConfig k t)) := by
  unfold twoTranslatePhaseTest
  simpa [twoTranslatePhaseWitness] using
    zeta_W_twoTranslateCombination_eq_matrixQuadratic
      hk hkc t
      (‖weilRelativeCorrelation zetaZeroConfig k t‖ : ℂ)
      (-weilRelativeCorrelation zetaZeroConfig k t)

/-- Strict correlation-over-diagonal dominance contracts to one physical test
with strictly negative Weil self-value. -/
theorem zeta_W_twoTranslatePhaseTest_neg_of_diagonal_norm_lt
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k)
    (t : ℝ)
    (hgt :
      ‖zetaZeroConfig.W k k‖ <
        ‖weilRelativeCorrelation zetaZeroConfig k t‖) :
    (zetaZeroConfig.W
      (twoTranslatePhaseTest zetaZeroConfig k t)
      (twoTranslatePhaseTest zetaZeroConfig k t)).re < 0 := by
  rw [zeta_W_twoTranslatePhaseTest_eq_phaseWitness hk hkc]
  exact
    twoTranslatePhaseWitness_neg_of_diagonal_norm_lt
      zetaZeroConfig k t hgt

/-- A Fourier zero of the base test is preserved by the physical phase
contraction. -/
theorem paperFT_twoTranslatePhaseTest_eq_zero_of_base_eq_zero
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k)
    (t : ℝ) (z : ℂ)
    (hz : paperFT k z = 0) :
    paperFT (twoTranslatePhaseTest zetaZeroConfig k t) z = 0 := by
  unfold twoTranslatePhaseTest
  rw [paperFT_twoTranslateCombination hk hkc]
  rw [paperFT_translateRight, hz]
  simp

/-- **W0, strong endpoint.** Every hypothetical off-line zero produces one
compact C² pole-neutral physical test with strictly negative genuine Weil
self-value. -/
theorem exists_poleNeutral_negativeWeilTest_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ h : ℝ → ℂ,
      ContDiff ℝ 2 h ∧
      HasCompactSupport h ∧
      paperFT h (I / 2) = 0 ∧
      paperFT h (-I / 2) = 0 ∧
      (zetaZeroConfig.W h h).re < 0 := by
  obtain ⟨k, a, hk, hkc, _heven, _hreal, hp, hn, _ha, hgt, _hneg⟩ :=
    exists_realEven_poleKilled_twoTranslate_negativeWitness_of_offLine_zero
      ρ₀ hoff
  let h : ℝ → ℂ :=
    twoTranslatePhaseTest zetaZeroConfig k (2 * a)
  refine ⟨h, ?_, ?_, ?_, ?_, ?_⟩
  · exact twoTranslatePhaseTest_contDiff zetaZeroConfig hk (2 * a)
  · exact twoTranslatePhaseTest_hasCompactSupport zetaZeroConfig hkc (2 * a)
  · exact
      paperFT_twoTranslatePhaseTest_eq_zero_of_base_eq_zero
        hk hkc (2 * a) (I / 2) hp
  · exact
      paperFT_twoTranslatePhaseTest_eq_zero_of_base_eq_zero
        hk hkc (2 * a) (-I / 2) hn
  · exact
      zeta_W_twoTranslatePhaseTest_neg_of_diagonal_norm_lt
        hk hkc (2 * a) hgt

/-- Minimal W0 endpoint for downstream route composition. -/
theorem exists_negativeWeilTest_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ h : ℝ → ℂ,
      ContDiff ℝ 2 h ∧
      HasCompactSupport h ∧
      (zetaZeroConfig.W h h).re < 0 := by
  obtain ⟨h, hh, hhc, _hp, _hn, hneg⟩ :=
    exists_poleNeutral_negativeWeilTest_of_offLine_zero ρ₀ hoff
  exact ⟨h, hh, hhc, hneg⟩

/-- Logical existential wrapper used by the F1 roadmap. -/
theorem exists_negativeWeilTest_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ h : ℝ → ℂ,
      ContDiff ℝ 2 h ∧
      HasCompactSupport h ∧
      (zetaZeroConfig.W h h).re < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_negativeWeilTest_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero
