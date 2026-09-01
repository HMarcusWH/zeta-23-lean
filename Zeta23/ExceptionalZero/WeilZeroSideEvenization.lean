import Zeta23.ZetaReflect
import Zeta23.Statement.SeamClosed
import Zeta23.ExceptionalZero.WeilLiteratureBridge
import Zeta23.ExceptionalZero.NegativeWeilTestSupport
import Zeta23.CCM.LocalizedWeilRestriction

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

/-!
# W2-ZS: concrete-zeta zero-side evenization

This module avoids opening the pole/prime/gamma decomposition of
`EF.literatureRHS`.  Instead it uses the unconditional concrete zeta symmetry
`rho -> 1-rho` to reindex the summable zero side supplied by `EF_lit`.

The final theorem identifies the genuine diagonal Weil form with the repository
localized additive RHS for every compact C² complex-valued test.  Composed with
W1, this produces a strict-aperture negative localized additive witness from any
hypothetical off-line zero.

Claim firewall: no generic `ZeroConfig` one-sub symmetry is asserted; this
argument is concrete-zeta-specific.
-/

/-! ## 1. Concrete zeta carrier involution -/

private def zetaOneSubPoint
    (ρ : zetaZeroConfig.carrier) : zetaZeroConfig.carrier :=
  ⟨1 - (ρ : ℂ), by
    have hρ : IsNontrivialZero (ρ : ℂ) := by
      simpa using ρ.property
    simpa using zeta_one_sub_zero hρ⟩

/-- The direct concrete-zeta involution `rho |-> 1-rho` on the exact carrier. -/
def zetaOneSubEquiv :
    zetaZeroConfig.carrier ≃ zetaZeroConfig.carrier where
  toFun := zetaOneSubPoint
  invFun := zetaOneSubPoint
  left_inv := by
    intro ρ
    apply Subtype.ext
    simp [zetaOneSubPoint]
  right_inv := by
    intro ρ
    apply Subtype.ext
    simp [zetaOneSubPoint]

@[simp] theorem zetaOneSubEquiv_coe
    (ρ : zetaZeroConfig.carrier) :
    ((zetaOneSubEquiv ρ : zetaZeroConfig.carrier) : ℂ) =
      1 - (ρ : ℂ) := rfl

@[simp] theorem zetaOneSubEquiv_mult
    (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.mult (zetaOneSubEquiv ρ) =
      zetaZeroConfig.mult ρ := by
  have hρ : IsNontrivialZero (ρ : ℂ) := by
    simpa using ρ.property
  change zeroMult ((zetaOneSubEquiv ρ : zetaZeroConfig.carrier) : ℂ) =
    zeroMult (ρ : ℂ)
  rw [zetaOneSubEquiv_coe]
  exact zeta_mult_one_sub hρ

/-- The direct one-sub involution reverses the `gammaOf` spectral coordinate. -/
@[simp] theorem gammaOf_one_sub (ρ : ℂ) :
    gammaOf (1 - ρ) = -gammaOf ρ := by
  unfold gammaOf
  ring

@[simp] theorem gammaOf_zetaOneSubEquiv
    (ρ : zetaZeroConfig.carrier) :
    gammaOf (zetaOneSubEquiv ρ) = -gammaOf ρ := by
  rw [show ((zetaOneSubEquiv ρ : zetaZeroConfig.carrier) : ℂ) =
      1 - (ρ : ℂ) from zetaOneSubEquiv_coe ρ]
  exact gammaOf_one_sub (ρ : ℂ)

/-! ## 2. Reflection of physical tests -/

/-- Reflection in the additive test coordinate. -/
def zeroSideReflectTest (k : ℝ → ℂ) : ℝ → ℂ :=
  fun x => k (-x)

theorem zeroSideReflectTest_contDiff
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) :
    ContDiff ℝ 2 (zeroSideReflectTest k) := by
  change ContDiff ℝ 2 (fun x : ℝ => k (-x))
  exact hk.comp contDiff_neg

theorem zeroSideReflectTest_hasCompactSupport
    {k : ℝ → ℂ}
    (hkc : HasCompactSupport k) :
    HasCompactSupport (zeroSideReflectTest k) := by
  change HasCompactSupport (fun x : ℝ => k (-x))
  exact hkc.comp_homeomorph (Homeomorph.neg ℝ)

/-- Exact paper-Fourier convention under reflection:
`paperFT(k(-·))(z) = paperFT(k)(-z)`. -/
theorem paperFT_zeroSideReflectTest
    (k : ℝ → ℂ) (z : ℂ) :
    paperFT (zeroSideReflectTest k) z = paperFT k (-z) := by
  unfold paperFT zeroSideReflectTest
  rw [← integral_neg_eq_self]
  congr 1
  funext u
  simp only [neg_neg, Complex.ofReal_neg]
  congr 1
  ring_nf

/-! ## 3. Zero-side summand and reindexing -/

/-- The concrete literature-form zero summand, named locally for readable reindexing. -/
def zetaLiteratureZeroSummand
    (k : ℝ → ℂ)
    (ρ : zetaZeroConfig.carrier) : ℂ :=
  (zetaZeroConfig.mult ρ : ℂ) * paperFT k (gammaOf ρ)

theorem zetaLiteratureZeroSummand_reflect
    (k : ℝ → ℂ)
    (ρ : zetaZeroConfig.carrier) :
    zetaLiteratureZeroSummand (zeroSideReflectTest k) ρ =
      zetaLiteratureZeroSummand k (zetaOneSubEquiv ρ) := by
  unfold zetaLiteratureZeroSummand
  rw [paperFT_zeroSideReflectTest, zetaOneSubEquiv_mult,
    gammaOf_zetaOneSubEquiv]

/-- Bijective reindexing of the concrete zeta zero side under `rho |-> 1-rho`.
This step is a pure equivalence reindex; additive `tsum` distribution is handled
separately below under explicit `Summable` certificates. -/
theorem zetaLiteratureZeroTsum_reflect_eq
    (k : ℝ → ℂ) :
    (∑' ρ : zetaZeroConfig.carrier,
      zetaLiteratureZeroSummand (zeroSideReflectTest k) ρ) =
    ∑' ρ : zetaZeroConfig.carrier,
      zetaLiteratureZeroSummand k ρ := by
  calc
    (∑' ρ : zetaZeroConfig.carrier,
      zetaLiteratureZeroSummand (zeroSideReflectTest k) ρ)
        =
      ∑' ρ : zetaZeroConfig.carrier,
        zetaLiteratureZeroSummand k (zetaOneSubEquiv ρ) := by
          apply tsum_congr
          intro ρ
          exact zetaLiteratureZeroSummand_reflect k ρ
    _ =
      ∑' ρ : zetaZeroConfig.carrier,
        zetaLiteratureZeroSummand k ρ :=
      Equiv.tsum_eq zetaOneSubEquiv
        (fun ρ => zetaLiteratureZeroSummand k ρ)

/-! ## 4. Half-evenization and legal Fourier linearity -/

/-- Half-evenization of a physical additive test. -/
def zeroSideHalfEvenTest (k : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (1 / 2 : ℂ) * (k x + k (-x))

theorem zeroSideHalfEvenTest_contDiff
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) :
    ContDiff ℝ 2 (zeroSideHalfEvenTest k) := by
  have hr : ContDiff ℝ 2 (zeroSideReflectTest k) :=
    zeroSideReflectTest_contDiff hk
  have hadd : ContDiff ℝ 2 (fun x => k x + zeroSideReflectTest k x) :=
    hk.add hr
  have hconst : ContDiff ℝ 2 (fun _ : ℝ => (1 / 2 : ℂ)) := contDiff_const
  change ContDiff ℝ 2
    (fun x => (1 / 2 : ℂ) * (k x + zeroSideReflectTest k x))
  exact hconst.mul hadd

theorem zeroSideHalfEvenTest_hasCompactSupport
    {k : ℝ → ℂ}
    (hkc : HasCompactSupport k) :
    HasCompactSupport (zeroSideHalfEvenTest k) := by
  have hr : HasCompactSupport (zeroSideReflectTest k) :=
    zeroSideReflectTest_hasCompactSupport hkc
  have hadd : HasCompactSupport (k + zeroSideReflectTest k) :=
    hkc.add hr
  have hmul :=
    hadd.comp_left
      (g := fun w : ℂ => (1 / 2 : ℂ) * w)
      (by simp)
  change HasCompactSupport
    ((fun w : ℂ => (1 / 2 : ℂ) * w) ∘ (k + zeroSideReflectTest k))
  exact hmul

/-- A continuous compactly supported test has an integrable paper-FT integrand
at every complex spectral argument. -/
theorem integrable_paperFT_integrand_of_continuous_compact
    {k : ℝ → ℂ}
    (hk : Continuous k)
    (hkc : HasCompactSupport k)
    (z : ℂ) :
    Integrable
      (fun x : ℝ => k x * Complex.exp (Complex.I * z * (x : ℂ))) := by
  have hc :
      Continuous
        (fun x : ℝ => k x * Complex.exp (Complex.I * z * (x : ℂ))) := by
    fun_prop
  have hs :
      HasCompactSupport
        (fun x : ℝ => k x * Complex.exp (Complex.I * z * (x : ℂ))) := by
    exact hkc.mul_right
  exact hc.integrable_of_hasCompactSupport hs

/-- Legal Fourier linearity for the half-even test on the compact continuous
class needed by `EF_lit`. -/
theorem paperFT_zeroSideHalfEvenTest
    {k : ℝ → ℂ}
    (hk : Continuous k)
    (hkc : HasCompactSupport k)
    (z : ℂ) :
    paperFT (zeroSideHalfEvenTest k) z =
      (1 / 2 : ℂ) * (paperFT k z + paperFT k (-z)) := by
  have hrcont : Continuous (zeroSideReflectTest k) := by
    change Continuous (fun x : ℝ => k (-x))
    exact hk.comp continuous_neg
  have hrsupp : HasCompactSupport (zeroSideReflectTest k) :=
    zeroSideReflectTest_hasCompactSupport hkc
  have hki :=
    integrable_paperFT_integrand_of_continuous_compact hk hkc z
  have hri :=
    integrable_paperFT_integrand_of_continuous_compact hrcont hrsupp z
  calc
    paperFT (zeroSideHalfEvenTest k) z
        =
      (1 / 2 : ℂ) *
        (paperFT k z + paperFT (zeroSideReflectTest k) z) := by
          unfold paperFT zeroSideHalfEvenTest
          have hpoint :
              (fun u : ℝ =>
                (1 / 2 : ℂ) * (k u + k (-u)) *
                  Complex.exp (Complex.I * z * (u : ℂ))) =
              (fun u : ℝ =>
                (1 / 2 : ℂ) *
                  (k u * Complex.exp (Complex.I * z * (u : ℂ)) +
                    zeroSideReflectTest k u *
                      Complex.exp (Complex.I * z * (u : ℂ)))) := by
            funext u
            simp only [zeroSideReflectTest]
            ring
          rw [hpoint, Zeta23.EF.cintegral_const_mul, integral_add hki hri]
    _ =
      (1 / 2 : ℂ) * (paperFT k z + paperFT k (-z)) := by
        rw [paperFT_zeroSideReflectTest]

/-! ## 5. EF_lit contraction on the zero side -/

private theorem zetaLiteratureZeroSummand_halfEven
    {k : ℝ → ℂ}
    (hk : Continuous k)
    (hkc : HasCompactSupport k)
    (ρ : zetaZeroConfig.carrier) :
    zetaLiteratureZeroSummand (zeroSideHalfEvenTest k) ρ =
      (1 / 2 : ℂ) *
        (zetaLiteratureZeroSummand k ρ +
          zetaLiteratureZeroSummand (zeroSideReflectTest k) ρ) := by
  unfold zetaLiteratureZeroSummand
  rw [paperFT_zeroSideHalfEvenTest hk hkc, paperFT_zeroSideReflectTest]
  ring

/-- Concrete-zeta half-evenization leaves the literature RHS unchanged.

The proof never opens `literatureRHS`: `EF_lit` is applied independently to
`k`, its reflection, and its half-evenization; the zero side is then
recombined only under the explicit summability certificates returned by
`EF_lit`. -/
theorem zeta_literatureRHS_halfEven_eq
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) :
    Zeta23.EF.literatureRHS (zeroSideHalfEvenTest k) =
      Zeta23.EF.literatureRHS k := by
  have hrk : ContDiff ℝ 2 (zeroSideReflectTest k) :=
    zeroSideReflectTest_contDiff hk
  have hrkc : HasCompactSupport (zeroSideReflectTest k) :=
    zeroSideReflectTest_hasCompactSupport hkc
  have hhk : ContDiff ℝ 2 (zeroSideHalfEvenTest k) :=
    zeroSideHalfEvenTest_contDiff hk
  have hhkc : HasCompactSupport (zeroSideHalfEvenTest k) :=
    zeroSideHalfEvenTest_hasCompactSupport hkc

  obtain ⟨hsumk, heqk⟩ :=
    zeta_explicit_formula_literature k hk hkc
  obtain ⟨hsumr, heqr⟩ :=
    zeta_explicit_formula_literature
      (zeroSideReflectTest k) hrk hrkc
  obtain ⟨hsumh, heqh⟩ :=
    zeta_explicit_formula_literature
      (zeroSideHalfEvenTest k) hhk hhkc

  have hsumk' :
      Summable
        (fun ρ : zetaZeroConfig.carrier =>
          zetaLiteratureZeroSummand k ρ) := by
    simpa [zetaLiteratureZeroSummand] using hsumk
  have hsumr' :
      Summable
        (fun ρ : zetaZeroConfig.carrier =>
          zetaLiteratureZeroSummand (zeroSideReflectTest k) ρ) := by
    simpa [zetaLiteratureZeroSummand] using hsumr

  have hreflect :
      (∑' ρ : zetaZeroConfig.carrier,
        zetaLiteratureZeroSummand (zeroSideReflectTest k) ρ) =
      ∑' ρ : zetaZeroConfig.carrier,
        zetaLiteratureZeroSummand k ρ :=
    zetaLiteratureZeroTsum_reflect_eq k

  have hhalf_hasSum :
      HasSum
        (fun ρ : zetaZeroConfig.carrier =>
          (1 / 2 : ℂ) *
            (zetaLiteratureZeroSummand k ρ +
              zetaLiteratureZeroSummand (zeroSideReflectTest k) ρ))
        ((1 / 2 : ℂ) *
          ((∑' ρ : zetaZeroConfig.carrier,
              zetaLiteratureZeroSummand k ρ) +
            (∑' ρ : zetaZeroConfig.carrier,
              zetaLiteratureZeroSummand (zeroSideReflectTest k) ρ))) :=
    (hsumk'.hasSum.add hsumr'.hasSum).mul_left (1 / 2 : ℂ)

  have hhalf :
      (∑' ρ : zetaZeroConfig.carrier,
        zetaLiteratureZeroSummand (zeroSideHalfEvenTest k) ρ) =
      ∑' ρ : zetaZeroConfig.carrier,
        zetaLiteratureZeroSummand k ρ := by
    calc
      (∑' ρ : zetaZeroConfig.carrier,
        zetaLiteratureZeroSummand (zeroSideHalfEvenTest k) ρ)
          =
        ∑' ρ : zetaZeroConfig.carrier,
          (1 / 2 : ℂ) *
            (zetaLiteratureZeroSummand k ρ +
              zetaLiteratureZeroSummand (zeroSideReflectTest k) ρ) := by
                apply tsum_congr
                intro ρ
                exact zetaLiteratureZeroSummand_halfEven hk.continuous hkc ρ
      _ =
        (1 / 2 : ℂ) *
          ((∑' ρ : zetaZeroConfig.carrier,
              zetaLiteratureZeroSummand k ρ) +
            (∑' ρ : zetaZeroConfig.carrier,
              zetaLiteratureZeroSummand (zeroSideReflectTest k) ρ)) :=
        hhalf_hasSum.tsum_eq
      _ =
        ∑' ρ : zetaZeroConfig.carrier,
          zetaLiteratureZeroSummand k ρ := by
            rw [hreflect]
            ring

  rw [← heqh, ← heqk]
  simpa [zetaLiteratureZeroSummand] using hhalf

/-! ## 6. Diagonal localized normalization and production bridge -/

/-- On the diagonal, the repository localized half-correlation is exactly the
half-evenization of the W2-A Weil convolution test. -/
theorem localizedWeilHalfTest_self_eq_zeroSideHalfEvenTest
    (h : ℝ → ℂ) :
    Zeta23.CCM.localizedWeilHalfTest h h =
      zeroSideHalfEvenTest (Zeta23.EF.weilTest h h) := by
  funext y
  simp [Zeta23.CCM.localizedWeilHalfTest,
    Zeta23.CCM.localizedWeilCorrelation,
    zeroSideHalfEvenTest]

/-- **W2-ZS / diagonal W2-C endpoint.**  For every compact C² concrete-zeta
test, the genuine diagonal Weil form is exactly the repository localized
additive explicit-formula RHS.  No aperture, pole-neutrality, gamma/digamma
symmetry, or weighted gamma-integrability hypothesis is required. -/
theorem zeta_W_self_eq_localizedWeilAdditiveRHS
    {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) :
    zetaZeroConfig.W h h =
      Zeta23.CCM.localizedWeilAdditiveRHS h h := by
  have hkd : ContDiff ℝ 2 (Zeta23.EF.weilTest h h) :=
    Zeta23.EF.weilTest_contDiff hh hh.continuous hhc
  have hkc : HasCompactSupport (Zeta23.EF.weilTest h h) :=
    Zeta23.EF.weilTest_hasCompactSupport hhc hhc
  calc
    zetaZeroConfig.W h h
        =
      Zeta23.EF.literatureRHS (Zeta23.EF.weilTest h h) :=
        zeta_W_self_eq_literatureRHS_weilTest hh hhc
    _ =
      Zeta23.EF.literatureRHS
        (zeroSideHalfEvenTest (Zeta23.EF.weilTest h h)) :=
        (zeta_literatureRHS_halfEven_eq hkd hkc).symm
    _ =
      Zeta23.EF.literatureRHS
        (Zeta23.CCM.localizedWeilHalfTest h h) := by
          rw [localizedWeilHalfTest_self_eq_zeroSideHalfEvenTest]
    _ =
      Zeta23.CCM.localizedWeilAdditiveRHS h h := rfl

/-! ## 7. Cash out W1 into a negative localized additive witness -/

/-- Strong W1+W2-ZS endpoint: every hypothetical off-line zero yields a
pole-neutral compact C² test in an explicit strict aperture margin whose
localized additive RHS is strictly negative. -/
theorem
    exists_strictAperture_poleNeutral_negativeLocalizedWeilAdditiveRHS_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ r : ℝ, 0 < r ∧ L = 4 * r ∧
        ∃ h : ℝ → ℂ,
          ContDiff ℝ 2 h ∧
          HasCompactSupport h ∧
          tsupport h ⊆ Ioo r (3 * r) ∧
          tsupport h ⊆ Ioo 0 L ∧
          paperFT h (I / 2) = 0 ∧
          paperFT h (-I / 2) = 0 ∧
          (Zeta23.CCM.localizedWeilAdditiveRHS h h).re < 0 := by
  obtain ⟨L, hL, r, hr, hLr, h, hh, hhc, hmargin, hsupp, hp, hn, hneg⟩ :=
    exists_strictAperture_poleNeutral_negativeWeilTest_of_offLine_zero ρ₀ hoff
  refine ⟨L, hL, r, hr, hLr, h, hh, hhc, hmargin, hsupp, hp, hn, ?_⟩
  rw [← zeta_W_self_eq_localizedWeilAdditiveRHS hh hhc]
  exact hneg

/-- Minimal strict-aperture negative localized-additive endpoint for F0-B. -/
theorem exists_strictAperture_negativeLocalizedWeilAdditiveRHS_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ h : ℝ → ℂ,
        ContDiff ℝ 2 h ∧
        HasCompactSupport h ∧
        tsupport h ⊆ Ioo 0 L ∧
        (Zeta23.CCM.localizedWeilAdditiveRHS h h).re < 0 := by
  obtain ⟨L, hL, r, _hr, _hLr, h, hh, hhc, _hmargin, hsupp, _hp, _hn, hneg⟩ :=
    exists_strictAperture_poleNeutral_negativeLocalizedWeilAdditiveRHS_of_offLine_zero
      ρ₀ hoff
  exact ⟨L, hL, h, hh, hhc, hsupp, hneg⟩

/-- Existential logical wrapper used by the F1 roadmap. -/
theorem
    exists_strictAperture_negativeLocalizedWeilAdditiveRHS_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ h : ℝ → ℂ,
        ContDiff ℝ 2 h ∧
        HasCompactSupport h ∧
        tsupport h ⊆ Ioo 0 L ∧
        (Zeta23.CCM.localizedWeilAdditiveRHS h h).re < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_strictAperture_negativeLocalizedWeilAdditiveRHS_of_offLine_zero
    ρ₀ hρ₀

end Zeta23.ExceptionalZero
