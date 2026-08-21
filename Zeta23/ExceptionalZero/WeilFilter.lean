import Zeta23.ExceptionalZero.ExposedPole
import Zeta23.ExceptionalZero.PoleKiller
import Zeta23.ExceptionalZero.WeilBridge
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex MeasureTheory

/-! ## The natural Weil zero filter

`weilZeroFilter k` evaluates the paper Fourier transform of a test function at the spectral
points `gammaOf ρ = (ρ - 1/2)/i` of the distinct nontrivial zeta zeros.  Its
multiplicity-weighted coefficients are exactly the zero-side summands of the literature-form
Weil explicit formula, so absolute summability and the aperture-translation identity are
inherited from `EF_lit` with no second zero model. -/

/-- The natural spectral filter attached to a Weil test function. -/
def weilZeroFilter (k : ℝ → ℂ) : ZeroFilter :=
  fun ρ => paperFT k (gammaOf (ρ : ℂ))

/-- The multiplicity-weighted Weil filter coefficient is the explicit-formula zero-side
summand. -/
theorem zeroFilterCoeff_weilZeroFilter (k : ℝ → ℂ) (ρ : zetaZeroConfig.carrier) :
    zeroFilterCoeff (weilZeroFilter k) ρ =
      (zeroMult (ρ : ℂ) : ℂ) * paperFT k (gammaOf (ρ : ℂ)) := rfl

/-- Under the exact `C²` compact-support Weil hypotheses, the natural filter is absolutely
summable: `EF_lit`'s summability clause upgrades to norm summability because `ℂ` is
finite-dimensional over `ℝ`. -/
theorem absolutelySummableZeroFilter_weil {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    AbsolutelySummableZeroFilter (weilZeroFilter k) := by
  have hsum := (zeta_explicit_formula_literature k hk hkc).1
  have hnorm : Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖(zetaZeroConfig.mult (ρ : ℂ) : ℂ) * paperFT k (gammaOf (ρ : ℂ))‖) :=
    summable_norm_iff.mpr hsum
  exact hnorm

/-! ## Exact aperture-translation identity

Right translation of the test by `t = 2a` multiplies each spectral mode at `gammaOf ρ` by
exactly `exp(2(ρ - 1/2)a)`: the factor `i·gammaOf ρ = ρ - 1/2` converts the Fourier phase into
the centered exponential of the filtered zero family.  Every sign and factor of two below is
claim-bearing. -/

theorem contDiff_translateRight {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (t : ℝ) :
    ContDiff ℝ 2 (translateRight k t) := by
  have heq : translateRight k t = k ∘ (fun x : ℝ => x - t) := rfl
  rw [heq]
  exact hk.comp (contDiff_id.sub contDiff_const)

theorem hasCompactSupport_translateRight {k : ℝ → ℂ}
    (hkc : HasCompactSupport k) (t : ℝ) :
    HasCompactSupport (translateRight k t) := by
  have heq : translateRight k t = k ∘ (Homeomorph.subRight t) := rfl
  rw [heq]
  exact hkc.comp_homeomorph _

/-- Translation by `2a`, evaluated at a spectral point: the phase is the centered
exponential `exp((2(ρ - 1/2))·a)`. -/
theorem paperFT_translateRight_gammaOf (k : ℝ → ℂ) (a : ℝ) (ρ : ℂ) :
    paperFT (translateRight k (2 * a)) (gammaOf ρ) =
      Complex.exp ((2 * (ρ - (1 / 2 : ℂ))) * (a : ℂ)) * paperFT k (gammaOf ρ) := by
  rw [paperFT_translateRight]
  have harg : I * gammaOf ρ * ((2 * a : ℝ) : ℂ) =
      (2 * (ρ - (1 / 2 : ℂ))) * (a : ℂ) := by
    unfold gammaOf
    push_cast
    field_simp
  rw [harg]

/-- **The exact Weil bridge.**  For a `C²` compactly supported test, the filtered zero family of
the natural Weil filter at critical-line center `1/2` coincides, at every aperture `a`, with the
literature explicit-formula right-hand side of the right-translated test `k(· - 2a)`.  No second
zero model and no normalization slack: the zero side of `EF_lit` for `translateRight k (2a)` IS
the filtered exponential family. -/
theorem filteredZeroFamily_weilZeroFilter_eq_literatureRHS {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (a : ℝ) :
    filteredZeroFamily (weilZeroFilter k) (1 / 2 : ℂ) a =
      Zeta23.EF.literatureRHS (translateRight k (2 * a)) := by
  have hk' : ContDiff ℝ 2 (translateRight k (2 * a)) := contDiff_translateRight hk _
  have hkc' : HasCompactSupport (translateRight k (2 * a)) :=
    hasCompactSupport_translateRight hkc _
  have hEF := (zeta_explicit_formula_literature _ hk' hkc').2
  rw [← hEF]
  unfold filteredZeroFamily
  refine tsum_congr fun ρ => ?_
  rw [paperFT_translateRight_gammaOf k a (ρ : ℂ)]
  show (zeroMult (ρ : ℂ) : ℂ) * paperFT k (gammaOf (ρ : ℂ)) *
      Complex.exp ((2 * ((ρ : ℂ) - (1 / 2 : ℂ))) * (a : ℂ)) =
    (zeroMult (ρ : ℂ) : ℂ) *
      (Complex.exp ((2 * ((ρ : ℂ) - (1 / 2 : ℂ))) * (a : ℂ)) *
        paperFT k (gammaOf (ρ : ℂ)))
  ring

/-! ## Instantiated exposed-pole theorem for the zeta explicit formula -/

/-- **Concrete zero-side detector for ζ.**  If a `C²` compactly supported Weil test sees a zeta
zero lying strictly to the right of the critical line, then the literature explicit-formula RHS
of the right-translated tests `k(· - 2a)` cannot be subexponential in the aperture `a`.  The
whole growth obstruction therefore sits on the arithmetic side of the explicit formula. -/
theorem not_subexponential_weilLiteratureRHS_of_right_zero {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (ρ₀ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ₀ : ℂ).re)
    (hvis : paperFT k (gammaOf (ρ₀ : ℂ)) ≠ 0) :
    ¬ Subexponential
      (fun a => ‖Zeta23.EF.literatureRHS (translateRight k (2 * a))‖) := by
  have hφ := absolutelySummableZeroFilter_weil hk hkc
  have hc : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have hcoeff : zeroFilterCoeff (weilZeroFilter k) ρ₀ ≠ 0 := by
    rw [zeroFilterCoeff_weilZeroFilter]
    refine mul_ne_zero ?_ hvis
    have h1 : 1 ≤ zeroMult (ρ₀ : ℂ) := zetaZeroConfig.one_le_mult _ ρ₀.2
    exact_mod_cast Nat.one_le_iff_ne_zero.mp h1
  have hmain := not_subexponential_filteredZeroFamily_of_right_zero hφ hc ρ₀ hright hcoeff
  intro hsubRHS
  apply hmain
  intro ε hε
  obtain ⟨A, hA⟩ := hsubRHS ε hε
  refine ⟨A, fun a ha => ?_⟩
  show ‖filteredZeroFamily (weilZeroFilter k) (1 / 2 : ℂ) a‖ ≤ Real.exp (ε * a)
  rw [filteredZeroFamily_weilZeroFilter_eq_literatureRHS hk hkc a]
  exact hA a ha

/-! ## The pole-killing operator

The literature RHS carries the deterministic pole transforms `h(±i/2)`; under right translation
by `2a` the term `h(-i/2)` grows like `e^a` for the trivial reason that ζ has a pole at `s = 1`.
Applying the second-order operator `q ↦ q'' - (1/4)q` kills both pole evaluations exactly, while
at a spectral point `gammaOf ρ` it multiplies the transform by `ρ(ρ-1) ≠ 0` — visibility inside
the open critical strip survives.  Minimum clean regularity: `q ∈ C⁴` makes `q''` a legal `C²`
Weil test. -/

/-- The pole-killing differential operator `q ↦ q'' − (1/4)·q`. -/
def poleKilled (q : ℝ → ℂ) : ℝ → ℂ :=
  fun x => deriv (deriv q) x - (1 / 4 : ℂ) * q x

theorem contDiff_poleKilled {q : ℝ → ℂ} (hq : ContDiff ℝ 4 q) :
    ContDiff ℝ 2 (poleKilled q) := by
  have h3 : ContDiff ℝ 3 (deriv q) := hq.deriv'
  have h2 : ContDiff ℝ 2 (deriv (deriv q)) := h3.deriv'
  exact h2.sub (contDiff_const.mul (hq.of_le (by norm_num)))

theorem hasCompactSupport_poleKilled {q : ℝ → ℂ} (hqc : HasCompactSupport q) :
    HasCompactSupport (poleKilled q) := by
  have h1 : HasCompactSupport (deriv (deriv q)) := hqc.deriv.deriv
  have h2 : HasCompactSupport (fun x : ℝ => (1 / 4 : ℂ) * q x) := hqc.mul_left
  exact h1.sub h2

/-- Exact transform of the pole-killed test: `(q'' − q/4)^ (z) = −(z² + 1/4)·q̂(z)`. -/
theorem paperFT_poleKilled {q : ℝ → ℂ} (hq : ContDiff ℝ 2 q)
    (hqc : HasCompactSupport q) (z : ℂ) :
    paperFT (poleKilled q) z = -(z ^ 2 + 1 / 4) * paperFT q z := by
  have hce : Continuous fun u : ℝ => cexp (I * z * u) := by fun_prop
  have hcont2 : Continuous (deriv (deriv q)) := (hq.deriv').continuous_deriv le_rfl
  have hint1 : Integrable (fun u : ℝ => deriv (deriv q) u * cexp (I * z * u)) :=
    (hcont2.mul hce).integrable_of_hasCompactSupport (hqc.deriv.deriv.mul_right)
  have hint2 : Integrable (fun u : ℝ => (1 / 4 : ℂ) * (q u * cexp (I * z * u))) :=
    ((hq.continuous.mul hce).integrable_of_hasCompactSupport hqc.mul_right).const_mul _
  unfold poleKilled paperFT
  have hsplit : (fun u : ℝ =>
      (deriv (deriv q) u - (1 / 4 : ℂ) * q u) * cexp (I * z * u)) =
      fun u : ℝ => deriv (deriv q) u * cexp (I * z * u) -
        (1 / 4 : ℂ) * (q u * cexp (I * z * u)) := by
    funext u
    ring
  rw [hsplit, integral_sub hint1 hint2, integral_const_mul_C]
  have hdd : (∫ u : ℝ, deriv (deriv q) u * cexp (I * z * u)) =
      -z ^ 2 * ∫ u : ℝ, q u * cexp (I * z * u) := paperFT_deriv_deriv hq hqc z
  rw [hdd]
  ring

/-- The pole-killed test annihilates the explicit-formula pole point `+i/2`. -/
theorem paperFT_poleKilled_I_half {q : ℝ → ℂ} (hq : ContDiff ℝ 2 q)
    (hqc : HasCompactSupport q) :
    paperFT (poleKilled q) (I / 2) = 0 := by
  rw [paperFT_poleKilled hq hqc]
  have hfac : -((I / 2 : ℂ) ^ 2 + 1 / 4) = 0 := by
    have h2 : (I / 2 : ℂ) ^ 2 = I ^ 2 / 4 := by ring
    rw [h2, I_sq]
    norm_num
  rw [hfac, zero_mul]

/-- The pole-killed test annihilates the explicit-formula pole point `−i/2`. -/
theorem paperFT_poleKilled_neg_I_half {q : ℝ → ℂ} (hq : ContDiff ℝ 2 q)
    (hqc : HasCompactSupport q) :
    paperFT (poleKilled q) (-I / 2) = 0 := by
  rw [paperFT_poleKilled hq hqc]
  have hfac : -((-I / 2 : ℂ) ^ 2 + 1 / 4) = 0 := by
    have h2 : (-I / 2 : ℂ) ^ 2 = I ^ 2 / 4 := by ring
    rw [h2, I_sq]
    norm_num
  rw [hfac, zero_mul]

/-- Translation cannot resurrect the killed poles: the translated pole-killed test still
vanishes at both explicit-formula pole points. -/
theorem paperFT_translateRight_poleKilled_I_half {q : ℝ → ℂ} (hq : ContDiff ℝ 2 q)
    (hqc : HasCompactSupport q) (t : ℝ) :
    paperFT (translateRight (poleKilled q) t) (I / 2) = 0 ∧
      paperFT (translateRight (poleKilled q) t) (-I / 2) = 0 := by
  constructor
  · rw [paperFT_translateRight, paperFT_poleKilled_I_half hq hqc, mul_zero]
  · rw [paperFT_translateRight, paperFT_poleKilled_neg_I_half hq hqc, mul_zero]

/-- For a pole-killed translated test the literature explicit-formula RHS is exactly the
arithmetic side: minus the weighted prime sum plus the Archimedean integral.  The two
deterministic pole transforms are identically zero at every aperture, so any residual growth of
the RHS is arithmetic, never the trivial `e^a` from the pole of ζ at `s = 1`. -/
theorem literatureRHS_translateRight_poleKilled_eq {q : ℝ → ℂ} (hq : ContDiff ℝ 2 q)
    (hqc : HasCompactSupport q) (t : ℝ) :
    Zeta23.EF.literatureRHS (translateRight (poleKilled q) t) =
      -(∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
          * (translateRight (poleKilled q) t (Real.log n) +
             translateRight (poleKilled q) t (-Real.log n)))
        + (1 / (2 * Real.pi) : ℂ) *
          ∫ r : ℝ, paperFT (translateRight (poleKilled q) t) r *
            ((Zeta23.EF.gammaBracket r : ℝ) : ℂ) := by
  unfold Zeta23.EF.literatureRHS
  rw [(paperFT_translateRight_poleKilled_I_half hq hqc t).1,
    (paperFT_translateRight_poleKilled_I_half hq hqc t).2]
  ring

/-- At a spectral point `gammaOf ρ` the pole-killer polynomial factor is exactly `ρ(ρ − 1)`. -/
theorem poleKiller_factor_eq (ρ : ℂ) :
    -((gammaOf ρ) ^ 2 + 1 / 4) = ρ * (ρ - 1) := by
  unfold gammaOf
  have h1 : ((ρ - 1 / 2) / I) ^ 2 = -((ρ - 1 / 2) ^ 2) := by
    rw [div_pow, I_sq]
    ring
  rw [h1]
  ring

/-- Pole-killing preserves visibility at every nontrivial zero: the factor `ρ(ρ−1)` cannot
vanish inside the open critical strip. -/
theorem paperFT_poleKilled_ne_zero_at_zero {q : ℝ → ℂ} (hq : ContDiff ℝ 2 q)
    (hqc : HasCompactSupport q) (ρ : zetaZeroConfig.carrier)
    (hvis : paperFT q (gammaOf (ρ : ℂ)) ≠ 0) :
    paperFT (poleKilled q) (gammaOf (ρ : ℂ)) ≠ 0 := by
  rw [paperFT_poleKilled hq hqc, poleKiller_factor_eq]
  have h0 : (ρ : ℂ) ≠ 0 := by
    intro h
    have hre : 0 < (ρ : ℂ).re := ρ.2.2.1
    rw [h] at hre
    simp at hre
  have h1 : (ρ : ℂ) - 1 ≠ 0 := by
    intro h
    have hre : (ρ : ℂ).re < 1 := ρ.2.2.2
    rw [sub_eq_zero] at h
    rw [h] at hre
    simp at hre
  exact mul_ne_zero (mul_ne_zero h0 h1) hvis

/-! ## Target-adaptive visibility

A single frozen compactly supported test cannot be declared nonvanishing on every possible
spectral point.  Under the contradiction hypothesis that a particular zero exists, however, a
complex-modulated smooth bump sees it: modulating by the full (complex) target frequency turns
the paper transform at the target into the strictly positive integral of the bump. -/

/-- Every complex spectral point is visible to some smooth compactly supported test. -/
theorem exists_contDiff_visible_test (w : ℂ) :
    ∃ q : ℝ → ℂ, ContDiff ℝ 4 q ∧ HasCompactSupport q ∧ paperFT q w ≠ 0 := by
  let ψ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun u : ℝ => (ψ u : ℂ) * Complex.exp (-(I * w * u)), ?_, ?_, ?_⟩
  · have hcoe : ContDiff ℝ 4 (fun u : ℝ => ((ψ u : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ψ.contDiff
    have hphase : ContDiff ℝ 4 (fun u : ℝ => -(I * w * (u : ℂ))) :=
      (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
    exact hcoe.mul hphase.cexp
  · have hψc : HasCompactSupport (fun u : ℝ => ((ψ u : ℝ) : ℂ)) :=
      ψ.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
    exact hψc.mul_right
  · have hpt : ∀ u : ℝ,
        ((ψ u : ℂ) * Complex.exp (-(I * w * u))) * Complex.exp (I * w * u) =
          ((ψ u : ℝ) : ℂ) := by
      intro u
      rw [mul_assoc, ← Complex.exp_add]
      simp
    unfold paperFT
    rw [show (fun u : ℝ =>
        ((ψ u : ℂ) * Complex.exp (-(I * w * u))) * Complex.exp (I * w * u)) =
        fun u : ℝ => ((ψ u : ℝ) : ℂ) from funext hpt]
    rw [integral_complex_ofReal]
    exact_mod_cast (ψ.integral_pos).ne'

/-- **Adaptive pole-killed zero-side closure for ζ.**  For every hypothetical zeta zero strictly
to the right of the critical line there exists an admissible Weil test — `C²`, compactly
supported, with both explicit-formula pole transforms killed — whose translated literature RHS
fails every subexponential bound.  Combined with the reflection `ρ ↦ 1 − ρ̄`, this reduces RH to
one theorem: an unconditional subexponential upper bound for the arithmetic side of the same
translated tests. -/
theorem exists_poleKilled_test_not_subexponential_of_right_zero
    (ρ₀ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ₀ : ℂ).re) :
    ∃ k : ℝ → ℂ, ContDiff ℝ 2 k ∧ HasCompactSupport k ∧
      paperFT k (I / 2) = 0 ∧ paperFT k (-I / 2) = 0 ∧
      ¬ Subexponential
        (fun a => ‖Zeta23.EF.literatureRHS (translateRight k (2 * a))‖) := by
  obtain ⟨q, hq4, hqc, hqvis⟩ := exists_contDiff_visible_test (gammaOf (ρ₀ : ℂ))
  have hq2 : ContDiff ℝ 2 q := hq4.of_le (by norm_num)
  refine ⟨poleKilled q, contDiff_poleKilled hq4, hasCompactSupport_poleKilled hqc,
    paperFT_poleKilled_I_half hq2 hqc, paperFT_poleKilled_neg_I_half hq2 hqc, ?_⟩
  exact not_subexponential_weilLiteratureRHS_of_right_zero
    (contDiff_poleKilled hq4) (hasCompactSupport_poleKilled hqc) ρ₀ hright
    (paperFT_poleKilled_ne_zero_at_zero hq2 hqc ρ₀ hqvis)

end Zeta23.ExceptionalZero
