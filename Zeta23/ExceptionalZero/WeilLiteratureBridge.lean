import Zeta23.ExceptionalZero.WeilBridge

noncomputable section

namespace Zeta23.ExceptionalZero

/-- **W2-A, generic form.**  The literature explicit formula applied to the exact
convolution test `weilTest f g = f ⋆ g̃` supplies both absolute zero-side
summability and the genuine Weil-pair identity.

The regularity is intentionally asymmetric and minimal for the existing
convolution theorem: `f` is `C²`, while `g` need only be continuous; both are
compactly supported.  No aperture, `nuX`, real/even hypothesis, or Fourier-side
integrability assumption is used here. -/
theorem W_literatureRHS_package_of_lit
    (Z : ZeroConfig)
    (hEF : Zeta23.EF.EF_lit Z)
    {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hg : Continuous g)
    (hfc : HasCompactSupport f)
    (hgc : HasCompactSupport g) :
    Summable (fun ρ : Z.carrier => Z.Wsummand f g ρ) ∧
      Z.W f g = Zeta23.EF.literatureRHS (Zeta23.EF.weilTest f g) := by
  have hkd : ContDiff ℝ 2 (Zeta23.EF.weilTest f g) :=
    Zeta23.EF.weilTest_contDiff hf hg hfc
  have hkc : HasCompactSupport (Zeta23.EF.weilTest f g) :=
    Zeta23.EF.weilTest_hasCompactSupport hfc hgc
  obtain ⟨hsum, heq⟩ :=
    hEF (Zeta23.EF.weilTest f g) hkd hkc
  have hfac : ∀ z : ℂ,
      paperFT (Zeta23.EF.weilTest f g) z =
        paperFT f z * conj (paperFT g (conj z)) :=
    Zeta23.EF.paperFT_weilTest hf.continuous hg hfc hgc
  have hterm :
      (fun ρ : Z.carrier =>
        (Z.mult ρ : ℂ) * paperFT (Zeta23.EF.weilTest f g) (gammaOf ρ)) =
      (fun ρ : Z.carrier => Z.Wsummand f g ρ) := by
    ext ρ
    simp only [ZeroConfig.Wsummand, hfac, mul_assoc]
  refine ⟨hterm ▸ hsum, ?_⟩
  rw [ZeroConfig.W, ← hterm]
  exact heq

/-- **W2-A, concrete zeta form.**  The repository's unconditional
literature-form explicit formula yields the generic W2-A package for the actual
zeta zero configuration. -/
theorem zeta_W_literatureRHS_package
    {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hg : Continuous g)
    (hfc : HasCompactSupport f)
    (hgc : HasCompactSupport g) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand f g ρ) ∧
      zetaZeroConfig.W f g =
        Zeta23.EF.literatureRHS (Zeta23.EF.weilTest f g) := by
  exact W_literatureRHS_package_of_lit
    zetaZeroConfig zeta_explicit_formula_literature hf hg hfc hgc

/-- Convenience projection of W2-A: the genuine zeta Weil summand family is
summable on the exact admissible pair class. -/
theorem zeta_Wsummand_summable
    {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hg : Continuous g)
    (hfc : HasCompactSupport f)
    (hgc : HasCompactSupport g) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand f g ρ) :=
  (zeta_W_literatureRHS_package hf hg hfc hgc).1

/-- Convenience projection of W2-A: the genuine zeta Weil form equals the
literature explicit-formula RHS of the exact pair test. -/
theorem zeta_W_eq_literatureRHS_weilTest
    {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hg : Continuous g)
    (hfc : HasCompactSupport f)
    (hgc : HasCompactSupport g) :
    zetaZeroConfig.W f g =
      Zeta23.EF.literatureRHS (Zeta23.EF.weilTest f g) :=
  (zeta_W_literatureRHS_package hf hg hfc hgc).2

/-- Diagonal specialization used by the forthcoming self-form/evenization
bridge. -/
theorem zeta_W_self_eq_literatureRHS_weilTest
    {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    zetaZeroConfig.W f f =
      Zeta23.EF.literatureRHS (Zeta23.EF.weilTest f f) :=
  zeta_W_eq_literatureRHS_weilTest hf hf.continuous hfc hfc

end Zeta23.ExceptionalZero
