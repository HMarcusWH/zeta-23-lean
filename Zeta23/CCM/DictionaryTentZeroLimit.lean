import Zeta23.CCM.DictionaryTentMollifierLimit
import Zeta23.CCM.DictionaryTentZeroSummability
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

namespace Zeta23.CCM

open Complex Filter Topology

/-!
# Varying-family zero-side limit for the mollified dictionary tent

This is Route M milestone M7.

For each fixed zero, the mollified tent transform converges to the literal tent
transform by M3.5.  The exact M2 factorization and the uniform critical-strip
bound on the mollifier transform give one fixed summable majorant, namely a
constant multiple of the already-summable literal tent zero series.  Mathlib's
Tannery theorem then exchanges the mollification limit with the full zero-side
`tsum`.

No explicit-formula identity is used here, and no new zero-counting argument is
introduced.
-/

/-- Pointwise convergence of one multiplicity-weighted zero summand. -/
private theorem dictionaryTent_zeroSummand_mollified_tendsto
    (Z : ZeroConfig)
    {L : ℝ} (hL : 0 < L)
    (ρ : Z.carrier) :
    Tendsto
      (fun n : ℕ =>
        (Z.mult ρ : ℂ) *
          Zeta23.paperFT
            (dictionaryTentMollified L n) (gammaOf ρ))
      atTop
      (𝓝
        ((Z.mult ρ : ℂ) *
          Zeta23.paperFT
            (dictionaryTent L) (gammaOf ρ))) := by
  exact tendsto_const_nhds.mul
    (paperFT_dictionaryTentMollified_tendsto hL (gammaOf ρ))

/-- Uniform domination of every mollified zero summand by the literal-tent
summand times the strip constant `exp(1/2)`. -/
private theorem norm_dictionaryTent_zeroSummand_mollified_le
    (Z : ZeroConfig)
    {L : ℝ} (hL : 0 < L)
    (n : ℕ) (ρ : Z.carrier) :
    ‖(Z.mult ρ : ℂ) *
        Zeta23.paperFT
          (dictionaryTentMollified L n) (gammaOf ρ)‖
      ≤
    Real.exp (1 / 2 : ℝ) *
      ‖(Z.mult ρ : ℂ) *
        Zeta23.paperFT
          (dictionaryTent L) (gammaOf ρ)‖ := by
  have hstripρ := Z.strip (ρ : ℂ) ρ.2
  have hstripγ :
      |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 :=
    Zeta23.WeilEF.abs_gammaOf_im_le hstripρ
  have hphi :
      ‖dictionaryTentMollifierTransform n (gammaOf (ρ : ℂ))‖
        ≤ Real.exp (1 / 2) :=
    norm_dictionaryTentMollifierTransform_le_exp_half n hstripγ
  rw [paperFT_dictionaryTentMollified_factor hL n (gammaOf (ρ : ℂ))]
  simp only [norm_mul]
  calc
    ‖(Z.mult ρ : ℂ)‖ *
          (‖dictionaryTentMollifierTransform n (gammaOf (ρ : ℂ))‖ *
            ‖Zeta23.paperFT (dictionaryTent L) (gammaOf (ρ : ℂ))‖) =
        ‖dictionaryTentMollifierTransform n (gammaOf (ρ : ℂ))‖ *
          (‖(Z.mult ρ : ℂ)‖ *
            ‖Zeta23.paperFT (dictionaryTent L) (gammaOf (ρ : ℂ))‖) := by
      ring
    _ ≤ Real.exp (1 / 2) *
          (‖(Z.mult ρ : ℂ)‖ *
            ‖Zeta23.paperFT (dictionaryTent L) (gammaOf (ρ : ℂ))‖) :=
      mul_le_mul_of_nonneg_right hphi
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Generic M7 theorem.  Once the literal zero series is summable, no further
zero-counting input is needed to pass the mollification limit through the
zero-side `tsum`. -/
theorem dictionaryTent_zero_sum_mollified_tendsto_gen
    (Z : ZeroConfig)
    {L : ℝ} (hL : 0 < L)
    (hsum :
      Summable (fun ρ : Z.carrier =>
        (Z.mult ρ : ℂ) *
          Zeta23.paperFT (dictionaryTent L) (gammaOf ρ))) :
    Tendsto
      (fun n : ℕ =>
        ∑' ρ : Z.carrier,
          (Z.mult ρ : ℂ) *
            Zeta23.paperFT
              (dictionaryTentMollified L n) (gammaOf ρ))
      atTop
      (𝓝
        (∑' ρ : Z.carrier,
          (Z.mult ρ : ℂ) *
            Zeta23.paperFT
              (dictionaryTent L) (gammaOf ρ))) := by
  let bound : Z.carrier → ℝ :=
    fun ρ =>
      Real.exp (1 / 2 : ℝ) *
        ‖(Z.mult ρ : ℂ) *
          Zeta23.paperFT (dictionaryTent L) (gammaOf ρ)‖
  have hbound : Summable bound := by
    dsimp [bound]
    exact hsum.norm.mul_left (Real.exp (1 / 2 : ℝ))
  refine tendsto_tsum_of_dominated_convergence hbound
    (fun ρ => dictionaryTent_zeroSummand_mollified_tendsto Z hL ρ) ?_
  exact Eventually.of_forall fun n ρ => by
    simpa [bound] using
      norm_dictionaryTent_zeroSummand_mollified_le Z hL n ρ

/-- Concrete zeta M7 endpoint, using the already-proved literal-tent zero-side
absolute summability theorem. -/
theorem dictionaryTent_zero_sum_mollified_tendsto
    (hs : ZetaSeam)
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun n : ℕ =>
        ∑' ρ : (zetaZeros hs).carrier,
          ((zetaZeros hs).mult ρ : ℂ) *
            Zeta23.paperFT
              (dictionaryTentMollified L n) (gammaOf ρ))
      atTop
      (𝓝
        (∑' ρ : (zetaZeros hs).carrier,
          ((zetaZeros hs).mult ρ : ℂ) *
            Zeta23.paperFT
              (dictionaryTent L) (gammaOf ρ))) := by
  exact dictionaryTent_zero_sum_mollified_tendsto_gen
    (zetaZeros hs) hL (dictionaryTent_zero_sum_summable hs hL)

end Zeta23.CCM

#print axioms Zeta23.CCM.dictionaryTent_zero_sum_mollified_tendsto_gen
#print axioms Zeta23.CCM.dictionaryTent_zero_sum_mollified_tendsto
