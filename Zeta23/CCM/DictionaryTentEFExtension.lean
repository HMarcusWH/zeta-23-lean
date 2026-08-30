import Zeta23.CCM.DictionaryTentZeroLimit
import Zeta23.CCM.DictionaryTentArchLimit
import Zeta23.CCM.DictionaryTentPolePrimeLimit
import Zeta23.WeilEF.Main

noncomputable section

namespace Zeta23.CCM

open Complex Filter Topology

/-!
# Literal-tent explicit-formula assembly

This is Route M milestone M8.

All analytic limit passages are already compiler-closed upstream:

- M4: pole channel;
- M5: truncate-first prime channel;
- M6: archimedean dominated convergence;
- M7: varying-family zero-side Tannery convergence.

This file performs only the final assembly.  The inherited explicit formula is
applied to each smooth compactly supported mollified tent, never directly to
the nonsmooth literal tent.
-/

/-- The deterministic literature RHS of the smooth mollified tents converges
to the deterministic literature RHS of the literal tent by composing the
already-proved pole, prime, and archimedean channel limits. -/
theorem literatureRHS_dictionaryTentMollified_tendsto
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun n : ℕ =>
        Zeta23.EF.literatureRHS (dictionaryTentMollified L n))
      atTop
      (𝓝 (Zeta23.EF.literatureRHS (dictionaryTent L))) := by
  have hpole :=
    dictionaryPoleRHS_dictionaryTentMollified_tendsto hL
  have hprime :=
    dictionaryPrimeRHS_dictionaryTentMollified_tendsto hL
  have harch :=
    dictionaryArchRHS_dictionaryTentMollified_tendsto hL
  simpa only [literatureRHS_eq_dictionaryChannels] using
    (hpole.add hprime).add harch

/-- M8 equality endpoint: the concrete zeta zero side of the literal canonical
 tent equals its deterministic literature explicit-formula RHS. -/
theorem dictionaryTent_zero_sum_eq_literatureRHS
    (hs : ZetaSeam)
    {L : ℝ} (hL : 0 < L) :
    (∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        Zeta23.paperFT
          (dictionaryTent L)
          (gammaOf ρ))
      =
    Zeta23.EF.literatureRHS (dictionaryTent L) := by
  have hzero :=
    dictionaryTent_zero_sum_mollified_tendsto hs hL
  have hrhs :=
    literatureRHS_dictionaryTentMollified_tendsto hL
  have hEF := Zeta23.WeilEF.EF_lit_zeta hs
  have hseq :
      (fun n : ℕ =>
        ∑' ρ : (zetaZeros hs).carrier,
          ((zetaZeros hs).mult ρ : ℂ) *
            Zeta23.paperFT
              (dictionaryTentMollified L n)
              (gammaOf ρ))
        =
      (fun n : ℕ =>
        Zeta23.EF.literatureRHS (dictionaryTentMollified L n)) := by
    funext n
    exact
      (hEF
        (dictionaryTentMollified L n)
        (contDiff_two_dictionaryTentMollified L n)
        (dictionaryTentMollified_hasCompactSupport hL n)).2
  rw [hseq] at hzero
  exact tendsto_nhds_unique hzero hrhs

/-- Production M8 endpoint: the literal canonical tent satisfies the concrete
zeta literature explicit formula, including absolute zero-side summability. -/
theorem dictionaryTent_explicitFormula
    (hs : ZetaSeam)
    {L : ℝ} (hL : 0 < L) :
    Summable (fun ρ : (zetaZeros hs).carrier =>
      ((zetaZeros hs).mult ρ : ℂ) *
        Zeta23.paperFT
          (dictionaryTent L)
          (gammaOf ρ)) ∧
    (∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        Zeta23.paperFT
          (dictionaryTent L)
          (gammaOf ρ))
      =
    Zeta23.EF.literatureRHS (dictionaryTent L) := by
  exact ⟨
    dictionaryTent_zero_sum_summable hs hL,
    dictionaryTent_zero_sum_eq_literatureRHS hs hL
  ⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.dictionaryTent_zero_sum_eq_literatureRHS
#print axioms Zeta23.CCM.dictionaryTent_explicitFormula
