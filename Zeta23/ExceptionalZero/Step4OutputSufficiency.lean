import Zeta23.ExceptionalZero.Step123OutputProducer
import Zeta23.CCM.OriginalDetectorSchurLoss
import Zeta23.ExceptionalZero.NativeAnalyticOutputSufficiency

/-!
# Three source-preserving Step 4 conditional sufficiency cuts

A-X, B-Y and C-Schur are *independent proposed closing mechanisms*,
not proved premises. The conditional theorem for each consumes one
exact source, and C-Schur uses the whole original detector complement,
not the selected-ground one-shell scalar.

This file never supplies, infers, or asserts the missing A-X, B-Y or
C-Schur source-specific upper law. The full N01-N40 packet/D2 release
gate is also separate from the conditional implication.
-/

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-- The actual prime field's all-damping L2 condition (OPEN). -/
theorem riemannHypothesis_of_step4_AX
    (hAX : NativeOriginalPrimeFieldAllDampedIntegral) : RiemannHypothesis :=
  riemannHypothesis_of_originalPrimeField_allDampedIntegral hAX

/-- The actual causal-completion input range-closure condition (OPEN). -/
theorem riemannHypothesis_of_step4_BY
    (hBY : NativeInputAllRangeClosure) : RiemannHypothesis :=
  riemannHypothesis_of_nativeInput_allRangeClosure hBY

/-- An independent source-specific upper bound on the full original
detector's exact shifted Schur loss, if proved, conflicts with the
generated exponential lower obstruction. No C upper bound is proved
here; in particular, generic source positivity is insufficient. -/
theorem riemannHypothesis_of_originalDetectorSchurSubexponential
    (hC : NativeOriginalDetectorSchurSubexponential) : RiemannHypothesis := by
  intro s hz htriv hs1
  have hs : IsNontrivialZero s :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  have hmem : s ∈ zetaZeroConfig.carrier := by simpa using hs
  let ρ : zetaZeroConfig.carrier := ⟨s, hmem⟩
  by_contra hoff
  have hδ : 0 < |(ρ : ℂ).re - 1 / 2| :=
    abs_pos.mpr (sub_ne_zero.mpr hoff)
  let β : ℝ := |(ρ : ℂ).re - 1 / 2| / 2
  have hβ : 0 < β := half_pos hδ
  have hβρ : β < |(ρ : ℂ).re - 1 / 2| := by
    dsimp [β]
    linarith
  let ε : ℝ := β / 2
  have hε : 0 < ε := half_pos hβ
  obtain ⟨C, L0, hCpos, hL0four, hbound⟩ := hC β ε hβ hε
  let R : ℝ := max L0 (4 * C / β)
  obtain ⟨out⟩ := exists_generatedStep123Output ρ hβ hβρ .even R
  let L : ℝ := fixedOriginalSincTrialAperture out.sourceData.separation
  have hR : R < L := (le_max_left R 4).trans_lt out.native_aperture_bound
  have hL0 : L0 < L := (le_max_left L0 (4 * C / β)).trans_lt hR
  have hbig : 4 * C / β < L :=
    (le_max_right L0 (4 * C / β)).trans_lt hR
  have hβL : 4 * C < β * L := by
    have hh := (div_lt_iff₀ hβ).mp hbig
    nlinarith
  have hcoef : 2 * C < Real.exp (β * L / 2) := by
    have he := Real.add_one_le_exp (β * L / 2)
    linarith
  have hUpper : nativeOriginalAdmissibleSchurLoss .even
        out.native.source_selector ≤ C * Real.exp (ε * L) :=
    hbound .even L out.native.retained.state.selection.eta
      out.native.retained.state.selection.cutoff out.native.source_selector hL0
  have hLower : Real.exp (β * L) / 2 <
        nativeOriginalAdmissibleSchurLoss .even out.native.source_selector :=
    nativeOriginalAdmissibleSchurLoss_gt_half_depth .even
      out.native.retained.state out.native.source_selector
      out.native.detector_source_eq
  have htwice : Real.exp (β * L) =
      Real.exp (β * L / 2) * Real.exp (β * L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hStrict : C * Real.exp (ε * L) < Real.exp (β * L) / 2 := by
    rw [show ε * L = β * L / 2 by dsimp [ε]; ring, htwice]
    have hm := mul_lt_mul_of_pos_right hcoef
      (Real.exp_pos (β * L / 2))
    nlinarith
  linarith

/-- The three cuts are alternative exact conditional implications,
not an assertion that any cut has been established. -/
theorem riemannHypothesis_of_any_step4_output_cut
    (h : NativeOriginalPrimeFieldAllDampedIntegral ∨
      NativeInputAllRangeClosure ∨
      NativeOriginalDetectorSchurSubexponential) : RiemannHypothesis := by
  rcases h with hAX | hBY | hC
  · exact riemannHypothesis_of_step4_AX hAX
  · exact riemannHypothesis_of_step4_BY hBY
  · exact riemannHypothesis_of_originalDetectorSchurSubexponential hC

/-- Original required name for the *conditional* C-Schur theorem.
Its source-specific subexponential premise remains explicitly OPEN. -/
theorem riemannHypothesis_of_detectorSchurLoss_subexponential
    (hC : NativeOriginalDetectorSchurSubexponential) : RiemannHypothesis :=
  riemannHypothesis_of_originalDetectorSchurSubexponential hC

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_step4_AX
#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_step4_BY
#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_originalDetectorSchurSubexponential
#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_any_step4_output_cut
