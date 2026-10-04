import Zeta23.CCM.ProductionWeightedTestCalculus
import Zeta23.CCM.QuadraticNormalSourceJets
import Zeta23.CCM.CanonicalSourceEnergyJets
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ComplexConjugate Interval

/-!
# Post-#282 compact even lifts for weighted production tests

The positive-half production tests are not, by themselves, legitimate inputs to
the global explicit formula.  This module constructs the actual compact even
whole-line lift and proves the reusable C² gluing theorem from endpoint jets.

No arithmetic identity is stored in the lift data.  The explicit-formula
authority is obtained afterwards from
`ProductionWeightedGlobalLift.physical_authority`.
-/

/-- Even compact extension of a real positive-half test. -/
def productionEvenCompactLiftReal (L : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y =>
    if y ≤ -L then 0
    else if y ≤ 0 then f (-y)
    else if y < L then f y
    else 0

/-- First derivative candidate for the compact even lift. -/
def productionEvenCompactLiftRealDerivative
    (L : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y =>
    if y ≤ -L then 0
    else if y ≤ 0 then - deriv f (-y)
    else if y < L then deriv f y
    else 0

/-- Second derivative candidate for the compact even lift. -/
def productionEvenCompactLiftRealSecondDerivative
    (L : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y =>
    if y ≤ -L then 0
    else if y ≤ 0 then deriv (deriv f) (-y)
    else if y < L then deriv (deriv f) y
    else 0

/-- Complex adapter used by the explicit formula. -/
def productionEvenCompactLift (L : ℝ) (f : ℝ → ℝ) : ℝ → ℂ :=
  fun y => (productionEvenCompactLiftReal L f y : ℂ)

@[simp] theorem productionEvenCompactLiftReal_zero
    {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    productionEvenCompactLiftReal L f 0 = f 0 := by
  simp [productionEvenCompactLiftReal, hL]

@[simp] theorem productionEvenCompactLiftReal_right
    {L t : ℝ} (hL : 0 < L) (f : ℝ → ℝ)
    (ht0 : 0 ≤ t) (htL : t ≤ L) :
    productionEvenCompactLiftReal L f t = f t := by
  by_cases ht : t = L
  · subst t
    simp [productionEvenCompactLiftReal, hL]
  · have hlt : t < L := lt_of_le_of_ne htL ht
    simp [productionEvenCompactLiftReal, hL, ht0, hlt,
      not_le.mpr (by linarith : -L < t)]

@[simp] theorem productionEvenCompactLiftReal_left
    {L t : ℝ} (hL : 0 < L) (f : ℝ → ℝ)
    (htL : -L ≤ t) (ht0 : t ≤ 0) :
    productionEvenCompactLiftReal L f t = f (-t) := by
  have hn : ¬ t ≤ -L ∨ t = -L := lt_or_eq_of_le htL |>.imp
    (fun h => not_le.mpr h) id
  rcases lt_or_eq_of_le htL with hlt | rfl
  · simp [productionEvenCompactLiftReal, not_le.mpr hlt, ht0]
  · simp [productionEvenCompactLiftReal]

theorem productionEvenCompactLiftReal_eq_zero_of_lt_abs
    {L t : ℝ} (hL : 0 < L) (f : ℝ → ℝ)
    (ht : L < |t|) :
    productionEvenCompactLiftReal L f t = 0 := by
  rcases lt_or_ge t 0 with hneg | hnonneg
  · have hleft : t < -L := by
      rw [abs_of_neg hneg] at ht
      linarith
    simp [productionEvenCompactLiftReal, le_of_lt hleft]
  · have hright : L < t := by
      rw [abs_of_nonneg hnonneg] at ht
      exact ht
    have hnleft : ¬ t ≤ -L := by linarith
    have hnzero : ¬ t ≤ 0 := by linarith
    have hnlt : ¬ t < L := by linarith
    simp [productionEvenCompactLiftReal, hnleft, hnzero, hnlt]

theorem productionEvenCompactLiftReal_support_subset
    {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    Function.support (productionEvenCompactLiftReal L f) ⊆ Icc (-L) L := by
  intro t ht
  have habs : |t| ≤ L := by
    by_contra h
    exact ht (productionEvenCompactLiftReal_eq_zero_of_lt_abs hL f
      (lt_of_not_ge h))
  exact abs_le.mp habs

theorem productionEvenCompactLiftReal_even
    (L : ℝ) (f : ℝ → ℝ) :
    Function.Even (productionEvenCompactLiftReal L f) := by
  intro t
  unfold productionEvenCompactLiftReal
  by_cases h1 : t ≤ -L <;> by_cases h2 : t ≤ 0 <;>
    by_cases h3 : t < L <;> simp_all [neg_le, lt_neg]

/-- Generic C² gluing contract.  The center condition is the standard even
matching condition; the three right-end conditions are exactly the value,
first-jet and second-jet conditions needed to glue to the zero exterior. -/
structure ProductionEvenCompactLiftJets
    (L : ℝ) (f : ℝ → ℝ) : Prop where
  contDiff_two : ContDiff ℝ 2 f
  value_zero : f 0 = 0
  deriv_zero : deriv f 0 = 0
  value_endpoint : f L = 0
  deriv_endpoint : deriv f L = 0
  second_endpoint : deriv (deriv f) L = 0

private theorem hasDerivAt_productionEvenCompactLiftReal
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (h : ProductionEvenCompactLiftJets L f) (y : ℝ) :
    HasDerivAt (productionEvenCompactLiftReal L f)
      (productionEvenCompactLiftRealDerivative L f y) y := by
  by_cases hleft : y < -L
  · have hev : productionEvenCompactLiftReal L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hleft] with z hz
      simp [productionEvenCompactLiftReal, le_of_lt hz]
    have hc := (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
    simpa [productionEvenCompactLiftRealDerivative, le_of_lt hleft] using hc
  by_cases hleftEq : y = -L
  · subst y
    have hzeroExt :
        HasDerivWithinAt (productionEvenCompactLiftReal L f) 0
          (Iic (-L)) (-L) := by
      have hc : HasDerivWithinAt (fun _ : ℝ => 0) 0 (Iic (-L)) (-L) :=
        (hasDerivAt_const (-L) (0 : ℝ)).hasDerivWithinAt
      refine hc.congr_of_mem ?_ ?_
      · intro z hz
        simp [productionEvenCompactLiftReal, hz]
      · simp [productionEvenCompactLiftReal, h.value_endpoint]
    have hint0 :
        HasDerivAt (fun y : ℝ => f (-y)) (-deriv f L) (-L) := by
      have hf := h.contDiff_two.differentiableAt.hasDerivAt
      have hn := (hasDerivAt_neg (-L))
      simpa using (hf.comp (-L) hn)
    have hint : HasDerivWithinAt (productionEvenCompactLiftReal L f) 0
        (Icc (-L) 0) (-L) := by
      have hz : -deriv f L = 0 := by rw [h.deriv_endpoint]; simp
      rw [hz] at hint0
      refine hint0.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hzmem
        simp [productionEvenCompactLiftReal, hL, hzmem.1, hzmem.2,
          not_le.mpr (lt_of_le_of_ne hzmem.1 (Ne.symm (by linarith)))]
      · simp [productionEvenCompactLiftReal, h.value_endpoint]
    have hmem : Iic (-L) ∪ Icc (-L) 0 ∈ 𝓝 (-L) := by
      apply mem_of_superset (Iio_mem_nhds (show -L < 0 by linarith))
      intro z hz
      by_cases hh : z ≤ -L
      · exact Or.inl hh
      · exact Or.inr ⟨le_of_not_ge hh, le_of_lt hz⟩
    have hh := (hzeroExt.union hint).hasDerivAt hmem
    simpa [productionEvenCompactLiftRealDerivative, h.deriv_endpoint] using hh
  have hgtLeft : -L < y :=
    lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hleftEq)
  by_cases hneg : y < 0
  · have hev :
        productionEvenCompactLiftReal L f =ᶠ[𝓝 y] fun z => f (-z) := by
      filter_upwards [Ioo_mem_nhds hgtLeft hneg] with z hz
      simp [productionEvenCompactLiftReal, not_le.mpr hz.1, le_of_lt hz.2]
    have hf := h.contDiff_two.differentiableAt.hasDerivAt
    have hc := (hf.comp y (hasDerivAt_neg y)).congr_of_eventuallyEq hev
    simpa [productionEvenCompactLiftRealDerivative, not_le.mpr hgtLeft,
      le_of_lt hneg] using hc
  by_cases hzero : y = 0
  · subst y
    have hleft0 :
        HasDerivWithinAt (productionEvenCompactLiftReal L f) 0
          (Icc (-L) 0) 0 := by
      have hf := h.contDiff_two.differentiableAt.hasDerivAt
      have hc : HasDerivAt (fun y : ℝ => f (-y)) 0 0 := by
        have hh := hf.comp 0 (hasDerivAt_neg 0)
        simpa [h.deriv_zero] using hh
      refine hc.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        simp [productionEvenCompactLiftReal, hL, hz.1, hz.2,
          not_le.mpr (by linarith : -L < z)]
      · simp [productionEvenCompactLiftReal]
    have hright0 :
        HasDerivWithinAt (productionEvenCompactLiftReal L f) 0
          (Icc 0 L) 0 := by
      have hc : HasDerivAt f 0 0 := by
        simpa [h.deriv_zero] using h.contDiff_two.differentiableAt.hasDerivAt
      refine hc.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = L
        · subst z
          simp [productionEvenCompactLiftReal, h.value_endpoint]
        · simp [productionEvenCompactLiftReal, hL, hz.1,
            lt_of_le_of_ne hz.2 hzL, not_le.mpr (by linarith : -L < z)]
      · simp [productionEvenCompactLiftReal]
    have hmem : Icc (-L) 0 ∪ Icc 0 L ∈ 𝓝 (0 : ℝ) := by
      apply mem_of_superset (Ioo_mem_nhds (show -L < 0 by linarith) hL)
      intro z hz
      by_cases hh : z ≤ 0
      · exact Or.inl ⟨le_of_lt hz.1, hh⟩
      · exact Or.inr ⟨le_of_not_ge hh, le_of_lt hz.2⟩
    have hh := (hleft0.union hright0).hasDerivAt hmem
    simpa [productionEvenCompactLiftRealDerivative, hL, h.deriv_zero] using hh
  have hypos : 0 < y :=
    lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
  by_cases hright : y < L
  · have hev : productionEvenCompactLiftReal L f =ᶠ[𝓝 y] f := by
      filter_upwards [Ioo_mem_nhds hypos hright] with z hz
      simp [productionEvenCompactLiftReal, hL, hz.1, hz.2,
        not_le.mpr (by linarith : -L < z)]
    have hc := h.contDiff_two.differentiableAt.hasDerivAt.congr_of_eventuallyEq hev
    simpa [productionEvenCompactLiftRealDerivative, hL, hypos, hright,
      not_le.mpr (by linarith : -L < y)] using hc
  by_cases hrightEq : y = L
  · subst y
    have hint0 : HasDerivAt f 0 L := by
      simpa [h.deriv_endpoint] using h.contDiff_two.differentiableAt.hasDerivAt
    have hint :
        HasDerivWithinAt (productionEvenCompactLiftReal L f) 0
          (Icc 0 L) L := by
      refine hint0.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = L
        · subst z
          simp [productionEvenCompactLiftReal, h.value_endpoint]
        · simp [productionEvenCompactLiftReal, hL, hz.1,
            lt_of_le_of_ne hz.2 hzL, not_le.mpr (by linarith : -L < z)]
      · simp [productionEvenCompactLiftReal, h.value_endpoint]
    have hext :
        HasDerivWithinAt (productionEvenCompactLiftReal L f) 0
          (Ici L) L := by
      have hc := (hasDerivAt_const L (0 : ℝ)).hasDerivWithinAt
      refine hc.congr_of_mem ?_ ?_
      · intro z hz
        have hnleft : ¬ z ≤ -L := by linarith
        have hnzero : ¬ z ≤ 0 := by linarith
        have hnlt : ¬ z < L := not_lt.mpr hz
        simp [productionEvenCompactLiftReal, hnleft, hnzero, hnlt]
      · simp [productionEvenCompactLiftReal, h.value_endpoint]
    have hmem : Icc 0 L ∪ Ici L ∈ 𝓝 L := by
      apply mem_of_superset (Ioi_mem_nhds hL)
      intro z hz
      by_cases hh : z ≤ L
      · exact Or.inl ⟨le_of_lt hz, hh⟩
      · exact Or.inr (le_of_not_ge hh)
    have hh := (hint.union hext).hasDerivAt hmem
    simpa [productionEvenCompactLiftRealDerivative, hL, h.deriv_endpoint] using hh
  · have hgt : L < y :=
      lt_of_le_of_ne (le_of_not_gt hright) (Ne.symm hrightEq)
    have hev : productionEvenCompactLiftReal L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hgt] with z hz
      have hnleft : ¬ z ≤ -L := by linarith
      have hnzero : ¬ z ≤ 0 := by linarith
      have hnlt : ¬ z < L := by linarith
      simp [productionEvenCompactLiftReal, hnleft, hnzero, hnlt]
    have hc := (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
    simpa [productionEvenCompactLiftRealDerivative, not_le.mpr (by linarith : -L < y),
      not_le.mpr hypos, not_lt.mpr (le_of_lt hgt)] using hc

private theorem hasDerivAt_productionEvenCompactLiftRealDerivative
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (h : ProductionEvenCompactLiftJets L f) (y : ℝ) :
    HasDerivAt (productionEvenCompactLiftRealDerivative L f)
      (productionEvenCompactLiftRealSecondDerivative L f y) y := by
  -- This is the same three-seam gluing argument one derivative higher.
  -- C² of f supplies C¹ of deriv f; the endpoint second jet is exactly the
  -- condition required to glue to the exterior zero branch.
  have hdf : ContDiff ℝ 1 (deriv f) := h.contDiff_two.deriv_contDiff
  by_cases hleft : y < -L
  · have hev : productionEvenCompactLiftRealDerivative L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hleft] with z hz
      simp [productionEvenCompactLiftRealDerivative, le_of_lt hz]
    simpa [productionEvenCompactLiftRealSecondDerivative, le_of_lt hleft] using
      (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
  by_cases hleftEq : y = -L
  · subst y
    have hzeroExt :
        HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f) 0
          (Iic (-L)) (-L) := by
      refine (hasDerivAt_const (-L) (0 : ℝ)).hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz; simp [productionEvenCompactLiftRealDerivative, hz]
      · simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint]
    have hint0 :
        HasDerivAt (fun y : ℝ => - deriv f (-y))
          (deriv (deriv f) L) (-L) := by
      have hh := hdf.differentiableAt.hasDerivAt.comp (-L) (hasDerivAt_neg (-L))
      simpa using hh.neg
    have hint : HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f) 0
        (Icc (-L) 0) (-L) := by
      rw [h.second_endpoint] at hint0
      refine hint0.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        simp [productionEvenCompactLiftRealDerivative, hz.2,
          not_le.mpr (lt_of_le_of_ne hz.1 (Ne.symm (by linarith)))]
      · simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint]
    have hmem : Iic (-L) ∪ Icc (-L) 0 ∈ 𝓝 (-L) := by
      apply mem_of_superset (Iio_mem_nhds (show -L < 0 by linarith))
      intro z hz; by_cases hh : z ≤ -L
      · exact Or.inl hh
      · exact Or.inr ⟨le_of_not_ge hh, le_of_lt hz⟩
    have hh := (hzeroExt.union hint).hasDerivAt hmem
    simpa [productionEvenCompactLiftRealSecondDerivative, h.second_endpoint] using hh
  have hgtLeft : -L < y :=
    lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hleftEq)
  by_cases hneg : y < 0
  · have hev :
        productionEvenCompactLiftRealDerivative L f =ᶠ[𝓝 y]
          fun z => - deriv f (-z) := by
      filter_upwards [Ioo_mem_nhds hgtLeft hneg] with z hz
      simp [productionEvenCompactLiftRealDerivative,
        not_le.mpr hz.1, le_of_lt hz.2]
    have hh := hdf.differentiableAt.hasDerivAt.comp y (hasDerivAt_neg y)
    have hc := hh.neg.congr_of_eventuallyEq hev
    simpa [productionEvenCompactLiftRealSecondDerivative,
      not_le.mpr hgtLeft, le_of_lt hneg] using hc
  by_cases hzero : y = 0
  · subst y
    have hleft0 :
        HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f)
          (deriv (deriv f) 0) (Icc (-L) 0) 0 := by
      have hh := hdf.differentiableAt.hasDerivAt.comp 0 (hasDerivAt_neg 0)
      have hc : HasDerivAt (fun z : ℝ => -deriv f (-z))
          (deriv (deriv f) 0) 0 := by simpa using hh.neg
      refine hc.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        simp [productionEvenCompactLiftRealDerivative, hz.2,
          not_le.mpr (by linarith : -L < z)]
      · simp [productionEvenCompactLiftRealDerivative, h.deriv_zero]
    have hright0 :
        HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f)
          (deriv (deriv f) 0) (Icc 0 L) 0 := by
      refine hdf.differentiableAt.hasDerivAt.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = L
        · subst z; simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint]
        · simp [productionEvenCompactLiftRealDerivative, hz.1,
            lt_of_le_of_ne hz.2 hzL, not_le.mpr (by linarith : -L < z)]
      · simp [productionEvenCompactLiftRealDerivative, h.deriv_zero]
    have hmem : Icc (-L) 0 ∪ Icc 0 L ∈ 𝓝 (0 : ℝ) := by
      apply mem_of_superset (Ioo_mem_nhds (show -L < 0 by linarith) hL)
      intro z hz; by_cases hh : z ≤ 0
      · exact Or.inl ⟨le_of_lt hz.1, hh⟩
      · exact Or.inr ⟨le_of_not_ge hh, le_of_lt hz.2⟩
    have hh := (hleft0.union hright0).hasDerivAt hmem
    simpa [productionEvenCompactLiftRealSecondDerivative, hL] using hh
  have hypos : 0 < y :=
    lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
  by_cases hright : y < L
  · have hev :
        productionEvenCompactLiftRealDerivative L f =ᶠ[𝓝 y] deriv f := by
      filter_upwards [Ioo_mem_nhds hypos hright] with z hz
      simp [productionEvenCompactLiftRealDerivative, hz.1, hz.2,
        not_le.mpr (by linarith : -L < z)]
    have hc := hdf.differentiableAt.hasDerivAt.congr_of_eventuallyEq hev
    simpa [productionEvenCompactLiftRealSecondDerivative, hypos, hright,
      not_le.mpr (by linarith : -L < y)] using hc
  by_cases hrightEq : y = L
  · subst y
    have hint0 : HasDerivAt (deriv f) 0 L := by
      simpa [h.second_endpoint] using hdf.differentiableAt.hasDerivAt
    have hint :
        HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f) 0
          (Icc 0 L) L := by
      refine hint0.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = L
        · subst z; simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint]
        · simp [productionEvenCompactLiftRealDerivative, hz.1,
            lt_of_le_of_ne hz.2 hzL, not_le.mpr (by linarith : -L < z)]
      · simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint]
    have hext :
        HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f) 0
          (Ici L) L := by
      refine (hasDerivAt_const L (0 : ℝ)).hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        have hnleft : ¬ z ≤ -L := by linarith
        have hnzero : ¬ z ≤ 0 := by linarith
        have hnlt : ¬ z < L := not_lt.mpr hz
        simp [productionEvenCompactLiftRealDerivative, hnleft, hnzero, hnlt]
      · simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint]
    have hmem : Icc 0 L ∪ Ici L ∈ 𝓝 L := by
      apply mem_of_superset (Ioi_mem_nhds hL)
      intro z hz; by_cases hh : z ≤ L
      · exact Or.inl ⟨le_of_lt hz, hh⟩
      · exact Or.inr (le_of_not_ge hh)
    have hh := (hint.union hext).hasDerivAt hmem
    simpa [productionEvenCompactLiftRealSecondDerivative, h.second_endpoint] using hh
  · have hgt : L < y :=
      lt_of_le_of_ne (le_of_not_gt hright) (Ne.symm hrightEq)
    have hev : productionEvenCompactLiftRealDerivative L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hgt] with z hz
      have hnleft : ¬ z ≤ -L := by linarith
      have hnzero : ¬ z ≤ 0 := by linarith
      have hnlt : ¬ z < L := by linarith
      simp [productionEvenCompactLiftRealDerivative, hnleft, hnzero, hnlt]
    simpa [productionEvenCompactLiftRealSecondDerivative,
      not_le.mpr (by linarith : -L < y), not_le.mpr hypos,
      not_lt.mpr (le_of_lt hgt)] using
      (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev

private theorem continuous_productionEvenCompactLiftRealSecondDerivative
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (h : ProductionEvenCompactLiftJets L f) :
    Continuous (productionEvenCompactLiftRealSecondDerivative L f) := by
  have hdd : Continuous (deriv (deriv f)) :=
    h.contDiff_two.deriv_contDiff.continuous
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hleft : y < -L
  · have hev : productionEvenCompactLiftRealSecondDerivative L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hleft] with z hz
      simp [productionEvenCompactLiftRealSecondDerivative, le_of_lt hz]
    exact continuousAt_const.congr_of_eventuallyEq hev
  by_cases hleftEq : y = -L
  · subst y
    have hzero : ContinuousWithinAt (fun _ : ℝ => 0) (Iic (-L)) (-L) :=
      continuousAt_const.continuousWithinAt
    have hneg :
        ContinuousWithinAt (fun y : ℝ => deriv (deriv f) (-y))
          (Icc (-L) 0) (-L) :=
      hdd.comp_continuousWithinAt (by fun_prop)
    have hz : deriv (deriv f) L = 0 := h.second_endpoint
    have hmem : Iic (-L) ∪ Icc (-L) 0 ∈ 𝓝 (-L) := by
      apply mem_of_superset (Iio_mem_nhds (show -L < 0 by linarith))
      intro z hz'; by_cases hh : z ≤ -L
      · exact Or.inl hh
      · exact Or.inr ⟨le_of_not_ge hh, le_of_lt hz'⟩
    exact ((hzero.congr_of_mem (fun z hz' => by
      simp [productionEvenCompactLiftRealSecondDerivative, hz']) (by simp [hz])).union
      (hneg.congr_of_mem (fun z hz' => by
        simp [productionEvenCompactLiftRealSecondDerivative, hz'.2,
          not_le.mpr (lt_of_le_of_ne hz'.1 (Ne.symm (by linarith)))])
        (by simp [productionEvenCompactLiftRealSecondDerivative, hz]))).continuousAt hmem
  have hgtLeft : -L < y :=
    lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hleftEq)
  by_cases hneg : y < 0
  · have hev :
        productionEvenCompactLiftRealSecondDerivative L f =ᶠ[𝓝 y]
          fun z => deriv (deriv f) (-z) := by
      filter_upwards [Ioo_mem_nhds hgtLeft hneg] with z hz
      simp [productionEvenCompactLiftRealSecondDerivative,
        not_le.mpr hz.1, le_of_lt hz.2]
    exact (hdd.comp continuous_neg).continuousAt.congr_of_eventuallyEq hev
  by_cases hzero : y = 0
  · subst y
    have hn :
        ContinuousWithinAt (fun z : ℝ => deriv (deriv f) (-z))
          (Icc (-L) 0) 0 :=
      (hdd.comp continuous_neg).continuousAt.continuousWithinAt
    have hp :
        ContinuousWithinAt (deriv (deriv f)) (Icc 0 L) 0 :=
      hdd.continuousAt.continuousWithinAt
    have hmem : Icc (-L) 0 ∪ Icc 0 L ∈ 𝓝 (0 : ℝ) := by
      apply mem_of_superset (Ioo_mem_nhds (show -L < 0 by linarith) hL)
      intro z hz; by_cases hh : z ≤ 0
      · exact Or.inl ⟨le_of_lt hz.1, hh⟩
      · exact Or.inr ⟨le_of_not_ge hh, le_of_lt hz.2⟩
    exact ((hn.congr_of_mem (fun z hz => by
      simp [productionEvenCompactLiftRealSecondDerivative, hz.2,
        not_le.mpr (by linarith : -L < z)]) (by simp)).union
      (hp.congr_of_mem (fun z hz => by
        by_cases hzL : z = L
        · subst z; simp [productionEvenCompactLiftRealSecondDerivative, h.second_endpoint]
        · simp [productionEvenCompactLiftRealSecondDerivative, hz.1,
            lt_of_le_of_ne hz.2 hzL, not_le.mpr (by linarith : -L < z)])
        (by simp))).continuousAt hmem
  have hypos : 0 < y :=
    lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
  by_cases hright : y < L
  · have hev :
        productionEvenCompactLiftRealSecondDerivative L f =ᶠ[𝓝 y]
          deriv (deriv f) := by
      filter_upwards [Ioo_mem_nhds hypos hright] with z hz
      simp [productionEvenCompactLiftRealSecondDerivative, hz.1, hz.2,
        not_le.mpr (by linarith : -L < z)]
    exact hdd.continuousAt.congr_of_eventuallyEq hev
  by_cases hrightEq : y = L
  · subst y
    have hp := hdd.continuousAt.continuousWithinAt
    have hz : deriv (deriv f) L = 0 := h.second_endpoint
    have hzero : ContinuousWithinAt (fun _ : ℝ => 0) (Ici L) L :=
      continuousAt_const.continuousWithinAt
    have hmem : Icc 0 L ∪ Ici L ∈ 𝓝 L := by
      apply mem_of_superset (Ioi_mem_nhds hL)
      intro z hz'; by_cases hh : z ≤ L
      · exact Or.inl ⟨le_of_lt hz', hh⟩
      · exact Or.inr (le_of_not_ge hh)
    exact ((hp.congr_of_mem (fun z hz' => by
      by_cases he : z = L
      · subst z; simp [productionEvenCompactLiftRealSecondDerivative, hz]
      · simp [productionEvenCompactLiftRealSecondDerivative, hz'.1,
          lt_of_le_of_ne hz'.2 he, not_le.mpr (by linarith : -L < z)])
      (by simp [productionEvenCompactLiftRealSecondDerivative, hz])).union
      (hzero.congr_of_mem (fun z hz' => by
        have hnleft : ¬ z ≤ -L := by linarith
        have hnzero : ¬ z ≤ 0 := by linarith
        have hnlt : ¬ z < L := not_lt.mpr hz'
        simp [productionEvenCompactLiftRealSecondDerivative, hnleft, hnzero, hnlt])
        (by simp [productionEvenCompactLiftRealSecondDerivative, hz]))).continuousAt hmem
  · have hgt : L < y :=
      lt_of_le_of_ne (le_of_not_gt hright) (Ne.symm hrightEq)
    have hev :
        productionEvenCompactLiftRealSecondDerivative L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hgt] with z hz
      have hnleft : ¬ z ≤ -L := by linarith
      have hnzero : ¬ z ≤ 0 := by linarith
      have hnlt : ¬ z < L := by linarith
      simp [productionEvenCompactLiftRealSecondDerivative, hnleft, hnzero, hnlt]
    exact continuousAt_const.congr_of_eventuallyEq hev

theorem contDiff_two_productionEvenCompactLiftReal
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (h : ProductionEvenCompactLiftJets L f) :
    ContDiff ℝ 2 (productionEvenCompactLiftReal L f) := by
  have hd : Differentiable ℝ (productionEvenCompactLiftReal L f) :=
    fun y => (hasDerivAt_productionEvenCompactLiftReal hL h y).differentiableAt
  have hd1 :
      Differentiable ℝ (productionEvenCompactLiftRealDerivative L f) :=
    fun y =>
      (hasDerivAt_productionEvenCompactLiftRealDerivative hL h y).differentiableAt
  have hderiv :
      deriv (productionEvenCompactLiftReal L f) =
        productionEvenCompactLiftRealDerivative L f := by
    funext y
    exact (hasDerivAt_productionEvenCompactLiftReal hL h y).deriv
  have hderiv1 :
      deriv (productionEvenCompactLiftRealDerivative L f) =
        productionEvenCompactLiftRealSecondDerivative L f := by
    funext y
    exact (hasDerivAt_productionEvenCompactLiftRealDerivative hL h y).deriv
  have hc1 :
      ContDiff ℝ 1 (productionEvenCompactLiftRealDerivative L f) := by
    rw [contDiff_one_iff_deriv, hderiv1]
    exact ⟨hd1, continuous_productionEvenCompactLiftRealSecondDerivative hL h⟩
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨hd, by simp, by simpa [hderiv] using hc1⟩

theorem contDiff_two_productionEvenCompactLift
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (h : ProductionEvenCompactLiftJets L f) :
    ContDiff ℝ 2 (productionEvenCompactLift L f) := by
  unfold productionEvenCompactLift
  exact
    Complex.ofRealCLM.contDiff.comp x
      (contDiff_two_productionEvenCompactLiftReal hL h)
  where x := fun y : ℝ => productionEvenCompactLiftReal L f y

theorem productionEvenCompactLift_hasCompactSupport
    {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    HasCompactSupport (productionEvenCompactLift L f) := by
  apply HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc
  intro y hy
  have habs : L < |y| := by
    rw [Set.mem_compl_iff, Set.mem_Icc] at hy
    push_neg at hy
    exact (not_abs_le.mp hy)
  simp [productionEvenCompactLift,
    productionEvenCompactLiftReal_eq_zero_of_lt_abs hL f habs]

theorem productionEvenCompactLift_toGlobalLift
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (h : ProductionEvenCompactLiftJets L f) :
    ProductionWeightedGlobalLift L
      (productionEvenCompactLift L f) f := by
  refine ⟨contDiff_two_productionEvenCompactLift hL h,
    productionEvenCompactLift_hasCompactSupport hL f, ?_, ?_, ?_, ?_⟩
  · intro y
    simp [productionEvenCompactLift, productionEvenCompactLiftReal_even]
  · simp [productionEvenCompactLift, productionEvenCompactLiftReal_zero hL, h.value_zero]
  · intro y hy
    apply productionEvenCompactLiftReal_support_subset hL f
    simpa [productionEvenCompactLift] using hy
  · intro y hy
    simp [productionEvenCompactLift, productionEvenCompactLiftReal_right hL f hy.1 hy.2]

/-!
Concrete weighted tests are instantiated below.  Their endpoint proofs are
separated from the generic gluing theorem so downstream arithmetic identities
can cite exactly which source-coordinate cancellations were used.
-/

/-- Zero coefficient sum for every strict-even legal vector. -/
theorem evenBoundaryFlat_coordinateSum_zero
    (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) :
    ∑ i, (evenBoundaryFlatRawCoefficients K z) i = 0 := by
  exact (evenBoundaryFlatRawCoefficients_boundaryFlat K z).1

/-- The actual first source-energy derivative vanishes at both source
endpoints for a boundary-flat state. -/
theorem sourceAtomRealEnergyDerivative_endpoints_zero
    (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) :
    sourceAtomRealEnergyDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 0 = 0 ∧
      sourceAtomRealEnergyDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 1 = 0 := by
  let u := evenBoundaryFlatRawCoefficients K z
  have hsum : ∑ i, u i = 0 := evenBoundaryFlat_coordinateSum_zero K z
  have hri :=
    coefficientSumReal_re_im_eq_zero_of_sum_eq_zero K u hsum
  unfold sourceAtomRealEnergyDerivative
  constructor <;>
    simp [sourceContractRealDerivative_zero_eq_two_coefficientSum_sq,
      sourceContractRealDerivative_one_eq_two_coefficientSum_sq,
      hri.1, hri.2]

/-- The first weighted physical derivative has the endpoint jets needed by the
compact even lift. -/
theorem productionFirstDerivativePhysicalRaw_liftJets
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    ProductionEvenCompactLiftJets L
      (productionFirstDerivativePhysicalRaw L K z) := by
  have hend := sourceAtomRealEnergyDerivative_endpoints_zero K z
  refine ⟨contDiff_two_productionFirstDerivativePhysicalRaw hL K z,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [productionFirstDerivativePhysicalRaw]
  · have hd :=
      (hasDerivAt_id 0).mul
        ((hasDerivAt_const 0 (L ^ 2)).inv (by positivity) |>.mul
          ((hasDerivAt_sourceAtomRealEnergyDerivative_transport K
            (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 1).comp 0
              (by convert (hasDerivAt_const 0 (1 : ℝ)).sub
                ((hasDerivAt_id 0).div_const L) using 1 <;> ring)))
    simpa [productionFirstDerivativePhysicalRaw, hend.2] using hd.deriv
  · simp [productionFirstDerivativePhysicalRaw,
      sourceAtomRealEnergyDerivative_zero_of_boundaryFlat K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (evenBoundaryFlatRawCoefficients_boundaryFlat K z)]
  · have hjet :=
      sourceAtomRealEnergy_boundaryFlat_jets_through_six K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (evenBoundaryFlatRawCoefficients_boundaryFlat K z)
    simp [productionFirstDerivativePhysicalRaw, hjet] 
  · have hjet :=
      sourceAtomRealEnergy_boundaryFlat_jets_through_six K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (evenBoundaryFlatRawCoefficients_boundaryFlat K z)
    simp [productionFirstDerivativePhysicalRaw, hjet]

/-- First weighted derivative global test. -/
def productionFirstDerivativeGlobalTest
    (L : ℝ) (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℂ :=
  productionEvenCompactLift L (productionFirstDerivativePhysicalRaw L K z)

/-- Complete explicit-formula authority for the first weighted derivative. -/
theorem productionFirstDerivativeGlobalLift
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    ProductionWeightedGlobalLift L
      (productionFirstDerivativeGlobalTest L K z)
      (productionFirstDerivativePhysicalRaw L K z) := by
  exact productionEvenCompactLift_toGlobalLift hL
    (productionFirstDerivativePhysicalRaw_liftJets hL K z)

/-- The first raw and clamped tests agree on the production interval. -/
theorem productionFirstDerivativeRaw_eq_test_on_Icc
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    productionFirstDerivativePhysicalRaw L K z t =
      productionFirstDerivativePhysicalTest L K z t := by
  simp [productionFirstDerivativePhysicalTest, productionPhysicalClamp_eq ht]

/-- Full authority for k1. -/
theorem productionFirstDerivativeTest_authority
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    (1 / 2 : ℂ) * Zeta23.EF.literatureRHS
        (productionFirstDerivativeGlobalTest L K z) =
      productionArithmeticComplexValue L
        (fun t => (productionFirstDerivativePhysicalTest L K z t : ℂ)) := by
  have hg := (productionFirstDerivativeGlobalLift hL K z).physical_authority hL
  unfold productionArithmeticComplexValue dictionaryCompletePhysicalRHS at hg ⊢
  -- Only values on [0,L] and positive prime logs are sampled.
  simpa [productionFirstDerivativePhysicalTest, productionPhysicalClamp] using hg

end Zeta23.CCM

#print axioms Zeta23.CCM.productionEvenCompactLift_toGlobalLift
#print axioms Zeta23.CCM.productionFirstDerivativeGlobalLift
#print axioms Zeta23.CCM.productionFirstDerivativeTest_authority
