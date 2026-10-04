import Zeta23.CCM.ProductionWeightedTestCalculus
import Zeta23.CCM.QuadraticNormalSourceJets
import Zeta23.CCM.CanonicalSourceEnergyJets
import Zeta23.CCM.CanonicalCompressedSeamJets
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
    (ht0 : 0 ≤ t) (htL : t < L) :
    productionEvenCompactLiftReal L f t = f t := by
  by_cases ht : t = 0
  · subst t
    simp [productionEvenCompactLiftReal, hL]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hnleft : ¬ t ≤ -L := by linarith
    have hnzero : ¬ t ≤ 0 := not_le.mpr htpos
    simp [productionEvenCompactLiftReal, hnleft, hnzero, htL]

@[simp] theorem productionEvenCompactLiftReal_left
    {L t : ℝ} (hL : 0 < L) (f : ℝ → ℝ)
    (htL : -L < t) (ht0 : t ≤ 0) :
    productionEvenCompactLiftReal L f t = f (-t) := by
  simp [productionEvenCompactLiftReal, not_le.mpr htL, ht0]

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
    {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    Function.Even (productionEvenCompactLiftReal L f) := by
  intro t
  by_cases ht0 : 0 ≤ t
  · by_cases htL : t < L
    · by_cases ht : t = 0
      · subst t
        simp [productionEvenCompactLiftReal, hL]
      · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
        have htNotLeft : ¬ t ≤ -L := by linarith
        have hnegNotLeft : ¬ -t ≤ -L := by linarith
        have hnegZero : -t ≤ 0 := by linarith
        simp [productionEvenCompactLiftReal, htNotLeft, not_le.mpr htpos,
          htL, hnegNotLeft, hnegZero]
    · have hLt : L ≤ t := le_of_not_gt htL
      have htpos : 0 < t := lt_of_lt_of_le hL hLt
      have hnegLeft : -t ≤ -L := by linarith
      have htNotLeft : ¬ t ≤ -L := by linarith
      simp [productionEvenCompactLiftReal, hnegLeft, htNotLeft,
        not_le.mpr htpos, htL]
  · have htneg : t < 0 := lt_of_not_ge ht0
    by_cases hleft : -L < t
    · have htNotLeft : ¬ t ≤ -L := not_le.mpr hleft
      have hnegpos : 0 < -t := by linarith
      have hnegL : -t < L := by linarith
      have hnegNotLeft : ¬ -t ≤ -L := by linarith
      simp [productionEvenCompactLiftReal, htNotLeft, le_of_lt htneg,
        hnegNotLeft, not_le.mpr hnegpos, hnegL]
    · have htLeft : t ≤ -L := le_of_not_gt hleft
      have hnegRight : L ≤ -t := by linarith
      have hnegpos : 0 < -t := by linarith
      simp [productionEvenCompactLiftReal, htLeft, hnegRight,
        not_le.mpr hnegpos]

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

private theorem productionEvenCompactLiftJets_differentiable
    {L : ℝ} {f : ℝ → ℝ} (h : ProductionEvenCompactLiftJets L f) :
    Differentiable ℝ f :=
  h.contDiff_two.differentiable (by norm_num)

private theorem productionEvenCompactLiftJets_deriv_contDiff_one
    {L : ℝ} {f : ℝ → ℝ} (h : ProductionEvenCompactLiftJets L f) :
    ContDiff ℝ 1 (deriv f) := by
  simpa using h.contDiff_two.deriv'

private theorem productionEvenCompactLiftJets_deriv_differentiable
    {L : ℝ} {f : ℝ → ℝ} (h : ProductionEvenCompactLiftJets L f) :
    Differentiable ℝ (deriv f) :=
  (productionEvenCompactLiftJets_deriv_contDiff_one h).differentiable (by norm_num)

private theorem productionEvenCompactLiftJets_second_deriv_continuous
    {L : ℝ} {f : ℝ → ℝ} (h : ProductionEvenCompactLiftJets L f) :
    Continuous (deriv (deriv f)) := by
  have h1 : ContDiff ℝ (0 + 1) (deriv f) := by
    simpa using productionEvenCompactLiftJets_deriv_contDiff_one h
  have h0 : ContDiff ℝ 0 (deriv (deriv f)) := h1.deriv'
  exact h0.continuous

private theorem hasDerivAt_productionEvenCompactLiftReal
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (h : ProductionEvenCompactLiftJets L f) (y : ℝ) :
    HasDerivAt (productionEvenCompactLiftReal L f)
      (productionEvenCompactLiftRealDerivative L f y) y := by
  have hL0 : ¬ L ≤ 0 := not_le.mpr hL
  have hLL : ¬ L ≤ -L := by linarith
  by_cases hleft : y < -L
  · have hev : productionEvenCompactLiftReal L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hleft] with z hz
      have hzlt : z < -L := hz
      simp [productionEvenCompactLiftReal, le_of_lt hzlt]
    have hc := (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
    simpa [productionEvenCompactLiftRealDerivative, le_of_lt hleft] using hc
  by_cases hleftEq : y = -L
  · subst y
    have hzeroExt :
        HasDerivWithinAt (productionEvenCompactLiftReal L f) 0
          (Iic (-L)) (-L) := by
      have hc :
          HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Iic (-L)) (-L) :=
        (hasDerivAt_const (-L) (0 : ℝ)).hasDerivWithinAt
      refine hc.congr_of_mem ?_ ?_
      · intro z hz
        have hzle : z ≤ -L := hz
        simp [productionEvenCompactLiftReal, hzle]
      · simp [productionEvenCompactLiftReal]
    have hint0 :
        HasDerivAt (fun y : ℝ => f (-y)) (-deriv f L) (-L) := by
      have hf := (productionEvenCompactLiftJets_differentiable h L).hasDerivAt
      have hf' : HasDerivAt f (deriv f L) (-(-L)) := by
        simpa using hf
      have hh := hf'.comp (-L) (hasDerivAt_neg (-L))
      simpa only [Function.comp_apply, neg_neg, mul_neg, mul_one] using hh
    have hint :
        HasDerivWithinAt (productionEvenCompactLiftReal L f) 0
          (Icc (-L) 0) (-L) := by
      have hzder : -deriv f L = 0 := by
        rw [h.deriv_endpoint]
        simp
      rw [hzder] at hint0
      refine hint0.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = -L
        · subst z
          simp [productionEvenCompactLiftReal, h.value_endpoint, hL.le]
        · have hzgt : -L < z := lt_of_le_of_ne hz.1 (Ne.symm hzL)
          exact productionEvenCompactLiftReal_left hL f hzgt hz.2
      · simp [productionEvenCompactLiftReal, h.value_endpoint, hL.le]
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
      exact productionEvenCompactLiftReal_left hL f hz.1 (le_of_lt hz.2)
    have hf :=
      (productionEvenCompactLiftJets_differentiable h (-y)).hasDerivAt
    have hc := (hf.comp y (hasDerivAt_neg y)).congr_of_eventuallyEq hev
    simpa [productionEvenCompactLiftRealDerivative, not_le.mpr hgtLeft,
      le_of_lt hneg] using hc
  by_cases hzero : y = 0
  · subst y
    have hleft0 :
        HasDerivWithinAt (productionEvenCompactLiftReal L f) 0
          (Icc (-L) 0) 0 := by
      have hf := (productionEvenCompactLiftJets_differentiable h 0).hasDerivAt
      have hf' : HasDerivAt f (deriv f 0) (-0) := by
        simpa using hf
      have hc : HasDerivAt (fun y : ℝ => f (-y)) 0 0 := by
        have hh := hf'.comp 0 (hasDerivAt_neg (0 : ℝ))
        simpa [Function.comp_def, h.deriv_zero] using hh
      refine hc.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = -L
        · subst z
          simp [productionEvenCompactLiftReal, h.value_endpoint, hL.le]
        · have hzgt : -L < z := lt_of_le_of_ne hz.1 (Ne.symm hzL)
          exact productionEvenCompactLiftReal_left hL f hzgt hz.2
      · simp [productionEvenCompactLiftReal]
    have hright0 :
        HasDerivWithinAt (productionEvenCompactLiftReal L f) 0
          (Icc 0 L) 0 := by
      have hc : HasDerivAt f 0 0 := by
        simpa [h.deriv_zero] using
          (productionEvenCompactLiftJets_differentiable h 0).hasDerivAt
      refine hc.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = L
        · subst z
          simp [productionEvenCompactLiftReal, h.value_endpoint, hL.le]
        · have hzlt : z < L := lt_of_le_of_ne hz.2 hzL
          exact productionEvenCompactLiftReal_right hL f hz.1 hzlt
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
      exact productionEvenCompactLiftReal_right hL f (le_of_lt hz.1) hz.2
    have hc :=
      (productionEvenCompactLiftJets_differentiable h y).hasDerivAt
        |>.congr_of_eventuallyEq hev
    have hnleft : ¬ y ≤ -L := by linarith
    have hnzero : ¬ y ≤ 0 := not_le.mpr hypos
    simpa [productionEvenCompactLiftRealDerivative, hnleft, hnzero, hright] using hc
  by_cases hrightEq : y = L
  · subst y
    have hint0 : HasDerivAt f 0 L := by
      simpa [h.deriv_endpoint] using
        (productionEvenCompactLiftJets_differentiable h L).hasDerivAt
    have hint :
        HasDerivWithinAt (productionEvenCompactLiftReal L f) 0
          (Icc 0 L) L := by
      refine hint0.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = L
        · subst z
          simp [productionEvenCompactLiftReal, h.value_endpoint, hL.le]
        · have hzlt : z < L := lt_of_le_of_ne hz.2 hzL
          exact productionEvenCompactLiftReal_right hL f hz.1 hzlt
      · simp [productionEvenCompactLiftReal, h.value_endpoint, hL.le]
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
      · simp [productionEvenCompactLiftReal]
    have hmem : Icc 0 L ∪ Ici L ∈ 𝓝 L := by
      apply mem_of_superset (Ioi_mem_nhds hL)
      intro z hz
      by_cases hh : z ≤ L
      · exact Or.inl ⟨le_of_lt hz, hh⟩
      · exact Or.inr (le_of_not_ge hh)
    have hh := (hint.union hext).hasDerivAt hmem
    have hnleft : ¬ L ≤ -L := by linarith
    have hnzero : ¬ L ≤ 0 := by linarith
    simpa [productionEvenCompactLiftRealDerivative, hnleft, hnzero,
      h.deriv_endpoint] using hh
  · have hgt : L < y :=
      lt_of_le_of_ne (le_of_not_gt hright) (Ne.symm hrightEq)
    have hev : productionEvenCompactLiftReal L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hgt] with z hz
      have hzL : L < z := hz
      have hnleft : ¬ z ≤ -L := by linarith
      have hnzero : ¬ z ≤ 0 := by linarith
      have hnlt : ¬ z < L := by linarith
      simp [productionEvenCompactLiftReal, hnleft, hnzero, hnlt]
    have hc := (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
    have hnleft : ¬ y ≤ -L := by linarith
    have hnzero : ¬ y ≤ 0 := by linarith
    have hnlt : ¬ y < L := by linarith
    simpa [productionEvenCompactLiftRealDerivative, hnleft, hnzero, hnlt] using hc

private theorem productionEvenCompactLiftRealDerivative_left
    {L t : ℝ} (f : ℝ → ℝ)
    (htL : -L < t) (ht0 : t ≤ 0) :
    productionEvenCompactLiftRealDerivative L f t = -deriv f (-t) := by
  simp [productionEvenCompactLiftRealDerivative, not_le.mpr htL, ht0]

private theorem productionEvenCompactLiftRealDerivative_right
    {L t : ℝ} (hL : 0 < L) (f : ℝ → ℝ)
    (ht0 : 0 < t) (htL : t < L) :
    productionEvenCompactLiftRealDerivative L f t = deriv f t := by
  have hnleft : ¬ t ≤ -L := by linarith
  have hnzero : ¬ t ≤ 0 := not_le.mpr ht0
  simp [productionEvenCompactLiftRealDerivative, hnleft, hnzero, htL]

private theorem hasDerivAt_productionEvenCompactLiftRealDerivative
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (h : ProductionEvenCompactLiftJets L f) (y : ℝ) :
    HasDerivAt (productionEvenCompactLiftRealDerivative L f)
      (productionEvenCompactLiftRealSecondDerivative L f y) y := by
  have hL0 : ¬ L ≤ 0 := not_le.mpr hL
  have hLL : ¬ L ≤ -L := by linarith
  have hdfdiff : Differentiable ℝ (deriv f) :=
    productionEvenCompactLiftJets_deriv_differentiable h
  by_cases hleft : y < -L
  · have hev :
        productionEvenCompactLiftRealDerivative L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hleft] with z hz
      have hzlt : z < -L := hz
      simp [productionEvenCompactLiftRealDerivative, le_of_lt hzlt]
    have hc := (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
    simpa [productionEvenCompactLiftRealSecondDerivative, le_of_lt hleft] using hc
  by_cases hleftEq : y = -L
  · subst y
    have hzeroExt :
        HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f) 0
          (Iic (-L)) (-L) := by
      have hc :
          HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Iic (-L)) (-L) :=
        (hasDerivAt_const (-L) (0 : ℝ)).hasDerivWithinAt
      refine hc.congr_of_mem ?_ ?_
      · intro z hz
        have hzle : z ≤ -L := hz
        simp [productionEvenCompactLiftRealDerivative, hzle]
      · simp [productionEvenCompactLiftRealDerivative]
    have hint0 :
        HasDerivAt (fun y : ℝ => -deriv f (-y))
          (deriv (deriv f) L) (-L) := by
      have hf := (hdfdiff L).hasDerivAt
      have hf' : HasDerivAt (deriv f) (deriv (deriv f) L) (-(-L)) := by
        simpa using hf
      have hh := hf'.comp (-L) (hasDerivAt_neg (-L))
      simpa [Function.comp_def, mul_comm] using hh.neg
    have hint :
        HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f) 0
          (Icc (-L) 0) (-L) := by
      rw [h.second_endpoint] at hint0
      refine hint0.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = -L
        · subst z
          simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint, hL.le]
        · have hzgt : -L < z := lt_of_le_of_ne hz.1 (Ne.symm hzL)
          exact productionEvenCompactLiftRealDerivative_left f hzgt hz.2
      · simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint, hL.le]
    have hmem : Iic (-L) ∪ Icc (-L) 0 ∈ 𝓝 (-L) := by
      apply mem_of_superset (Iio_mem_nhds (show -L < 0 by linarith))
      intro z hz
      by_cases hh : z ≤ -L
      · exact Or.inl hh
      · exact Or.inr ⟨le_of_not_ge hh, le_of_lt hz⟩
    have hh := (hzeroExt.union hint).hasDerivAt hmem
    simpa [productionEvenCompactLiftRealSecondDerivative, h.second_endpoint] using hh
  have hgtLeft : -L < y :=
    lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hleftEq)
  by_cases hneg : y < 0
  · have hev :
        productionEvenCompactLiftRealDerivative L f =ᶠ[𝓝 y]
          fun z => -deriv f (-z) := by
      filter_upwards [Ioo_mem_nhds hgtLeft hneg] with z hz
      exact productionEvenCompactLiftRealDerivative_left f hz.1 (le_of_lt hz.2)
    have hh := (hdfdiff (-y)).hasDerivAt.comp y (hasDerivAt_neg y)
    have hc := hh.neg.congr_of_eventuallyEq hev
    simpa [productionEvenCompactLiftRealSecondDerivative,
      not_le.mpr hgtLeft, le_of_lt hneg, mul_comm] using hc
  by_cases hzero : y = 0
  · subst y
    have hleft0 :
        HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f)
          (deriv (deriv f) 0) (Icc (-L) 0) 0 := by
      have hf := (hdfdiff 0).hasDerivAt
      have hf' : HasDerivAt (deriv f) (deriv (deriv f) 0) (-0) := by
        simpa using hf
      have hh := hf'.comp 0 (hasDerivAt_neg (0 : ℝ))
      have hc :
          HasDerivAt (fun z : ℝ => -deriv f (-z))
            (deriv (deriv f) 0) 0 := by
        simpa [Function.comp_def, mul_comm] using hh.neg
      refine hc.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = -L
        · subst z
          simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint, hL.le]
        · have hzgt : -L < z := lt_of_le_of_ne hz.1 (Ne.symm hzL)
          exact productionEvenCompactLiftRealDerivative_left f hzgt hz.2
      · simp [productionEvenCompactLiftRealDerivative, h.deriv_zero]
    have hright0 :
        HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f)
          (deriv (deriv f) 0) (Icc 0 L) 0 := by
      refine (hdfdiff 0).hasDerivAt.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hz0 : z = 0
        · subst z
          simp [productionEvenCompactLiftRealDerivative, h.deriv_zero, hL0, hLL]
        by_cases hzL : z = L
        · subst z
          simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint,
            hL.le, hL0, hLL]
        · have hzpos : 0 < z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
          have hzlt : z < L := lt_of_le_of_ne hz.2 hzL
          exact productionEvenCompactLiftRealDerivative_right hL f hzpos hzlt
      · simp [productionEvenCompactLiftRealDerivative, h.deriv_zero, hL0, hLL]
    have hmem : Icc (-L) 0 ∪ Icc 0 L ∈ 𝓝 (0 : ℝ) := by
      apply mem_of_superset (Ioo_mem_nhds (show -L < 0 by linarith) hL)
      intro z hz
      by_cases hh : z ≤ 0
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
      exact productionEvenCompactLiftRealDerivative_right hL f hz.1 hz.2
    have hc := (hdfdiff y).hasDerivAt.congr_of_eventuallyEq hev
    have hnleft : ¬ y ≤ -L := by linarith
    have hnzero : ¬ y ≤ 0 := not_le.mpr hypos
    simpa [productionEvenCompactLiftRealSecondDerivative,
      hnleft, hnzero, hright] using hc
  by_cases hrightEq : y = L
  · subst y
    have hint0 : HasDerivAt (deriv f) 0 L := by
      simpa [h.second_endpoint] using (hdfdiff L).hasDerivAt
    have hint :
        HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f) 0
          (Icc 0 L) L := by
      refine hint0.hasDerivWithinAt.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hz0 : z = 0
        · subst z
          simp [productionEvenCompactLiftRealDerivative, h.deriv_zero, hL0, hLL]
        by_cases hzL : z = L
        · subst z
          simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint,
            hL.le, hL0, hLL]
        · have hzpos : 0 < z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
          have hzlt : z < L := lt_of_le_of_ne hz.2 hzL
          exact productionEvenCompactLiftRealDerivative_right hL f hzpos hzlt
      · simp [productionEvenCompactLiftRealDerivative, h.deriv_endpoint,
          hL.le, hL0, hLL]
    have hext :
        HasDerivWithinAt (productionEvenCompactLiftRealDerivative L f) 0
          (Ici L) L := by
      have hc := (hasDerivAt_const L (0 : ℝ)).hasDerivWithinAt
      refine hc.congr_of_mem ?_ ?_
      · intro z hz
        have hnleft : ¬ z ≤ -L := by linarith
        have hnzero : ¬ z ≤ 0 := by linarith
        have hnlt : ¬ z < L := not_lt.mpr hz
        simp [productionEvenCompactLiftRealDerivative, hnleft, hnzero, hnlt]
      · simp [productionEvenCompactLiftRealDerivative]
    have hmem : Icc 0 L ∪ Ici L ∈ 𝓝 L := by
      apply mem_of_superset (Ioi_mem_nhds hL)
      intro z hz
      by_cases hh : z ≤ L
      · exact Or.inl ⟨le_of_lt hz, hh⟩
      · exact Or.inr (le_of_not_ge hh)
    have hh := (hint.union hext).hasDerivAt hmem
    have hnleft : ¬ L ≤ -L := by linarith
    have hnzero : ¬ L ≤ 0 := by linarith
    simpa [productionEvenCompactLiftRealSecondDerivative, hnleft, hnzero,
      h.second_endpoint] using hh
  · have hgt : L < y :=
      lt_of_le_of_ne (le_of_not_gt hright) (Ne.symm hrightEq)
    have hev :
        productionEvenCompactLiftRealDerivative L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hgt] with z hz
      have hzL : L < z := hz
      have hnleft : ¬ z ≤ -L := by linarith
      have hnzero : ¬ z ≤ 0 := by linarith
      have hnlt : ¬ z < L := by linarith
      simp [productionEvenCompactLiftRealDerivative, hnleft, hnzero, hnlt]
    have hc := (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
    have hnleft : ¬ y ≤ -L := by linarith
    have hnzero : ¬ y ≤ 0 := by linarith
    have hnlt : ¬ y < L := by linarith
    simpa [productionEvenCompactLiftRealSecondDerivative, hnleft, hnzero, hnlt] using hc

private theorem productionEvenCompactLiftRealSecondDerivative_left
    {L t : ℝ} (f : ℝ → ℝ)
    (htL : -L < t) (ht0 : t ≤ 0) :
    productionEvenCompactLiftRealSecondDerivative L f t =
      deriv (deriv f) (-t) := by
  simp [productionEvenCompactLiftRealSecondDerivative, not_le.mpr htL, ht0]

private theorem productionEvenCompactLiftRealSecondDerivative_right
    {L t : ℝ} (hL : 0 < L) (f : ℝ → ℝ)
    (ht0 : 0 ≤ t) (htL : t < L) :
    productionEvenCompactLiftRealSecondDerivative L f t =
      deriv (deriv f) t := by
  by_cases ht : t = 0
  · subst t
    simp [productionEvenCompactLiftRealSecondDerivative, hL]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hnleft : ¬ t ≤ -L := by linarith
    have hnzero : ¬ t ≤ 0 := not_le.mpr htpos
    simp [productionEvenCompactLiftRealSecondDerivative, hnleft, hnzero, htL]

private theorem continuous_productionEvenCompactLiftRealSecondDerivative
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (h : ProductionEvenCompactLiftJets L f) :
    Continuous (productionEvenCompactLiftRealSecondDerivative L f) := by
  have hL0 : ¬ L ≤ 0 := not_le.mpr hL
  have hLL : ¬ L ≤ -L := by linarith
  have hdd : Continuous (deriv (deriv f)) :=
    productionEvenCompactLiftJets_second_deriv_continuous h
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hleft : y < -L
  · have hev :
        productionEvenCompactLiftRealSecondDerivative L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hleft] with z hz
      have hzlt : z < -L := hz
      simp [productionEvenCompactLiftRealSecondDerivative, le_of_lt hzlt]
    exact continuousAt_const.congr_of_eventuallyEq hev
  by_cases hleftEq : y = -L
  · subst y
    have hzero :
        ContinuousWithinAt (fun _ : ℝ => 0) (Iic (-L)) (-L) :=
      continuousAt_const.continuousWithinAt
    have hneg :
        ContinuousWithinAt (fun y : ℝ => deriv (deriv f) (-y))
          (Icc (-L) 0) (-L) :=
      (hdd.comp continuous_neg).continuousAt.continuousWithinAt
    have hzero' :
        ContinuousWithinAt
          (productionEvenCompactLiftRealSecondDerivative L f)
          (Iic (-L)) (-L) := by
      refine hzero.congr_of_mem ?_ ?_
      · intro z hz
        have hzle : z ≤ -L := hz
        simp [productionEvenCompactLiftRealSecondDerivative, hzle]
      · simp [productionEvenCompactLiftRealSecondDerivative]
    have hneg' :
        ContinuousWithinAt
          (productionEvenCompactLiftRealSecondDerivative L f)
          (Icc (-L) 0) (-L) := by
      refine hneg.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = -L
        · subst z
          simp [productionEvenCompactLiftRealSecondDerivative, h.second_endpoint, hL.le]
        · have hzgt : -L < z := lt_of_le_of_ne hz.1 (Ne.symm hzL)
          exact productionEvenCompactLiftRealSecondDerivative_left f hzgt hz.2
      · simp [productionEvenCompactLiftRealSecondDerivative, h.second_endpoint, hL.le]
    have hmem : Iic (-L) ∪ Icc (-L) 0 ∈ 𝓝 (-L) := by
      apply mem_of_superset (Iio_mem_nhds (show -L < 0 by linarith))
      intro z hz
      by_cases hh : z ≤ -L
      · exact Or.inl hh
      · exact Or.inr ⟨le_of_not_ge hh, le_of_lt hz⟩
    exact (hzero'.union hneg').continuousAt hmem
  have hgtLeft : -L < y :=
    lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hleftEq)
  by_cases hneg : y < 0
  · have hev :
        productionEvenCompactLiftRealSecondDerivative L f =ᶠ[𝓝 y]
          fun z => deriv (deriv f) (-z) := by
      filter_upwards [Ioo_mem_nhds hgtLeft hneg] with z hz
      exact productionEvenCompactLiftRealSecondDerivative_left f
        hz.1 (le_of_lt hz.2)
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
    have hn' :
        ContinuousWithinAt
          (productionEvenCompactLiftRealSecondDerivative L f)
          (Icc (-L) 0) 0 := by
      refine hn.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = -L
        · subst z
          simp [productionEvenCompactLiftRealSecondDerivative, h.second_endpoint, hL.le]
        · have hzgt : -L < z := lt_of_le_of_ne hz.1 (Ne.symm hzL)
          exact productionEvenCompactLiftRealSecondDerivative_left f hzgt hz.2
      · simp [productionEvenCompactLiftRealSecondDerivative, hL]
    have hp' :
        ContinuousWithinAt
          (productionEvenCompactLiftRealSecondDerivative L f)
          (Icc 0 L) 0 := by
      refine hp.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = L
        · subst z
          simp [productionEvenCompactLiftRealSecondDerivative, h.second_endpoint, hL.le]
        · have hzlt : z < L := lt_of_le_of_ne hz.2 hzL
          exact productionEvenCompactLiftRealSecondDerivative_right hL f hz.1 hzlt
      · simp [productionEvenCompactLiftRealSecondDerivative, hL]
    have hmem : Icc (-L) 0 ∪ Icc 0 L ∈ 𝓝 (0 : ℝ) := by
      apply mem_of_superset (Ioo_mem_nhds (show -L < 0 by linarith) hL)
      intro z hz
      by_cases hh : z ≤ 0
      · exact Or.inl ⟨le_of_lt hz.1, hh⟩
      · exact Or.inr ⟨le_of_not_ge hh, le_of_lt hz.2⟩
    exact (hn'.union hp').continuousAt hmem
  have hypos : 0 < y :=
    lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
  by_cases hright : y < L
  · have hev :
        productionEvenCompactLiftRealSecondDerivative L f =ᶠ[𝓝 y]
          deriv (deriv f) := by
      filter_upwards [Ioo_mem_nhds hypos hright] with z hz
      exact productionEvenCompactLiftRealSecondDerivative_right hL f
        (le_of_lt hz.1) hz.2
    exact hdd.continuousAt.congr_of_eventuallyEq hev
  by_cases hrightEq : y = L
  · subst y
    have hp :
        ContinuousWithinAt (deriv (deriv f)) (Icc 0 L) L :=
      hdd.continuousAt.continuousWithinAt
    have hzero :
        ContinuousWithinAt (fun _ : ℝ => 0) (Ici L) L :=
      continuousAt_const.continuousWithinAt
    have hp' :
        ContinuousWithinAt
          (productionEvenCompactLiftRealSecondDerivative L f)
          (Icc 0 L) L := by
      refine hp.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = L
        · subst z
          simp [productionEvenCompactLiftRealSecondDerivative, h.second_endpoint, hL.le]
        · have hzlt : z < L := lt_of_le_of_ne hz.2 hzL
          exact productionEvenCompactLiftRealSecondDerivative_right hL f hz.1 hzlt
      · simp [productionEvenCompactLiftRealSecondDerivative, h.second_endpoint, hL.le]
    have hzero' :
        ContinuousWithinAt
          (productionEvenCompactLiftRealSecondDerivative L f)
          (Ici L) L := by
      refine hzero.congr_of_mem ?_ ?_
      · intro z hz
        by_cases hzL : z = L
        · subst z
          simp [productionEvenCompactLiftRealSecondDerivative]
        · have hzgt : L < z := lt_of_le_of_ne hz (Ne.symm hzL)
          have hnleft : ¬ z ≤ -L := by linarith
          have hnzero : ¬ z ≤ 0 := by linarith
          have hnlt : ¬ z < L := not_lt.mpr (le_of_lt hzgt)
          simp [productionEvenCompactLiftRealSecondDerivative,
            hnleft, hnzero, hnlt]
      · simp [productionEvenCompactLiftRealSecondDerivative]
    have hmem : Icc 0 L ∪ Ici L ∈ 𝓝 L := by
      apply mem_of_superset (Ioi_mem_nhds hL)
      intro z hz
      by_cases hh : z ≤ L
      · exact Or.inl ⟨le_of_lt hz, hh⟩
      · exact Or.inr (le_of_not_ge hh)
    exact (hp'.union hzero').continuousAt hmem
  · have hgt : L < y :=
      lt_of_le_of_ne (le_of_not_gt hright) (Ne.symm hrightEq)
    have hev :
        productionEvenCompactLiftRealSecondDerivative L f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hgt] with z hz
      have hzL : L < z := hz
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
  simpa [Function.comp_def] using
    Complex.ofRealCLM.contDiff.comp
      (contDiff_two_productionEvenCompactLiftReal hL h)

theorem productionEvenCompactLift_hasCompactSupport
    {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    HasCompactSupport (productionEvenCompactLift L f) := by
  apply HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc
  intro y hy
  have habs : L < |y| := by
    by_contra hnot
    apply hy
    exact abs_le.mp (le_of_not_gt hnot)
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
    change
      ((productionEvenCompactLiftReal L f (-y) : ℝ) : ℂ) =
        ((productionEvenCompactLiftReal L f y : ℝ) : ℂ)
    rw [productionEvenCompactLiftReal_even hL f y]
  · simp [productionEvenCompactLift, productionEvenCompactLiftReal_zero hL, h.value_zero]
  · intro y hy
    apply productionEvenCompactLiftReal_support_subset hL f
    simpa [productionEvenCompactLift] using hy
  · intro y hy
    by_cases hyL : y = L
    · subst y
      simp [productionEvenCompactLift, productionEvenCompactLiftReal,
        hL, h.value_endpoint]
    · have hylt : y < L := lt_of_le_of_ne hy.2 hyL
      simp [productionEvenCompactLift,
        productionEvenCompactLiftReal_right hL f hy.1 hylt]

/-!
Concrete weighted tests are instantiated below.  Their endpoint proofs are
separated from the generic gluing theorem so downstream arithmetic identities
can cite exactly which source-coordinate cancellations were used.
-/

/-- Zero coefficient sum for every strict-even legal vector. -/
theorem evenBoundaryFlat_coordinateSum_zero
    (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) :
    ∑ i, (evenBoundaryFlatRawCoefficients K z) i = 0 := by
  exact sum_eq_zero_of_boundaryFlat
    (evenBoundaryFlatRawCoefficients_boundaryFlat K z)

/-- The actual first source-energy derivative vanishes at both source
endpoints for a boundary-flat state. -/
theorem sourceAtomRealEnergyDerivative_endpoints_zero
    (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) :
    sourceAtomRealEnergyDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 0 = 0 ∧
      sourceAtomRealEnergyDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 1 = 0 := by
  let x : EuclideanSpace ℂ (Fin (2 * K + 1)) := z
  let u : Fin (2 * K + 1) → ℂ :=
    (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  have hflat : BoundaryFlatCoefficients K u := by
    simpa [x, u, evenBoundaryFlatRawCoefficients] using
      evenBoundaryFlatRawCoefficients_boundaryFlat K z
  have hsum : ∑ i, u i = 0 := sum_eq_zero_of_boundaryFlat hflat
  have hri := coefficientSumReal_re_im_eq_zero_of_sum_eq_zero K u hsum
  unfold sourceAtomRealEnergyDerivative
  change
    sourceContractRealDerivative K (fun i => (u i).re) 0 +
          sourceContractRealDerivative K (fun i => (u i).im) 0 = 0 ∧
      sourceContractRealDerivative K (fun i => (u i).re) 1 +
          sourceContractRealDerivative K (fun i => (u i).im) 1 = 0
  constructor
  · rw [sourceContractRealDerivative_zero_eq_two_coefficientSum_sq,
      sourceContractRealDerivative_zero_eq_two_coefficientSum_sq,
      hri.1, hri.2]
    ring
  · rw [sourceContractRealDerivative_one_eq_two_coefficientSum_sq,
      sourceContractRealDerivative_one_eq_two_coefficientSum_sq,
      hri.1, hri.2]
    ring

/-- The first weighted physical derivative has the endpoint jets needed by the
compact even lift. -/
theorem productionFirstDerivativePhysicalRaw_liftJets
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    ProductionEvenCompactLiftJets L
      (productionFirstDerivativePhysicalRaw L K z) := by
  have hend := sourceAtomRealEnergyDerivative_endpoints_zero K z
  have hcoordL : 1 - L / L = 0 := by
    rw [div_self hL.ne']
    ring
  refine ⟨contDiff_two_productionFirstDerivativePhysicalRaw hL.ne' K z,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [productionFirstDerivativePhysicalRaw]
  · have hcoord :
        HasDerivAt (fun t : ℝ => 1 - t / L) (-(1 / L)) 0 := by
      simpa only [zero_sub] using
        (hasDerivAt_const 0 (1 : ℝ)).sub
          ((hasDerivAt_id 0).div_const L)
    have hcoord0 : 1 - 0 / L = 1 := by simp [hL.ne']
    have hsource :=
      (hasDerivAt_sourceAtomRealEnergyDerivative_transport K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - 0 / L)).comp 0 hcoord
    have hd :=
      (hasDerivAt_id 0).mul
        (((hasDerivAt_const 0 (L ^ 2)).inv
          (pow_ne_zero 2 hL.ne')).mul hsource)
    simpa [productionFirstDerivativePhysicalRaw, hcoord0, hend.2] using hd.deriv
  · simp [productionFirstDerivativePhysicalRaw, hcoordL,
      sourceAtomRealEnergyDerivative_zero_of_boundaryFlat K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (evenBoundaryFlatRawCoefficients_boundaryFlat K z)]
  · have hjet :=
      sourceAtomRealEnergy_boundaryFlat_jets_through_six K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (evenBoundaryFlatRawCoefficients_boundaryFlat K z)
    simp [productionFirstDerivativePhysicalRaw, hcoordL, hjet] 
  · have hjet :=
      sourceAtomRealEnergy_boundaryFlat_jets_through_six K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (evenBoundaryFlatRawCoefficients_boundaryFlat K z)
    simp [productionFirstDerivativePhysicalRaw, hcoordL, hjet]

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

/-- The complete production RHS only samples the physical interval and the
prime logarithms lying in that interval. -/
private theorem productionArithmeticComplexValue_congr_on_Icc
    {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hfg : ∀ t : ℝ, t ∈ Icc (0 : ℝ) L → f t = g t) :
    productionArithmeticComplexValue L f =
      productionArithmeticComplexValue L g := by
  unfold productionArithmeticComplexValue dictionaryCompletePhysicalRHS
  have hpole :
      (∫ t in (0 : ℝ)..L,
        f t * (completeSourcePoleWeight t : ℂ)) =
      ∫ t in (0 : ℝ)..L,
        g t * (completeSourcePoleWeight t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    rw [hfg t ht]
  have harch :
      (∫ t in (0 : ℝ)..L,
        f t * (archDensity t : ℂ)) =
      ∫ t in (0 : ℝ)..L,
        g t * (archDensity t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    rw [hfg t ht]
  have hprime :
      (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q * f (Real.log q)) =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q * g (Real.log q) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqmem := Finset.mem_Icc.mp hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hqmem.1)
    have hqexp : (q : ℝ) ≤ Real.exp L :=
      (Nat.le_floor_iff (Real.exp_pos L).le).mp hqmem.2
    have hlog0 : 0 ≤ Real.log (q : ℝ) :=
      Real.log_natCast_nonneg q
    have hlogL : Real.log (q : ℝ) ≤ L := by
      rw [← Real.log_exp L]
      exact Real.log_le_log hqpos hqexp
    rw [hfg (Real.log q) ⟨hlog0, hlogL⟩]
  rw [hpole, harch, hprime]

/-- Full authority for k1. -/
theorem productionFirstDerivativeTest_authority
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    (1 / 2 : ℂ) * Zeta23.EF.literatureRHS
        (productionFirstDerivativeGlobalTest L K z) =
      productionArithmeticComplexValue L
        (fun t => (productionFirstDerivativePhysicalTest L K z t : ℂ)) := by
  have hg := (productionFirstDerivativeGlobalLift hL K z).physical_authority hL
  calc
    (1 / 2 : ℂ) * Zeta23.EF.literatureRHS
        (productionFirstDerivativeGlobalTest L K z) =
        productionArithmeticComplexValue L
          (fun t => (productionFirstDerivativePhysicalRaw L K z t : ℂ)) := hg
    _ = productionArithmeticComplexValue L
          (fun t => (productionFirstDerivativePhysicalTest L K z t : ℂ)) := by
      apply productionArithmeticComplexValue_congr_on_Icc hL
      intro t ht
      exact congrArg (fun x : ℝ => (x : ℂ))
        (productionFirstDerivativeRaw_eq_test_on_Icc hL K z ht)


/-! ## Second and mixed weighted derivative lifts -/

private theorem hasDerivAt_sourceAtomRealEnergySecondDerivative_from_contDiff
    (K : ℕ) (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (u : ℝ) :
    HasDerivAt (sourceAtomRealEnergySecondDerivative K z)
      (deriv (sourceAtomRealEnergySecondDerivative K z) u) u :=
  ((contDiff_two_sourceAtomRealEnergySecondDerivative K z).differentiable
    (by norm_num) u).hasDerivAt

/-- Boundary-flat source energy has zero second through fourth source jets at
the entering endpoint.  This packages exactly the endpoint information used by
the t²-weighted second variation. -/
theorem sourceAtomRealEnergy_second_through_four_zero
    (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) :
    sourceAtomRealEnergySecondDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 0 = 0 ∧
      deriv (sourceAtomRealEnergySecondDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) 0 = 0 ∧
      deriv (deriv (sourceAtomRealEnergySecondDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1))))) 0 = 0 := by
  let x : EuclideanSpace ℂ (Fin (2 * K + 1)) := z
  have hflat := evenBoundaryFlatRawCoefficients_boundaryFlat K z
  have hj :=
    sourceAtomRealEnergy_boundaryFlat_jets_through_six K x hflat
  have h2 : iteratedDeriv 2 (sourceAtomRealEnergy K x) 0 = 0 :=
    hj 2 (by omega) (by omega)
  have h3 : iteratedDeriv 3 (sourceAtomRealEnergy K x) 0 = 0 :=
    hj 3 (by omega) (by omega)
  have h4 : iteratedDeriv 4 (sourceAtomRealEnergy K x) 0 = 0 :=
    hj 4 (by omega) (by omega)
  have hderiv1 :
      deriv (sourceAtomRealEnergy K x) =
        sourceAtomRealEnergyDerivative K x := by
    funext t
    exact (hasDerivAt_sourceAtomRealEnergy_transport K x t).deriv
  have hderiv2 :
      deriv (sourceAtomRealEnergyDerivative K x) =
        sourceAtomRealEnergySecondDerivative K x := by
    funext t
    exact (hasDerivAt_sourceAtomRealEnergyDerivative_transport K x t).deriv
  have hiter2 :
      iteratedDeriv 2 (sourceAtomRealEnergy K x) =
        sourceAtomRealEnergySecondDerivative K x := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
      hderiv1, hderiv2]
  have hiter3 :
      iteratedDeriv 3 (sourceAtomRealEnergy K x) =
        deriv (sourceAtomRealEnergySecondDerivative K x) := by
    rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ, hiter2]
  have hiter4 :
      iteratedDeriv 4 (sourceAtomRealEnergy K x) =
        deriv (deriv (sourceAtomRealEnergySecondDerivative K x)) := by
    rw [show 4 = 3 + 1 by norm_num, iteratedDeriv_succ, hiter3]
  constructor
  · rw [← congrFun hiter2 0, h2]
  constructor
  · rw [← congrFun hiter3 0, h3]
  · rw [← congrFun hiter4 0, h4]

theorem productionSecondDerivativePhysicalRaw_liftJets
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    ProductionEvenCompactLiftJets L
      (productionSecondDerivativePhysicalRaw L K z) := by
  have hj := sourceAtomRealEnergy_second_through_four_zero K z
  have hcoordL : 1 - L / L = 0 := by
    rw [div_self hL.ne']
    ring
  refine ⟨contDiff_two_productionSecondDerivativePhysicalRaw hL.ne' K z,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [productionSecondDerivativePhysicalRaw]
  · simp [productionSecondDerivativePhysicalRaw]
  · simp [productionSecondDerivativePhysicalRaw, hcoordL, hj.1]
  · have hinner :
        HasDerivAt
          (fun t : ℝ =>
            sourceAtomRealEnergySecondDerivative K
              (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - t / L))
          (-(1 / L) *
            deriv (sourceAtomRealEnergySecondDerivative K
              (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) 0) L := by
      have hcoord :
          HasDerivAt (fun t : ℝ => 1 - t / L) (-(1 / L)) L := by
        convert (hasDerivAt_const L (1 : ℝ)).sub
          ((hasDerivAt_id L).div_const L) using 1 <;> ring
      have hcoordL : 1 - L / L = 0 := by
        rw [div_self hL.ne']
        ring
      have hs :=
        (hasDerivAt_sourceAtomRealEnergySecondDerivative_from_contDiff K
          (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 0).comp L hcoord
      simpa [hcoordL, mul_comm] using hs
    have hp :=
      ((hasDerivAt_id L).pow 2).div_const (L ^ 4) |>.mul hinner
    simpa [productionSecondDerivativePhysicalRaw, hcoordL, hj.1, hj.2.1] using hp.deriv
  · have hC2 := contDiff_two_productionSecondDerivativePhysicalRaw hL.ne' K z
    have hD1 : ContDiff ℝ 1
        (deriv (productionSecondDerivativePhysicalRaw L K z)) := by
      have hC2' :
          ContDiff ℝ (1 + 1 : ℕ∞ω)
            (productionSecondDerivativePhysicalRaw L K z) := by
        simpa using hC2
      simpa using hC2'.deriv'
    have hsecond := ((hD1.differentiable (by norm_num)) L).hasDerivAt
    have hzero :
        deriv (productionSecondDerivativePhysicalRaw L K z) L = 0 := by
      have hinner :
          HasDerivAt
            (fun t : ℝ =>
              sourceAtomRealEnergySecondDerivative K
                (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - t / L))
            (-(1 / L) *
              deriv (sourceAtomRealEnergySecondDerivative K
                (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) 0) L := by
        have hcoord :
            HasDerivAt (fun t : ℝ => 1 - t / L) (-(1 / L)) L := by
          convert (hasDerivAt_const L (1 : ℝ)).sub
            ((hasDerivAt_id L).div_const L) using 1 <;> field_simp [hL.ne'] <;> ring
        exact
          (by
        simpa [hL.ne', mul_comm] using
          (hasDerivAt_sourceAtomRealEnergySecondDerivative_from_contDiff K
            (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - L / L)).comp L hcoord)
      have hp :=
        ((hasDerivAt_id L).pow 2).div_const (L ^ 4) |>.mul hinner
      simpa [productionSecondDerivativePhysicalRaw, hcoordL, hj.1, hj.2.1] using hp.deriv
    rw [hzero] at hsecond
    have hthird := hj.2.2
    simpa [productionSecondDerivativePhysicalRaw, hcoordL, hj.1, hj.2.1, hthird] using hsecond.deriv

def productionSecondDerivativeGlobalTest
    (L : ℝ) (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℂ :=
  productionEvenCompactLift L (productionSecondDerivativePhysicalRaw L K z)

theorem productionSecondDerivativeGlobalLift
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    ProductionWeightedGlobalLift L
      (productionSecondDerivativeGlobalTest L K z)
      (productionSecondDerivativePhysicalRaw L K z) :=
  productionEvenCompactLift_toGlobalLift hL
    (productionSecondDerivativePhysicalRaw_liftJets hL K z)

private theorem production_sum_sum_pairing_factor
    {ι : Type*} [Fintype ι]
    (u v : ι → ℂ) :
    (∑ i, ∑ j, star (u i) * v j) =
      star (∑ i, u i) * (∑ j, v j) := by
  classical
  calc
    (∑ i, ∑ j, star (u i) * v j) =
        ∑ i, star (u i) * (∑ j, v j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = (∑ i, star (u i)) * (∑ j, v j) := by
          rw [Finset.sum_mul]
    _ = star (∑ i, u i) * (∑ j, v j) := by
          congr 1
          change
            (∑ i, (starRingEnd ℂ) (u i)) =
              (starRingEnd ℂ) (∑ i, u i)
          rw [map_sum]

private theorem production_sum_sum_real_smul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ℝ) (f : ι → κ → ℂ) :
    (∑ i, ∑ j, a • f i j) = a • (∑ i, ∑ j, f i j) := by
  classical
  symm
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.smul_sum]

/-- Mixed source derivative vanishes at both source endpoints when both legal
vectors have zero coefficient sum. -/
theorem sourceAtomPairingDerivative_endpoints_zero
    (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    sourceAtomPairingDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (w : EuclideanSpace ℂ (Fin (2 * K + 1))) 0 = 0 ∧
      sourceAtomPairingDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (w : EuclideanSpace ℂ (Fin (2 * K + 1))) 1 = 0 := by
  let x : EuclideanSpace ℂ (Fin (2 * K + 1)) := z
  let y : EuclideanSpace ℂ (Fin (2 * K + 1)) := w
  have hx0 : sourcePairingCoefficientSum K x = 0 := by
    simpa [x, sourcePairingCoefficientSum, evenBoundaryFlatRawCoefficients] using
      evenBoundaryFlat_coordinateSum_zero K z
  have hy0 : sourcePairingCoefficientSum K y = 0 := by
    simpa [y, sourcePairingCoefficientSum, evenBoundaryFlatRawCoefficients] using
      evenBoundaryFlat_coordinateSum_zero K w
  have endpoint_zero :
      sourceAtomPairingDerivative K x y 0 =
        (2 : ℝ) •
          (star (sourcePairingCoefficientSum K x) *
            sourcePairingCoefficientSum K y) :=
    sourceAtomPairingDerivative_zero_eq_two_sum_pairing K x y
  have endpoint_one :
      sourceAtomPairingDerivative K x y 1 =
        (2 : ℝ) •
          (star (sourcePairingCoefficientSum K x) *
            sourcePairingCoefficientSum K y) := by
    let ux := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
    let uy := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) y
    unfold sourceAtomPairingDerivative
    simp_rw [sourceEntryDerivative_one]
    calc
      (∑ i, ∑ j, (2 : ℝ) • (star (ux i) * uy j)) =
          (2 : ℝ) • (∑ i, ∑ j, star (ux i) * uy j) := by
            exact production_sum_sum_real_smul 2
              (fun i j => star (ux i) * uy j)
      _ = (2 : ℝ) • (star (∑ i, ux i) * (∑ j, uy j)) := by
            rw [production_sum_sum_pairing_factor]
      _ = _ := by rfl
  constructor
  · simpa [x, y, hx0, hy0] using endpoint_zero
  · simpa [x, y, hx0, hy0] using endpoint_one

/-- Third mixed source jet vanishes at the entering endpoint for even
boundary-flat z,w. -/
theorem sourceAtomPairingDerivative_secondDerivative_zero
    (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    deriv (deriv (sourceAtomPairingDerivative K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (w : EuclideanSpace ℂ (Fin (2 * K + 1))))) 0 = 0 := by
  have hw0 : sourcePairingCoefficientSum K
      (w : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
    simpa [sourcePairingCoefficientSum, evenBoundaryFlatRawCoefficients] using
      evenBoundaryFlat_coordinateSum_zero K w
  have h3 :=
    iteratedDeriv_three_sourceAtomPairing_eq_moments_of_right_sum_zero
      K (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (w : EuclideanSpace ℂ (Fin (2 * K + 1))) hw0
  have hzflat := evenBoundaryFlatRawCoefficients_boundaryFlat K z
  have hwflat := evenBoundaryFlatRawCoefficients_boundaryFlat K w
  have hzeven := evenBoundaryFlatRawCoefficients_mem_even K z
  have hweven := evenBoundaryFlatRawCoefficients_mem_even K w
  have hm1z :
      centeredMoment K 1 (evenBoundaryFlatRawCoefficients K z) = 0 := hzflat.2.1
  have hm1w :
      centeredMoment K 1 (evenBoundaryFlatRawCoefficients K w) = 0 := hwflat.2.1
  have hm0z :
      centeredMoment K 0 (evenBoundaryFlatRawCoefficients K z) = 0 := hzflat.1
  have hm0w :
      centeredMoment K 0 (evenBoundaryFlatRawCoefficients K w) = 0 := hwflat.1
  have hz3 :
      iteratedDeriv 3
        (sourceAtomPairing K
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (w : EuclideanSpace ℂ (Fin (2 * K + 1)))) 0 = 0 := by
    rw [h3]
    simp [hm0z, hm0w, hm1z, hm1w]
  have hderiv1 :
      deriv
        (sourceAtomPairing K
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (w : EuclideanSpace ℂ (Fin (2 * K + 1)))) =
        sourceAtomPairingDerivative K
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (w : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
    funext t
    exact (hasDerivAt_sourceAtomPairing K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (w : EuclideanSpace ℂ (Fin (2 * K + 1))) t).deriv
  have hiter3 :
      iteratedDeriv 3
        (sourceAtomPairing K
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (w : EuclideanSpace ℂ (Fin (2 * K + 1)))) =
        deriv (deriv (sourceAtomPairingDerivative K
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (w : EuclideanSpace ℂ (Fin (2 * K + 1))))) := by
    rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ,
      show 2 = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one, hderiv1]
  rw [← congrFun hiter3 0, hz3]

theorem productionMixedDerivativePhysicalRaw_liftJets
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    ProductionEvenCompactLiftJets L
      (productionMixedDerivativePhysicalRaw L K z w) := by
  have hend := sourceAtomPairingDerivative_endpoints_zero K z w
  have hcoordL : 1 - L / L = 0 := by
    rw [div_self hL.ne']
    ring
  refine ⟨contDiff_two_productionMixedDerivativePhysicalRaw hL.ne' K z w,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [productionMixedDerivativePhysicalRaw]
  · simp [productionMixedDerivativePhysicalRaw, hend.2]
  · simp [productionMixedDerivativePhysicalRaw, hcoordL, hend.1]
  · have hpair2 :
        deriv (sourceAtomPairingDerivative K
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (w : EuclideanSpace ℂ (Fin (2 * K + 1)))) 0 = 0 := by
      have hsumz : sourcePairingCoefficientSum K
          (z : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
        simpa [sourcePairingCoefficientSum, evenBoundaryFlatRawCoefficients] using
          evenBoundaryFlat_coordinateSum_zero K z
      have hsumw : sourcePairingCoefficientSum K
          (w : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
        simpa [sourcePairingCoefficientSum, evenBoundaryFlatRawCoefficients] using
          evenBoundaryFlat_coordinateSum_zero K w
      rw [(hasDerivAt_sourceAtomPairingDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (w : EuclideanSpace ℂ (Fin (2 * K + 1))) 0).deriv]
      rw [sourceAtomPairingSecondDerivative_eq_indexActions K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (w : EuclideanSpace ℂ (Fin (2 * K + 1))) 0 hsumz hsumw]
      simp [sourceAtomPairing]
    simp [productionMixedDerivativePhysicalRaw, hcoordL, hend.1, hpair2]
  · have h3 := sourceAtomPairingDerivative_secondDerivative_zero K z w
    simp [productionMixedDerivativePhysicalRaw, hcoordL, hend.1, h3]

def productionMixedDerivativeGlobalTest
    (L : ℝ) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) : ℝ → ℂ :=
  productionEvenCompactLift L (productionMixedDerivativePhysicalRaw L K z w)

theorem productionMixedDerivativeGlobalLift
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    ProductionWeightedGlobalLift L
      (productionMixedDerivativeGlobalTest L K z w)
      (productionMixedDerivativePhysicalRaw L K z w) :=
  productionEvenCompactLift_toGlobalLift hL
    (productionMixedDerivativePhysicalRaw_liftJets hL K z w)

theorem productionSecondDerivativeTest_authority
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    (1 / 2 : ℂ) * Zeta23.EF.literatureRHS
        (productionSecondDerivativeGlobalTest L K z) =
      productionArithmeticComplexValue L
        (fun t => (productionSecondDerivativePhysicalTest L K z t : ℂ)) := by
  have hg := (productionSecondDerivativeGlobalLift hL K z).physical_authority hL
  calc
    (1 / 2 : ℂ) * Zeta23.EF.literatureRHS
        (productionSecondDerivativeGlobalTest L K z) =
        productionArithmeticComplexValue L
          (fun t => (productionSecondDerivativePhysicalRaw L K z t : ℂ)) := hg
    _ = productionArithmeticComplexValue L
          (fun t => (productionSecondDerivativePhysicalTest L K z t : ℂ)) := by
      apply productionArithmeticComplexValue_congr_on_Icc hL
      intro t ht
      simp [productionSecondDerivativePhysicalTest, productionPhysicalClamp, ht]

theorem productionMixedDerivativeTest_authority
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    (1 / 2 : ℂ) * Zeta23.EF.literatureRHS
        (productionMixedDerivativeGlobalTest L K z w) =
      productionArithmeticComplexValue L
        (fun t => (productionMixedDerivativePhysicalTest L K z w t : ℂ)) := by
  have hg := (productionMixedDerivativeGlobalLift hL K z w).physical_authority hL
  calc
    (1 / 2 : ℂ) * Zeta23.EF.literatureRHS
        (productionMixedDerivativeGlobalTest L K z w) =
        productionArithmeticComplexValue L
          (fun t => (productionMixedDerivativePhysicalRaw L K z w t : ℂ)) := hg
    _ = productionArithmeticComplexValue L
          (fun t => (productionMixedDerivativePhysicalTest L K z w t : ℂ)) := by
      apply productionArithmeticComplexValue_congr_on_Icc hL
      intro t ht
      simp [productionMixedDerivativePhysicalTest, productionPhysicalClamp, ht]

/-- Full F02 packages for the actual derivative tests. -/
theorem productionDerivativeWeightedTests_admissible
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    ProductionWeightedTestAdmissible L
        (productionFirstDerivativeGlobalTest L K z)
        (productionFirstDerivativePhysicalTest L K z) ∧
      ProductionWeightedTestAdmissible L
        (productionSecondDerivativeGlobalTest L K z)
        (productionSecondDerivativePhysicalTest L K z) ∧
      ProductionWeightedTestAdmissible L
        (productionMixedDerivativeGlobalTest L K z w)
        (productionMixedDerivativePhysicalTest L K z w) := by
  have hp := production_derivative_tests_admissible hL K z w
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨(productionFirstDerivativeGlobalLift hL K z).contDiff_two,
      (productionFirstDerivativeGlobalLift hL K z).compact_support,
      hp.1, ?_⟩
    exact productionFirstDerivativeTest_authority hL K z
  · refine ⟨(productionSecondDerivativeGlobalLift hL K z).contDiff_two,
      (productionSecondDerivativeGlobalLift hL K z).compact_support,
      hp.2.1, ?_⟩
    exact productionSecondDerivativeTest_authority hL K z
  · refine ⟨(productionMixedDerivativeGlobalLift hL K z w).contDiff_two,
      (productionMixedDerivativeGlobalLift hL K z w).compact_support,
      hp.2.2, ?_⟩
    exact productionMixedDerivativeTest_authority hL K z w

end Zeta23.CCM

#print axioms Zeta23.CCM.productionEvenCompactLift_toGlobalLift
#print axioms Zeta23.CCM.productionFirstDerivativeGlobalLift
#print axioms Zeta23.CCM.productionFirstDerivativeTest_authority
#print axioms Zeta23.CCM.productionSecondDerivativeTest_authority
#print axioms Zeta23.CCM.productionMixedDerivativeTest_authority
#print axioms Zeta23.CCM.productionDerivativeWeightedTests_admissible
