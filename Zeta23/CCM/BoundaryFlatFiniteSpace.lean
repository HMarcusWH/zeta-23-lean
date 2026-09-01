import Zeta23.CCM.LocalizedFiniteSpace
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Piecewise

noncomputable section

namespace Zeta23.CCM

open Complex Set Filter
open scoped BigOperators

/-!
# F0-B1A: boundary-flat finite sector

This module isolates the finite centered Fourier sector on which the hard
zero-extension from `[0,L]` is genuinely global `C²`.

The coefficient condition is exactly the vanishing of centered moments
of orders 0, 1 and 2.  Those conditions force the formula-level finite
Fourier function and its first two derivatives to vanish at both endpoints.

The module deliberately stops before approximation/density, continuity of the
genuine Weil form on an approximation family, strict-negativity transfer, F1,
or RH.
-/

/-- Common complex frequency factor for one unit centered Fourier index. -/
def localizedBaseFrequency (L : ℝ) : ℂ :=
  Complex.I * ((((2 * Real.pi) / L : ℝ)) : ℂ)

/-- Frequency of the normalized localized mode with integer index `n`. -/
def localizedFrequency (L : ℝ) (n : ℤ) : ℂ :=
  localizedBaseFrequency L * (n : ℂ)

/-- First derivative formula for a finite centered Fourier combination. -/
def localizedFiniteFirstJet
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (x : ℝ) : ℂ :=
  ∑ i,
    u i * localizedFrequency L (centeredIndex N i) *
      localizedMode L (centeredIndex N i) x

/-- Second derivative formula for a finite centered Fourier combination. -/
def localizedFiniteSecondJet
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (x : ℝ) : ℂ :=
  ∑ i,
    u i * localizedFrequency L (centeredIndex N i) ^ 2 *
      localizedMode L (centeredIndex N i) x

/-- Centered coefficient moment of order `k`. -/
def centeredMoment
    (N : ℕ) (k : ℕ) (u : Fin (2 * N + 1) → ℂ) : ℂ :=
  ∑ i, (centeredIndex N i : ℂ) ^ k * u i

/-- The codimension-at-most-three coefficient condition that kills value,
first derivative and second derivative at the hard-window boundary. -/
def BoundaryFlatCoefficients
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) : Prop :=
  centeredMoment N 0 u = 0 ∧
  centeredMoment N 1 u = 0 ∧
  centeredMoment N 2 u = 0

/-- The phase in `localizedMode` is the centered frequency times the real
coordinate embedded in `ℂ`. -/
theorem localizedMode_eq_frequency_exp
    (L : ℝ) (n : ℤ) (x : ℝ) :
    localizedMode L n x =
      ((1 / Real.sqrt L : ℝ) : ℂ) *
        Complex.exp (localizedFrequency L n * (x : ℂ)) := by
  unfold localizedMode localizedFrequency localizedBaseFrequency
  congr 2
  push_cast
  ring

/-- Exact real derivative of one normalized localized Fourier mode. -/
theorem hasDerivAt_localizedMode
    (L : ℝ) (n : ℤ) (x : ℝ) :
    HasDerivAt
      (localizedMode L n)
      (localizedFrequency L n * localizedMode L n x) x := by
  let c : ℂ := ((1 / Real.sqrt L : ℝ) : ℂ)
  let a : ℂ := localizedFrequency L n
  have hphase : HasDerivAt (fun z : ℂ => a * z) a (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul a
  have hcomplex :
      HasDerivAt
        (fun z : ℂ => c * Complex.exp (a * z))
        (a * (c * Complex.exp (a * (x : ℂ)))) (x : ℂ) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      hphase.cexp.const_mul c
  have hreal := hcomplex.comp_ofReal
  have hrepr :
      localizedMode L n =
        fun y : ℝ => c * Complex.exp (a * (y : ℂ)) := by
    funext y
    simp only [c, a, localizedMode_eq_frequency_exp]
  rw [hrepr]
  simpa only [c, a, mul_comm, mul_left_comm, mul_assoc] using hreal

/-- The explicit first jet is the derivative of the finite Fourier formula. -/
theorem hasDerivAt_localizedFiniteFunction
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (x : ℝ) :
    HasDerivAt
      (localizedFiniteFunction L N u)
      (localizedFiniteFirstJet L N u x) x := by
  unfold localizedFiniteFunction localizedFiniteFirstJet
  simpa only [mul_assoc] using
    (HasDerivAt.fun_sum
      (u := Finset.univ)
      (fun i _ =>
        (hasDerivAt_localizedMode L (centeredIndex N i) x).const_mul (u i)))

/-- The explicit second jet is the derivative of the first jet. -/
theorem hasDerivAt_localizedFiniteFirstJet
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (x : ℝ) :
    HasDerivAt
      (localizedFiniteFirstJet L N u)
      (localizedFiniteSecondJet L N u x) x := by
  unfold localizedFiniteFirstJet localizedFiniteSecondJet
  simpa only [pow_two, mul_assoc] using
    (HasDerivAt.fun_sum
      (u := Finset.univ)
      (fun i _ =>
        (hasDerivAt_localizedMode L (centeredIndex N i) x).const_mul
          (u i * localizedFrequency L (centeredIndex N i))))

/-- The second jet is continuous globally. -/
@[fun_prop] theorem continuous_localizedFiniteSecondJet
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    Continuous (localizedFiniteSecondJet L N u) := by
  unfold localizedFiniteSecondJet
  fun_prop

@[simp] theorem localizedMode_zero
    (L : ℝ) (n : ℤ) :
    localizedMode L n 0 = ((1 / Real.sqrt L : ℝ) : ℂ) := by
  simp [localizedMode]

/-- The formula-level finite Fourier function is periodic with period `L`. -/
theorem localizedFiniteFunction_add_period
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (x : ℝ) (hL : L ≠ 0) :
    localizedFiniteFunction L N u (x + L) =
      localizedFiniteFunction L N u x := by
  unfold localizedFiniteFunction
  apply Finset.sum_congr rfl
  intro i hi
  rw [localizedMode_add_period L (centeredIndex N i) x hL]

/-- The first jet is periodic with period `L`. -/
theorem localizedFiniteFirstJet_add_period
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (x : ℝ) (hL : L ≠ 0) :
    localizedFiniteFirstJet L N u (x + L) =
      localizedFiniteFirstJet L N u x := by
  unfold localizedFiniteFirstJet
  apply Finset.sum_congr rfl
  intro i hi
  rw [localizedMode_add_period L (centeredIndex N i) x hL]

/-- The second jet is periodic with period `L`. -/
theorem localizedFiniteSecondJet_add_period
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (x : ℝ) (hL : L ≠ 0) :
    localizedFiniteSecondJet L N u (x + L) =
      localizedFiniteSecondJet L N u x := by
  unfold localizedFiniteSecondJet
  apply Finset.sum_congr rfl
  intro i hi
  rw [localizedMode_add_period L (centeredIndex N i) x hL]

/-- Moment zero kills the value at the left endpoint. -/
theorem localizedFiniteFunction_zero_of_boundaryFlat
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients N u) :
    localizedFiniteFunction L N u 0 = 0 := by
  have hm := hflat.1
  have hmass : (∑ i, u i) = 0 := by
    simpa [centeredMoment] using hm
  unfold localizedFiniteFunction
  simp_rw [localizedMode_zero]
  rw [← Finset.sum_mul]
  simp [hmass]

/-- Moment one kills the first derivative at the left endpoint. -/
theorem localizedFiniteFirstJet_zero_of_boundaryFlat
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients N u) :
    localizedFiniteFirstJet L N u 0 = 0 := by
  have hm := hflat.2.1
  unfold localizedFiniteFirstJet localizedFrequency
  simp_rw [localizedMode_zero]
  calc
    (∑ i,
      u i * (localizedBaseFrequency L * (centeredIndex N i : ℂ)) *
        ((1 / Real.sqrt L : ℝ) : ℂ)) =
      (localizedBaseFrequency L * ((1 / Real.sqrt L : ℝ) : ℂ)) *
        centeredMoment N 1 u := by
          unfold centeredMoment
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = 0 := by rw [hm, mul_zero]

/-- Moment two kills the second derivative at the left endpoint. -/
theorem localizedFiniteSecondJet_zero_of_boundaryFlat
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients N u) :
    localizedFiniteSecondJet L N u 0 = 0 := by
  have hm := hflat.2.2
  unfold localizedFiniteSecondJet localizedFrequency
  simp_rw [localizedMode_zero]
  calc
    (∑ i,
      u i * (localizedBaseFrequency L * (centeredIndex N i : ℂ)) ^ 2 *
        ((1 / Real.sqrt L : ℝ) : ℂ)) =
      (localizedBaseFrequency L ^ 2 * ((1 / Real.sqrt L : ℝ) : ℂ)) *
        centeredMoment N 2 u := by
          unfold centeredMoment
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = 0 := by rw [hm, mul_zero]

/-- Boundary-flat coefficients kill the right-endpoint value by periodicity. -/
theorem localizedFiniteFunction_rightEndpoint_zero_of_boundaryFlat
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients N u) :
    localizedFiniteFunction L N u L = 0 := by
  calc
    localizedFiniteFunction L N u L =
        localizedFiniteFunction L N u (0 + L) := by ring_nf
    _ = localizedFiniteFunction L N u 0 :=
      localizedFiniteFunction_add_period L N u 0 hL.ne'
    _ = 0 := localizedFiniteFunction_zero_of_boundaryFlat L N u hflat

/-- Boundary-flat coefficients kill the right-endpoint first derivative. -/
theorem localizedFiniteFirstJet_rightEndpoint_zero_of_boundaryFlat
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients N u) :
    localizedFiniteFirstJet L N u L = 0 := by
  calc
    localizedFiniteFirstJet L N u L =
        localizedFiniteFirstJet L N u (0 + L) := by ring_nf
    _ = localizedFiniteFirstJet L N u 0 :=
      localizedFiniteFirstJet_add_period L N u 0 hL.ne'
    _ = 0 := localizedFiniteFirstJet_zero_of_boundaryFlat L N u hflat

/-- Boundary-flat coefficients kill the right-endpoint second derivative. -/
theorem localizedFiniteSecondJet_rightEndpoint_zero_of_boundaryFlat
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients N u) :
    localizedFiniteSecondJet L N u L = 0 := by
  calc
    localizedFiniteSecondJet L N u L =
        localizedFiniteSecondJet L N u (0 + L) := by ring_nf
    _ = localizedFiniteSecondJet L N u 0 :=
      localizedFiniteSecondJet_add_period L N u 0 hL.ne'
    _ = 0 := localizedFiniteSecondJet_zero_of_boundaryFlat L N u hflat

/-- First-order hard-window gluing.

If `f` and its derivative witness `f₁` both vanish at the endpoints,
the derivative of the hard zero extension is the hard zero extension of
`f₁`. -/
theorem hasDerivAt_indicator_Icc_of_endpoint_jets_zero
    {f f₁ : ℝ → ℂ} {L x : ℝ}
    (hL : 0 < L)
    (hf : ∀ y, HasDerivAt f (f₁ y) y)
    (hf0 : f 0 = 0) (hfL : f L = 0)
    (hf10 : f₁ 0 = 0) (hf1L : f₁ L = 0) :
    HasDerivAt
      ((Icc (0 : ℝ) L).indicator f)
      ((Icc (0 : ℝ) L).indicator f₁ x) x := by
  by_cases hxlt0 : x < 0
  · have hxmem : x ∉ Icc (0 : ℝ) L := by
      intro hx
      exact (not_lt_of_ge hx.1) hxlt0
    rw [Set.indicator_of_notMem hxmem]
    refine (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hxlt0] with y hy
    have hymem : y ∉ Icc (0 : ℝ) L := by
      intro h
      exact (not_lt_of_ge h.1) hy
    exact Set.indicator_of_notMem hymem f
  · have hx0 : 0 ≤ x := le_of_not_gt hxlt0
    by_cases hxgtL : L < x
    · have hxmem : x ∉ Icc (0 : ℝ) L := by
        intro hx
        exact (not_lt_of_ge hx.2) hxgtL
      rw [Set.indicator_of_notMem hxmem]
      refine (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hxgtL] with y hy
      have hymem : y ∉ Icc (0 : ℝ) L := by
        intro h
        exact (not_lt_of_ge h.2) hy
      exact Set.indicator_of_notMem hymem f
    · have hxL : x ≤ L := le_of_not_gt hxgtL
      by_cases hxzero : x = 0
      · subst x
        have hleft :
            HasDerivWithinAt
              ((Icc (0 : ℝ) L).indicator f) 0 (Iic (0 : ℝ)) 0 := by
          refine (hasDerivWithinAt_const (x := (0 : ℝ)) (s := Iic (0 : ℝ))
            (c := (0 : ℂ))).congr ?_ ?_
          · intro y hy
            by_cases hyzero : y = 0
            · subst y
              simpa [Set.indicator_apply, hf0, hL.le]
            · have hylt : y < 0 := lt_of_le_of_ne hy hyzero
              have hymem : y ∉ Icc (0 : ℝ) L := by
                intro h
                exact (not_lt_of_ge h.1) hylt
              exact Set.indicator_of_notMem hymem f
          · simpa [Set.indicator_apply, hf0, hL.le]
        have hright :
            HasDerivWithinAt
              ((Icc (0 : ℝ) L).indicator f) 0 (Icc (0 : ℝ) L) 0 := by
          have h := (hf 0).hasDerivWithinAt (s := Icc (0 : ℝ) L)
          rw [hf10] at h
          refine h.congr ?_ ?_
          · intro y hy
            exact Set.indicator_of_mem hy f
          · simpa [Set.indicator_apply, hf0, hL.le]
        have hu := hleft.union hright
        rw [Iic_union_Icc_eq_Iic hL.le] at hu
        have hat := hu.hasDerivAt (Iic_mem_nhds hL)
        simpa [Set.indicator_apply, hf10, hL.le] using hat
      · by_cases hxright : x = L
        · subst x
          have hleft :
              HasDerivWithinAt
                ((Icc (0 : ℝ) L).indicator f) 0 (Icc (0 : ℝ) L) L := by
            have h := (hf L).hasDerivWithinAt (s := Icc (0 : ℝ) L)
            rw [hf1L] at h
            refine h.congr ?_ ?_
            · intro y hy
              exact Set.indicator_of_mem hy f
            · simpa [Set.indicator_apply, hfL, hL.le]
          have hright :
              HasDerivWithinAt
                ((Icc (0 : ℝ) L).indicator f) 0 (Ici L) L := by
            refine (hasDerivWithinAt_const (x := L) (s := Ici L)
              (c := (0 : ℂ))).congr ?_ ?_
            · intro y hy
              by_cases hyeq : y = L
              · subst y
                simpa [Set.indicator_apply, hfL, hL.le]
              · have hygt : L < y := lt_of_le_of_ne hy (Ne.symm hyeq)
                have hymem : y ∉ Icc (0 : ℝ) L := by
                  intro h
                  exact (not_lt_of_ge h.2) hygt
                exact Set.indicator_of_notMem hymem f
            · simpa [Set.indicator_apply, hfL, hL.le]
          have hu := hleft.union hright
          rw [Icc_union_Ici_eq_Ici hL.le] at hu
          have hat := hu.hasDerivAt (Ici_mem_nhds hL)
          simpa [Set.indicator_apply, hf1L, hL.le] using hat
        · have hx0pos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
          have hxLlt : x < L := lt_of_le_of_ne hxL hxright
          have hxmem : x ∈ Icc (0 : ℝ) L := ⟨hx0pos.le, hxLlt.le⟩
          have heq :
              ((Icc (0 : ℝ) L).indicator f) =ᶠ[𝓝 x] f := by
            filter_upwards [Ioo_mem_nhds hx0pos hxLlt] with y hy
            exact Set.indicator_of_mem ⟨hy.1.le, hy.2.le⟩ f
          have h' := (hf x).congr_of_eventuallyEq heq
          simpa [Set.indicator_apply, hxmem] using h'

/-- Continuous hard zero extension of a continuous function vanishing at both
endpoints. -/
theorem continuous_indicator_Icc_of_endpoint_zero
    {f : ℝ → ℂ} {L : ℝ}
    (hL : 0 < L)
    (hf : Continuous f)
    (hf0 : f 0 = 0) (hfL : f L = 0) :
    Continuous ((Icc (0 : ℝ) L).indicator f) := by
  classical
  have hboundary :
      ∀ x ∈ frontier (Icc (0 : ℝ) L), f x = (0 : ℝ → ℂ) x := by
    intro x hx
    rw [frontier_Icc hL.le] at hx
    rcases hx with rfl | rfl <;> simp [hf0, hfL]
  have hpiece :
      Continuous (Set.piecewise (Icc (0 : ℝ) L) f (0 : ℝ → ℂ)) :=
    hf.piecewise hboundary continuous_const
  simpa only [Set.piecewise_eq_indicator] using hpiece

/-- Second-order hard-window gluing from explicit derivative witnesses. -/
theorem contDiff_two_indicator_Icc_of_endpoint_jets_zero
    {f f₁ f₂ : ℝ → ℂ} {L : ℝ}
    (hL : 0 < L)
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : Continuous f₂)
    (hf0 : f 0 = 0) (hfL : f L = 0)
    (hf10 : f₁ 0 = 0) (hf1L : f₁ L = 0)
    (hf20 : f₂ 0 = 0) (hf2L : f₂ L = 0) :
    ContDiff ℝ 2 ((Icc (0 : ℝ) L).indicator f) := by
  let F : ℝ → ℂ := (Icc (0 : ℝ) L).indicator f
  let F₁ : ℝ → ℂ := (Icc (0 : ℝ) L).indicator f₁
  let F₂ : ℝ → ℂ := (Icc (0 : ℝ) L).indicator f₂
  have hF (x : ℝ) : HasDerivAt F (F₁ x) x := by
    simpa [F, F₁] using
      hasDerivAt_indicator_Icc_of_endpoint_jets_zero
        hL hf hf0 hfL hf10 hf1L (x := x)
  have hF₁ (x : ℝ) : HasDerivAt F₁ (F₂ x) x := by
    simpa [F₁, F₂] using
      hasDerivAt_indicator_Icc_of_endpoint_jets_zero
        hL hf₁ hf10 hf1L hf20 hf2L (x := x)
  have hF₂ : Continuous F₂ := by
    simpa [F₂] using
      continuous_indicator_Icc_of_endpoint_zero hL hf₂ hf20 hf2L
  have hderivF : deriv F = F₁ := deriv_eq hF
  have hderivF₁ : deriv F₁ = F₂ := deriv_eq hF₁
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hF x).differentiableAt, ?_, ?_⟩
  · intro h
    norm_num at h
  · rw [hderivF, contDiff_one_iff_deriv]
    refine ⟨fun x => (hF₁ x).differentiableAt, ?_⟩
    rw [hderivF₁]
    exact hF₂

/-- **F0-B1A legality endpoint.**

Boundary-flat finite coefficients make the repository hard zero extension a
global compactly supported `C²` test, exactly the regularity needed by PR #83. -/
theorem contDiff_localizedFiniteVector_of_boundaryFlat
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L)
    (hflat : BoundaryFlatCoefficients N u) :
    ContDiff ℝ 2 (localizedFiniteVector L N u) := by
  rw [localizedFiniteVector_eq_indicator]
  exact contDiff_two_indicator_Icc_of_endpoint_jets_zero
    hL
    (hasDerivAt_localizedFiniteFunction L N u)
    (hasDerivAt_localizedFiniteFirstJet L N u)
    (continuous_localizedFiniteSecondJet L N u)
    (localizedFiniteFunction_zero_of_boundaryFlat L N u hflat)
    (localizedFiniteFunction_rightEndpoint_zero_of_boundaryFlat hL N u hflat)
    (localizedFiniteFirstJet_zero_of_boundaryFlat L N u hflat)
    (localizedFiniteFirstJet_rightEndpoint_zero_of_boundaryFlat hL N u hflat)
    (localizedFiniteSecondJet_zero_of_boundaryFlat L N u hflat)
    (localizedFiniteSecondJet_rightEndpoint_zero_of_boundaryFlat hL N u hflat)

/-- Explicit five-mode coefficients of `(1-cos θ)^2` on centered indices
`-2,-1,0,1,2`.  This witnesses that the boundary-flat sector is nontrivial. -/
def boundaryKillerCoefficients : Fin 5 → ℂ :=
  ![(1 / 4 : ℂ), -1, (3 / 2 : ℂ), -1, (1 / 4 : ℂ)]

/-- The explicit five-mode boundary killer satisfies moments 0, 1 and 2. -/
theorem boundaryKillerCoefficients_boundaryFlat :
    BoundaryFlatCoefficients 2 boundaryKillerCoefficients := by
  norm_num [BoundaryFlatCoefficients, centeredMoment,
    boundaryKillerCoefficients, centeredIndex, Fin.sum_univ_succ]

/-- The boundary-flat sector is not the zero sector. -/
theorem boundaryKillerCoefficients_ne_zero :
    boundaryKillerCoefficients ≠ 0 := by
  intro h
  have h0 := congr_fun h (0 : Fin 5)
  norm_num [boundaryKillerCoefficients] at h0

end Zeta23.CCM

#print axioms Zeta23.CCM.contDiff_localizedFiniteVector_of_boundaryFlat
#print axioms Zeta23.CCM.boundaryKillerCoefficients_boundaryFlat
