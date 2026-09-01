import Zeta23.CCM.BoundaryFlatProjection
import Zeta23.CCM.LocalizedFourierApproximation

noncomputable section

namespace Zeta23.CCM

open Complex Function MeasureTheory Real Set
open scoped BigOperators

/-!
# F0-B1C-B: quantitative boundary-flat finite approximation

PR #91 produces raw centered finite Fourier formulas with uniform control of
value, first jet and second jet on one fixed positive aperture.

PR #88 provides an exact three-mode projection onto the boundary-flat sector.

This module proves that the projection is quantitatively harmless in exactly
the topology consumed by WCONT-A.  The proof deliberately uses the exact
endpoint scale factors from the already-proved moment/jet identities rather
than first normalizing them to optimized closed-form constants.  All constants
depend only on the fixed aperture `L`, never on the Fourier bandwidth `N`.

The complete projected hard-window vector is the legal object.  The correction
alone is never promoted to a globally C² Weil test.

No Weil-sign transfer, finite negativity, F1, or RH is proved here.
-/

/-- Formula-level finite Fourier combinations are additive in their
coefficient vector. -/
theorem localizedFiniteFunction_add_coefficients
    (L : ℝ) (N : ℕ)
    (u v : Fin (2 * N + 1) → ℂ)
    (x : ℝ) :
    localizedFiniteFunction L N (fun i => u i + v i) x =
      localizedFiniteFunction L N u x +
        localizedFiniteFunction L N v x := by
  unfold localizedFiniteFunction
  simp_rw [add_mul]
  exact Finset.sum_add_distrib

/-- Formula-level second jets are additive in their coefficient vector. -/
theorem localizedFiniteSecondJet_add_coefficients
    (L : ℝ) (N : ℕ)
    (u v : Fin (2 * N + 1) → ℂ)
    (x : ℝ) :
    localizedFiniteSecondJet L N (fun i => u i + v i) x =
      localizedFiniteSecondJet L N u x +
        localizedFiniteSecondJet L N v x := by
  unfold localizedFiniteSecondJet
  simp_rw [add_mul]
  exact Finset.sum_add_distrib

/-- A single coefficient contributes exactly one localized Fourier mode. -/
theorem localizedFiniteFunction_coefficientSingle
    {L : ℝ} {N : ℕ}
    (j : Fin (2 * N + 1)) (z : ℂ) (x : ℝ) :
    localizedFiniteFunction L N (coefficientSingle j z) x =
      z * localizedMode L (centeredIndex N j) x := by
  classical
  unfold localizedFiniteFunction coefficientSingle
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    simp [hbj]
  · simp

/-- A single coefficient contributes exactly one formula-level second-jet
mode. -/
theorem localizedFiniteSecondJet_coefficientSingle
    {L : ℝ} {N : ℕ}
    (j : Fin (2 * N + 1)) (z : ℂ) (x : ℝ) :
    localizedFiniteSecondJet L N (coefficientSingle j z) x =
      z * localizedFrequency L (centeredIndex N j) ^ 2 *
        localizedMode L (centeredIndex N j) x := by
  classical
  unfold localizedFiniteSecondJet coefficientSingle
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    simp [hbj]
  · simp

/-- The exact projector is raw formula plus its three-mode correction. -/
theorem localizedFiniteFunction_boundaryFlatProject
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ)
    (x : ℝ) :
    localizedFiniteFunction L N (boundaryFlatProject N hN u) x =
      localizedFiniteFunction L N u x +
        localizedFiniteFunction L N
          (boundaryFlatCorrection N hN u) x := by
  change
    localizedFiniteFunction L N
        (fun i => u i + boundaryFlatCorrection N hN u i) x =
      localizedFiniteFunction L N u x +
        localizedFiniteFunction L N
          (boundaryFlatCorrection N hN u) x
  exact localizedFiniteFunction_add_coefficients
    L N u (boundaryFlatCorrection N hN u) x

/-- The exact projector is raw second jet plus the correction second jet. -/
theorem localizedFiniteSecondJet_boundaryFlatProject
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ)
    (x : ℝ) :
    localizedFiniteSecondJet L N (boundaryFlatProject N hN u) x =
      localizedFiniteSecondJet L N u x +
        localizedFiniteSecondJet L N
          (boundaryFlatCorrection N hN u) x := by
  change
    localizedFiniteSecondJet L N
        (fun i => u i + boundaryFlatCorrection N hN u i) x =
      localizedFiniteSecondJet L N u x +
        localizedFiniteSecondJet L N
          (boundaryFlatCorrection N hN u) x
  exact localizedFiniteSecondJet_add_coefficients
    L N u (boundaryFlatCorrection N hN u) x

/-- Explicit formula for the three-mode correction at function level. -/
theorem localizedFiniteFunction_boundaryFlatCorrection_eq
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) (x : ℝ) :
    localizedFiniteFunction L N
        (boundaryFlatCorrection N hN u) x =
      ((centeredMoment N 1 u - centeredMoment N 2 u) / 2) *
          localizedMode L (-1) x +
        (centeredMoment N 2 u - centeredMoment N 0 u) *
          localizedMode L 0 x +
        (-(centeredMoment N 1 u + centeredMoment N 2 u) / 2) *
          localizedMode L 1 x := by
  unfold boundaryFlatCorrection
  rw [localizedFiniteFunction_add_coefficients]
  rw [localizedFiniteFunction_add_coefficients]
  rw [localizedFiniteFunction_coefficientSingle]
  rw [localizedFiniteFunction_coefficientSingle]
  rw [localizedFiniteFunction_coefficientSingle]
  simp

/-- Explicit formula for the three-mode correction at second-jet level.  The
zero mode vanishes automatically. -/
theorem localizedFiniteSecondJet_boundaryFlatCorrection_eq
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) (x : ℝ) :
    localizedFiniteSecondJet L N
        (boundaryFlatCorrection N hN u) x =
      ((centeredMoment N 1 u - centeredMoment N 2 u) / 2) *
          localizedFrequency L (-1) ^ 2 *
          localizedMode L (-1) x +
        (-(centeredMoment N 1 u + centeredMoment N 2 u) / 2) *
          localizedFrequency L 1 ^ 2 *
          localizedMode L 1 x := by
  unfold boundaryFlatCorrection
  rw [localizedFiniteSecondJet_add_coefficients]
  rw [localizedFiniteSecondJet_add_coefficients]
  rw [localizedFiniteSecondJet_coefficientSingle]
  rw [localizedFiniteSecondJet_coefficientSingle]
  rw [localizedFiniteSecondJet_coefficientSingle]
  simp [localizedFrequency]

/-- Every normalized localized mode has constant modulus on a positive
aperture. -/
@[simp] theorem norm_localizedMode_of_pos
    {L : ℝ} (hL : 0 < L)
    (n : ℤ) (x : ℝ) :
    ‖localizedMode L n x‖ = 1 / Real.sqrt L := by
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  unfold localizedMode
  rw [norm_mul, Complex.norm_exp]
  simp [hsqrt.ne', abs_of_pos (one_div_pos.mpr hsqrt)]

/-- The base Fourier frequency is nonzero on a positive aperture. -/
theorem localizedBaseFrequency_ne_zero
    {L : ℝ} (hL : 0 < L) :
    localizedBaseFrequency L ≠ 0 := by
  simpa [localizedFrequency] using
    (localizedFrequency_ne_zero hL (n := (1 : ℤ)) (by norm_num))

/-- The scalar multiplying moment one in the exact endpoint first-jet identity
has strictly positive norm. -/
theorem firstMomentEndpointScale_pos
    {L : ℝ} (hL : 0 < L) :
    0 <
      ‖localizedBaseFrequency L *
        (((1 / Real.sqrt L : ℝ) : ℂ))‖ := by
  have hsqrt : Real.sqrt L ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hL)
  have hscale :
      (((1 / Real.sqrt L : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (one_div_ne_zero hsqrt)
  exact norm_pos_iff.mpr
    (mul_ne_zero (localizedBaseFrequency_ne_zero hL) hscale)

/-- The scalar multiplying moment two in the exact endpoint second-jet
identity has strictly positive norm. -/
theorem secondMomentEndpointScale_pos
    {L : ℝ} (hL : 0 < L) :
    0 <
      ‖localizedBaseFrequency L ^ 2 *
        (((1 / Real.sqrt L : ℝ) : ℂ))‖ := by
  have hsqrt : Real.sqrt L ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hL)
  have hscale :
      (((1 / Real.sqrt L : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (one_div_ne_zero hsqrt)
  exact norm_pos_iff.mpr
    (mul_ne_zero
      (pow_ne_zero 2 (localizedBaseFrequency_ne_zero hL))
      hscale)

/-- The exact anchor `q(0)=0` kills centered moment zero. -/
theorem centeredMoment_zero_eq_zero_of_localizedFiniteFunction_zero
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    (hq0 : localizedFiniteFunction L N u 0 = 0) :
    centeredMoment N 0 u = 0 := by
  rw [localizedFiniteFunction_zero_eq_centeredMoment_zero] at hq0
  have hsqrt : Real.sqrt L ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hL)
  have hscale :
      (((1 / Real.sqrt L : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (one_div_ne_zero hsqrt)
  exact (mul_eq_zero.mp hq0).resolve_left hscale

/-- Small endpoint first jet implies a small first centered moment when measured
against the exact nonzero endpoint scale. -/
theorem norm_centeredMoment_one_lt_of_endpoint_firstJet_lt
    {L δ : ℝ} (hL : 0 < L)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    (hjet :
      ‖localizedFiniteFirstJet L N u 0‖ <
        δ *
          ‖localizedBaseFrequency L *
            (((1 / Real.sqrt L : ℝ) : ℂ))‖) :
    ‖centeredMoment N 1 u‖ < δ := by
  have hscale := firstMomentEndpointScale_pos hL
  have heq :=
    congrArg norm
      (localizedFiniteFirstJet_zero_eq_centeredMoment_one L N u)
  rw [norm_mul] at heq
  rw [heq] at hjet
  nlinarith [norm_nonneg (centeredMoment N 1 u)]

/-- Small endpoint second jet implies a small second centered moment when
measured against the exact nonzero endpoint scale. -/
theorem norm_centeredMoment_two_lt_of_endpoint_secondJet_lt
    {L δ : ℝ} (hL : 0 < L)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    (hjet :
      ‖localizedFiniteSecondJet L N u 0‖ <
        δ *
          ‖localizedBaseFrequency L ^ 2 *
            (((1 / Real.sqrt L : ℝ) : ℂ))‖) :
    ‖centeredMoment N 2 u‖ < δ := by
  have hscale := secondMomentEndpointScale_pos hL
  have heq :=
    congrArg norm
      (localizedFiniteSecondJet_zero_eq_centeredMoment_two L N u)
  rw [norm_mul] at heq
  rw [heq] at hjet
  nlinarith [norm_nonneg (centeredMoment N 2 u)]

/-- Norm algebra for the full three-mode correction when moment zero is
already zero. -/
theorem boundaryFlatCorrection_three_mode_norm_le
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ)
    (hm0 : centeredMoment N 0 u = 0) :
    ‖boundaryFlatCorrection N hN u
        (boundaryFlatNegOneIndex N hN)‖ +
      ‖boundaryFlatCorrection N hN u
        (boundaryFlatZeroIndex N)‖ +
      ‖boundaryFlatCorrection N hN u
        (boundaryFlatOneIndex N hN)‖
    ≤
      ‖centeredMoment N 1 u‖ +
        2 * ‖centeredMoment N 2 u‖ := by
  rw [
    boundaryFlatCorrection_apply_negOne,
    boundaryFlatCorrection_apply_zero,
    boundaryFlatCorrection_apply_one,
    hm0
  ]
  simp only [sub_zero, norm_neg, norm_div]
  norm_num
  nlinarith [
    norm_sub_le (centeredMoment N 1 u) (centeredMoment N 2 u),
    norm_add_le (centeredMoment N 1 u) (centeredMoment N 2 u),
    norm_nonneg (centeredMoment N 1 u),
    norm_nonneg (centeredMoment N 2 u)
  ]

/-- Norm algebra for the two nonzero-frequency correction coefficients. -/
theorem boundaryFlatCorrection_nonzeroModes_norm_le
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    ‖boundaryFlatCorrection N hN u
        (boundaryFlatNegOneIndex N hN)‖ +
      ‖boundaryFlatCorrection N hN u
        (boundaryFlatOneIndex N hN)‖
    ≤
      ‖centeredMoment N 1 u‖ +
        ‖centeredMoment N 2 u‖ := by
  rw [
    boundaryFlatCorrection_apply_negOne,
    boundaryFlatCorrection_apply_one
  ]
  simp only [norm_neg, norm_div]
  norm_num
  nlinarith [
    norm_sub_le (centeredMoment N 1 u) (centeredMoment N 2 u),
    norm_add_le (centeredMoment N 1 u) (centeredMoment N 2 u),
    norm_nonneg (centeredMoment N 1 u),
    norm_nonneg (centeredMoment N 2 u)
  ]

/-- Pointwise function-level correction bound.  The constant is fixed by the
aperture and does not depend on `N`. -/
theorem norm_localizedFiniteFunction_boundaryFlatCorrection_le
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ)
    (hm0 : centeredMoment N 0 u = 0)
    (x : ℝ) :
    ‖localizedFiniteFunction L N
        (boundaryFlatCorrection N hN u) x‖
      ≤
      (1 / Real.sqrt L) *
        (‖centeredMoment N 1 u‖ +
          2 * ‖centeredMoment N 2 u‖) := by
  rw [localizedFiniteFunction_boundaryFlatCorrection_eq]
  rw [hm0, sub_zero]
  have hcoeff :=
    boundaryFlatCorrection_three_mode_norm_le N hN u hm0
  have hsqrt : 0 ≤ 1 / Real.sqrt L := by
    positivity
  calc
    ‖((centeredMoment N 1 u - centeredMoment N 2 u) / 2) *
          localizedMode L (-1) x +
        centeredMoment N 2 u * localizedMode L 0 x +
        (-(centeredMoment N 1 u + centeredMoment N 2 u) / 2) *
          localizedMode L 1 x‖
        ≤
      ‖((centeredMoment N 1 u - centeredMoment N 2 u) / 2) *
          localizedMode L (-1) x‖ +
        ‖centeredMoment N 2 u * localizedMode L 0 x‖ +
        ‖(-(centeredMoment N 1 u + centeredMoment N 2 u) / 2) *
          localizedMode L 1 x‖ := by
            calc
              _ ≤
                ‖((centeredMoment N 1 u - centeredMoment N 2 u) / 2) *
                    localizedMode L (-1) x +
                  centeredMoment N 2 u * localizedMode L 0 x‖ +
                  ‖(-(centeredMoment N 1 u + centeredMoment N 2 u) / 2) *
                    localizedMode L 1 x‖ := norm_add_le _ _
              _ ≤
                (‖((centeredMoment N 1 u - centeredMoment N 2 u) / 2) *
                    localizedMode L (-1) x‖ +
                  ‖centeredMoment N 2 u * localizedMode L 0 x‖) +
                  ‖(-(centeredMoment N 1 u + centeredMoment N 2 u) / 2) *
                    localizedMode L 1 x‖ := by
                      gcongr
                      exact norm_add_le _ _
    _ =
      (1 / Real.sqrt L) *
        (‖boundaryFlatCorrection N hN u
            (boundaryFlatNegOneIndex N hN)‖ +
          ‖boundaryFlatCorrection N hN u
            (boundaryFlatZeroIndex N)‖ +
          ‖boundaryFlatCorrection N hN u
            (boundaryFlatOneIndex N hN)‖) := by
          rw [
            boundaryFlatCorrection_apply_negOne,
            boundaryFlatCorrection_apply_zero,
            boundaryFlatCorrection_apply_one,
            hm0
          ]
          simp only [sub_zero, norm_mul, norm_localizedMode_of_pos hL]
          ring
    _ ≤
      (1 / Real.sqrt L) *
        (‖centeredMoment N 1 u‖ +
          2 * ‖centeredMoment N 2 u‖) :=
      mul_le_mul_of_nonneg_left hcoeff hsqrt

/-- Pointwise second-jet correction bound.  Only the ±1 reserved modes
contribute after two derivatives. -/
theorem norm_localizedFiniteSecondJet_boundaryFlatCorrection_le
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ)
    (x : ℝ) :
    ‖localizedFiniteSecondJet L N
        (boundaryFlatCorrection N hN u) x‖
      ≤
      (1 / Real.sqrt L) *
        ‖localizedBaseFrequency L‖ ^ 2 *
        (‖centeredMoment N 1 u‖ +
          ‖centeredMoment N 2 u‖) := by
  rw [localizedFiniteSecondJet_boundaryFlatCorrection_eq]
  have hcoeff :=
    boundaryFlatCorrection_nonzeroModes_norm_le N hN u
  have hsqrt : 0 ≤ 1 / Real.sqrt L := by
    positivity
  have hfreq : 0 ≤ ‖localizedBaseFrequency L‖ ^ 2 := sq_nonneg _
  calc
    ‖((centeredMoment N 1 u - centeredMoment N 2 u) / 2) *
          localizedFrequency L (-1) ^ 2 *
          localizedMode L (-1) x +
        (-(centeredMoment N 1 u + centeredMoment N 2 u) / 2) *
          localizedFrequency L 1 ^ 2 *
          localizedMode L 1 x‖
        ≤
      ‖((centeredMoment N 1 u - centeredMoment N 2 u) / 2) *
          localizedFrequency L (-1) ^ 2 *
          localizedMode L (-1) x‖ +
        ‖(-(centeredMoment N 1 u + centeredMoment N 2 u) / 2) *
          localizedFrequency L 1 ^ 2 *
          localizedMode L 1 x‖ := norm_add_le _ _
    _ =
      (1 / Real.sqrt L) *
        ‖localizedBaseFrequency L‖ ^ 2 *
        (‖boundaryFlatCorrection N hN u
            (boundaryFlatNegOneIndex N hN)‖ +
          ‖boundaryFlatCorrection N hN u
            (boundaryFlatOneIndex N hN)‖) := by
          rw [
            boundaryFlatCorrection_apply_negOne,
            boundaryFlatCorrection_apply_one
          ]
          simp only [norm_mul, norm_pow, norm_localizedMode_of_pos hL]
          simp [localizedFrequency]
          ring
    _ ≤
      (1 / Real.sqrt L) *
        ‖localizedBaseFrequency L‖ ^ 2 *
        (‖centeredMoment N 1 u‖ +
          ‖centeredMoment N 2 u‖) := by
          gcongr

/-- The global derivative of a legal boundary-flat hard-window vector is
exactly the hard zero extension of the formula-level first jet. -/
theorem deriv_localizedFiniteVector_eq_indicator_firstJet
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L)
    (hflat : BoundaryFlatCoefficients N u) :
    deriv (localizedFiniteVector L N u) =
      (Icc (0 : ℝ) L).indicator
        (localizedFiniteFirstJet L N u) := by
  rw [localizedFiniteVector_eq_indicator]
  apply deriv_eq
  intro x
  exact
    hasDerivAt_indicator_Icc_of_endpoint_jets_zero
      hL
      (hasDerivAt_localizedFiniteFunction L N u)
      (localizedFiniteFunction_zero_of_boundaryFlat L N u hflat)
      (localizedFiniteFunction_rightEndpoint_zero_of_boundaryFlat
        hL N u hflat)
      (localizedFiniteFirstJet_zero_of_boundaryFlat L N u hflat)
      (localizedFiniteFirstJet_rightEndpoint_zero_of_boundaryFlat
        hL N u hflat)

/-- The global second derivative of a legal boundary-flat hard-window vector
is exactly the hard zero extension of the formula-level second jet. -/
theorem deriv_deriv_localizedFiniteVector_eq_indicator_secondJet
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L)
    (hflat : BoundaryFlatCoefficients N u) :
    deriv (deriv (localizedFiniteVector L N u)) =
      (Icc (0 : ℝ) L).indicator
        (localizedFiniteSecondJet L N u) := by
  rw [deriv_localizedFiniteVector_eq_indicator_firstJet N u hL hflat]
  apply deriv_eq
  intro x
  exact
    hasDerivAt_indicator_Icc_of_endpoint_jets_zero
      hL
      (hasDerivAt_localizedFiniteFirstJet L N u)
      (localizedFiniteFirstJet_zero_of_boundaryFlat L N u hflat)
      (localizedFiniteFirstJet_rightEndpoint_zero_of_boundaryFlat
        hL N u hflat)
      (localizedFiniteSecondJet_zero_of_boundaryFlat L N u hflat)
      (localizedFiniteSecondJet_rightEndpoint_zero_of_boundaryFlat
        hL N u hflat)

/-- For two global C² functions, second derivatives distribute over
subtraction pointwise. -/
theorem deriv_deriv_sub_of_contDiff_two
    {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) :
    deriv (deriv (f - g)) =
      deriv (deriv f) - deriv (deriv g) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfirst : deriv (f - g) = deriv f - deriv g := by
    funext x
    exact deriv_sub (hfd x) (hgd x)
  rw [hfirst]
  have hf1 : ContDiff ℝ 1 (deriv f) := by
    simpa using hf.deriv'
  have hg1 : ContDiff ℝ 1 (deriv g) := by
    simpa using hg.deriv'
  funext x
  exact
    deriv_sub
      ((hf1.differentiable (by norm_num)) x)
      ((hg1.differentiable (by norm_num)) x)

/-- A continuous function supported in `[0,L]` and uniformly bounded there
has the expected elementary L¹ bound. -/
theorem integral_norm_le_length_mul_of_support_Icc
    {L B : ℝ} (hL : 0 ≤ L)
    {f : ℝ → ℂ}
    (hf : Continuous f)
    (hsupp : Function.support f ⊆ Icc (0 : ℝ) L)
    (hbound : ∀ x ∈ Icc (0 : ℝ) L, ‖f x‖ ≤ B) :
    (∫ x, ‖f x‖) ≤ L * B := by
  have hnorm : Continuous (fun x : ℝ => ‖f x‖) := hf.norm
  have heq :
      (fun x : ℝ => ‖f x‖) =
        (Icc (0 : ℝ) L).indicator (fun x : ℝ => ‖f x‖) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) L
    · simp [hx]
    · have hfx : f x = 0 := by
        by_contra hne
        exact hx (hsupp hne)
      simp [hx, hfx]
  rw [heq, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]
  calc
    (∫ x in (0 : ℝ)..L, ‖f x‖)
        ≤ ∫ x in (0 : ℝ)..L, B :=
      intervalIntegral.integral_mono_on
        hL
        (hnorm.intervalIntegrable 0 L)
        intervalIntegrable_const
        hbound
    _ = L * B := by
      rw [intervalIntegral.integral_const]
      simp

/-- **F0-B1C-B production endpoint.**

Every strict-collar C² target on one fixed positive aperture admits a legal
boundary-flat finite hard-window approximation in exactly the
`L¹ + second-derivative L¹` topology consumed by WCONT-A. -/
theorem exists_boundaryFlatFinite_WCONT_approx
    {L : ℝ} (hL : 0 < L)
    {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h)
    (hs : tsupport h ⊆ Ioo 0 L)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∃ u : Fin (2 * N + 1) → ℂ,
        BoundaryFlatCoefficients N u ∧
        (∫ x,
          ‖(localizedFiniteVector L N u - h) x‖) < η ∧
        (∫ x,
          ‖deriv
              (deriv
                (localizedFiniteVector L N u - h)) x‖) < η := by
  let s : ℝ := 1 / Real.sqrt L
  let b : ℝ := ‖localizedBaseFrequency L‖
  let a1 : ℝ :=
    ‖localizedBaseFrequency L *
      (((1 / Real.sqrt L : ℝ) : ℂ))‖
  let a2 : ℝ :=
    ‖localizedBaseFrequency L ^ 2 *
      (((1 / Real.sqrt L : ℝ) : ℂ))‖
  let A0 : ℝ := 1 + 3 * s
  let A2 : ℝ := 1 + 2 * s * b ^ 2
  let C : ℝ := 1 + L * A0 + L * A2
  let δ : ℝ := η / C
  let ε : ℝ := min δ (min (δ * a1) (δ * a2))

  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have hbpos : 0 < b := by
    dsimp [b]
    exact norm_pos_iff.mpr (localizedBaseFrequency_ne_zero hL)
  have ha1pos : 0 < a1 := by
    dsimp [a1]
    exact firstMomentEndpointScale_pos hL
  have ha2pos : 0 < a2 := by
    dsimp [a2]
    exact secondMomentEndpointScale_pos hL
  have hA0pos : 0 < A0 := by
    dsimp [A0]
    positivity
  have hA2pos : 0 < A2 := by
    dsimp [A2]
    positivity
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos hη hCpos
  have hεpos : 0 < ε := by
    dsimp [ε]
    apply lt_min
    · exact hδpos
    · apply lt_min
      · positivity
      · positivity
  have hεδ : ε ≤ δ := by
    dsimp [ε]
    exact min_le_left _ _
  have hεa1 : ε ≤ δ * a1 := by
    dsimp [ε]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεa2 : ε ≤ δ * a2 := by
    dsimp [ε]
    exact (min_le_right _ _).trans (min_le_right _ _)

  obtain ⟨N, hN, u, hq0, hfunc, hfirst, hsecond⟩ :=
    exists_localizedFinite_uniform_C2_approx
      hL hh hs hεpos

  let v : Fin (2 * N + 1) → ℂ :=
    boundaryFlatProject N hN u

  have hvflat : BoundaryFlatCoefficients N v := by
    simpa [v] using boundaryFlatProject_boundaryFlat N hN u

  have hm0 : centeredMoment N 0 u = 0 :=
    centeredMoment_zero_eq_zero_of_localizedFiniteFunction_zero
      hL N u hq0

  have hj := strictSupport_endpoint_jet_package (L := L) (h := h) hs
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hL.le⟩

  have hfirst0 : ‖localizedFiniteFirstJet L N u 0‖ < ε := by
    have h := hfirst 0 h0mem
    simpa [hj.2.2.1] using h
  have hsecond0 : ‖localizedFiniteSecondJet L N u 0‖ < ε := by
    have h := hsecond 0 h0mem
    simpa [hj.2.2.2.2.1] using h

  have hm1 : ‖centeredMoment N 1 u‖ < δ := by
    apply norm_centeredMoment_one_lt_of_endpoint_firstJet_lt hL N u
    exact lt_of_lt_of_le hfirst0 hεa1

  have hm2 : ‖centeredMoment N 2 u‖ < δ := by
    apply norm_centeredMoment_two_lt_of_endpoint_secondJet_lt hL N u
    exact lt_of_lt_of_le hsecond0 hεa2

  have hcorr0 :
      ∀ x : ℝ,
        ‖localizedFiniteFunction L N
            (boundaryFlatCorrection N hN u) x‖ <
          3 * s * δ := by
    intro x
    have hle :=
      norm_localizedFiniteFunction_boundaryFlatCorrection_le
        hL N hN u hm0 x
    dsimp [s] at *
    calc
      ‖localizedFiniteFunction L N
          (boundaryFlatCorrection N hN u) x‖
          ≤
        (1 / Real.sqrt L) *
          (‖centeredMoment N 1 u‖ +
            2 * ‖centeredMoment N 2 u‖) := hle
      _ < 3 * (1 / Real.sqrt L) * δ := by
        have hsnonneg : 0 ≤ 1 / Real.sqrt L := by positivity
        nlinarith
      _ = 3 * s * δ := by rfl

  have hcorr2 :
      ∀ x : ℝ,
        ‖localizedFiniteSecondJet L N
            (boundaryFlatCorrection N hN u) x‖ <
          2 * s * b ^ 2 * δ := by
    intro x
    have hle :=
      norm_localizedFiniteSecondJet_boundaryFlatCorrection_le
        hL N hN u x
    dsimp [s, b] at *
    calc
      ‖localizedFiniteSecondJet L N
          (boundaryFlatCorrection N hN u) x‖
          ≤
        (1 / Real.sqrt L) *
          ‖localizedBaseFrequency L‖ ^ 2 *
          (‖centeredMoment N 1 u‖ +
            ‖centeredMoment N 2 u‖) := hle
      _ <
        2 * (1 / Real.sqrt L) *
          ‖localizedBaseFrequency L‖ ^ 2 * δ := by
        have hsum :
            ‖centeredMoment N 1 u‖ + ‖centeredMoment N 2 u‖ <
              2 * δ := by
          nlinarith
        have hcoef :
            0 <
              (1 / Real.sqrt L) *
                ‖localizedBaseFrequency L‖ ^ 2 := by
          positivity
        have hmul := mul_lt_mul_of_pos_left hsum hcoef
        nlinarith
      _ = 2 * s * b ^ 2 * δ := by rfl

  have hfuncδ :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖localizedFiniteFunction L N u x - h x‖ < δ := by
    intro x hx
    exact lt_of_lt_of_le (hfunc x hx) hεδ

  have hsecondδ :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖localizedFiniteSecondJet L N u x -
            deriv (deriv h) x‖ < δ := by
    intro x hx
    exact lt_of_lt_of_le (hsecond x hx) hεδ

  have hproj0 :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖localizedFiniteFunction L N v x - h x‖ <
          A0 * δ := by
    intro x hx
    rw [show localizedFiniteFunction L N v x =
        localizedFiniteFunction L N u x +
          localizedFiniteFunction L N
            (boundaryFlatCorrection N hN u) x by
      simpa [v] using
        localizedFiniteFunction_boundaryFlatProject L N hN u x]
    calc
      ‖localizedFiniteFunction L N u x +
          localizedFiniteFunction L N
            (boundaryFlatCorrection N hN u) x - h x‖
          =
        ‖(localizedFiniteFunction L N u x - h x) +
          localizedFiniteFunction L N
            (boundaryFlatCorrection N hN u) x‖ := by
              congr 1
              ring
      _ ≤
        ‖localizedFiniteFunction L N u x - h x‖ +
          ‖localizedFiniteFunction L N
            (boundaryFlatCorrection N hN u) x‖ :=
        norm_add_le _ _
      _ < δ + 3 * s * δ :=
        add_lt_add (hfuncδ x hx) (hcorr0 x)
      _ = A0 * δ := by
        dsimp [A0]
        ring

  have hproj2 :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖localizedFiniteSecondJet L N v x -
            deriv (deriv h) x‖ <
          A2 * δ := by
    intro x hx
    rw [show localizedFiniteSecondJet L N v x =
        localizedFiniteSecondJet L N u x +
          localizedFiniteSecondJet L N
            (boundaryFlatCorrection N hN u) x by
      simpa [v] using
        localizedFiniteSecondJet_boundaryFlatProject L N hN u x]
    calc
      ‖localizedFiniteSecondJet L N u x +
          localizedFiniteSecondJet L N
            (boundaryFlatCorrection N hN u) x -
          deriv (deriv h) x‖
          =
        ‖(localizedFiniteSecondJet L N u x -
            deriv (deriv h) x) +
          localizedFiniteSecondJet L N
            (boundaryFlatCorrection N hN u) x‖ := by
              congr 1
              ring
      _ ≤
        ‖localizedFiniteSecondJet L N u x -
            deriv (deriv h) x‖ +
          ‖localizedFiniteSecondJet L N
            (boundaryFlatCorrection N hN u) x‖ :=
        norm_add_le _ _
      _ < δ + 2 * s * b ^ 2 * δ :=
        add_lt_add (hsecondδ x hx) (hcorr2 x)
      _ = A2 * δ := by
        dsimp [A2]
        ring

  let p : ℝ → ℂ := localizedFiniteVector L N v
  have hpC2 : ContDiff ℝ 2 p := by
    simpa [p] using
      contDiff_localizedFiniteVector_of_boundaryFlat N v hL hvflat
  have heC2 : ContDiff ℝ 2 (p - h) := hpC2.sub hh
  have hepCont : Continuous (p - h) := heC2.continuous

  have heSupp :
      Function.support (p - h) ⊆ Icc (0 : ℝ) L := by
    intro x hx
    by_contra hxmem
    have hp0 : p x = 0 := by
      by_contra hpx
      exact hxmem
        (localizedFiniteVector_support_subset L N v
          (by simpa [p] using hpx))
    have hh0 : h x = 0 := by
      by_contra hhx
      have hxt : x ∈ tsupport h :=
        subset_closure (by simpa [Function.mem_support] using hhx)
      have hxi := hs hxt
      exact hxmem ⟨hxi.1.le, hxi.2.le⟩
    exact hx (by simp [hp0, hh0])

  have hePoint :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖(p - h) x‖ ≤ A0 * δ := by
    intro x hx
    have hp :
        p x = localizedFiniteFunction L N v x := by
      dsimp [p]
      rw [localizedFiniteVector_eq_indicator,
        Set.indicator_of_mem hx]
    rw [Pi.sub_apply, hp]
    exact (hproj0 x hx).le

  have hInt0 :
      (∫ x, ‖(p - h) x‖) ≤ L * (A0 * δ) :=
    integral_norm_le_length_mul_of_support_Icc
      hL.le hepCont heSupp hePoint

  have hderiv2 :
      deriv (deriv (p - h)) =
        deriv (deriv p) - deriv (deriv h) :=
    deriv_deriv_sub_of_contDiff_two hpC2 hh

  have hpDeriv2 :
      deriv (deriv p) =
        (Icc (0 : ℝ) L).indicator
          (localizedFiniteSecondJet L N v) := by
    simpa [p] using
      deriv_deriv_localizedFiniteVector_eq_indicator_secondJet
        N v hL hvflat

  have he2Cont : Continuous (deriv (deriv (p - h))) := by
    have he1 : ContDiff ℝ 1 (deriv (p - h)) := by
      simpa using heC2.deriv'
    exact he1.continuous_deriv_one

  have he2Supp :
      Function.support (deriv (deriv (p - h))) ⊆
        Icc (0 : ℝ) L := by
    have hetsupp : tsupport (p - h) ⊆ Icc (0 : ℝ) L :=
      closure_minimal heSupp isClosed_Icc
    have hds :
        tsupport (deriv (p - h)) ⊆ tsupport (p - h) :=
      tsupport_deriv_subset
    have hdds :
        tsupport (deriv (deriv (p - h))) ⊆
          tsupport (deriv (p - h)) :=
      tsupport_deriv_subset
    intro x hx
    exact hetsupp (hds (hdds (subset_closure hx)))

  have he2Point :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖deriv (deriv (p - h)) x‖ ≤ A2 * δ := by
    intro x hx
    rw [hderiv2, hpDeriv2]
    simp only [Pi.sub_apply]
    rw [Set.indicator_of_mem hx]
    exact (hproj2 x hx).le

  have hInt2 :
      (∫ x, ‖deriv (deriv (p - h)) x‖) ≤
        L * (A2 * δ) :=
    integral_norm_le_length_mul_of_support_Icc
      hL.le he2Cont he2Supp he2Point

  have hCδ : C * δ = η := by
    dsimp [δ]
    field_simp [hCpos.ne']

  have h0budget : L * (A0 * δ) < η := by
    have hLA0 : L * A0 < C := by
      dsimp [C]
      nlinarith [hL, hA2pos]
    calc
      L * (A0 * δ) = (L * A0) * δ := by ring
      _ < C * δ := mul_lt_mul_of_pos_right hLA0 hδpos
      _ = η := hCδ

  have h2budget : L * (A2 * δ) < η := by
    have hLA2 : L * A2 < C := by
      dsimp [C]
      nlinarith [hL, hA0pos]
    calc
      L * (A2 * δ) = (L * A2) * δ := by ring
      _ < C * δ := mul_lt_mul_of_pos_right hLA2 hδpos
      _ = η := hCδ

  refine ⟨N, hN, v, hvflat, ?_, ?_⟩
  · simpa [p] using lt_of_le_of_lt hInt0 h0budget
  · simpa [p] using lt_of_le_of_lt hInt2 h2budget

end Zeta23.CCM

#print axioms Zeta23.CCM.centeredMoment_zero_eq_zero_of_localizedFiniteFunction_zero
#print axioms Zeta23.CCM.deriv_deriv_localizedFiniteVector_eq_indicator_secondJet
#print axioms Zeta23.CCM.exists_boundaryFlatFinite_WCONT_approx
