import Zeta23.CCM.FirstCrossingStrictEvenSourceEnergy

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#279 optimized-curvature source-remainder algebra

This module formalizes the algebraic core of the handoff equality derivation.
It deliberately separates two layers:

* a pointwise source-transport identity for the optimized curvature integrand;
* application of an arbitrary real-linear arithmetic functional.

The actual production aperture functional is not silently assumed here. A
later theorem must instantiate the linear functional with the exact
pole/archimedean/von-Mangoldt derivative functional and discharge its
convergence hypotheses.
-/

/-- Source-side integrand entering optimized curvature before source
subtraction. -/
def optimizedCurvatureSourceIntegrand
    (L t eSecond mixedDeriv : ℝ) : ℝ :=
  t ^ 2 / L ^ 4 * eSecond +
    2 * t / L ^ 2 * mixedDeriv

/-- Exact remainder integrand after adding and subtracting the unweighted
quadratic-normal source channel. -/
def optimizedCurvatureSourceRemainderIntegrand
    (L t mH ehz mixedDeriv : ℝ) : ℝ :=
  (2 * Real.pi) ^ 2 * (L ^ 2 - t ^ 2) / L ^ 4 * mH -
    (2 * Real.pi) ^ 2 * t ^ 2 / L ^ 4 * ehz +
    2 * t / L ^ 2 * mixedDeriv

/-- Pointwise algebra behind the exact source-remainder identity. The only
mathematical input is the production second-derivative transport equation. -/
theorem optimizedCurvatureSourceIntegrand_eq_remainder_sub_source
    (L t eSecond mixedDeriv mH ehz : ℝ)
    (hL : L ≠ 0)
    (htransport :
      eSecond = -(2 * Real.pi) ^ 2 * (ehz + mH)) :
    optimizedCurvatureSourceIntegrand L t eSecond mixedDeriv =
      optimizedCurvatureSourceRemainderIntegrand
          L t mH ehz mixedDeriv -
        (2 * Real.pi) ^ 2 / L ^ 2 * mH := by
  unfold optimizedCurvatureSourceIntegrand
    optimizedCurvatureSourceRemainderIntegrand
  have hfrac :
      (2 * Real.pi) ^ 2 * (L ^ 2 - t ^ 2) / L ^ 4 * mH -
          (2 * Real.pi) ^ 2 / L ^ 2 * mH =
        -(2 * Real.pi) ^ 2 * t ^ 2 / L ^ 4 * mH := by
    field_simp [hL]
    ring
  rw [htransport]
  calc
    t ^ 2 / L ^ 4 * (-(2 * Real.pi) ^ 2 * (ehz + mH)) +
          2 * t / L ^ 2 * mixedDeriv =
        -(2 * Real.pi) ^ 2 * t ^ 2 / L ^ 4 * ehz +
          2 * t / L ^ 2 * mixedDeriv +
          (-(2 * Real.pi) ^ 2 * t ^ 2 / L ^ 4 * mH) := by
            ring
    _ =
        -(2 * Real.pi) ^ 2 * t ^ 2 / L ^ 4 * ehz +
          2 * t / L ^ 2 * mixedDeriv +
          ((2 * Real.pi) ^ 2 * (L ^ 2 - t ^ 2) / L ^ 4 * mH -
            (2 * Real.pi) ^ 2 / L ^ 2 * mH) := by
            rw [hfrac]
    _ =
        (2 * Real.pi) ^ 2 * (L ^ 2 - t ^ 2) / L ^ 4 * mH -
          (2 * Real.pi) ^ 2 * t ^ 2 / L ^ 4 * ehz +
          2 * t / L ^ 2 * mixedDeriv -
          (2 * Real.pi) ^ 2 / L ^ 2 * mH := by
            ring

/-- The pointwise identity lifts through any real-linear arithmetic functional.
This is the precise algebraic step used when the production derivative
functional is eventually instantiated. -/
theorem optimizedCurvatureLinearFunctional_eq_remainder_sub_source
    (A : (ℝ → ℝ) →ₗ[ℝ] ℝ)
    (L : ℝ)
    (hL : L ≠ 0)
    (eSecond mixedDeriv mH ehz : ℝ → ℝ)
    (htransport :
      ∀ t : ℝ,
        eSecond t = -(2 * Real.pi) ^ 2 * (ehz t + mH t)) :
    A (fun t =>
        optimizedCurvatureSourceIntegrand
          L t (eSecond t) (mixedDeriv t)) =
      A (fun t =>
        optimizedCurvatureSourceRemainderIntegrand
          L t (mH t) (ehz t) (mixedDeriv t)) -
        (2 * Real.pi) ^ 2 / L ^ 2 * A mH := by
  have hfun :
      (fun t =>
        optimizedCurvatureSourceIntegrand
          L t (eSecond t) (mixedDeriv t)) =
      (fun t =>
        optimizedCurvatureSourceRemainderIntegrand
            L t (mH t) (ehz t) (mixedDeriv t) -
          (2 * Real.pi) ^ 2 / L ^ 2 * mH t) := by
    funext t
    exact
      optimizedCurvatureSourceIntegrand_eq_remainder_sub_source
        L t (eSecond t) (mixedDeriv t) (mH t) (ehz t)
        hL (htransport t)
  rw [hfun]
  have hsub :
      (fun t =>
        optimizedCurvatureSourceRemainderIntegrand
            L t (mH t) (ehz t) (mixedDeriv t) -
          (2 * Real.pi) ^ 2 / L ^ 2 * mH t) =
      (fun t =>
        optimizedCurvatureSourceRemainderIntegrand
          L t (mH t) (ehz t) (mixedDeriv t)) -
        ((2 * Real.pi) ^ 2 / L ^ 2) • mH := by
    rfl
  rw [hsub, map_sub, map_smul]
  simp [smul_eq_mul]

/-- Concrete scalar balance used by the strict-even equality-rigidity lane. -/
def OptimizedCurvatureRemainderBalance
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (kappa remainder : ℝ) : Prop :=
  kappa =
    remainder -
      (2 * Real.pi) ^ 2 / L ^ 2 *
        strictEvenSourceMomentPairing L K v

/-- Any exact linear-functional source derivation of curvature constructs the
scalar remainder balance. -/
theorem optimizedCurvatureRemainderBalance_of_linearFunctional
    (A : (ℝ → ℝ) →ₗ[ℝ] ℝ)
    (L : ℝ) (hL : L ≠ 0) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (eSecond mixedDeriv mH ehz : ℝ → ℝ)
    (kappa : ℝ)
    (htransport :
      ∀ t : ℝ,
        eSecond t = -(2 * Real.pi) ^ 2 * (ehz t + mH t))
    (hkappa :
      kappa =
        A (fun t =>
          optimizedCurvatureSourceIntegrand
            L t (eSecond t) (mixedDeriv t)))
    (hsource :
      A mH = strictEvenSourceMomentPairing L K v) :
    OptimizedCurvatureRemainderBalance
      L K v kappa
        (A (fun t =>
          optimizedCurvatureSourceRemainderIntegrand
            L t (mH t) (ehz t) (mixedDeriv t))) := by
  unfold OptimizedCurvatureRemainderBalance
  rw [hkappa]
  rw [optimizedCurvatureLinearFunctional_eq_remainder_sub_source
    A L hL eSecond mixedDeriv mH ehz htransport]
  rw [hsource]

/-- Saturation is exactly equality of the arithmetic remainder and the scaled
source/M4 pairing. This theorem does not assert that saturation is impossible. -/
theorem optimizedCurvatureRemainderBalance_zero_iff
    {L : ℝ} {K : ℕ}
    {v : euclideanEvenBoundaryFlatSubspace K}
    {kappa remainder : ℝ}
    (hbal :
      OptimizedCurvatureRemainderBalance L K v kappa remainder) :
    kappa = 0 ↔
      remainder =
        (2 * Real.pi) ^ 2 / L ^ 2 *
          strictEvenSourceMomentPairing L K v := by
  unfold OptimizedCurvatureRemainderBalance at hbal
  constructor
  · intro hk
    rw [hk] at hbal
    linarith
  · intro hr
    rw [hr] at hbal
    linarith

/-- In a strict-even zero-ground branch, saturation forces the arithmetic
remainder to equal the scaled positive odd-sector energy. -/
theorem optimizedCurvatureRemainderBalance_zero_iff_oddEnergy
    {L : ℝ} (hL : 0 < L)
    {K : ℕ} (hK : 2 ≤ K)
    {v : euclideanEvenBoundaryFlatSubspace K}
    {kappa remainder : ℝ}
    (hveig : evenCompressedCanonical L K v = 0)
    (hbal :
      OptimizedCurvatureRemainderBalance L K v kappa remainder) :
    kappa = 0 ↔
      remainder =
        (2 * Real.pi) ^ 2 / L ^ 2 *
          Complex.re
            (inner ℂ
              (oddCompressedCanonical L K
                (euclideanEvenToOddIndexLinearMap K v))
              (euclideanEvenToOddIndexLinearMap K v)) := by
  rw [optimizedCurvatureRemainderBalance_zero_iff hbal]
  rw [strictEvenSourceMomentPairing_eq_oddEnergy_of_even_zero_eigenmode
    hL K hK v hveig]

/-- Consequently, under strict odd-sector separation the saturated remainder is
strictly positive. This is the formal positive-balance endpoint of the paper
derivation; it is not an exclusion theorem. -/
theorem optimizedCurvatureRemainder_pos_of_saturation_even_zero_ground_strict
    {L : ℝ} (hL : 0 < L)
    {K : ℕ} (hK : 2 ≤ K)
    {v : euclideanEvenBoundaryFlatSubspace K}
    (hvne : v ≠ 0)
    (hground : parityRayleighBottom .even L K = 0)
    (hveig : evenCompressedCanonical L K v = 0)
    (hodd : 0 < parityRayleighBottom .odd L K)
    {kappa remainder : ℝ}
    (hbal :
      OptimizedCurvatureRemainderBalance L K v kappa remainder)
    (hkappa : kappa = 0) :
    0 < remainder := by
  have hpair :
      0 < strictEvenSourceMomentPairing L K v :=
    strictEvenSourceMomentPairing_pos_of_even_zero_ground_strict
      hL K hK v hvne hground hveig hodd
  have hscale :
      0 < (2 * Real.pi) ^ 2 / L ^ 2 := by
    positivity
  have hEq :=
    (optimizedCurvatureRemainderBalance_zero_iff hbal).mp hkappa
  rw [hEq]
  exact mul_pos hscale hpair

end Zeta23.CCM

#print axioms Zeta23.CCM.optimizedCurvatureSourceIntegrand_eq_remainder_sub_source
#print axioms Zeta23.CCM.optimizedCurvatureLinearFunctional_eq_remainder_sub_source
#print axioms Zeta23.CCM.optimizedCurvatureRemainderBalance_of_linearFunctional
#print axioms Zeta23.CCM.optimizedCurvatureRemainderBalance_zero_iff
#print axioms Zeta23.CCM.optimizedCurvatureRemainderBalance_zero_iff_oddEnergy
#print axioms Zeta23.CCM.optimizedCurvatureRemainder_pos_of_saturation_even_zero_ground_strict
