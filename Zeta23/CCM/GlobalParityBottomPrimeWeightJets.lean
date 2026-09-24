import Zeta23.CCM.GlobalParityBottomPrimeWeight
import Zeta23.CCM.GlobalParityBottomRetainedGeometry
import Zeta23.CCM.CanonicalSourceMomentJets

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#261 — true-ground prime-weight endpoint jets

The actual arithmetic test weight from #247 is

  w(t) = E'(1 - t/L),

where E is the production source-atom real energy of the same true global
ground vector used by the branch geometry and the prime-remainder integral.

This module transports the already-proved source-coordinate endpoint jets of E
through that affine change of variables.  On an even-selected true ground, the
boundary-flat and reversal-even constraints kill source jets 1 through 8.  On
a strict-even global-bottom branch, the existing source/M4 rigidity makes the
ninth source jet strictly positive, so the arithmetic weight has exact
order-eight contact at t=L.

Firewalls:
* this is an endpoint-shape theorem for the exact #247 test weight;
* it is not a global sign theorem for the weight;
* it does not exclude a residual state;
* it does not prove prime-remainder dominance;
* it does not close the odd-strict or tie branches;
* it does not prove RH.
-/

/-- Exact affine transport from source-coordinate jets to endpoint jets of the
actual prime-test weight. -/
theorem GlobalBottomResidualState.iteratedDeriv_primeTestWeight_at_aperture
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (j : ℕ) :
    iteratedDeriv j s.primeTestWeight s.aligned.firstBad.L =
      (-1 / s.aligned.firstBad.L) ^ j *
        iteratedDeriv (j + 1)
          (sourceAtomRealEnergy
            (s.aligned.firstBad.Nstar + 1)
            (s.groundTrial : EuclideanSpace ℂ
              (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))))
          0 := by
  let L := s.aligned.firstBad.L
  let K := s.aligned.firstBad.Nstar + 1
  let x : EuclideanSpace ℂ (Fin (2 * K + 1)) :=
    (s.groundTrial : EuclideanSpace ℂ
      (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1)))
  let E : ℝ → ℝ := sourceAtomRealEnergy K x
  have hLne : L ≠ 0 := ne_of_gt s.aligned.firstBad.L_pos
  have hE : ContDiff ℝ ⊤ E := by
    simpa [E, K, x] using contDiff_sourceAtomRealEnergy K x
  have hEderiv : ContDiff ℝ j (deriv E) := by
    have hEj1 : ContDiff ℝ (j + 1) E := hE.of_le (by simp)
    exact hEj1.deriv'
  have hsub : ContDiff ℝ j (fun z : ℝ => deriv E (1 - z)) := by
    fun_prop
  change
    iteratedDeriv j
        (fun t : ℝ =>
          deriv E (1 - t / L)) L =
      (-1 / L) ^ j * iteratedDeriv (j + 1) E 0
  have hfun :
      (fun t : ℝ => deriv E (1 - t / L)) =
        fun t : ℝ => (fun z : ℝ => deriv E (1 - z)) ((1 / L) * t) := by
    funext t
    congr 1
    ring
  rw [hfun]
  rw [iteratedDeriv_comp_const_mul hsub (1 / L)]
  have hscale : (1 / L) * L = 1 := by
    field_simp [hLne]
  change
    (1 / L) ^ j *
        iteratedDeriv j (fun z : ℝ => deriv E (1 - z)) ((1 / L) * L) =
      (-1 / L) ^ j * iteratedDeriv (j + 1) E 0
  rw [hscale]
  rw [iteratedDeriv_comp_const_sub]
  simp only [sub_self, smul_eq_mul]
  rw [← iteratedDeriv_succ']
  have hpow :
      (1 / L) ^ j * (-1 : ℝ) ^ j = (-1 / L) ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  rw [← mul_assoc, hpow]

/-- On every even-selected global-bottom state, the true-ground vector is an
even boundary-flat carrier, so the actual prime-test weight and its first seven
derivatives vanish at the arithmetic endpoint t=L. -/
theorem GlobalBottomResidualState.primeTestWeight_endpoint_jets_through_seven_of_even
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even) :
    ∀ j : ℕ, j ≤ 7 →
      iteratedDeriv j s.primeTestWeight s.aligned.firstBad.L = 0 := by
  let K := s.aligned.firstBad.Nstar + 1
  let v := s.aligned.evenShiftedTrial
  have htrial :=
    s.groundTrial_coe_eq_evenShiftedTrial_of_even hp
  have hmem :
      evenBoundaryFlatRawCoefficients K v ∈
        evenBoundaryFlatSubspace K := by
    change
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
        evenBoundaryFlatSubspace K
    exact
      (mem_euclideanEvenBoundaryFlatSubspace_iff K
        (v : EuclideanSpace ℂ (Fin (2 * K + 1)))).mp v.property
  have hflat :
      BoundaryFlatCoefficients K
        (evenBoundaryFlatRawCoefficients K v) :=
    (mem_boundaryFlatSubspace_iff K _).mp hmem.1
  have heven :
      evenBoundaryFlatRawCoefficients K v ∈
        evenCoefficientSubspace K :=
    hmem.2
  intro j hj
  rw [s.iteratedDeriv_primeTestWeight_at_aperture j]
  have hsource :
      iteratedDeriv (j + 1)
          (sourceAtomRealEnergy K
            (s.groundTrial : EuclideanSpace ℂ
              (Fin (2 * K + 1)))) 0 = 0 := by
    rw [htrial]
    exact
      sourceAtomRealEnergy_even_boundaryFlat_jets_through_eight
        K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))
        hflat heven (j + 1) (by omega) (by omega)
  rw [hsource, mul_zero]

/-- Exact eighth endpoint derivative of the true-ground prime-test weight on an
even-selected state.  The coefficient is positive because the affine pullback
has even order; strict positivity is deliberately deferred to a separate
strict-even theorem. -/
theorem GlobalBottomResidualState.primeTestWeight_eighth_deriv_eq_momentFour_of_even
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even) :
    iteratedDeriv 8 s.primeTestWeight s.aligned.firstBad.L =
      (-1 / s.aligned.firstBad.L) ^ 8 *
        (2 * (2 * Real.pi) ^ 8 *
          Complex.normSq
            (centeredMoment (s.aligned.firstBad.Nstar + 1) 4
              (evenBoundaryFlatRawCoefficients
                (s.aligned.firstBad.Nstar + 1)
                s.aligned.evenShiftedTrial))) := by
  let K := s.aligned.firstBad.Nstar + 1
  let v := s.aligned.evenShiftedTrial
  have htrial :=
    s.groundTrial_coe_eq_evenShiftedTrial_of_even hp
  have hmem :
      evenBoundaryFlatRawCoefficients K v ∈
        evenBoundaryFlatSubspace K := by
    change
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
        evenBoundaryFlatSubspace K
    exact
      (mem_euclideanEvenBoundaryFlatSubspace_iff K
        (v : EuclideanSpace ℂ (Fin (2 * K + 1)))).mp v.property
  have hflat :
      BoundaryFlatCoefficients K
        (evenBoundaryFlatRawCoefficients K v) :=
    (mem_boundaryFlatSubspace_iff K _).mp hmem.1
  have heven :
      evenBoundaryFlatRawCoefficients K v ∈
        evenCoefficientSubspace K :=
    hmem.2
  rw [s.iteratedDeriv_primeTestWeight_at_aperture 8]
  rw [htrial]
  have hsource :
      iteratedDeriv 9
          (sourceAtomRealEnergy K
            (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) 0 =
        2 * (2 * Real.pi) ^ 8 *
          Complex.normSq
            (centeredMoment K 4
              (evenBoundaryFlatRawCoefficients K v)) := by
    simpa [evenBoundaryFlatRawCoefficients] using
      (iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
        K
        (v : EuclideanSpace ℂ (Fin (2 * K + 1)))
        hflat heven)
  rw [hsource]

/-- Even selection alone gives nonnegativity of the first potentially
nonvanishing prime-weight endpoint jet. -/
theorem GlobalBottomResidualState.primeTestWeight_eighth_deriv_nonneg_of_even
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even) :
    0 ≤ iteratedDeriv 8 s.primeTestWeight s.aligned.firstBad.L := by
  rw [s.primeTestWeight_eighth_deriv_eq_momentFour_of_even hp]
  have hscale :
      0 ≤ (-1 / s.aligned.firstBad.L) ^ (8 : ℕ) := by
    rw [show
      (-1 / s.aligned.firstBad.L) ^ (8 : ℕ) =
        ((-1 / s.aligned.firstBad.L) ^ (4 : ℕ)) ^ 2 by ring]
    exact sq_nonneg _
  have hcoeff : 0 ≤ 2 * (2 * Real.pi) ^ (8 : ℕ) := by
    positivity
  exact
    mul_nonneg hscale
      (mul_nonneg hcoeff (Complex.normSq_nonneg _))

/-- Headline cross-view compatibility law.

On a strict-even global-bottom branch the exact same true-ground vector used by
the branch package and the prime-remainder integral gives a prime-test weight
with exact order-eight endpoint contact:

  w^(j)(L) = 0 for 0 <= j <= 7,
  w^(8)(L) > 0.

This is a local endpoint-shape theorem, not a global weight-sign theorem or a
residual-state exclusion theorem. -/
theorem GlobalBottomResidualState.primeTestWeight_endpoint_order_eight_of_evenStrict
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even)
    (hstrict :
      parityRayleighBottom .even s.aligned.firstBad.L
          (s.aligned.firstBad.Nstar + 1) <
        parityRayleighBottom .odd s.aligned.firstBad.L
          (s.aligned.firstBad.Nstar + 1)) :
    (∀ j : ℕ, j ≤ 7 →
      iteratedDeriv j s.primeTestWeight s.aligned.firstBad.L = 0) ∧
    0 < iteratedDeriv 8 s.primeTestWeight s.aligned.firstBad.L := by
  refine ⟨s.primeTestWeight_endpoint_jets_through_seven_of_even hp, ?_⟩
  have hground :
      s.aligned.lam =
        parityRayleighBottom .even s.aligned.firstBad.L
          (s.aligned.firstBad.Nstar + 1) := by
    rw [s.aligned_lam_is_global, globalParitySuccessorBottom,
      min_eq_left (le_of_lt hstrict)]
  have hM4ne :=
    s.aligned.retainedMomentFour_ne_zero_of_evenGround_strict
      hp hground hstrict
  rw [s.primeTestWeight_eighth_deriv_eq_momentFour_of_even hp]
  have hbase :
      -1 / s.aligned.firstBad.L ≠ 0 := by
    exact div_ne_zero (by norm_num) (ne_of_gt s.aligned.firstBad.L_pos)
  have hscale : 0 < (-1 / s.aligned.firstBad.L) ^ (8 : ℕ) := by
    rw [show
      (-1 / s.aligned.firstBad.L) ^ (8 : ℕ) =
        ((-1 / s.aligned.firstBad.L) ^ (4 : ℕ)) ^ 2 by ring]
    exact sq_pos_of_ne_zero (pow_ne_zero 4 hbase)
  have hmoment :
      0 <
        Complex.normSq
          (centeredMoment (s.aligned.firstBad.Nstar + 1) 4
            (evenBoundaryFlatRawCoefficients
              (s.aligned.firstBad.Nstar + 1)
              s.aligned.evenShiftedTrial)) :=
    Complex.normSq_pos.mpr hM4ne
  have hcoeff : 0 < 2 * (2 * Real.pi) ^ (8 : ℕ) := by
    positivity
  exact mul_pos hscale (mul_pos hcoeff hmoment)

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomResidualState.iteratedDeriv_primeTestWeight_at_aperture
#print axioms Zeta23.CCM.GlobalBottomResidualState.primeTestWeight_endpoint_jets_through_seven_of_even
#print axioms Zeta23.CCM.GlobalBottomResidualState.primeTestWeight_eighth_deriv_eq_momentFour_of_even
#print axioms Zeta23.CCM.GlobalBottomResidualState.primeTestWeight_eighth_deriv_nonneg_of_even
#print axioms Zeta23.CCM.GlobalBottomResidualState.primeTestWeight_endpoint_order_eight_of_evenStrict
