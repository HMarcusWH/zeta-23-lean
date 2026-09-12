import Zeta23.CCM.CanonicalPolePrimeDiscrepancyIntegrability
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

noncomputable section

namespace Zeta23.CCM

open MeasureTheory Set
open scoped Interval

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB03: generic discrepancy smoothing

This module integrates the exact FB-02 finite pole-prime discrepancy.  The
prime staircase is never differentiated.  Instead, every new primitive is
anchored at zero, is absolutely continuous, and has the previous primitive as
its derivative almost everywhere on the physical interval.

Repeated integration by parts is therefore licensed by absolute continuity.
All right-endpoint terms are discharged only by explicit source-energy jet
hypotheses at source coordinate zero.  No sign theorem is asserted here.
-/

/-- Left-anchored iterated primitives of the exact finite pole-prime
discrepancy. -/
def canonicalPolePrimeRieszPrimitive (L : ℝ) : ℕ → ℝ → ℝ
  | 0 => canonicalPolePrimeDiscrepancy L
  | r + 1 => fun t =>
      ∫ s in (0 : ℝ)..t, canonicalPolePrimeRieszPrimitive L r s

@[simp] theorem canonicalPolePrimeRieszPrimitive_zero
    (L t : ℝ) :
    canonicalPolePrimeRieszPrimitive L 0 t =
      canonicalPolePrimeDiscrepancy L t := rfl

@[simp] theorem canonicalPolePrimeRieszPrimitive_succ_zero
    (L : ℝ) (r : ℕ) :
    canonicalPolePrimeRieszPrimitive L (r + 1) 0 = 0 := by
  simp [canonicalPolePrimeRieszPrimitive]

/-- Every iterated primitive is interval-integrable on a positive physical
aperture. -/
theorem intervalIntegrable_canonicalPolePrimeRieszPrimitive
    {L : ℝ} (hL : 0 < L) (r : ℕ) :
    IntervalIntegrable
      (canonicalPolePrimeRieszPrimitive L r) volume 0 L := by
  induction r with
  | zero =>
      change IntervalIntegrable (canonicalPolePrimeDiscrepancy L) volume 0 L
      exact intervalIntegrable_canonicalPolePrimeDiscrepancy hL
  | succ r ih =>
      have h0 : (0 : ℝ) ∈ uIcc (0 : ℝ) L := by
        rw [uIcc_of_le hL.le]
        exact ⟨le_rfl, hL.le⟩
      have hac : AbsolutelyContinuousOnInterval
          (fun t => ∫ s in (0 : ℝ)..t,
            canonicalPolePrimeRieszPrimitive L r s) 0 L := by
        exact ih.absolutelyContinuousOnInterval_intervalIntegral h0
      simpa [canonicalPolePrimeRieszPrimitive] using
        hac.continuousOn.intervalIntegrable

/-- Every positive-order primitive is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_canonicalPolePrimeRieszPrimitive_succ
    {L : ℝ} (hL : 0 < L) (r : ℕ) :
    AbsolutelyContinuousOnInterval
      (canonicalPolePrimeRieszPrimitive L (r + 1)) 0 L := by
  have h0 : (0 : ℝ) ∈ uIcc (0 : ℝ) L := by
    rw [uIcc_of_le hL.le]
    exact ⟨le_rfl, hL.le⟩
  simpa [canonicalPolePrimeRieszPrimitive] using
    (intervalIntegrable_canonicalPolePrimeRieszPrimitive hL r).absolutelyContinuousOnInterval_intervalIntegral h0

/-- On the physical interval, the derivative of the `(r+1)`st primitive is the
`r`th primitive almost everywhere.  This is deliberately an a.e. theorem:
the base discrepancy has finite prime-log jumps. -/
theorem ae_deriv_canonicalPolePrimeRieszPrimitive_succ
    {L : ℝ} (hL : 0 < L) (r : ℕ) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) L →
      deriv (canonicalPolePrimeRieszPrimitive L (r + 1)) t =
        canonicalPolePrimeRieszPrimitive L r t := by
  have h0 : (0 : ℝ) ∈ uIcc (0 : ℝ) L := by
    rw [uIcc_of_le hL.le]
    exact ⟨le_rfl, hL.le⟩
  have hae :=
    IntervalIntegrable.ae_hasDerivAt_integral
      (intervalIntegrable_canonicalPolePrimeRieszPrimitive hL r)
  filter_upwards [hae] with t ht
  intro htmem
  have hder := ht htmem 0 h0
  simpa [canonicalPolePrimeRieszPrimitive] using hder.deriv

/-- Source-energy iterated jet pulled back along the FB-02 affine source
coordinate `ω = 1-t/L`. -/
def sourceAtomComposedJet
    (L : ℝ)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (r : ℕ)
    (t : ℝ) : ℝ :=
  iteratedDeriv r (sourceAtomRealEnergy K x) (1 - t / L)

/-- Every pulled-back source-energy jet is `C¹`; `C^∞` of the underlying source
atom is more than sufficient. -/
theorem contDiff_one_sourceAtomComposedJet
    (L : ℝ)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (r : ℕ) :
    ContDiff ℝ 1 (sourceAtomComposedJet L K x r) := by
  have hg : ContDiff ℝ ⊤ (sourceAtomRealEnergy K x) :=
    contDiff_sourceAtomRealEnergy K x
  have hfinite : ContDiff ℝ (r + 1 : ℕ) (sourceAtomRealEnergy K x) :=
    hg.of_le (by simp)
  have hout : ContDiff ℝ 1 (iteratedDeriv r (sourceAtomRealEnergy K x)) :=
    (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hfinite).2
  unfold sourceAtomComposedJet
  exact hout.comp (by fun_prop)

/-- Exact chain rule for the pulled-back source-energy jets. -/
theorem deriv_sourceAtomComposedJet
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (r : ℕ)
    (t : ℝ) :
    deriv (sourceAtomComposedJet L K x r) t =
      -(1 / L) * sourceAtomComposedJet L K x (r + 1) t := by
  have hg : ContDiff ℝ ⊤ (sourceAtomRealEnergy K x) :=
    contDiff_sourceAtomRealEnergy K x
  have hdiff : Differentiable ℝ (iteratedDeriv r (sourceAtomRealEnergy K x)) :=
    hg.differentiable_iteratedDeriv r (by simp)
  have hout : HasDerivAt
      (iteratedDeriv r (sourceAtomRealEnergy K x))
      (iteratedDeriv (r + 1) (sourceAtomRealEnergy K x) (1 - t / L))
      (1 - t / L) := by
    simpa only [← iteratedDeriv_succ] using
      (hdiff (1 - t / L)).hasDerivAt
  have hin : HasDerivAt (fun s : ℝ => 1 - s / L) (-(1 / L)) t := by
    simpa using ((hasDerivAt_id t).div_const L).const_sub 1
  have hcomp := hout.comp t hin
  change deriv
      ((iteratedDeriv r (sourceAtomRealEnergy K x)) ∘
        (fun s : ℝ => 1 - s / L)) t =
    -(1 / L) * iteratedDeriv (r + 1) (sourceAtomRealEnergy K x) (1 - t / L)
  rw [hcomp.deriv]
  ring

/-- One legal integration-by-parts step.  The left endpoint vanishes because
the next primitive is anchored at zero; the right endpoint vanishes because
the corresponding source-energy jet at `ω=0` is explicitly assumed zero. -/
theorem canonicalPolePrimeRiesz_integral_step
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (r : ℕ)
    (hjet :
      iteratedDeriv (r + 1) (sourceAtomRealEnergy K x) 0 = 0) :
    (∫ t in (0 : ℝ)..L,
      canonicalPolePrimeRieszPrimitive L r t *
        sourceAtomComposedJet L K x (r + 1) t) =
      (1 / L) *
        ∫ t in (0 : ℝ)..L,
          canonicalPolePrimeRieszPrimitive L (r + 1) t *
            sourceAtomComposedJet L K x (r + 2) t := by
  let P : ℝ → ℝ := canonicalPolePrimeRieszPrimitive L (r + 1)
  let G : ℝ → ℝ := sourceAtomComposedJet L K x (r + 1)
  have hPac : AbsolutelyContinuousOnInterval P 0 L := by
    simpa [P] using
      absolutelyContinuousOnInterval_canonicalPolePrimeRieszPrimitive_succ hL r
  have hGac : AbsolutelyContinuousOnInterval G 0 L := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact (contDiff_one_sourceAtomComposedJet L K x (r + 1)).contDiffOn
  have hparts := hPac.integral_mul_deriv_eq_deriv_mul hGac
  have hP0 : P 0 = 0 := by
    simp [P]
  have hGL : G L = 0 := by
    dsimp [G, sourceAtomComposedJet]
    rw [div_self hL.ne']
    simpa using hjet
  have hleft :
      (∫ t in (0 : ℝ)..L, P t * deriv G t) =
        -(1 / L) *
          ∫ t in (0 : ℝ)..L,
            canonicalPolePrimeRieszPrimitive L (r + 1) t *
              sourceAtomComposedJet L K x (r + 2) t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp [P, G]
    rw [deriv_sourceAtomComposedJet hL K x (r + 1) t]
    ring
  have hright :
      (∫ t in (0 : ℝ)..L, deriv P t * G t) =
        ∫ t in (0 : ℝ)..L,
          canonicalPolePrimeRieszPrimitive L r t *
            sourceAtomComposedJet L K x (r + 1) t := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [ae_deriv_canonicalPolePrimeRieszPrimitive_succ hL r] with t ht hmem
      have htIcc : t ∈ uIcc (0 : ℝ) L := by
        rw [uIcc_of_le hL.le]
        exact ⟨hmem.1.le, hmem.2⟩
      dsimp [P, G]
      rw [ht htIcc]
    · filter_upwards with t
      intro hmem
      exfalso
      linarith [hL, hmem.1, hmem.2]
  rw [hleft, hright, hP0, hGL] at hparts
  dsimp [P, G] at hparts
  linarith

/-- The normalized order-`r` Riesz form.  Order zero is definitionally aligned
with FB-02 after the standard `iteratedDeriv 1 = deriv` simplification. -/
def canonicalPolePrimeRieszEnergy
    (L : ℝ)
    (r K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  (1 / L) ^ (r + 1) *
    ∫ t in (0 : ℝ)..L,
      canonicalPolePrimeRieszPrimitive L r t *
        sourceAtomComposedJet L K x (r + 1) t

/-- Riesz order zero is exactly the FB-02 discrepancy energy. -/
theorem canonicalPolePrimeRieszEnergy_zero
    (L : ℝ)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    canonicalPolePrimeRieszEnergy L 0 K x =
      canonicalPolePrimeDiscrepancyEnergy L K x := by
  simp [canonicalPolePrimeRieszEnergy, sourceAtomComposedJet,
    canonicalPolePrimeDiscrepancyEnergy, canonicalPolePrimeRieszPrimitive]

/-- One normalized Riesz step. -/
theorem canonicalPolePrimeRieszEnergy_succ
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (r : ℕ)
    (hjet :
      iteratedDeriv (r + 1) (sourceAtomRealEnergy K x) 0 = 0) :
    canonicalPolePrimeRieszEnergy L r K x =
      canonicalPolePrimeRieszEnergy L (r + 1) K x := by
  unfold canonicalPolePrimeRieszEnergy
  rw [canonicalPolePrimeRiesz_integral_step hL K x r hjet]
  rw [show r + 1 + 1 = (r + 1) + 1 by omega, pow_succ]
  ring

/-- Generic repeated smoothing theorem.  The admissible Riesz order is an
output of whatever endpoint-jet theorem supplies the hypotheses; this theorem
does not assume a historical order in advance. -/
theorem canonicalPolePrimeDiscrepancyEnergy_eq_rieszEnergy
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (r : ℕ)
    (hjets :
      ∀ j : ℕ, 1 ≤ j → j ≤ r →
        iteratedDeriv j (sourceAtomRealEnergy K x) 0 = 0) :
    canonicalPolePrimeDiscrepancyEnergy L K x =
      canonicalPolePrimeRieszEnergy L r K x := by
  calc
    canonicalPolePrimeDiscrepancyEnergy L K x =
        canonicalPolePrimeRieszEnergy L 0 K x :=
      (canonicalPolePrimeRieszEnergy_zero L K x).symm
    _ = canonicalPolePrimeRieszEnergy L r K x := by
      induction r with
      | zero => rfl
      | succ r ih =>
          calc
            canonicalPolePrimeRieszEnergy L 0 K x =
                canonicalPolePrimeRieszEnergy L r K x := by
                  apply ih
                  intro j hj1 hjr
                  exact hjets j hj1 (by omega)
            _ = canonicalPolePrimeRieszEnergy L (r + 1) K x := by
                  apply canonicalPolePrimeRieszEnergy_succ hL
                  exact hjets (r + 1) (by omega) (by omega)

end Zeta23.CCM

#print axioms Zeta23.CCM.intervalIntegrable_canonicalPolePrimeRieszPrimitive
#print axioms Zeta23.CCM.canonicalPolePrimeRiesz_integral_step
#print axioms Zeta23.CCM.canonicalPolePrimeDiscrepancyEnergy_eq_rieszEnergy
