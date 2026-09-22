import Zeta23.ExceptionalZero.GeneratedFamilyFinalGateEquivalence
import Zeta23.CCM.CanonicalPrimeRemainder

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# Canonical arithmetic criterion: every candidate last lemma, audited

PR #245 proved that the two terminal certificate gates are equivalent to
Mathlib's `RiemannHypothesis`.  After #245 several candidate "last lemmas" were
proposed for a closing PR.  This module applies the same dumbassery firewall to
each of them *before* any attempt is made to prove one, and records the result
as compiled equivalences rather than prose.

Proved here, all with no new hypothesis:

* `CanonicalFiniteWeilPositivity ↔ RiemannHypothesis`: nonnegativity of the
  complete canonical source energy on every legal boundary-flat carrier at
  every aperture.
* `CanonicalRieszSixPositivity ↔ RiemannHypothesis`: the same statement for the
  complete order-six Riesz source channel, which coincides with the canonical
  energy on every boundary-flat carrier.
* `GeneratedRetainedRieszSixEventuallyNonnegative ↔ RiemannHypothesis`: eventual
  nonnegativity of the order-six Riesz channel on the exact generated
  whole-cell retained cubic trial.  This was proposed as the primitive target
  of a closing PR; it is another RH-equivalent gate, not a lemma below RH.
* `CanonicalPrimeRemainderDominance ↔ RiemannHypothesis`: the explicit
  arithmetic inequality produced by `CCM.CanonicalPrimeRemainder`, in which
  the only prime-dependent quantity is the classical weighted-Chebyshev
  remainder `R(x) = ∑_{n ≤ x} Λ(n)/√n - 2√x`.
* `GeneratedRetainedPrimeRemainderDominance ↔ RiemannHypothesis`: the same
  inequality required only eventually along the generated family.

It also exhibits the exact first failed inequality forced by a hypothetical
off-line zero: at arbitrarily large retained aperture, the prime-free budget
strictly exceeds minus the prime-remainder energy on the retained trial.

Consequently the remaining node of this route is RH itself, stated as one
explicit weighted von Mangoldt inequality.  This file proves no new
unconditional information about zeta zeros and does not prove RH.
-/

/-- Legal boundary-flat carrier predicate in Euclidean coordinates. -/
abbrev EuclideanBoundaryFlat
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) : Prop :=
  BoundaryFlatCoefficients K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)

/-- Retained cubic zero-shift trial of a whole-cell generated certificate. -/
abbrev wholeCellRetainedTrial
    {Q : ℕ}
    (c : WholeCellBiRegularNegativeEnergyCertificate Q) :
    EuclideanSpace ℂ (Fin (2 * (c.retained.energy.firstBad.Nstar + 1) + 1)) :=
  (cubicZeroShiftTrialVector
    c.retained.energy.firstBad.p c.retained.energy.firstBad.L
    c.retained.energy.firstBad.Nstar c.retained.energy.x₀ :
    EuclideanSpace ℂ (Fin (2 * (c.retained.energy.firstBad.Nstar + 1) + 1)))

/-! ## Canonical finite Weil positivity -/

/-- Nonnegativity of the complete canonical source energy on every legal
boundary-flat carrier at every positive aperture. -/
def CanonicalFiniteWeilPositivity : Prop :=
  ∀ L : ℝ, 0 < L →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      EuclideanBoundaryFlat K x →
        0 ≤ canonicalSourceChannelEnergy L K x

/-- Canonical finite Weil positivity excludes every retained regular first-bad
certificate. -/
theorem noRegularFirstBadCertificates_of_canonicalFiniteWeilPositivity
    (h : CanonicalFiniteWeilPositivity) :
    NoRegularFirstBadCertificates := by
  intro Q c
  exact
    (not_lt_of_ge
      (h c.firstBad.L c.firstBad.L_pos (c.firstBad.Nstar + 1) _
        c.trial_boundaryFlat))
      c.channelEnergyNeg

/-- Mathlib RH implies canonical finite Weil positivity. -/
theorem canonicalFiniteWeilPositivity_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    CanonicalFiniteWeilPositivity := by
  intro L hL K x hx
  exact canonicalSourceChannelEnergy_nonnegative_of_criticalLine
    (fun rho hrho => RH_implies_on_line hRH (by simpa using hrho)) hL K x hx

/-- Canonical finite Weil positivity is exactly Mathlib's RH. -/
theorem canonicalFiniteWeilPositivity_iff_riemannHypothesis :
    CanonicalFiniteWeilPositivity ↔ RiemannHypothesis :=
  ⟨fun h =>
      riemannHypothesis_of_noRegularFirstBadCertificates
        (noRegularFirstBadCertificates_of_canonicalFiniteWeilPositivity h),
    canonicalFiniteWeilPositivity_of_riemannHypothesis⟩

/-! ## Complete order-six Riesz channel -/

/-- Nonnegativity of the complete order-six Riesz source channel on every legal
boundary-flat carrier at every positive aperture. -/
def CanonicalRieszSixPositivity : Prop :=
  ∀ L : ℝ, 0 < L →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      EuclideanBoundaryFlat K x →
        0 ≤ canonicalRieszSourceChannelEnergy L 6 K x

/-- Order-six Riesz positivity and canonical finite Weil positivity are the same
statement: the two energies coincide on every boundary-flat carrier. -/
theorem canonicalRieszSixPositivity_iff_canonicalFiniteWeilPositivity :
    CanonicalRieszSixPositivity ↔ CanonicalFiniteWeilPositivity := by
  constructor
  · intro h L hL K x hx
    rw [canonicalSourceChannelEnergy_eq_rieszSix_of_boundaryFlat hL K x hx]
    exact h L hL K x hx
  · intro h L hL K x hx
    rw [← canonicalSourceChannelEnergy_eq_rieszSix_of_boundaryFlat hL K x hx]
    exact h L hL K x hx

/-- Order-six Riesz positivity is exactly Mathlib's RH. -/
theorem canonicalRieszSixPositivity_iff_riemannHypothesis :
    CanonicalRieszSixPositivity ↔ RiemannHypothesis :=
  canonicalRieszSixPositivity_iff_canonicalFiniteWeilPositivity.trans
    canonicalFiniteWeilPositivity_iff_riemannHypothesis

/-! ## Generated retained order-six Riesz energy -/

/-- Eventual nonnegativity of the order-six Riesz channel on the exact
generated whole-cell retained cubic trial.  Proposed after #245 as the primitive
target of a closing PR. -/
def GeneratedRetainedRieszSixEventuallyNonnegative : Prop :=
  ∃ A : ℝ,
    ∀ Q : ℕ, ∀ c : WholeCellBiRegularNegativeEnergyCertificate Q,
      A < c.retained.energy.firstBad.L →
        0 ≤ canonicalRieszSourceChannelEnergy
          c.retained.energy.firstBad.L 6
          (c.retained.energy.firstBad.Nstar + 1) (wholeCellRetainedTrial c)

/-- Eventual generated Riesz-six nonnegativity bounds the retained aperture,
because every retained certificate already has strictly negative Riesz-six
energy. -/
theorem noArbitrarilyLargeWholeCellRetainedFamily_of_generatedRetainedRieszSixEventuallyNonnegative
    (h : GeneratedRetainedRieszSixEventuallyNonnegative) :
    NoArbitrarilyLargeWholeCellRetainedFamily := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun Q c => ?_⟩
  by_contra hlt
  exact (not_lt_of_ge (hA Q c (not_le.mp hlt))) c.retained.energy.rieszSixNeg

/-- The generated retained Riesz-six target is exactly Mathlib's RH.  It is not
a lemma strictly below RH. -/
theorem generatedRetainedRieszSixEventuallyNonnegative_iff_riemannHypothesis :
    GeneratedRetainedRieszSixEventuallyNonnegative ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_noArbitrarilyLargeWholeCellRetainedFamily
      (noArbitrarilyLargeWholeCellRetainedFamily_of_generatedRetainedRieszSixEventuallyNonnegative
        h)
  · intro hRH
    refine ⟨0, fun Q c _ => ?_⟩
    exact False.elim
      (noRegularFirstBadCertificates_of_riemannHypothesis hRH Q c.retained.energy)

/-! ## Explicit prime-remainder dominance -/

/-- The explicit arithmetic form of canonical finite Weil positivity: on every
legal boundary-flat carrier, minus the energy of the classical remainder
`R(x) = ∑_{n ≤ x} Λ(n)/√n - 2√x` dominates the prime-free budget. -/
def CanonicalPrimeRemainderDominance : Prop :=
  ∀ L : ℝ, 0 < L →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      EuclideanBoundaryFlat K x →
        canonicalPrimeFreeBudget L K x ≤ -canonicalPrimeRemainderEnergy L K x

/-- Prime-remainder dominance is canonical finite Weil positivity. -/
theorem canonicalPrimeRemainderDominance_iff_canonicalFiniteWeilPositivity :
    CanonicalPrimeRemainderDominance ↔ CanonicalFiniteWeilPositivity := by
  constructor
  · intro h L hL K x hx
    exact (canonicalSourceChannelEnergy_nonneg_iff_budget_le hL K x).mpr
      (h L hL K x hx)
  · intro h L hL K x hx
    exact (canonicalSourceChannelEnergy_nonneg_iff_budget_le hL K x).mp
      (h L hL K x hx)

/-- **The remaining node, stated arithmetically.**  Explicit prime-remainder
dominance is exactly Mathlib's RH. -/
theorem canonicalPrimeRemainderDominance_iff_riemannHypothesis :
    CanonicalPrimeRemainderDominance ↔ RiemannHypothesis :=
  canonicalPrimeRemainderDominance_iff_canonicalFiniteWeilPositivity.trans
    canonicalFiniteWeilPositivity_iff_riemannHypothesis

/-- Prime-remainder dominance required only eventually along the generated
whole-cell retained family, on its exact cubic trial. -/
def GeneratedRetainedPrimeRemainderDominance : Prop :=
  ∃ A : ℝ,
    ∀ Q : ℕ, ∀ c : WholeCellBiRegularNegativeEnergyCertificate Q,
      A < c.retained.energy.firstBad.L →
        canonicalPrimeFreeBudget
            c.retained.energy.firstBad.L
            (c.retained.energy.firstBad.Nstar + 1) (wholeCellRetainedTrial c) ≤
          -canonicalPrimeRemainderEnergy
            c.retained.energy.firstBad.L
            (c.retained.energy.firstBad.Nstar + 1) (wholeCellRetainedTrial c)

/-- The generated-family arithmetic dominance is exactly Mathlib's RH. -/
theorem generatedRetainedPrimeRemainderDominance_iff_riemannHypothesis :
    GeneratedRetainedPrimeRemainderDominance ↔ RiemannHypothesis := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := h
    apply riemannHypothesis_of_noArbitrarilyLargeWholeCellRetainedFamily
    refine ⟨A, fun Q c => ?_⟩
    by_contra hlt
    have hdom := hA Q c (not_le.mp hlt)
    have hnonneg :=
      (canonicalSourceChannelEnergy_nonneg_iff_budget_le
        c.retained.energy.firstBad.L_pos
        (c.retained.energy.firstBad.Nstar + 1) (wholeCellRetainedTrial c)).mpr hdom
    exact (not_lt_of_ge hnonneg) c.retained.energy.channelEnergyNeg
  · intro hRH
    refine ⟨0, fun Q c _ => ?_⟩
    exact False.elim
      (noRegularFirstBadCertificates_of_riemannHypothesis hRH Q c.retained.energy)

/-! ## The exact first failed inequality -/

/-- **First failed inequality.**  A hypothetical off-line zero forces, beyond
every aperture threshold, a whole-cell generated retained certificate on whose
exact cubic trial the prime-free budget strictly exceeds minus the classical
prime-remainder energy.

This is the precise arithmetic inequality a closing argument would have to
rule out.  By `generatedRetainedPrimeRemainderDominance_iff_riemannHypothesis`,
ruling it out is equivalent to RH. -/
theorem exists_arbitrarilyLarge_primeRemainderDominance_failure_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2)
    (A : ℝ) :
    ∃ Q : ℕ, ∃ c : WholeCellBiRegularNegativeEnergyCertificate Q,
      A < c.retained.energy.firstBad.L ∧
        -canonicalPrimeRemainderEnergy
            c.retained.energy.firstBad.L
            (c.retained.energy.firstBad.Nstar + 1) (wholeCellRetainedTrial c) <
          canonicalPrimeFreeBudget
            c.retained.energy.firstBad.L
            (c.retained.energy.firstBad.Nstar + 1) (wholeCellRetainedTrial c) := by
  obtain ⟨Q, c, hlarge⟩ :=
    exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
      ρ₀ hoff A
  refine ⟨Q, c, hlarge, ?_⟩
  have hneg :
      canonicalSourceChannelEnergy
          c.retained.energy.firstBad.L
          (c.retained.energy.firstBad.Nstar + 1)
          (wholeCellRetainedTrial c) < 0 :=
    c.retained.energy.channelEnergyNeg
  rw [canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget
    c.retained.energy.firstBad.L_pos] at hneg
  linarith

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.canonicalFiniteWeilPositivity_iff_riemannHypothesis
#print axioms Zeta23.ExceptionalZero.canonicalRieszSixPositivity_iff_riemannHypothesis
#print axioms Zeta23.ExceptionalZero.generatedRetainedRieszSixEventuallyNonnegative_iff_riemannHypothesis
#print axioms Zeta23.ExceptionalZero.canonicalPrimeRemainderDominance_iff_riemannHypothesis
#print axioms Zeta23.ExceptionalZero.generatedRetainedPrimeRemainderDominance_iff_riemannHypothesis
#print axioms Zeta23.ExceptionalZero.exists_arbitrarilyLarge_primeRemainderDominance_failure_of_offLine_zero
