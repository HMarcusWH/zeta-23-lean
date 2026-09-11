import Zeta23.CCM.CanonicalApertureParameterHolomorphy
import Zeta23.CCM.FrozenCanonicalSourceComplex
import Mathlib.Analysis.Analytic.Constructions

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set Filter
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1d: assembled source holomorphy

PR #148 proved genuine parameter holomorphy of the three fixed-unit
archimedean cores on `complexArchSafeStrip`.  This module begins assembling
those pointwise core theorems into the actual frozen source continuation.

The natural common source domain removes the explicit prime/pole singularity at
zero from the archimedean safe strip.  The scalar principal-log branch is still
handled separately; merely defining this punctured strip does not assert that
the full source is analytic there.

No determinant density, positivity, negative-root exclusion, or RH theorem is
claimed here.
-/

/-- Common punctured strip for the frozen source channels before the scalar-log
branch condition is discharged. -/
def complexFrozenSourceDomain : Set ℂ :=
  complexArchSafeStrip \ {0}

/-- The punctured source strip is open. -/
theorem isOpen_complexFrozenSourceDomain : IsOpen complexFrozenSourceDomain := by
  exact isOpen_complexArchSafeStrip.sdiff isClosed_singleton

/-- Every nonzero real aperture lies in the punctured source strip. -/
@[simp] theorem ofReal_mem_complexFrozenSourceDomain_iff (L : ℝ) :
    (L : ℂ) ∈ complexFrozenSourceDomain ↔ L ≠ 0 := by
  simp [complexFrozenSourceDomain, ofReal_mem_complexArchSafeStrip]

/-- The exact `wCorrection`-free archimedean source entry is analytic throughout
#148's common strip. -/
theorem analyticOnNhd_complexCanonicalArchWithoutWComponent_strip
    (n m : ℤ) :
    AnalyticOnNhd ℂ
      (complexCanonicalArchWithoutWComponent n m)
      complexArchSafeStrip := by
  by_cases hnm : n = m
  · subst m
    have hg :=
      (analyticOnNhd_complexGammaCore_strip n).const_smul (c := (2 : ℂ))
    have hb :=
      (analyticOnNhd_complexBetaCore_strip n).const_smul (c := (2 : ℂ))
    simpa [complexCanonicalArchWithoutWComponent, smul_eq_mul] using hg.sub hb
  · have ha :=
      (analyticOnNhd_complexAlphaCore_strip m).sub
        (analyticOnNhd_complexAlphaCore_strip n)
    simpa [complexCanonicalArchWithoutWComponent, hnm] using
      ha.div_const (c := (((n - m : ℤ) : ℂ)))

/-- Matrix packaging of the exact archimedean remainder holomorphy. -/
theorem analyticOnNhd_complexCanonicalArchWithoutWMatrix_strip
    (K : ℕ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => complexCanonicalArchWithoutWMatrix z K)
      complexArchSafeStrip := by
  rw [analyticOnNhd_pi_iff]
  intro i
  rw [analyticOnNhd_pi_iff]
  intro j
  simpa [complexCanonicalArchWithoutWMatrix] using
    analyticOnNhd_complexCanonicalArchWithoutWComponent_strip
      (centeredIndex K i) (centeredIndex K j)

/-- The only singularity of one frozen prime coordinate on the selected source
domain has already been removed by definition. -/
theorem analyticOnNhd_complexPrimeSourceCoordinate_sourceDomain
    (q : ℕ) :
    AnalyticOnNhd ℂ
      (complexPrimeSourceCoordinate q)
      complexFrozenSourceDomain := by
  intro z hz
  have hz0 : z ≠ 0 := by
    have hnot : z ∉ ({0} : Set ℂ) := hz.2
    simpa using hnot
  have hquot : AnalyticAt ℂ (fun w : ℂ => (Real.log q : ℂ) / w) z :=
    analyticAt_const.div analyticAt_id hz0
  simpa [complexPrimeSourceCoordinate] using analyticAt_const.sub hquot

end Zeta23.CCM

#print axioms Zeta23.CCM.isOpen_complexFrozenSourceDomain
#print axioms Zeta23.CCM.analyticOnNhd_complexCanonicalArchWithoutWComponent_strip
#print axioms Zeta23.CCM.analyticOnNhd_complexCanonicalArchWithoutWMatrix_strip
#print axioms Zeta23.CCM.analyticOnNhd_complexPrimeSourceCoordinate_sourceDomain
