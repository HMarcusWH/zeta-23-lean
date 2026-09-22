import Zeta23.ExceptionalZero.RegularFirstBadClosure
import Zeta23.Statement.SeamClosed
import Mathlib.NumberTheory.LSeries.Nonvanishing

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.CCM

/-!
# Experimental terminal RH configuration attempt

This module intentionally does **not** claim RH.  It asks how short the final
Lean theorem becomes once the two remaining logical interfaces are supplied:

1. no retained regular cell-minimal negative-energy certificate can exist;
2. every Mathlib zeta zero excluded from the trivial-zero family is in the
   open critical strip.

The first interface is the live RH research bottleneck.  The second is the
terminal Mathlib statement seam.  Everything else in this file is composition
of already-existing theorem authority.

No `sorry`, project axiom, hidden RH assumption, or theorem promotion is used.
-/

/-- Exact finite-side terminal obstruction needed by the current route.

If this proposition is eventually proved without circular assumptions, the
existing off-line-zero-to-retained-certificate chain rules out off-line strip
zeros. -/
def NoRegularFirstBadCertificates : Prop :=
  ∀ Q : ℕ, ∀ c : RegularCellMinimalNegativeEnergyCertificate Q, False

/-- Classification obligation for Mathlib's statement boundary at non-positive
integers.  This is deliberately separated from the RH-specific finite route.

The right half-plane boundary is already handled below by Mathlib's
`riemannZeta_ne_zero_of_one_le_re`; away from negative integers the left
boundary follows from the functional equation and the same nonvanishing
theorem. -/
def NegativeIntegerZeroClassification : Prop :=
  ∀ n : ℕ, riemannZeta (-(n : ℂ)) = 0 →
    ∃ m : ℕ, (-(n : ℂ)) = -2 * (m + 1)

/-- Current theorem stack + exclusion of every retained regular first-bad
certificate implies the repository's strip-zero form of RH. -/
theorem criticalLine_of_noRegularFirstBadCertificates
    (hno : NoRegularFirstBadCertificates) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 := by
  intro ρ hρ
  by_contra hoff
  obtain ⟨Q, hc⟩ :=
    exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero
      ⟨ρ, hρ⟩ hoff
  obtain ⟨c⟩ := hc
  exact hno Q c

/-- A zeta zero cannot have real part at least one. -/
theorem re_lt_one_of_riemannZeta_zero
    {s : ℂ}
    (hz : riemannZeta s = 0) :
    s.re < 1 := by
  by_contra h
  have hge : 1 ≤ s.re := le_of_not_gt h
  exact (riemannZeta_ne_zero_of_one_le_re hge) hz

/-- Away from non-positive integers, a zeta zero cannot have non-positive real
part: reflect it through the functional equation to a zero with real part at
least one, contradicting Mathlib nonvanishing. -/
theorem re_pos_of_riemannZeta_zero_of_not_neg_nat
    {s : ℂ}
    (hz : riemannZeta s = 0)
    (hneg : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    0 < s.re := by
  by_contra h
  have hle : s.re ≤ 0 := le_of_not_gt h
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hle
  have hreflect :
      riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_one_sub hneg hs1, hz]
    simp
  have hre : 1 ≤ (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  exact (riemannZeta_ne_zero_of_one_le_re hre) hreflect

/-- The only still-separated part of the Mathlib seam is the negative-integer
zero classification.  Supplying that classification turns Mathlib's
"nontrivial" hypotheses into the repository's open-strip `IsNontrivialZero`.
-/
theorem isNontrivialZero_of_mathlib_nontrivialZero
    (hnegInt : NegativeIntegerZeroClassification)
    {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (hs1 : s ≠ 1) :
    IsNontrivialZero s := by
  refine ⟨hz, ?_, re_lt_one_of_riemannZeta_zero hz⟩
  by_cases hnegNat : ∃ n : ℕ, s = -(n : ℂ)
  · obtain ⟨n, hn⟩ := hnegNat
    subst s
    exfalso
    exact htriv (hnegInt n hz)
  · exact re_pos_of_riemannZeta_zero_of_not_neg_nat hz
      (fun n hn => hnegNat ⟨n, hn⟩)

/-- **Experimental terminal configuration theorem.**

The complete current route reaches Mathlib's `RiemannHypothesis` once the
retained finite contradiction and the negative-integer statement seam are
available.  This theorem is a composition surface, not a proof of either
remaining premise. -/
theorem riemannHypothesis_of_terminalConfig
    (hno : NoRegularFirstBadCertificates)
    (hnegInt : NegativeIntegerZeroClassification) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  have hs :
      IsNontrivialZero s :=
    isNontrivialZero_of_mathlib_nontrivialZero
      hnegInt hz htriv hs1
  have hmem : s ∈ zetaZeroConfig.carrier := by
    simpa using hs
  exact criticalLine_of_noRegularFirstBadCertificates hno s hmem

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.criticalLine_of_noRegularFirstBadCertificates
#print axioms Zeta23.ExceptionalZero.re_lt_one_of_riemannZeta_zero
#print axioms Zeta23.ExceptionalZero.re_pos_of_riemannZeta_zero_of_not_neg_nat
#print axioms Zeta23.ExceptionalZero.isNontrivialZero_of_mathlib_nontrivialZero
#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_terminalConfig
