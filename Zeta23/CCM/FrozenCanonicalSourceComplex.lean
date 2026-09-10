import Zeta23.CCM.CanonicalApertureComplexBridge
import Zeta23.CCM.CanonicalApertureComplexSource
import Zeta23.CCM.FrozenCanonicalSourceAnalytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section

namespace Zeta23.CCM

open Complex Matrix MeasureTheory Set Filter
open scoped BigOperators Interval ArithmeticFunction

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1b: complex frozen source remainder

This module assembles the complex aperture primitives into a single-valued
complex continuation of the *remainder* after the exact production `-log L`
scalar has been removed.  Every channel is theorem-locked to the real frozen
production source on `L > 0`.

The explicit logarithm in the physical decomposition is deliberately not
complexified here.  It will become `-z` only after passing to the logarithmic
cover `L = exp z`.

No determinant nonidentity, dense regularity, energy sign, negative-root
exclusion, or RH claim is made here.
-/

/-- Complex direct equation-(4.4) archimedean entry after removing only the
index-independent production `wCorrection`. -/
def complexCanonicalArchWithoutWComponent (n m : ℤ) (z : ℂ) : ℂ :=
  if n = m then
    2 * complexGammaCore n z - 2 * complexBetaCore n z
  else
    (complexAlphaCore m z - complexAlphaCore n z) / ((n - m : ℤ) : ℂ)

/-- Exact positive-real-axis agreement of the `wCorrection`-free archimedean
entry. -/
@[simp] theorem complexCanonicalArchWithoutWComponent_ofReal
    (n m : ℤ) {L : ℝ} (hL : 0 < L) :
    complexCanonicalArchWithoutWComponent n m (L : ℂ) =
      (canonicalArchWithoutWComponent n m L : ℂ) := by
  by_cases hnm : n = m
  · subst m
    simp [complexCanonicalArchWithoutWComponent,
      canonicalArchWithoutWComponent, hL]
    push_cast
  · simp [complexCanonicalArchWithoutWComponent,
      canonicalArchWithoutWComponent, hnm, hL]
    push_cast

/-- Centered finite complex archimedean remainder matrix. -/
def complexCanonicalArchWithoutWMatrix (z : ℂ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    complexCanonicalArchWithoutWComponent
      (centeredIndex K i) (centeredIndex K j) z

/-- Exact positive-real-axis agreement of the finite archimedean remainder. -/
@[simp] theorem complexCanonicalArchWithoutWMatrix_ofReal
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    complexCanonicalArchWithoutWMatrix (L : ℂ) K =
      canonicalArchWithoutWMatrix L K := by
  ext i j
  simp [complexCanonicalArchWithoutWMatrix,
    canonicalArchWithoutWMatrix, hL]

/-- Branch-sensitive scalar factor appearing in the #140 aperture remainder.
The physical base domain excludes zero; no artificial value is assigned there. -/
def complexApertureScalarFactor (z : ℂ) : ℂ :=
  z * ((Complex.exp z + 1) / (Complex.exp z - 1))

/-- Exact real-axis agreement of the scalar factor. -/
@[simp] theorem complexApertureScalarFactor_ofReal (L : ℝ) :
    complexApertureScalarFactor (L : ℂ) =
      ((L * ((Real.exp L + 1) / (Real.exp L - 1)) : ℝ) : ℂ) := by
  unfold complexApertureScalarFactor
  rw [← Complex.ofReal_exp]
  push_cast

/-- Complex continuation of the scalar remainder, using the principal complex
log only on domains where `complexApertureScalarFactor z ∈ Complex.slitPlane`.
The domain condition is stated separately in the analytic layer. -/
def complexApertureScalarRemainder (z : ℂ) : ℂ :=
  Complex.log (complexApertureScalarFactor z) -
    ((Real.eulerMascheroniConstant + Real.log (4 * Real.pi) : ℝ) : ℂ)

/-- Exact positive-real-axis agreement with the already-proved #140 scalar
remainder. -/
@[simp] theorem complexApertureScalarRemainder_ofReal
    {L : ℝ} (hL : 0 < L) :
    complexApertureScalarRemainder (L : ℂ) =
      (canonicalApertureScalarRemainder L : ℂ) := by
  have hExp : 1 < Real.exp L := Real.one_lt_exp_iff.mpr hL
  have hfactor :
      0 < L * ((Real.exp L + 1) / (Real.exp L - 1)) := by
    have hnum : 0 < Real.exp L + 1 := by positivity
    have hden : 0 < Real.exp L - 1 := sub_pos.mpr hExp
    positivity
  unfold complexApertureScalarRemainder canonicalApertureScalarRemainder
  rw [complexApertureScalarFactor_ofReal,
    ← Complex.ofReal_log hfactor.le]
  push_cast

/-- Full complex continuation of the frozen source remainder. -/
def complexFrozenCanonicalSourceRemainder
    (Q : ℕ) (z : ℂ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  complexCanonicalPoleMatrix z K -
    complexCanonicalArchWithoutWMatrix z K -
      complexFrozenCanonicalPrimeMatrix Q z K +
        complexApertureScalarRemainder z •
          (1 : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)

/-- Exact positive-real-axis agreement of the full complex remainder with the
real frozen production remainder used in the `-log L` split. -/
@[simp] theorem complexFrozenCanonicalSourceRemainder_ofReal
    (Q : ℕ) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    complexFrozenCanonicalSourceRemainder Q (L : ℂ) K =
      frozenCanonicalSourceRemainderReal Q L K := by
  unfold complexFrozenCanonicalSourceRemainder
  rw [complexCanonicalPoleMatrix_ofReal,
    complexCanonicalArchWithoutWMatrix_ofReal hL,
    complexFrozenCanonicalPrimeMatrix_ofReal,
    complexApertureScalarRemainder_ofReal hL]
  rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.complexCanonicalArchWithoutWMatrix_ofReal
#print axioms Zeta23.CCM.complexApertureScalarRemainder_ofReal
#print axioms Zeta23.CCM.complexFrozenCanonicalSourceRemainder_ofReal
