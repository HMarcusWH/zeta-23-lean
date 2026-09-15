import Zeta23.CCM.SchurEnvelopeDerivative
import Mathlib.Analysis.Complex.Basic

namespace Zeta23.CCM

/-!
# FB-05: Hermitian 2x2 Schur-envelope derivative calculus

The production q13/N2/K3 reduction is complex Hermitian, not merely real
symmetric.  For a Hermitian block with real diagonal coordinates `a,d` and
complex off-diagonal coordinate `b`, the scalar Schur pivot is

  P_H = d - |b|^2 / a,

and the determinant companion is

  Delta_H = a*d - |b|^2.

To keep the compiler-facing calculus in the same real one-variable API already
validated by `SchurEnvelopeDerivative`, the off-diagonal derivative is carried
by separate real and imaginary components.  The exact directional derivative
is

  P_H' = d' - 2 Re(conj(b) b')/a + |b|^2 a'/a^2.

At contact `P_H = 0`, `Delta_H' = a P_H'`; under H1 (`a>0`) the determinant
and Hermitian Schur-pivot derivative orientations therefore agree.

Firewalls:
* this module is generic Hermitian 2x2 algebra/calculus;
* it proves no production arithmetic sign;
* it does not identify or isolate a first-bad contact;
* it does not assert global Schur monotonicity;
* it does not prove negative-root exclusion or RH.
-/

/-- Squared Hermitian off-diagonal magnitude, written in real coordinates so
all downstream quotient differentiation stays in the real calculus API. -/
def hermitianOffdiagSq (b : ℂ) : ℝ :=
  b.re ^ 2 + b.im ^ 2

/-- Hermitian 2x2 Schur pivot. -/
noncomputable def hermitianSchurPivot2x2 (a : ℝ) (b : ℂ) (d : ℝ) : ℝ :=
  d - hermitianOffdiagSq b / a

/-- Determinant companion of the Hermitian block `[[a,conj b],[b,d]]`. -/
def hermitianSchurDet2x2 (a : ℝ) (b : ℂ) (d : ℝ) : ℝ :=
  a * d - hermitianOffdiagSq b

/-- Real-coordinate Hermitian correlation derivative
`Re(conj(b) b')`. -/
def hermitianOffdiagCorrelation
    (b : ℂ) (dbr dbi : ℝ) : ℝ :=
  b.re * dbr + b.im * dbi

/-- Envelope form of the Hermitian Schur-pivot directional derivative. -/
noncomputable def hermitianSchurPivot2x2Derivative
    (a : ℝ) (b : ℂ) (da dbr dbi dd : ℝ) : ℝ :=
  dd - 2 * hermitianOffdiagCorrelation b dbr dbi / a +
    hermitianOffdiagSq b * da / a ^ 2

/-- Direct directional derivative of the Hermitian determinant companion. -/
def hermitianSchurDet2x2Derivative
    (a : ℝ) (b : ℂ) (d : ℝ)
    (da dbr dbi dd : ℝ) : ℝ :=
  da * d + a * dd - 2 * hermitianOffdiagCorrelation b dbr dbi

/-- The Hermitian determinant is exactly `a` times its Schur pivot. -/
theorem hermitianSchurDet2x2_eq_mul_pivot
    (a : ℝ) (b : ℂ) (d : ℝ) (ha : a ≠ 0) :
    hermitianSchurDet2x2 a b d =
      a * hermitianSchurPivot2x2 a b d := by
  unfold hermitianSchurDet2x2 hermitianSchurPivot2x2
  field_simp [ha]

/-- The direct Hermitian determinant derivative factors as the derivative of
`a * P_H`. -/
theorem hermitianSchurDet2x2Derivative_eq_factorized
    (a : ℝ) (b : ℂ) (d : ℝ)
    (da dbr dbi dd : ℝ) (ha : a ≠ 0) :
    hermitianSchurDet2x2Derivative a b d da dbr dbi dd =
      da * hermitianSchurPivot2x2 a b d +
        a * hermitianSchurPivot2x2Derivative a b da dbr dbi dd := by
  unfold hermitianSchurDet2x2Derivative hermitianSchurPivot2x2
    hermitianSchurPivot2x2Derivative
  field_simp [ha]
  ring

/-- Hermitian pivot derivative in determinant-quotient form. -/
theorem hermitianSchurPivot2x2Derivative_eq_detQuotientDerivative
    (a : ℝ) (b : ℂ) (d : ℝ)
    (da dbr dbi dd : ℝ) (ha : a ≠ 0) :
    hermitianSchurPivot2x2Derivative a b da dbr dbi dd =
      (hermitianSchurDet2x2Derivative a b d da dbr dbi dd * a -
          hermitianSchurDet2x2 a b d * da) / a ^ 2 := by
  unfold hermitianSchurPivot2x2Derivative hermitianSchurDet2x2Derivative
    hermitianSchurDet2x2
  field_simp [ha]
  ring

/-- Real-component calculus theorem for the Hermitian Schur pivot.  This avoids
silently treating `|b|^2` as a holomorphic function of a complex parameter. -/
theorem hasDerivAt_hermitianSchurPivot2x2_components
    {a br bi d : ℝ → ℝ}
    {L da dbr dbi dd : ℝ}
    (ha : HasDerivAt a da L)
    (hbr : HasDerivAt br dbr L)
    (hbi : HasDerivAt bi dbi L)
    (hd : HasDerivAt d dd L)
    (ha0 : a L ≠ 0) :
    HasDerivAt
      (fun t : ℝ =>
        hermitianSchurPivot2x2 (a t) ⟨br t, bi t⟩ (d t))
      (hermitianSchurPivot2x2Derivative
        (a L) ⟨br L, bi L⟩ da dbr dbi dd) L := by
  change HasDerivAt
    (fun t : ℝ => d t - (br t ^ 2 + bi t ^ 2) / a t)
    (hermitianSchurPivot2x2Derivative
      (a L) ⟨br L, bi L⟩ da dbr dbi dd) L
  have hsq :
      HasDerivAt
        (fun t : ℝ => br t ^ 2 + bi t ^ 2)
        (2 * br L * dbr + 2 * bi L * dbi) L := by
    convert (hbr.mul hbr).add (hbi.mul hbi) using 1 <;> ring
  have hraw := hd.sub (hsq.div ha ha0)
  have hder :
      dd -
          (((2 * br L * dbr + 2 * bi L * dbi) * a L -
              (br L ^ 2 + bi L ^ 2) * da) /
            (a L) ^ 2) =
        hermitianSchurPivot2x2Derivative
          (a L) ⟨br L, bi L⟩ da dbr dbi dd := by
    unfold hermitianSchurPivot2x2Derivative hermitianOffdiagCorrelation
      hermitianOffdiagSq
    field_simp [ha0]
    ring
  rw [← hder]
  exact hraw

/-- Real-component calculus theorem for the Hermitian determinant companion. -/
theorem hasDerivAt_hermitianSchurDet2x2_components
    {a br bi d : ℝ → ℝ}
    {L da dbr dbi dd : ℝ}
    (ha : HasDerivAt a da L)
    (hbr : HasDerivAt br dbr L)
    (hbi : HasDerivAt bi dbi L)
    (hd : HasDerivAt d dd L) :
    HasDerivAt
      (fun t : ℝ =>
        hermitianSchurDet2x2 (a t) ⟨br t, bi t⟩ (d t))
      (hermitianSchurDet2x2Derivative
        (a L) ⟨br L, bi L⟩ (d L) da dbr dbi dd) L := by
  change HasDerivAt
    (fun t : ℝ => a t * d t - (br t ^ 2 + bi t ^ 2))
    (hermitianSchurDet2x2Derivative
      (a L) ⟨br L, bi L⟩ (d L) da dbr dbi dd) L
  have hsq :
      HasDerivAt
        (fun t : ℝ => br t ^ 2 + bi t ^ 2)
        (2 * br L * dbr + 2 * bi L * dbi) L := by
    convert (hbr.mul hbr).add (hbi.mul hbi) using 1 <;> ring
  have hraw := (ha.mul hd).sub hsq
  have hder :
      da * d L + a L * dd -
          (2 * br L * dbr + 2 * bi L * dbi) =
        hermitianSchurDet2x2Derivative
          (a L) ⟨br L, bi L⟩ (d L) da dbr dbi dd := by
    unfold hermitianSchurDet2x2Derivative hermitianOffdiagCorrelation
      hermitianOffdiagSq
    ring
  rw [← hder]
  exact hraw

/-- At a Hermitian Schur contact the determinant derivative is exactly
`a * P_H'`. -/
theorem hermitianSchurDet2x2Derivative_eq_mul_pivotDerivative_of_contact
    (a : ℝ) (b : ℂ) (d : ℝ)
    (da dbr dbi dd : ℝ)
    (ha : a ≠ 0)
    (hcontact : hermitianSchurPivot2x2 a b d = 0) :
    hermitianSchurDet2x2Derivative a b d da dbr dbi dd =
      a * hermitianSchurPivot2x2Derivative a b da dbr dbi dd := by
  rw [hermitianSchurDet2x2Derivative_eq_factorized
    a b d da dbr dbi dd ha,
    hcontact, mul_zero, zero_add]

/-- Under H1, Hermitian determinant and pivot derivatives have the same
negative orientation at contact. -/
theorem hermitianSchurDet2x2Derivative_neg_iff_pivotDerivative_neg_of_contact
    (a : ℝ) (b : ℂ) (d : ℝ)
    (da dbr dbi dd : ℝ)
    (ha : 0 < a)
    (hcontact : hermitianSchurPivot2x2 a b d = 0) :
    hermitianSchurDet2x2Derivative a b d da dbr dbi dd < 0 ↔
      hermitianSchurPivot2x2Derivative a b da dbr dbi dd < 0 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  rw [hermitianSchurDet2x2Derivative_eq_mul_pivotDerivative_of_contact
    a b d da dbr dbi dd ha0 hcontact]
  constructor <;> intro h <;> nlinarith

/-- Under H1, Hermitian determinant and pivot derivatives have the same
positive orientation at contact. -/
theorem hermitianSchurDet2x2Derivative_pos_iff_pivotDerivative_pos_of_contact
    (a : ℝ) (b : ℂ) (d : ℝ)
    (da dbr dbi dd : ℝ)
    (ha : 0 < a)
    (hcontact : hermitianSchurPivot2x2 a b d = 0) :
    0 < hermitianSchurDet2x2Derivative a b d da dbr dbi dd ↔
      0 < hermitianSchurPivot2x2Derivative a b da dbr dbi dd := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  rw [hermitianSchurDet2x2Derivative_eq_mul_pivotDerivative_of_contact
    a b d da dbr dbi dd ha0 hcontact]
  constructor <;> intro h <;> nlinarith

/-- Real symmetric specialization of the Hermitian pivot. -/
@[simp] theorem hermitianSchurPivot2x2_ofReal
    (a b d : ℝ) :
    hermitianSchurPivot2x2 a (b : ℂ) d = schurPivot2x2 a b d := by
  simp [hermitianSchurPivot2x2, hermitianOffdiagSq, schurPivot2x2]
  ring

/-- Real symmetric specialization of the Hermitian determinant. -/
@[simp] theorem hermitianSchurDet2x2_ofReal
    (a b d : ℝ) :
    hermitianSchurDet2x2 a (b : ℂ) d = schurDet2x2 a b d := by
  simp [hermitianSchurDet2x2, hermitianOffdiagSq, schurDet2x2]
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.hermitianSchurDet2x2_eq_mul_pivot
#print axioms Zeta23.CCM.hasDerivAt_hermitianSchurPivot2x2_components
#print axioms Zeta23.CCM.hermitianSchurDet2x2Derivative_eq_mul_pivotDerivative_of_contact
#print axioms Zeta23.CCM.hermitianSchurDet2x2Derivative_neg_iff_pivotDerivative_neg_of_contact
#print axioms Zeta23.CCM.hermitianSchurDet2x2Derivative_pos_iff_pivotDerivative_pos_of_contact
