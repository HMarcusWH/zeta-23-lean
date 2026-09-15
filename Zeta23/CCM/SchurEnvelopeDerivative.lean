import Mathlib.Analysis.Calculus.Deriv.Inv

namespace Zeta23.CCM

/-!
# FB-05: 2x2 Schur-envelope derivative calculus

The q13/N2/K3/even research microscope reduces the relevant successor block to

  H(L) = [[a(L), b(L)],
          [b(L), d(L)]].

Inside H1 (`a(L) > 0`) its Schur pivot is

  P(L) = d(L) - b(L)^2 / a(L),

while the determinant is

  Delta_2(L) = a(L)d(L) - b(L)^2 = a(L) P(L).

This module theoremizes the exact one-variable derivative identity used by the
post-#179 correlation-preserving research graph.  In particular,

  P' = d' - 2 (b/a) b' + (b/a)^2 a',

and this agrees exactly with the determinant-quotient derivative

  P' = (Delta_2' a - Delta_2 a') / a^2.

At a contact `P = 0`, the product identity differentiates to

  Delta_2' = a P'.

Thus, under H1 (`a > 0`), determinant and Schur-pivot derivative orientations
agree at contact.

Firewalls:
* this is generic 2x2 calculus/algebra, not a canonical arithmetic sign law;
* no claim is made that a contact exists or is unique;
* no global Schur monotonicity is asserted;
* no finite-width H1 certification is supplied;
* no first-bad exclusion, negative-root exclusion, or RH theorem is claimed.
-/

/-- Scalar Schur pivot for a real symmetric 2x2 block with nonzero predecessor
entry `a`.  The definition is algebraic and is meaningful even when `a = 0`,
but the derivative/factorization theorems below require `a ≠ 0`. -/
def schurPivot2x2 (a b d : ℝ) : ℝ :=
  d - b * b / a

/-- Determinant of the real symmetric 2x2 block `[[a,b],[b,d]]`. -/
def schurDet2x2 (a b d : ℝ) : ℝ :=
  a * d - b * b

/-- Correlation-preserving / envelope form of the Schur-pivot directional
derivative. -/
def schurPivot2x2Derivative
    (a b da db dd : ℝ) : ℝ :=
  dd - 2 * (b / a) * db + (b / a) ^ 2 * da

/-- Direct derivative of the 2x2 determinant. -/
def schurDet2x2Derivative
    (a b d da db dd : ℝ) : ℝ :=
  da * d + a * dd - 2 * b * db

/-- The determinant is exactly `a` times the Schur pivot whenever `a ≠ 0`. -/
theorem schurDet2x2_eq_mul_pivot
    (a b d : ℝ) (ha : a ≠ 0) :
    schurDet2x2 a b d = a * schurPivot2x2 a b d := by
  unfold schurDet2x2 schurPivot2x2
  field_simp [ha]
  ring

/-- The direct determinant derivative factors as the product-rule derivative of
`a * P`.  This is the algebraic bridge used for contact-local orientation. -/
theorem schurDet2x2Derivative_eq_factorized
    (a b d da db dd : ℝ) (ha : a ≠ 0) :
    schurDet2x2Derivative a b d da db dd =
      da * schurPivot2x2 a b d +
        a * schurPivot2x2Derivative a b da db dd := by
  unfold schurDet2x2Derivative schurPivot2x2 schurPivot2x2Derivative
  field_simp [ha]
  ring

/-- The envelope derivative is exactly the quotient-rule derivative currently
used by the finite q13/Q14 certifier. -/
theorem schurPivot2x2Derivative_eq_detQuotientDerivative
    (a b d da db dd : ℝ) (ha : a ≠ 0) :
    schurPivot2x2Derivative a b da db dd =
      (schurDet2x2Derivative a b d da db dd * a -
          schurDet2x2 a b d * da) / a ^ 2 := by
  unfold schurPivot2x2Derivative schurDet2x2Derivative schurDet2x2
  field_simp [ha]
  ring

/-- Calculus theorem for the 2x2 Schur pivot.  The optimizer/correlation terms
are retained in the envelope form instead of expanding them into a
cancellation-heavy determinant quotient. -/
theorem hasDerivAt_schurPivot2x2
    {a b d : ℝ → ℝ} {L da db dd : ℝ}
    (ha : HasDerivAt a da L)
    (hb : HasDerivAt b db L)
    (hd : HasDerivAt d dd L)
    (ha0 : a L ≠ 0) :
    HasDerivAt
      (fun t : ℝ => schurPivot2x2 (a t) (b t) (d t))
      (schurPivot2x2Derivative (a L) (b L) da db dd) L := by
  have hbb :
      HasDerivAt (fun t : ℝ => b t * b t)
        (db * b L + b L * db) L := by
    simpa using hb.mul hb
  have hquot :
      HasDerivAt (fun t : ℝ => (b t * b t) / a t)
        (((db * b L + b L * db) * a L - (b L * b L) * da) /
          (a L) ^ 2) L := by
    simpa using hbb.div ha ha0
  have hraw :
      HasDerivAt (fun t : ℝ => d t - (b t * b t) / a t)
        (dd - (((db * b L + b L * db) * a L - (b L * b L) * da) /
          (a L) ^ 2)) L := by
    simpa using hd.sub hquot
  have hder :
      dd - (((db * b L + b L * db) * a L - (b L * b L) * da) /
          (a L) ^ 2) =
        schurPivot2x2Derivative (a L) (b L) da db dd := by
    unfold schurPivot2x2Derivative
    field_simp [ha0]
    ring
  rw [hder] at hraw
  simpa [schurPivot2x2] using hraw

/-- Calculus theorem for the determinant companion. -/
theorem hasDerivAt_schurDet2x2
    {a b d : ℝ → ℝ} {L da db dd : ℝ}
    (ha : HasDerivAt a da L)
    (hb : HasDerivAt b db L)
    (hd : HasDerivAt d dd L) :
    HasDerivAt
      (fun t : ℝ => schurDet2x2 (a t) (b t) (d t))
      (schurDet2x2Derivative (a L) (b L) (d L) da db dd) L := by
  have hraw :
      HasDerivAt
        (fun t : ℝ => a t * d t - b t * b t)
        (da * d L + a L * dd - (db * b L + b L * db)) L := by
    simpa using (ha.mul hd).sub (hb.mul hb)
  have hder :
      da * d L + a L * dd - (db * b L + b L * db) =
        schurDet2x2Derivative (a L) (b L) (d L) da db dd := by
    unfold schurDet2x2Derivative
    ring
  rw [hder] at hraw
  simpa [schurDet2x2] using hraw

/-- At a Schur contact `P = 0`, the determinant derivative is exactly `a P'`.
This is the contact-local identity needed by the FB-05 orientation-clash route. -/
theorem schurDet2x2Derivative_eq_mul_pivotDerivative_of_contact
    (a b d da db dd : ℝ)
    (ha : a ≠ 0)
    (hcontact : schurPivot2x2 a b d = 0) :
    schurDet2x2Derivative a b d da db dd =
      a * schurPivot2x2Derivative a b da db dd := by
  rw [schurDet2x2Derivative_eq_factorized a b d da db dd ha,
    hcontact, mul_zero, zero_add]

/-- Under H1, determinant and Schur-pivot derivatives have the same negative
orientation at a contact. -/
theorem schurDet2x2Derivative_neg_iff_pivotDerivative_neg_of_contact
    (a b d da db dd : ℝ)
    (ha : 0 < a)
    (hcontact : schurPivot2x2 a b d = 0) :
    schurDet2x2Derivative a b d da db dd < 0 ↔
      schurPivot2x2Derivative a b da db dd < 0 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  rw [schurDet2x2Derivative_eq_mul_pivotDerivative_of_contact
    a b d da db dd ha0 hcontact]
  constructor <;> intro h <;> nlinarith

/-- Under H1, determinant and Schur-pivot derivatives have the same positive
orientation at a contact. -/
theorem schurDet2x2Derivative_pos_iff_pivotDerivative_pos_of_contact
    (a b d da db dd : ℝ)
    (ha : 0 < a)
    (hcontact : schurPivot2x2 a b d = 0) :
    0 < schurDet2x2Derivative a b d da db dd ↔
      0 < schurPivot2x2Derivative a b da db dd := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  rw [schurDet2x2Derivative_eq_mul_pivotDerivative_of_contact
    a b d da db dd ha0 hcontact]
  constructor <;> intro h <;> nlinarith

end Zeta23.CCM
