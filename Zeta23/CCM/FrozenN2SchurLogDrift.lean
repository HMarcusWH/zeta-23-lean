import Zeta23.CCM.HermitianSchurEnvelopeDerivative
import Zeta23.CCM.CubicShellIncidence
import Zeta23.CCM.FrozenIntrinsicPredecessorComplex

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# FB-05: lifted production parity block and N2 Hermitian log drift

The frozen-source infrastructure already proves the exact ambient decomposition

  M_Q(L) = -log(L) I + R_Q(L)

and its production parity-compressed counterpart.  This module lifts the *full
parity-compressed* family to the logarithmic cover, not merely the intrinsic
predecessor block:

  M~_{Q,p,N}(z) = -z I + R~_{Q,p,N}(z).

That is the correct interface for the q13/N2/K3 Schur block because its shell
coordinate and predecessor-shell coupling live outside the predecessor-only
operator.

On the real logarithmic axis, whenever `exp t` stays in one physical fixed-Q
cutoff cell, the lifted family is exactly the actual production parity
compression.  The scalar Schur derivative is then split algebraically into a
universal negative log drift plus a remainder-envelope derivative.

The N2 specialization records the exact predecessor/shell geometry used by the
q13/K3 microscope: every successor vector decomposes into predecessor plus
shell, the cubic shell vector is nonzero, and it is orthogonal to every
predecessor vector.

Firewalls:
* no remainder sign or domination estimate is proved here;
* no optimizer/minimizer existence theorem is asserted;
* no contact existence or uniqueness is asserted;
* no global Schur monotonicity, negative-root exclusion, or RH theorem is
  claimed.
-/

/-- Full frozen parity-compressed production family on the logarithmic cover.
The only nonperiodic term is the exact scalar `-z * id`. -/
def liftedFrozenParityCompressedCanonical
    (Q : ℕ) (p : ReversalParity) (z : ℂ) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p N →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p N :=
  (-z) • LinearMap.id +
    complexFrozenParityCompressedRemainder Q p (Complex.exp z) N

/-- Exact real-log production bridge at every point whose exponential remains
inside the selected fixed-Q cutoff cell. -/
theorem liftedFrozenParityCompressedCanonical_ofReal_of_exp_mem_fixedCell
    {Q : ℕ} (hQ : 1 ≤ Q)
    (p : ReversalParity) (N : ℕ)
    {t : ℝ}
    (ht : Real.exp t ∈ fixedCanonicalCutoffCell Q) :
    liftedFrozenParityCompressedCanonical Q p (t : ℂ) N =
      parityCompressedCanonical p (Real.exp t) N := by
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have hexpC : Complex.exp (t : ℂ) = (Real.exp t : ℂ) := by
    simpa using (Complex.ofReal_exp t).symm
  rw [liftedFrozenParityCompressedCanonical, hexpC,
    complexFrozenParityCompressedRemainder_ofReal Q p hpos N]
  rw [← frozenParityCompressedCanonical_eq_actual_fixedCell hQ ht p N,
    frozenParityCompressedCanonical_eq_neg_log_id_add_remainder Q p N hpos,
    Real.log_exp]

/-- Equivalent fixed-cell bridge written at the physical aperture `L` itself. -/
theorem liftedFrozenParityCompressedCanonical_of_log_fixedCell
    {Q : ℕ} (hQ : 1 ≤ Q)
    {L : ℝ} (hL : L ∈ fixedCanonicalCutoffCell Q)
    (p : ReversalParity) (N : ℕ) :
    liftedFrozenParityCompressedCanonical Q p (Real.log L : ℂ) N =
      parityCompressedCanonical p L N := by
  have hpos : 0 < L := fixedCanonicalCutoffCell_subset_Ioi hQ hL
  have hexp : Real.exp (Real.log L) = L := Real.exp_log hpos
  have h :=
    liftedFrozenParityCompressedCanonical_ofReal_of_exp_mem_fixedCell
      hQ p N (t := Real.log L) (by simpa [hexp] using hL)
  simpa [hexp] using h

/-- The lifted full parity family has the same deck law as the predecessor
lift: one logarithmic turn subtracts exactly `2*pi*i` times the identity. -/
theorem liftedFrozenParityCompressedCanonical_add_two_pi_I
    (Q : ℕ) (p : ReversalParity) (z : ℂ) (N : ℕ) :
    liftedFrozenParityCompressedCanonical Q p
        (z + 2 * (Real.pi : ℂ) * Complex.I) N =
      liftedFrozenParityCompressedCanonical Q p z N -
        (2 * (Real.pi : ℂ) * Complex.I) • LinearMap.id := by
  unfold liftedFrozenParityCompressedCanonical
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  module

/-- Squared envelope norm in orthogonal predecessor/shell coordinates.  In the
production N2 geometry, `wSq` and `cSq` become the squared predecessor and
shell norms and orthogonality removes the cross term. -/
noncomputable def hermitianEnvelopeNormSq
    (a : ℝ) (b : ℂ) (wSq cSq : ℝ) : ℝ :=
  cSq + hermitianOffdiagSq b * wSq / a ^ 2

/-- Remainder contribution to the Hermitian envelope derivative after the
universal log drift is removed from the predecessor and shell diagonals. -/
noncomputable def hermitianRemainderEnvelopeDerivative
    (a : ℝ) (b : ℂ)
    (daR dbr dbi ddR : ℝ) : ℝ :=
  ddR - 2 * hermitianOffdiagCorrelation b dbr dbi / a +
    hermitianOffdiagSq b * daR / a ^ 2

/-- Exact algebraic log-drift split for the Hermitian Schur derivative.  If
`a' = -wSq + a_R'`, `b' = b_R'`, and `d' = -cSq + d_R'`, then

  P' = - envelopeNormSq + remainderEnvelopeDerivative.

No sign estimate on the remainder term is assumed. -/
theorem hermitianSchurPivot2x2Derivative_eq_neg_envelopeNormSq_add_remainder
    (a : ℝ) (b : ℂ)
    (wSq cSq daR dbr dbi ddR : ℝ) :
    hermitianSchurPivot2x2Derivative
        a b (-wSq + daR) dbr dbi (-cSq + ddR) =
      -hermitianEnvelopeNormSq a b wSq cSq +
        hermitianRemainderEnvelopeDerivative a b daR dbr dbi ddR := by
  unfold hermitianSchurPivot2x2Derivative hermitianEnvelopeNormSq
    hermitianRemainderEnvelopeDerivative
  ring

/-- Pointwise corollary: if the remainder-envelope derivative is strictly
smaller than the envelope norm square, then the Hermitian Schur pivot has
strictly negative log-coordinate derivative.  This is only an implication;
this module does not prove the production bound. -/
theorem hermitianSchurPivot2x2Derivative_neg_of_remainder_lt_envelopeNormSq
    (a : ℝ) (b : ℂ)
    (wSq cSq daR dbr dbi ddR : ℝ)
    (hdom :
      hermitianRemainderEnvelopeDerivative a b daR dbr dbi ddR <
        hermitianEnvelopeNormSq a b wSq cSq) :
    hermitianSchurPivot2x2Derivative
        a b (-wSq + daR) dbr dbi (-cSq + ddR) < 0 := by
  rw [hermitianSchurPivot2x2Derivative_eq_neg_envelopeNormSq_add_remainder]
  linarith

/-- Canonical N2 cubic shell vector used by the q13/K3 production geometry. -/
def intrinsicN2CubicShellVector
    (p : ReversalParity) : intrinsicParitySuccShell p 2 :=
  intrinsicCubicShellPart p 2

/-- The canonical N2 cubic shell coordinate is genuinely nonzero. -/
theorem intrinsicN2CubicShellVector_ne_zero
    (p : ReversalParity) :
    intrinsicN2CubicShellVector p ≠ 0 := by
  exact intrinsicCubicShellPart_ne_zero p 2 (by norm_num)

/-- Every K3 successor vector decomposes exactly into its N2 predecessor part
plus its one-step shell part. -/
theorem intrinsicN2_predecessor_add_shell_reconstructs
    (p : ReversalParity)
    (v : euclideanParityBoundaryFlatSubspace p 3) :
    ((intrinsicPredecessorPart p 2 v :
        intrinsicParityPredecessorSubspace p 2) :
      euclideanParityBoundaryFlatSubspace p 3) +
      ((intrinsicShellPart p 2 v : intrinsicParitySuccShell p 2) :
        euclideanParityBoundaryFlatSubspace p 3) = v := by
  simpa using intrinsicPredecessorPart_add_shellPart p 2 v

/-- The canonical N2 cubic shell vector is orthogonal to every predecessor
vector.  This is the exact reason the scalar `-z I` contributes no universal
log drift to the predecessor-shell off-diagonal coordinate. -/
theorem inner_intrinsicN2CubicShellVector_predecessor_eq_zero
    (p : ReversalParity)
    (w : intrinsicParityPredecessorSubspace p 2) :
    inner ℂ
      ((intrinsicN2CubicShellVector p : intrinsicParitySuccShell p 2) :
        euclideanParityBoundaryFlatSubspace p 3)
      ((w : intrinsicParityPredecessorSubspace p 2) :
        euclideanParityBoundaryFlatSubspace p 3) = 0 := by
  exact inner_intrinsicShell_predecessor_eq_zero
    p 2 (intrinsicN2CubicShellVector p) w

end Zeta23.CCM

#print axioms Zeta23.CCM.liftedFrozenParityCompressedCanonical_of_log_fixedCell
#print axioms Zeta23.CCM.liftedFrozenParityCompressedCanonical_add_two_pi_I
#print axioms Zeta23.CCM.hermitianSchurPivot2x2Derivative_eq_neg_envelopeNormSq_add_remainder
#print axioms Zeta23.CCM.hermitianSchurPivot2x2Derivative_neg_of_remainder_lt_envelopeNormSq
#print axioms Zeta23.CCM.intrinsicN2CubicShellVector_ne_zero
#print axioms Zeta23.CCM.inner_intrinsicN2CubicShellVector_predecessor_eq_zero
