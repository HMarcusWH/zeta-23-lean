import Zeta23.CCM.CanonicalParityFirstCrossingShell

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#278 first-crossing contact regimes

The least right-crossing index `k` lies in the exact zero plateau starting
at `n`. There are therefore two genuinely different contact regimes:

* `k = n`: the responsible successor is the first zero-plateau size;
* `n < k`: the immediately smaller parity bottom is itself already on the
  zero plateau.

This file records only that exact N-flow dichotomy. It deliberately does not
identify a selected-parity first contact with the global even/odd ground
minimum, and it does not infer projected-block determinant regularity without
the required bridge.
-/

inductive FirstCrossingContactRegime
    (c : CanonicalParityFirstCrossingShell) : Prop
  | firstZero (h : c.k = c.n)
  | inheritedZero (h : c.n < c.k)

theorem CanonicalParityFirstCrossingShell.contactRegime
    (c : CanonicalParityFirstCrossingShell) :
    FirstCrossingContactRegime c := by
  rcases lt_or_eq_of_le c.n_le_k with hlt | heq
  · exact .inheritedZero hlt
  · exact .firstZero heq.symm

theorem CanonicalParityFirstCrossingShell.predecessorBottom_pos_of_k_eq_n
    (c : CanonicalParityFirstCrossingShell)
    (hk2 : 2 ≤ c.k)
    (hkn : c.k = c.n) :
    0 < parityRayleighBottom c.p c.Lstar c.k := by
  have hj1 : 1 ≤ c.k - 1 := by omega
  have hjn : c.k - 1 < c.n := by omega
  have hpos := c.below_strict_positive (c.k - 1) hj1 hjn
  have hsucc : c.k - 1 + 1 = c.k := by omega
  simpa [paritySuccessorGround, hsucc] using hpos

theorem CanonicalParityFirstCrossingShell.predecessorBottom_zero_of_n_lt_k
    (c : CanonicalParityFirstCrossingShell)
    (hnk : c.n < c.k) :
    parityRayleighBottom c.p c.Lstar c.k = 0 := by
  have hjn : c.n ≤ c.k - 1 := by omega
  have hjN : c.k - 1 ≤ c.N :=
    le_trans (Nat.sub_le c.k 1) c.k_le_N
  have hzero := c.plateau_zero (c.k - 1) hjn hjN
  have hsucc : c.k - 1 + 1 = c.k := by omega
  simpa [paritySuccessorGround, hsucc] using hzero

end Zeta23.CCM

#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.contactRegime
#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.predecessorBottom_pos_of_k_eq_n
#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.predecessorBottom_zero_of_n_lt_k
