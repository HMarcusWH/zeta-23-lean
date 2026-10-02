import Zeta23.CCM.FirstCrossingContactRegime

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#279 first-crossing branch bridge

The canonical first-crossing shell already comes with an exact N-flow contact
regime. This module packages the two predecessor profiles that are actually
proved at the contact:

* first-zero: `k = n`, with a strictly positive predecessor bottom when
  `2 ≤ k`;
* inherited-zero: `n < k`, with predecessor bottom exactly zero.

This is deliberately narrower than the older global-bottom strict/tie branch
packages. No theorem here identifies the selected first-crossing parity with a
global even/odd ground minimum.
-/

inductive FirstCrossingPredecessorProfile
    (c : CanonicalParityFirstCrossingShell) : Prop
  | firstZero
      (hk : c.k = c.n)
      (hprev :
        2 ≤ c.k →
          0 < parityRayleighBottom c.p c.Lstar c.k)
  | inheritedZero
      (hnk : c.n < c.k)
      (hprev :
        parityRayleighBottom c.p c.Lstar c.k = 0)

theorem CanonicalParityFirstCrossingShell.predecessorProfile
    (c : CanonicalParityFirstCrossingShell) :
    FirstCrossingPredecessorProfile c := by
  rcases c.contactRegime with hfirst | hinherited
  · exact .firstZero hfirst (fun hk2 =>
      c.predecessorBottom_pos_of_k_eq_n hk2 hfirst)
  · exact .inheritedZero hinherited
      (c.predecessorBottom_zero_of_n_lt_k hinherited)

theorem CanonicalParityFirstCrossingShell.k_eq_n_or_n_lt_k
    (c : CanonicalParityFirstCrossingShell) :
    c.k = c.n ∨ c.n < c.k := by
  rcases c.contactRegime with hfirst | hinherited
  · exact Or.inl hfirst
  · exact Or.inr hinherited

end Zeta23.CCM

#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.predecessorProfile
#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.k_eq_n_or_n_lt_k
