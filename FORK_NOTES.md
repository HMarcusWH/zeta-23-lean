# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

~~~text
theorem-state anchor = PR #113 merge d3b62817711c4c97f0d817c8b4a4ac0bc646d733
validated theorem head = 2da46eed0068613d904bc67e20790f46bc46818e
validated theorem tree = 066f5f51041b302dfa1a66d84a024660a09acbf5
theorem-bearing merged through = PR #113
RHRC #761 = SUCCESS
Permansson #534 = SUCCESS
CCM/ExceptionalZero/no-placeholder/source-firewall gates = SUCCESS
RH = OPEN
~~~

## Recent theorem packages

~~~text
#94  F1 canonical finite negative obstruction
#96  constrained canonical algebra
#98  Euclidean constrained sector
#100 exact centered N-flow + fixed-L negative tail
#102 exact reversal symmetry + even commutator collapse
#103 exact parity geometry + algebraic D-equivalence
#105 fixed-parity bad tail + least bad size + 1D successor shell
#107 parity compression + genuine negative eigenmode + non-inheritance
#109 nonzero ambient shell projection + exact parity normals + KKT
#110 cubic parity channel + rank-at-most-one compressed parity defect
#112 global first bad + intrinsic shell + exact cubic factorization
#113 intrinsic direct sum + shifted inverse + scalar Schur identity
~~~

## Current frontier

~~~text
FIRST-BAD-RIGIDITY-E
  E1  cubic generator vs intrinsic N-flow shell
      prove non-membership in centered predecessor W
      -> canonical cubic shell coordinate != 0
  E1b use dim_C S=1 to identify cubic/eigenmode shell lines
  E2  cubic-normalized scale-free Schur equation
  E3  projected predecessor symmetry + shifted coercivity/resolvent control
  E4  parity nullity + common-resonance / one-channel-resolvent dichotomy
  THEN classify or exclude the remaining global first-bad state
~~~

The key post-#113 simplification is `intrinsicShellPart x = 0 <-> x ∈ W`. Shell/cubic incidence no longer requires comparing two ad hoc ambient projections: it can be attacked by proving that the cubic generator (or its algebraic even pullback) is not a centered predecessor extension.

Current high-value hypothesis: derive the exact odd projection formula `g_K=d^3-alpha_K d`, check `alpha_K=(3K^2+3K-1)/5`, and use the predicted outer coefficient `K(K-1)(2K-1)/5` to prove non-membership for `K>=2`. This is a **LEAD**, not a theorem, until it is derived from the repository's exact orthogonal projection and indexing conventions.

Firewalls remain: D is algebraic rather than unitary; exact factorization does not prove the defect functional nonzero; shell nonzero does not mean pure shell; no `A^-1` at zero; no negative-index-one, resonance-exclusion, positivity, finite-to-infinite or RH theorem has been promoted.

Current research detail: `research/RHRC/RESEARCH_LEADS_POST_113_DELTA.md`.

**RH remains OPEN.**
