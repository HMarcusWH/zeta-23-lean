# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after theorem PR #137 = fa2f209a6eb8b4059968e8d61239d80588ca256c
live main tree = e3de4dc0377f0124832822b6f97ab5bbd7718640

theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
validated theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI remain authoritative. PR #137 supersedes #136 as theorem-state anchor; PR #117 remains the Control-v2 semantic anchor.

## Recent theorem packages

```text
#129 source-explicit cubic defect + exact cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport + direct zero-shift transfer
#135 documentation/control synchronization only
#136 absolute canonical source energy + scalar-sensitive production decomposition
#137 exact source pairing + one-step determinant reduction + global sign-failure endpoint
```

## Current frontier

```text
A4b1 absolute canonical source energy                            PROVED / #136
A4b2a one-step determinant/sufficiency reduction                 PROVED / #137
A4b2b canonical shell/determinant sign theorem                  OPEN / NOW
A4R   log-lift dense regular-aperture selection                 FALLBACK ONLY
global first-bad domination failure endpoint                    PROVED / #137
negative-root exclusion                                         OPEN
explicit terminal Mathlib RH bridge                             OPEN
RH                                                               OPEN
```

## Exact formal state after #137

For either parity, define

```text
q_c = cubicShellRealEnergy p L N
q_A(w) = intrinsicPredecessorRealEnergy p L N w
b(w) = cubicShellCoupling p L N w
Δ(w) = q_c*q_A(w) - |b(w)|^2.
```

The theorem package now gives exact channel formulas and proves:

```text
Δ(z) >= 0 and Az=0 -> b(z)=0
canonicalOneStepDomination -> exists x0, Ax0=b
canonicalOneStepDomination + predecessor nonnegativity -> Re S0 >= 0
canonicalOneStepDomination -> no safe negative explicit Schur root
```

The global ExceptionalZero wrapper proves:

```text
off-line zeta zero
  -> one global-first-bad predecessor-nonnegative canonical state
  -> NOT canonicalOneStepDomination
  -> q_c < 0 OR exists w, Δ(w) < 0.
```

No theorem proves `q_c>=0`, `Δ(w)>=0` for all `w`, domination, unconditional negative-root exclusion, finite-to-infinite closure, or RH.

## Why #137 matters

The previous target was expressed as a desired coercive inequality. #137 turns that wish into a theorem-checked finite certificate with an exact converse failure witness. The remaining arithmetic problem is therefore sharply localized: an off-line zero must manifest as either negative canonical shell energy or a negative two-dimensional one-step determinant.

This is useful localization, but not a free simplification. Under predecessor nonnegativity, full domination is essentially the missing positivity of the one-step extension. The next theorem must exploit arithmetic structure that generic Hermitian/parity/KKT models do not have.

## Research direction

- derive exact pole/arch/scalar/prime expressions for the shell sign and determinant sign;
- look for a positive Gram/integral representation of the full canonical pairing;
- test the smallest canonical first-bad-compatible states before attempting a universal proof;
- retarget the `omega^7 / omega^9` cancellation lead to the determinant remainder;
- keep A4R as a simplifier only, not as an exclusion argument.

## Firewalls

- RH remains OPEN.
- #136 source energy does not prove positivity.
- #137 domination is conditional; it is not asserted.
- `q_c<0 OR exists Δ<0` is a forced countercertificate under an off-line zero, not a contradiction.
- no termwise source-atom positivity is assumed.
- no `A^-1` at zero.
- no factorwise division by `alpha`, `Gamma`, overlap or source moment.
- D remains algebraic, not unitary/isometric.
- generic countermodels are not canonical CCM counterexamples.
- numerical evidence is not theorem authority.
- machine claim promotion remains separate.

Current research detail: `research/RHRC/RESEARCH_LEADS_POST_137_DELTA.md`.

**RH remains OPEN.**
