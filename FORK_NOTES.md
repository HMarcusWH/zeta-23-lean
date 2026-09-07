# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after PR #122 = b2d1210902d430f3cdd3c24c2961ab843469b5d6
live main tree = db51419fb7cc8b2e3dbe5cf2e770390086db9862

theorem-state anchor = PR #122 merge b2d1210902d430f3cdd3c24c2961ab843469b5d6
validated theorem head = 9c8154e3ea7a5762f8e65d508dc68bb9246db869
E3-B1 secular metric control + E4-A1 zero-resonance coupling classification = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean/compiler/CI remain authoritative. PRs #118/#119/#121/#122 advance theorem authority only; the latest merged Control-v2 change remains #117.

## Recent theorem packages

```text
#94  F1 canonical finite negative obstruction
#96  constrained canonical algebra
#98  Euclidean constrained sector
#100 exact centered N-flow + fixed-L negative tail
#102 exact reversal symmetry + even commutator collapse
#103 exact parity geometry + algebraic D-equivalence
#105 least bad parity size + 1d successor shell
#107 parity compression + genuine negative eigenmode + non-inheritance
#109 nonzero shell projection + exact parity normals + KKT
#110 cubic parity channel + rank-at-most-one compressed parity defect
#112 global first bad + intrinsic shell + exact cubic factorization
#113 intrinsic direct sum + shifted inverse + scalar Schur identity
#115 canonical cubic shell incidence
#118 canonical cubic quotient coordinate + normalized Schur
#119 exact canonical quotient-secular root/eigenmode equivalence
#121 exact explicit cubic Schur scalar bridge
#122 projected metric/resolvent control + E4-A1 zero-resonance coupling classification
```

## Current frontier

```text
FIRST-BAD-RIGIDITY-E
  E1    cubic-shell incidence                                      PROVED / #115
  E2    canonical cubic coordinate + normalized Schur              PROVED / #118
  E3-A  exact quotient secular root <-> eigenmode                   PROVED / #119
  E3-B2 exact explicit Schur bridge                                 PROVED / #121
  E3-B1 projected symmetry/coercivity/resolvent metric control      PROVED / #122
  E4-A1 ker(A) cubic-coupling classification                        PROVED / #122

  E4-A2 zero-shift/range-endpoint split                             NOW
  E3-C  resolvent identity / secular monotonicity / root uniqueness PARALLEL
  E4-B  parity shifted-nullity from rank-at-most-one algebra        PARALLEL
  E3-B3 general predecessor-floor deformation theorem               PARALLEL / OPEN

TARGET
  CCM-specific negative-root exclusion
  positivity / finite-to-infinite closure                           OPEN
  RH                                                                 OPEN
```

## What #121/#122 changed

#121 proved, for the canonical negative-shift trial problem,

```text
F(lam) = star(S(lam)) / <c,c>
```

where `F` is the exact quotient-coordinate root detector and

```text
S(lam)=<Tc,c>-lam<c,c>-<R_lam Bc,Bc>.
```

#122 then theoremized projected predecessor symmetry, negative-shift coercivity, resolvent symmetry/norm/quadratic bounds, nonnegative real resolvent quadratic values, and realness of `S`. Thus on the safe negative axis the exact bridge becomes

```text
F(lam)=S(lam)/<c,c>.
```

At a root #122 also proves the first denominator-free metric bound

```text
0 <= Re(<Tc,c>-lam<c,c>)
(-lam) * Re(<Tc,c>-lam<c,c>) <= ||Bc||^2.
```

## E4-A1 settlement

For `A=P_W T|_W`, `c=intrinsicCubicShellPart`, `b=Bc`, #122 proves that if `Az=0` then the full successor image `Tz` lies in the one-dimensional shell and

```text
<z,b> = star(kappa(Tz)) <c,c>.
```

Hence

```text
Az=0 -> (<z,b>=0 <-> Tz=0).
```

The quantified theorem says that `b` annihilates all of `ker A` iff every vector in `ker A` is already a genuine successor zero mode.

This does **not** decide whether either side holds for the actual global-first-bad state.

## Highest-leverage next split

### Decoupled branch

If `b` annihilates `ker A`, use finite-dimensional symmetry to prove `b ∈ range A` and obtain a zero-shift witness `x₀` satisfying `A x₀=b`. This is the correct algebraic endpoint; do not introduce `A^-1` at zero.

### Resonant branch

If some `z∈ker A` has `<z,b>!=0`, #122 says that vector is not a successor zero mode. The next theorem should expose the corresponding zero-resonant contribution to the shifted resolvent/secular scalar near `lam=0-`.

### Parallel monotonicity

The scalar representation is now real and exact, so E3-C can proceed. A monotonicity theorem may yield at most one negative root, but uniqueness remains strictly weaker than exclusion.

## Small upstream cleanup opportunity

`re_inner_shiftedIntrinsicPredecessorBlock_ge` currently carries `lam<0` although its quadratic comparison itself is algebraic from predecessor nonnegativity; negativity is needed later to turn `-lam` into a positive coercive floor. A future cleanup may split/generalize that theorem to reduce dependency debt. This is not required before E4-A2.

## Firewalls

- RH remains OPEN.
- `ker A` is the projected successor predecessor-block kernel, not the predecessor-size spectrum.
- E4-A1 is a classification, not a decoupling theorem.
- D is algebraic, not unitary/isometric.
- no shell invariance is proved.
- no `A^-1` at zero.
- monotonicity/uniqueness is not negative-root exclusion.
- no source-normalization or machine claim-registry promotion follows from #121/#122.
- positivity / finite-to-infinite closure / RH remain OPEN.

Current research detail: `research/RHRC/RESEARCH_LEADS_POST_122_DELTA.md`.

**RH remains OPEN.**