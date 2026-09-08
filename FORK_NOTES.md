# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after PR #131 = 436d524d0cdeb5986d76dcbb988f771d19836c55
live main tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a

theorem-state anchor = PR #131 merge 436d524d0cdeb5986d76dcbb988f771d19836c55
validated theorem head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
validated theorem tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a
RHRC #854 = SUCCESS
Permansson #627 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean/compiler/CI remain authoritative. PRs #127/#128/#129/#131 advanced theorem authority only; the latest merged Control-v2 semantic change remains #117.

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
#122 projected metric/resolvent control + E4-A1 zero-resonance classification
#124 zero-shift kernel/range dichotomy + resonant identity/bound
#125 canonical zero-shift Schur endpoint + complete square + Re S0<0
#127 canonical zero-shift shell response
#128 signed regular shell response + canonical resonant pole
#129 source-explicit cubic defect + exact cross-parity secular transfer
#131 exact canonical source-moment decomposition
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
  E4-A2 kernel/range zero-shift dichotomy + endpoint                PROVED / #124-#125
  E4-A3a canonical zero-shift shell response                        PROVED / #127
  E4-A3b signed response + canonical resonant kernel pole           PROVED / #128
  E4-A3c source-explicit cross-parity secular transfer              PROVED / #129
  E4-A4a exact source-moment decomposition                          PROVED / #131

  E4-A4b regular-branch source test                                 NOW
  E4-A4c resonant-branch source test                                NEXT / PARALLEL
  E4-B  parity shifted-nullity from rank-at-most-one algebra        PARALLEL
  E3-C  resolvent identity / secular monotonicity / root uniqueness PARALLEL
  E3-B3 general predecessor-floor deformation theorem               PARALLEL / OPEN

TARGET
  actual canonical first-bad negative-root exclusion
  no off-line zero through existing global reduction
  explicit terminal RH bridge
  RH                                                                 OPEN
```

## Exact post-#131 state

For the projected predecessor block `A=P_W T|_W`, canonical cubic shell vector `c`, coupling `b=Bc`, and safe negative root `lam<0`:

- #127 proves the decoupled zero-shift image `T u0` is exactly one-dimensional shell response and identifies its canonical scalar `sigma0`;
- #128 proves `Re sigma0<0` at the forced root and defines the canonical kernel coordinate `k=K(b)`, with `k=0` in the decoupled branch and `k!=0` plus an exact `1/(-lam)` pole in the resonant branch;
- #129 identifies the cubic defect functional with the actual canonical-source quadratic normal moment and transfers the exact secular equation from even to odd parity, retaining the predecessor correction in `D c+`;
- #131 decomposes that exact source moment into a surviving pole-even profile term, reduced arch diagonal and off-diagonal moments, and a finite von-Mangoldt weighted sum of elementary `sourceMatrix` moments. The index-independent arch scalar is annihilated and the pole odd profile cancels on the even boundary-flat sector.

The global ExceptionalZero wrapper still says that a hypothetical off-line zero forces one global-first-bad finite state carrying the exact source-explicit cross-parity certificate at the same negative explicit root.

Neither the regular nor resonant branch is excluded.

## Highest-leverage next split

### A4b-0 — source-expanded root interface

Compose the #131 identity directly into the #129 transfer theorem so the live equation is

```text
F_- = alpha F_+ + Gamma * explicitCanonicalSourceMoment(u_+).
```

The same tranche should theoremize linearity/negation/scalar covariance of the explicit source moment, isolate the elementary source-atom observable

```text
omega -> quadraticNormalMatrixMoment K (sourceMatrix omega K) v,
```

and theoremize its endpoint zeros at `omega=0,1`.

### Regular branch source exclusion

Combine

```text
k = 0
Re sigma0 < 0
F_- = alpha F_+ + Gamma * explicitCanonicalSourceMoment(u_+)
```

with predecessor nonnegativity and actual source structure. The useful target must be compositional: the raw source moment is linear in `v`, so universal positivity/nonnegativity on the whole vector space is not viable.

### Resonant branch source exclusion

Combine

```text
k != 0
(-lam) K(R_lam b) = k
F_- = alpha F_+ + Gamma * explicitCanonicalSourceMoment(u_+)
```

with the same canonical source formula and first-bad predecessor nonnegativity.

### Global exclusion

Only after both branches are actually excluded may the project claim no canonical first-bad negative root. The existing reduction from an arbitrary off-line zero would then rule out such a zero in the project carrier; the terminal Mathlib RH statement still requires an explicit final bridge.

## Falsification lesson after #131

Generic structural countermodels survive the already-proved shell/Schur/parity/KKT/N-flow framework. #131 adds actual source values, but it also reveals a permanent warning: `explicitCanonicalSourceMoment` is linear in the trial vector. Therefore a universal raw sign theorem is structurally the wrong target.

The next argument should instead test the canonically oriented source/overlap product, the elementary atom as a function of `omega`, or another source-sensitive invariant that depends on the branch/root orientation.

## Firewalls

- RH remains OPEN.
- `ker A` is the projected successor predecessor-block kernel, not the predecessor-size spectrum.
- D is algebraic, not unitary/isometric.
- the predecessor correction in `D c+` may not be dropped.
- no shell invariance is proved.
- no `A^-1` at zero.
- `Re S0<0` and `Re sigma0<0` are not branch exclusion.
- a canonical resonant pole is not automatically contradictory.
- #129/#131 give no useful sign/nonzeroness for `alpha`, `Gamma`, overlap or source moment.
- universal raw source-moment positivity is not a viable route for this linear observable.
- generic structural countermodels refute generic arguments, not the canonical CCM source formula.
- monotonicity/uniqueness is not negative-root exclusion.
- no machine claim-registry promotion follows automatically from #127-#131.
- RH remains OPEN.

Current research detail: `research/RHRC/RESEARCH_LEADS_POST_131_DELTA.md`.
