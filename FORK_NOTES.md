# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after PR #129 = e1192857afed9f68fa4a13143ce690b62191b997
live main tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7

theorem-state anchor = PR #129 merge e1192857afed9f68fa4a13143ce690b62191b997
validated theorem head = 440be3e5b6bf05e94ae2c65b1704d52d20acc9af
validated theorem tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7
RHRC #838 = SUCCESS
Permansson #611 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean/compiler/CI remain authoritative. PRs #127/#128/#129 advanced theorem authority only; the latest merged Control-v2 semantic change remains #117.

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

  E4-A4 canonical-source branch exclusion                           NOW
  E4-B  parity shifted-nullity from rank-at-most-one algebra        PARALLEL
  E3-C  resolvent identity / secular monotonicity / root uniqueness PARALLEL
  E3-B3 general predecessor-floor deformation theorem               PARALLEL / OPEN

TARGET
  actual canonical first-bad negative-root exclusion
  no off-line zero through existing global reduction
  explicit terminal RH bridge
  RH                                                                 OPEN
```

## Exact post-#129 state

For the projected predecessor block `A=P_W T|_W`, canonical cubic shell vector `c`, coupling `b=Bc`, and safe negative root `lam<0`:

- #127 proves the decoupled zero-shift image `T u0` is exactly one-dimensional shell response and identifies its canonical scalar `sigma0`;
- #128 proves `Re sigma0<0` at the forced root and defines the canonical kernel coordinate `k=K(b)`, with `k=0` in the decoupled branch and `k!=0` plus an exact `1/(-lam)` pole in the resonant branch;
- #129 identifies the cubic defect functional with the actual canonical-source quadratic normal moment and transfers the exact secular equation from even to odd parity, retaining the predecessor correction in `D c+`.

The global ExceptionalZero wrapper now says that a hypothetical off-line zero forces one global-first-bad finite state carrying the exact source-explicit cross-parity certificate at the same negative explicit root.

Neither the regular nor resonant branch is excluded.

## Highest-leverage next split

### Canonical-source moment decomposition

Open the exact production definition of `canonicalSourceMatrix` inside

```text
<n2, canonicalSourceMatrix(L,N+1) u+>.
```

The target is an exact decomposition/cancellation identity before any estimate. #129 has already exposed the correct source-sensitive scalar; the next job is to understand what the real CCM formula forces it to do.

### Regular branch source exclusion

Combine the theorem-backed package

```text
k = 0
Re sigma0 < 0
F_- = alpha F_+ + Gamma * sourceMoment(u_+)
```

with actual source structure. Do not assume or divide by `alpha`, `Gamma`, the overlap or the source moment.

### Resonant branch source exclusion

Combine

```text
k != 0
(-lam) K(R_lam b) = k
F_- = alpha F_+ + Gamma * sourceMoment(u_+)
```

with the same canonical source formula and first-bad predecessor nonnegativity.

### Global exclusion

Only after both branches are actually excluded may the project claim no canonical first-bad negative root. The existing reduction from an arbitrary off-line zero would then make the zeta-zero implication immediate; the terminal Mathlib RH statement still requires an explicit final bridge.

## Falsification lesson after #128/#129

Generic structural countermodels survive the already-proved shell/Schur/parity/KKT/N-flow framework. In particular, centered-grid diagonal perturbations can preserve reversal/displacement structure while producing regular, one-parity-bad, or resonant examples.

Therefore a proposed contradiction that still works for arbitrary reversal-symmetric diagonal perturbations is almost certainly using too little canonical source information.

These are synthetic/regression countermodels, not realizable zeta counterexamples and not refutations of the actual `canonicalSourceMatrix`.

## Firewalls

- RH remains OPEN.
- `ker A` is the projected successor predecessor-block kernel, not the predecessor-size spectrum.
- D is algebraic, not unitary/isometric.
- the predecessor correction in `D c+` may not be dropped.
- no shell invariance is proved.
- no `A^-1` at zero.
- `Re S0<0` and `Re sigma0<0` are not branch exclusion.
- a canonical resonant pole is not automatically contradictory.
- #129 gives no sign/nonzeroness for `alpha`, `Gamma`, the overlap or source moment.
- generic structural countermodels refute generic arguments, not the canonical CCM source formula.
- monotonicity/uniqueness is not negative-root exclusion.
- no machine claim-registry promotion follows automatically from #127-#129.
- RH remains OPEN.

Current research detail: `research/RHRC/RESEARCH_LEADS_POST_129_DELTA.md`.
