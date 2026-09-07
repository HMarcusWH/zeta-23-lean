# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after PR #125 = 615437fd5854b4473471d9826b4d4787b2e8e42f
live main tree = 245bba07addba0c5ad85fcf1b1b4218b4432c427

theorem-state anchor = PR #125 merge 615437fd5854b4473471d9826b4d4787b2e8e42f
validated theorem head = 533beb4a42fc96cd43a97e071c6e07e3178872b6
E4-A2 kernel/range dichotomy + strict regular endpoint = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean/compiler/CI remain authoritative. PRs #118/#119/#121/#122/#124/#125 advance theorem authority only; the latest merged Control-v2 semantic change remains #117.

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
  E4-A2 kernel/range zero-shift dichotomy                           PROVED / #124
  E4-A2 strict canonical zero-shift endpoint                        PROVED / #125

  E4-A3 zero-shift shell response / resonant pole / branch rigidity NOW
  E4-B  parity shifted-nullity from rank-at-most-one algebra        PARALLEL
  E3-C  resolvent identity / secular monotonicity / root uniqueness PARALLEL
  E3-B3 general predecessor-floor deformation theorem               PARALLEL / OPEN

TARGET
  CCM-specific negative-root exclusion
  positivity / finite-to-infinite closure                           OPEN
  RH                                                                 OPEN
```

## E4-A2 settlement

For `A=P_W T|_W`, `c=intrinsicCubicShellPart`, `b=Bc`, #124 proves

```text
range A ⟂ ker A
W = ker A ⊕ range A
b ⟂ ker A -> b ∈ range A.
```

In the decoupled branch there exists `x0` with `Ax0=b`, and `<x,b>` is identical for every solution `Ax=b`. In the resonant branch #124 proves

```text
<z,b> = (-lam)<z,R_lam b>
|<z,b>|^2 <= (-lam)||z||^2 Re<R_lam b,b>.
```

#125 defines the canonical zero-shift endpoint

```text
S0=<Tc,c>-<x0,b>
```

and the zero-shift trial vector `u0=-x0+c`. It proves zero predecessor residual for `T u0`, the exact identity `<T u0,u0>=S0`, the predecessor-fibre complete square, and at a safe negative secular root

```text
Re S0 < 0.
```

The actual global-first-bad state is therefore classified as a strictly negative regular endpoint or an exact kernel resonance. Neither branch is excluded.

## Highest-leverage next split

### Zero-shift shell response

Use the proved zero predecessor coordinate of `T u0` and `V=W⊕S`, `dim_C S=1` to theoremize the exact canonical shell coefficient of `T u0`. Do not infer that `u0` is an eigenvector.

### Resonant pole decomposition

Use #124's `ker A ⊕ range A` algebra to decompose `b` and theoremize the exact `1/(-lam)` kernel component of `R_lam b`.

### Branch rigidity

Compose both mechanisms with parity rank-at-most-one structure, KKT/normal-space geometry, cubic quotient information, first-bad minimality and exact N-flow. Generic Hermitian block systems admit both a negative Schur endpoint and zero resonance, so a contradiction must use genuinely CCM-specific structure.

### Parallel lanes

E4-B shifted-nullity and E3-C monotonicity remain useful. Monotonicity can yield root uniqueness, but uniqueness remains strictly weaker than exclusion.

## Firewalls

- RH remains OPEN.
- `ker A` is the projected successor predecessor-block kernel, not the predecessor-size spectrum.
- D is algebraic, not unitary/isometric.
- no shell invariance is proved.
- no `A^-1` at zero; #124/#125 deliberately use solution-space canonicity instead.
- `Re S0<0` is not branch exclusion.
- resonance is not automatically contradictory.
- `T u0 ∈ S`, if proved, is not `T u0 ∈ span(u0)`.
- monotonicity/uniqueness is not negative-root exclusion.
- no source-normalization or machine claim-registry promotion follows automatically from #124/#125.
- positivity / finite-to-infinite closure / RH remain OPEN.

Current research detail: `research/RHRC/RESEARCH_LEADS_POST_125_DELTA.md`.

**RH remains OPEN.**