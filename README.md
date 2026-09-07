# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after PR #122 = b2d1210902d430f3cdd3c24c2961ab843469b5d6
live main tree = db51419fb7cc8b2e3dbe5cf2e770390086db9862

theorem-state anchor = PR #122 merge b2d1210902d430f3cdd3c24c2961ab843469b5d6
validated theorem head = 9c8154e3ea7a5762f8e65d508dc68bb9246db869
theorem-bearing merged through = PR #122
E3-B1 secular metric control + E4-A1 zero-resonance coupling classification = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean compiler + CI remain authoritative over prose snapshots. PRs #118/#119/#121/#122 advanced theorem authority; Control-v2 semantics have not changed since #117.

## Current RH-directed theorem ladder

```text
off-line zeta zero
  -> compact C² pole-neutral negative W test                       PROVED
  -> strict aperture + legal finite approximation                 PROVED
  -> canonical finite negative obstruction                        PROVED / #94
  -> constrained algebra / Euclidean sector                       PROVED / #96-#98
  -> exact centered N-flow / fixed-L negative tail                PROVED / #100
  -> reversal/parity geometry / algebraic D-equivalence           PROVED / #102-#103
  -> global first bad + predecessor nonnegative                   PROVED / #105,#112
  -> negative first-bad eigenmode + KKT/cubic channel             PROVED / #107,#109,#110
  -> intrinsic V=W⊕S + safe shifted Schur reduction               PROVED / #112,#113
  -> canonical cubic shell + quotient coordinates                 PROVED / #115,#118
  -> exact quotient secular root iff negative eigenmode           PROVED / #119
  -> exact explicit Schur scalar bridge                           PROVED / #121
  -> projected symmetry/coercivity/resolvent metric control       PROVED / #122
  -> real unconjugated secular bridge + first root metric bound   PROVED / #122
  -> ker(A) cubic-coupling classification                         PROVED / #122

NOW
  E4-A2 zero-shift / range-endpoint split:
    classify the decoupled branch b ⟂ ker A without using A^-1
    classify the resonant branch when some z in ker A has <z,b> != 0

PARALLEL
  E3-C shifted-resolvent identity / strict secular monotonicity / root uniqueness
  E4-B parity shifted-nullity comparison from rank-at-most-one algebra
  E3-B3 general lower-floor deformation theorem
  deformation-budget falsification lane
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

TARGET
  CCM-specific negative-root exclusion at the global first-bad state
  positivity / finite-to-infinite closure                         OPEN
  RH                                                               OPEN
```

## What PR #121 changed

PR #121 connected the exact #119 quotient-coordinate root detector to the explicit cubic Schur scalar

```text
S(lam) = <Tc,c> - lam<c,c> - <R_lam Bc,Bc>.
```

Under the safe negative-shift hypotheses it proves

```text
cubicSecularScalar(lam)
  = star(S(lam)) / <c,c>
```

and equivalence of `S(lam)=0`, the canonical trial eigenmode, and existence of a nonzero eigenmode at `lam`.

## What PR #122 changed

PR #122 closes the metric layer deliberately left open by #121. On the projected predecessor block

```text
A = P_W T|_W,
b = Bc,
R_lam = (A-lam I)^(-1),  lam < 0,
```

Lean now proves projected symmetry, shifted symmetry/coercivity, resolvent norm and quadratic bounds, real/nonnegative resolvent quadratic value, and realness of the explicit cubic Schur scalar. Consequently the exact bridge becomes the unconjugated real identity

```text
cubicSecularScalar(lam) = S(lam) / <c,c>.
```

At an exact negative secular root, PR #122 also proves the first denominator-free metric constraint

```text
0 <= Re(<Tc,c> - lam<c,c>)
(-lam) * Re(<Tc,c> - lam<c,c>) <= ||Bc||^2.
```

The E4-A1 theorem classifies zero resonance on the projected block:

```text
Az = 0
  -> (<z,Bc> = 0 <-> T_(N+1) z = 0).
```

This is a classification theorem, **not** a theorem that `Bc` annihilates `ker A`.

## Current mathematical frontier

### E4-A2 — zero-shift / range endpoint

The highest-information next split is now determined by #122.

If the cubic coupling vanishes on all of `ker A`, symmetry should allow a finite-dimensional range/kernel argument

```text
b ⟂ ker A  ->  b ∈ range A
```

and hence an algebraic zero-shift endpoint witness `x₀` with `A x₀ = b`, without introducing `A^-1` at zero.

If the coupling does not vanish on `ker A`, #122 identifies a genuine successor zero-resonance direction. The next task is to theoremize how that component enters the negative-shift resolvent and secular scalar near `lam=0-`.

### E3-C — monotonicity / root count

The explicit scalar is now theorem-backed and real on the safe negative axis, so resolvent-identity and monotonicity work is no longer blocked by representation ambiguity. A strict monotonicity theorem may imply at most one negative root.

Permanent firewall:

```text
at most one negative root != no negative root.
```

### E4-B — parity shifted-nullity

The rank-at-most-one parity defect remains available for a purely algebraic shifted-nullity comparison. Do not use Hermitian interlacing through `D`; `D` is algebraic, not theoremized unitary/isometric.

## Permanent firewalls

- RH remains OPEN.
- `V=W⊕S` is proved; shell invariance is not.
- D-equivalence is algebraic, not unitary/isometric.
- exact cubic factorization gives rank at most one, not automatically exact rank one.
- `ker A` means the kernel of the projected successor predecessor block `P_W T|_W`; it is not the predecessor-size compressed-operator kernel.
- PR #122 classifies cubic coupling on `ker A`; it does not prove decoupling.
- use `A-lam I` for `lam<0`; no `A^-1` at zero.
- root uniqueness, if proved, is not root absence.
- the first metric root bound is not negative-root exclusion.
- no finite/fitted deformation tail is an infinite-horizon certificate.
- source-normalization, promoted-binding, positivity, finite-to-infinite closure and RH remain unchanged unless separately theorem-backed.

## Living research records

- `research/RHRC/README.md`
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_122_DELTA.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

Machine claim/binding promotion must not be inferred beyond entries actually present in the registries.

**RH remains OPEN.**