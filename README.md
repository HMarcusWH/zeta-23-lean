# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after PR #125 = 615437fd5854b4473471d9826b4d4787b2e8e42f
live main tree = 245bba07addba0c5ad85fcf1b1b4218b4432c427

theorem-state anchor = PR #125 merge 615437fd5854b4473471d9826b4d4787b2e8e42f
validated theorem head = 533beb4a42fc96cd43a97e071c6e07e3178872b6
theorem-bearing merged through = PR #125
E4-A2 zero-shift kernel/range dichotomy + strict regular endpoint = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean compiler + CI remain authoritative over prose snapshots. PRs #118/#119/#121/#122/#124/#125 advanced theorem authority; Control-v2 semantics have not changed since #117.

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
  -> real scalar bridge + first root metric bound                 PROVED / #122
  -> ker(A) cubic-coupling classification                         PROVED / #122
  -> ker/range zero-shift dichotomy + solution-independent scalar PROVED / #124
  -> exact resonant identity + denominator-free bound             PROVED / #124
  -> canonical zero-shift Schur endpoint + complete square        PROVED / #125
  -> decoupled branch forces Re S0 < 0                            PROVED / #125
  -> global strict-endpoint / resonance dichotomy                 PROVED / #125

NOW — E4-A3 BRANCH RIGIDITY
  E4-A3a zero-shift shell response:
    theoremize T u0 ∈ S and identify the canonical one-dimensional shell coefficient
  E4-A3b resonant pole decomposition:
    theoremize the exact ker/range decomposition of R_lam b
  E4-A3c branch rigidity:
    combine endpoint/pole information with parity/KKT/cubic/N-flow structure

PARALLEL
  E4-B parity shifted-nullity comparison from rank-at-most-one algebra
  E3-C shifted-resolvent identity / strict secular monotonicity / root uniqueness
  E3-B3 general lower-floor deformation theorem
  deformation-budget falsification lane
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

TARGET
  CCM-specific negative-root exclusion at the global first-bad state
  positivity / finite-to-infinite closure                         OPEN
  RH                                                               OPEN
```

## What PR #124 changed

Let

```text
A = P_W T|_W,
c = intrinsicCubicShellPart,
b = Bc.
```

PR #124 theoremizes the zero-shift geometry

```text
range A ⟂ ker A
range A ∩ ker A = {0}
W = ker A ⊕ range A.
```

If `b` annihilates `ker A`, then `b ∈ range A`, some `x0` satisfies `Ax0=b`, and `<x,b>` is independent of the chosen solution `Ax=b`. No inverse of `A` at zero is introduced.

In the complementary resonant branch, for `z∈ker A` and every safe `lam<0`, #124 proves

```text
<z,b> = (-lam)<z,R_lam b>
|<z,b>|^2 <= (-lam)||z||^2 Re<R_lam b,b>.
```

This is an exact classification and quantitative restriction, not branch exclusion.

## What PR #125 changed

In the decoupled branch define

```text
S0 = <Tc,c> - <x0,b>,
u0 = -x0 + c,
Ax0 = b.
```

PR #125 proves that `S0` is independent of the selected zero-shift preimage, that the predecessor coordinate of `T u0` vanishes, and that

```text
<Tu0,u0> = S0.
```

It further proves the exact complete-square identity along predecessor displacements. Predecessor nonnegativity then lets the existing negative secular eigenmode force

```text
Re S0 < 0.
```

Thus a hypothetical off-line zero now forces the same global-first-bad state into one of two mechanisms:

```text
REGULAR:  Ax0=b and Re S0<0,
or
RESONANT: ∃z∈ker A with <z,b>!=0 carrying the exact #124 identity/bound.
```

Neither branch is excluded.

## Current mathematical frontier

### E4-A3 — zero-shift branch rigidity

The regular endpoint is no longer an existence/sign problem. Its next high-information theorem is the shell response: because #125 proves the predecessor coordinate of `T u0` is zero and `V=W⊕S` with `dim_C S=1`, theoremize the exact shell coefficient of `T u0` without assuming shell invariance or calling `u0` an eigenvector.

On the resonant side, #124 already proves a useful lower bound. The stronger next target is an exact algebraic kernel-pole decomposition using `W=ker A⊕range A`, exposing the `1/(-lam)` component of `R_lam b`.

Then compose both branches with genuinely CCM-specific parity/KKT/cubic/N-flow structure and attack the finite countermodel space.

### E3-C — monotonicity / root count

The explicit scalar is theorem-backed and real on the safe negative axis, so resolvent-identity and monotonicity work remains admissible. A strict monotonicity theorem may imply at most one negative root.

Permanent firewall:

```text
at most one negative root != no negative root.
```

### E4-B — parity shifted-nullity

The rank-at-most-one parity defect remains available for a purely algebraic shifted-nullity comparison. Do not use Hermitian interlacing through `D`; `D` is algebraic, not theoremized unitary/isometric.

## Permanent firewalls

- RH remains OPEN.
- `V=W⊕S` is proved; shell invariance is not.
- `T u0 ∈ S`, once theoremized, would not by itself make `u0` an eigenvector.
- D-equivalence is algebraic, not unitary/isometric.
- exact cubic factorization gives rank at most one, not automatically exact rank one.
- `ker A` means the kernel of the projected successor predecessor block `P_W T|_W`; it is not the predecessor-size compressed-operator kernel.
- no whole-space or range-only `A^-1` is introduced at zero.
- `Re S0 < 0` is not branch exclusion; generic Hermitian Schur systems can have negative zero-shift Schur complements.
- resonance is not automatically contradictory; generic resonance may generate negative spectrum.
- root uniqueness, if proved, is not root absence.
- no finite/fitted deformation tail is an infinite-horizon certificate.
- source-normalization, promoted-binding, positivity, finite-to-infinite closure and RH remain unchanged unless separately theorem-backed.

## Living research records

- `research/RHRC/README.md`
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_125_DELTA.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

Machine claim/binding promotion must not be inferred beyond entries actually present in the registries.

**RH remains OPEN.**