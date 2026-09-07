# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after PR #125 = 615437fd5854b4473471d9826b4d4787b2e8e42f
live main tree = 245bba07addba0c5ad85fcf1b1b4218b4432c427

theorem-state anchor = PR #125 merge 615437fd5854b4473471d9826b4d4787b2e8e42f
validated theorem head = 533beb4a42fc96cd43a97e071c6e07e3178872b6
E4-A2 zero-shift kernel/range dichotomy + strict regular endpoint = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean compiler + CI are the exact authority. The control plane may select research actions but may not promote theorem or terminal RH status.

## Theorem-backed internal route

```text
F1 finite canonical negative obstruction                              PROVED / #94
constrained algebra / Euclidean sector                                PROVED / #96-#98
exact centered N-flow + fixed-L negative tail                         PROVED / #100
reversal symmetry / parity geometry / algebraic D                     PROVED / #102-#103
global first bad + predecessor nonnegative + 1d successor shell       PROVED / #105,#112
negative first-bad eigenmode + KKT/cubic channel                      PROVED / #107,#109,#110
canonical V=W⊕S + shifted predecessor Schur reduction                 PROVED / #113
canonical cubic shell incidence                                       PROVED / #115
canonical cubic quotient coordinate + normalized Schur                PROVED / #118
exact quotient secular root <-> negative-shift eigenmode              PROVED / #119
exact explicit cubic Schur scalar bridge                              PROVED / #121
projected symmetry/coercivity + real resolvent metric control         PROVED / #122
zero-resonance cubic-coupling classification on ker A                 PROVED / #122
zero-shift kernel/range dichotomy + solution-independent scalar       PROVED / #124
exact resonant identity + quantitative lower bound                    PROVED / #124
canonical zero-shift endpoint + predecessor-fibre complete square     PROVED / #125
decoupled branch at negative secular root -> Re S0<0                  PROVED / #125

E4-A3 branch rigidity / shell response / resonant pole                NOW
E4-B parity shifted-nullity comparison                                PARALLEL
E3-C resolvent monotonicity / root uniqueness                         PARALLEL
E3-B3 positive-floor deformation theorem                              PARALLEL / OPEN FORMALIZATION
negative-root exclusion                                               OPEN
positivity / finite-to-infinite closure                               OPEN
RH                                                                     OPEN
```

## Exact post-#125 finite state

A hypothetical off-line zero is reduced to one global-first-bad finite state carrying:

- a negative shift `lam<0`;
- predecessor nonnegativity;
- canonical `V=W⊕S` with one-dimensional shell;
- canonical cubic shell vector `c!=0`;
- safe shifted predecessor resolvent `R_lam`;
- exact quotient scalar `F(lam)` and explicit real Schur scalar `S(lam)`;
- exact root/eigenmode equivalence and metric bounds;
- `W=ker A⊕range A` for the projected predecessor block;
- the exact E4-A2 branch classification:

  ```text
  REGULAR:
    Ax0=b
    zero-shift quadratic coupling is solution-independent
    S0=<Tc,c>-<x0,b>
    Re S0<0

  RESONANT:
    ∃z∈ker A, <z,b>!=0
    <z,b>=(-lam)<z,R_lam b>
    |<z,b>|^2 <= (-lam)||z||^2 Re<R_lam b,b>.
  ```

This is the strongest current finite rigidity package. It is not branch exclusion, negative-root exclusion or RH.

## Current execution priority

1. **E4-A3a — zero-shift shell response.** Use the proved zero predecessor coordinate of `T u0` plus `V=W⊕S`, `dim_C S=1` to theoremize the exact canonical shell coefficient. Do not infer an eigenvector statement.
2. **E4-A3b — resonant pole decomposition.** Use #124's `ker A⊕range A` decomposition to isolate the exact `1/(-lam)` kernel component of `R_lam b`.
3. **E4-A3c — branch rigidity.** Compose the regular shell coefficient and resonant pole with parity rank-at-most-one algebra, KKT/normal-space structure, cubic quotient data and N-flow/first-bad minimality. Attack the constrained finite countermodel space.
4. **E4-B — parity shifted-nullity.** Use rank/kernel algebra only; no unitary/interlacing assumptions through `D`.
5. **E3-C — resolvent identity / monotonicity.** Prove strict scalar monotonicity if justified; conclude at most one negative root, not absence.
6. **E3-B3 — general lower-floor deformation theorem.** Advance only where it supplies independent information rather than duplicating E4-A3.
7. **Root exclusion.** Attempt only from CCM-specific structure; generic Schur systems admit negative roots.

The source-faithful `G1-B1B -> G1-final -> S-NEG -> G23` lane remains parallel.

## E4-A2 settlement / E4-A3 firewall

PRs #124/#125 do not prove that the regular branch is impossible, and they do not prove the resonant branch is impossible. They prove a sharper alternative.

Permanent controller rules:

```text
Re S0<0 != contradiction
resonant kernel coupling != contradiction
T u0∈S != u0 eigenvector
at most one negative root != no negative root
```

The next exclusion theorem must expose structure absent from generic Hermitian block matrices.

## Control-v2 authority

`research/RHRC/control_v2/` remains additive research-control infrastructure only. It may rank actions, select first-break falsifiers, record archaeology/replay evidence and build fail-closed deformation-budget certificates. It may not write theorem authority, promote claims, change `BOUNDARY.json` terminal status or emit RH.

The control-plane anchor remains #117 because #118/#119/#121/#122/#124/#125 changed theorem state but not controller semantics.

## Permanent firewalls

- RH remains OPEN.
- shell nonzero is not shell invariance or pure-shell behavior.
- D is algebraic, not unitary/isometric.
- exact cubic factorization is rank at most one, not automatically exact rank one.
- predecessor nonnegative is not a positive spectral gap.
- `ker A` is the projected successor predecessor-block kernel, not the predecessor-size compressed-operator kernel.
- no `A^-1` at zero.
- #124/#125 classification and endpoint negativity are not root exclusion.
- no finite/fitted deformation tail is a proof of complete future control.
- no source-normalization, promoted-binding, finite-to-infinite or RH change follows automatically from #124/#125.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_125_DELTA.md` — current post-green implications and falsification targets.
- `RESEARCH_LEADS.md` — accumulated lead ledger / historical option memory.
- `OBSTRUCTION_LEDGER.md` — reusable blockers and claim firewalls.
- `DEAD_ROUTES.md` — route failures requiring changed-premise justification before revival.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — research-control semantics.
- `CLAIM_REGISTRY.json` / `R003_PROMOTED_BINDINGS.json` — machine promotion surface; do not infer promotion from prose.

**RH remains OPEN.**