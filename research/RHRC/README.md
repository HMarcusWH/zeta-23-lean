# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

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
real unconjugated exact secular bridge + root metric bound            PROVED / #122
zero-resonance cubic-coupling classification on ker A                 PROVED / #122

E4-A2 zero-shift/range endpoint split                                 NOW
E3-C resolvent monotonicity / root uniqueness                         PARALLEL
E4-B parity shifted-nullity comparison                                PARALLEL
E3-B3 positive-floor deformation theorem                              PARALLEL / OPEN FORMALIZATION
negative-root exclusion                                               OPEN
positivity / finite-to-infinite closure                               OPEN
RH                                                                     OPEN
```

## Exact post-#122 finite state

A hypothetical off-line zero is reduced to one global-first-bad finite state carrying:

- a negative shift `lam<0`;
- predecessor nonnegativity;
- canonical `V=W⊕S` with one-dimensional shell;
- canonical cubic shell vector `c!=0`;
- safe shifted predecessor resolvent `R_lam`;
- exact quotient scalar `F(lam)`;
- explicit Schur scalar `S(lam)`;
- exact real bridge `F(lam)=S(lam)/<c,c>`;
- exact root/eigenmode equivalence;
- theorem-backed shifted metric/resolvent bounds;
- the first denominator-free metric restriction at the root;
- pointwise classification on `ker A`:

  ```text
  Az=0 -> (<z,Bc>=0 <-> Tz=0).
  ```

This is the strongest current finite rigidity package. It is not root exclusion and not RH.

## Current execution priority

1. **E4-A2 — zero-shift/range endpoint.** Split on the exact E4-A1 dichotomy. In the decoupled branch prove `Bc ∈ range A` and build a solution-based zero-shift endpoint without `A^-1`. In the resonant branch theoremize the zero-eigenspace contribution to `R_lam Bc` and its effect on the secular scalar near zero.
2. **E3-C — resolvent identity / monotonicity.** The representation barrier is closed. Prove a finite-dimensional shifted-resolvent identity and strict scalar monotonicity if justified; conclude at most one negative root, not absence.
3. **E4-B — parity shifted-nullity.** Use rank/kernel algebra only; no unitary/interlacing assumptions through `D`.
4. **E3-B3 — general lower-floor deformation theorem.** Generalize the #122 `mu=0` metric estimate to a certified floor `mu` and theoremize the one-step deformation inequality.
5. **Root exclusion.** Combine endpoint/zero-resonance information with shell/parity/KKT/N-flow structure. Generic Schur systems admit negative roots, so a contradiction must use genuinely CCM-specific structure.

The source-faithful `G1-B1B -> G1-final -> S-NEG -> G23` lane remains parallel.

## Zero-resonance firewall after #122

PR #122 does **not** prove `Bc ⟂ ker A`. It proves the exact equivalence

```text
Az=0 -> (<z,Bc>=0 <-> Tz=0)
```

and the quantified equivalence between vanishing of the coupling on the whole projected kernel and every projected-kernel vector being a genuine successor zero mode.

Therefore the controller must route both branches until one is excluded by theorem.

## Control-v2 authority

`research/RHRC/control_v2/` remains additive research-control infrastructure only. It may rank actions, select first-break falsifiers, record archaeology/replay evidence and build fail-closed deformation-budget certificates. It may not write theorem authority, promote claims, change `BOUNDARY.json` terminal status or emit RH.

The control-plane anchor remains #117 because #118/#119/#121/#122 changed theorem state but not controller semantics.

## Permanent firewalls

- RH remains OPEN.
- shell nonzero is not shell invariance or pure-shell behavior.
- D is algebraic, not unitary/isometric.
- exact cubic factorization is rank at most one, not automatically exact rank one.
- predecessor nonnegative is not a positive spectral gap.
- `ker A` is the projected successor predecessor-block kernel, not the predecessor-size compressed-operator kernel.
- no `A^-1` at zero.
- E4-A1 classification is not decoupling.
- #122 metric control is not root exclusion.
- root uniqueness, if proved, is not positivity.
- no finite/fitted deformation tail is a proof of complete future control.
- no source-normalization, promoted-binding, finite-to-infinite or RH change follows from #121/#122.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_122_DELTA.md` — current post-green theorem implications and falsification targets.
- `RESEARCH_LEADS.md` — accumulated lead ledger / historical option memory.
- `OBSTRUCTION_LEDGER.md` — reusable blockers and claim firewalls.
- `DEAD_ROUTES.md` — route failures requiring changed-premise justification before revival.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — research-control semantics.
- `CLAIM_REGISTRY.json` / `R003_PROMOTED_BINDINGS.json` — machine promotion surface; do not infer promotion from prose.

**RH remains OPEN.**