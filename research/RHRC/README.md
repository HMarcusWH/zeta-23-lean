# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after theorem PR #137 = fa2f209a6eb8b4059968e8d61239d80588ca256c
live main tree = e3de4dc0377f0124832822b6f97ab5bbd7718640

theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
validated theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
Control v2 / FFBBP v1.6 hardened semantics = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact Lean compiler + CI are authority. Control v2 may select research actions but may not promote theorem or terminal RH status.

## Theorem-backed internal route

```text
finite off-line-zero obstruction / legal approximation                 PROVED
canonical finite negative obstruction                                  PROVED / #94
constrained algebra / Euclidean sector                                  PROVED / #96-#98
exact centered N-flow + fixed-L negative tail                           PROVED / #100
reversal / parity / algebraic D                                         PROVED / #102-#103
global first bad + nonnegative predecessors + one-dimensional shell     PROVED / #105,#112
exact shifted Schur/secular and zero-shift package                      PROVED / #113-#128
source-explicit cross-parity transfer                                   PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131
denominator-free zero-shift source transport                            PROVED / #134
absolute canonical source-energy decomposition                          PROVED / #136
exact canonical source pairing                                          PROVED / #137
one-step determinant + domination sufficiency                           PROVED / #137
off-line zero -> domination failure / explicit sign witness             PROVED / #137

canonical shell/determinant sign theorem                                OPEN / NOW
canonical one-step domination                                           OPEN
negative-root exclusion                                                  OPEN
explicit terminal RH bridge                                              OPEN
RH                                                                       OPEN
```

## Post-#137 theorem conclusion

For either parity, let

```text
q_c = Re<Tc,c>
q_A(w) = Re<Aw,w>
b(w) = <w,P_WTc>
Δ(w) = q_c*q_A(w) - |b(w)|^2.
```

Lean now proves the exact channel representation and the sufficiency chain

```text
canonicalOneStepDomination
  -> shell coupling annihilates ker A
  -> shell coupling lies in range A
  -> zero-shift preimage exists
  -> Re S0 >= 0
  -> no safe negative explicit Schur root.
```

The global first-bad wrapper also proves

```text
off-line zeta zero
  -> NOT canonicalOneStepDomination
  -> q_c < 0 OR exists w, Δ(w) < 0.
```

No theorem proves the missing sign conditions.

## Current execution priority

1. **A4b2b — falsify or prove the canonical shell/determinant signs.** Work directly on `q_c` and `Δ` using the production pole/arch/scalar/prime channel formulas. First try to falsify on the smallest exact canonical predecessor-nonnegative states.
2. **Find a structural representation.** Prefer a positive Gram/integral representation or a Cauchy-Schwarz remainder identity for the full canonical pairing over a termwise source-atom sign argument.
3. **Retarget the quantitative cancellation lead.** Test whether the `omega^7 / omega^9` boundary-flat cancellations control the determinant remainder.
4. **A4R only if useful.** Dense regular apertures may simplify algebra, but regularity alone is not exclusion and #137 already makes resonance disappear conditionally on domination.
5. **Global exclusion and terminal wrapper only after the sign theorem.**

Parallel E4-B / E3-C / E3-B3 work remains available but should not displace the source-specific sign problem unless it adds independent exclusion information.

## Why the determinant reduction is useful but not magic

The one-dimensional-shell block is governed by predecessor energy, shell energy and shell coupling. The #137 determinant is the exact two-dimensional Gram/Schur obstruction on each predecessor direction. With `A>=0`, requiring `q_c>=0` and `Δ(w)>=0` for every `w` is essentially requiring positivity of the one-step extension.

So #137 does not make the central positivity problem disappear. It does something more disciplined: it turns every hypothetical off-line zero into a concrete, source-addressable sign failure that can be attacked or falsified directly.

## Permanent firewalls

- RH remains OPEN.
- `canonicalOneStepDomination` is not established.
- conditional sufficiency is not unconditional exclusion.
- `q_c<0 OR exists Δ<0` is a countercertificate, not an inconsistency.
- individual source atoms may be indefinite; no termwise positivity shortcut is licensed.
- D is algebraic, not unitary/isometric.
- no `A^-1` at zero.
- no division by `alpha`, `Gamma`, overlap or source moment without theoremized nonzeroness.
- generic structural countermodels do not refute the actual canonical source.
- numerical evidence is not theorem authority.
- machine claim promotion remains separate from supporting theorem validity.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_137_DELTA.md` — current post-green research delta.
- `RESEARCH_LEADS_POST_134_DELTA.md` — historical pre-#136/#137 frontier.
- `OBSTRUCTION_LEDGER.md` — reusable blockers and claim firewalls.
- `DEAD_ROUTES.md` — dead/quarantined routes requiring changed-premise justification.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — research-control semantics.
- `CLAIM_REGISTRY.json` / `R003_PROMOTED_BINDINGS.json` — machine promotion surface.

**RH remains OPEN.**
