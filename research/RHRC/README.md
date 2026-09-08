# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after documentation PR #132 = 38f65ce4abf5eec258d51425e7c9c88b63b21ffb
live main tree = 1cc939300fb269f798d25dc88f8eaff4eccc181a

theorem-state anchor = PR #131 merge 436d524d0cdeb5986d76dcbb988f771d19836c55
validated theorem head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
validated theorem tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a
RHRC #854 = SUCCESS
Permansson #627 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened semantics = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean compiler + CI are exact authority. PR #132 changed documentation/control metadata only. Control v2 may select research actions but may not promote theorem or terminal RH status.

## Theorem-backed internal route

```text
finite off-line-zero obstruction / legal approximation                 PROVED
canonical finite negative obstruction                                  PROVED / #94
constrained algebra / Euclidean sector                                  PROVED / #96-#98
exact centered N-flow + fixed-L negative tail                           PROVED / #100
reversal / parity / algebraic D                                         PROVED / #102-#103
global first bad + nonnegative predecessors + one-dimensional shell     PROVED / #105,#112
negative eigenmode + KKT / cubic channel                                PROVED / #107,#109,#110
canonical V=W⊕S + shifted Schur/secular machinery                       PROVED / #113-#122
zero-shift kernel/range dichotomy + endpoint                            PROVED / #124-#125
special zero-shift shell response                                       PROVED / #127
signed regular response + resonant kernel pole                          PROVED / #128
source-explicit cross-parity transfer                                   PROVED / #129
off-line zero -> source-explicit global first-bad certificate           PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131

kernel/source zero-shift transport                                      NEXT THEOREM
absolute canonical source-energy decomposition                          NEXT ARITHMETIC LAYER
canonical one-step domination / coercivity                              DECISIVE OPEN TARGET
regular-aperture log-lift selection                                     FALLBACK SIMPLIFIER
negative-root exclusion                                                 OPEN
explicit terminal RH bridge                                             OPEN
RH                                                                       OPEN
```

## Post-#132 research conclusion

The generic structural phase is close to exhausted. Exact rational post-#129 fixtures preserve almost the whole parity/KKT/rank-one/transfer package while allowing:

```text
sourceMoment != 0 with Gamma = 0 at a common negative root
Gamma != 0 with sourceMoment = 0 at a common negative root
alpha = 0 at an odd-only negative root with positive even successor
```

They are not canonical CCM sources and not RH counterexamples. They are reusable falsifiers for factorwise sign/nonzero arguments.

A stronger structural theorem is nevertheless available as a derived target. For `z in ker A+`:

```text
A-(Dz) = beta(z)d + mu(z)a
<b-,Dz>/rho- = beta(z)+mu(z)
```

hence

```text
(||K+b+||^2/rho+) K-d + mu(K+b+) K-a = 0
```

in the full odd predecessor kernel. Under both regular couplings one further derives `Gamma0 * mu(z)=0` on the entire even predecessor kernel. These statements are not yet compiled Lean theorems.

## Why the closure target changed

The simultaneous generic shift

```text
M -> M+tI
lambda -> lambda+t
```

can leave the trial vectors, defect/source functional, `alpha`, `Gamma`, and both secular scalars unchanged while moving the spectrum across zero. Therefore the structural transfer package cannot identify the absolute spectral origin.

PR #131's active moment also annihilates scalar identities by design. The missing channel is therefore absolute canonical normalization, not another shift-invariant decomposition.

## Current execution priority

1. **E4-A4b0 — kernel/source transport.** Formalize the denominator-free kernel identities, full kernel projection, direct zero-shift transfer, and regular-kernel overlap/source annihilation.
2. **E4-A4b1 — absolute source energy.** Decompose `Re<Tv,v>` through the production pole/arch/prime source while retaining the canonical arch scalar correction.
3. **E4-A4b2 — canonical one-step domination.** For each parity prove from the actual canonical source

   ```text
   q_c = Re<Tc,c> >= 0
   |<w,b>|^2 <= q_c Re<Aw,w>  for every w in W.
   ```

   This is equivalent to positivity of the one-step block extension when `A>=0` and is the current decisive finite theorem target.
4. **E4-A4R — log-lift regular-aperture selection, only if useful.** Use frozen-cutoff analyticity and `M_Q(L)=-log(L)I+B_Q(L)` to reselect a first-bad witness with PD predecessors. This removes resonance from the selected witness but does not prove positivity.
5. **Global exclusion and terminal wrapper.** Only after the canonical domination/exclusion theorem is proved.

## Why one-step domination would close the finite obstruction

If

```text
|<w,b>|^2 <= q_c Re<Aw,w>
```

holds with `A>=0`, then `w in ker A` forces `<w,b>=0`, eliminating resonant coupling. In the regular branch, `Ax0=b` then gives the zero-shift Schur endpoint `S0>=0`. But the existing first-bad theorem gives `Re S0<0` at the forced negative root. Contradiction.

Thus the remaining hard mathematical problem is a source-faithful arithmetic/coercive theorem for the actual canonical CCM normalization.

## Quantitative source lead

Boundary-flat Taylor algebra suggests first potentially nonzero source-coordinate terms at orders `omega^7` and `omega^9`, far beyond the currently formal C2 endpoint package. High-precision checks support the predicted coefficients. This remains **DERIVED / EXPERIMENTAL** and is useful only if it yields rigorous control for the absolute-energy/domination theorem.

## Permanent firewalls

- RH remains OPEN.
- D is algebraic, not unitary/isometric.
- the predecessor correction in `D c+` may not be dropped.
- `ker A` is the projected successor predecessor-block kernel, not the predecessor-size compressed spectrum.
- no `A^-1` at zero.
- `Re S0<0` and `Re sigma0<0` are not root exclusion.
- the resonant pole is classification, not contradiction.
- no division by `alpha`, `Gamma`, overlap or source moment without a theorem.
- universal raw source-moment positivity is dead by linearity.
- factorwise sign/nonzero closure is quarantined by exact rational countermodels.
- shift-invariant transfer data cannot determine absolute spectral sign.
- positive-definite predecessor selection is simplification, not exclusion.
- generic countermodels do not refute the actual canonical arithmetic source.
- numerical precision is not theorem authority.
- no machine claim, negative-root exclusion or RH change follows from research prose.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_132_DELTA.md` — current post-#132 research delta.
- `RESEARCH_LEADS_POST_131_DELTA.md` — previous source-decomposition delta.
- `OBSTRUCTION_LEDGER.md` — reusable blockers and claim firewalls.
- `DEAD_ROUTES.md` — dead/quarantined routes requiring changed-premise justification.
- `countermodels/POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md` — structural falsification fixtures.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — research-control semantics.
- `CLAIM_REGISTRY.json` / `R003_PROMOTED_BINDINGS.json` — machine promotion surface.

**RH remains OPEN.**
