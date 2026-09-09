# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after theorem PR #134 = 7f1fec480d1ccbff04a456ab937accf7b23cc1af
live main tree = c142efa141036331d139c532d06e7a976c5b50c2

theorem-state anchor = PR #134 merge 7f1fec480d1ccbff04a456ab937accf7b23cc1af
validated theorem head = 753ee53a7fc08bd3be9a5a0f37417629122395f9
validated theorem tree = c142efa141036331d139c532d06e7a976c5b50c2
RHRC #870 = SUCCESS
Permansson #643 = SUCCESS

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
negative eigenmode + KKT / cubic channel                                PROVED / #107,#109,#110
canonical V=W⊕S + shifted Schur/secular machinery                       PROVED / #113-#122
zero-shift kernel/range dichotomy + endpoint                            PROVED / #124-#125
special zero-shift shell response                                       PROVED / #127
signed regular response + resonant kernel pole                          PROVED / #128
source-explicit cross-parity transfer                                   PROVED / #129
off-line zero -> source-explicit global first-bad certificate           PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131
denominator-free whole-kernel source transport                          PROVED / #134
direct zero-shift cross-parity transfer                                 PROVED / #134
Gamma0 * mu(z)=0 on full even predecessor kernel                        PROVED / #134

absolute canonical source-energy decomposition                          NEXT THEOREM
canonical one-step domination / coercivity                              DECISIVE OPEN TARGET
regular-aperture log-lift selection                                     FALLBACK SIMPLIFIER
negative-root exclusion                                                 OPEN
explicit terminal RH bridge                                             OPEN
RH                                                                       OPEN
```

## Post-#134 theorem conclusion

The zero-shift transport tranche is complete enough for the current route. For every even predecessor-kernel vector `z`, Lean proves

```text
A-(Dz) = beta(z)d + mu(z)a
<b-,Dz>/rho- = beta(z)+mu(z)
```

and hence the whole odd-kernel vector compatibility

```text
beta(z) K-d + mu(z) K-a = 0.
```

Under an even zero-shift preimage, the odd coupling-kernel coordinate is exactly driven by the even zero-shift response and source term. Under both parity preimages Lean proves

```text
sigma- = alpha0 sigma+ + Gamma0 * mu(u+0)
Gamma0 = <u-0,g->/rho-
Gamma0 * mu(z)=0  for every z in ker A+.
```

These are direct finite zero-shift theorems. No pseudoinverse, Laurent expansion, whole-block inverse, one-dimensional kernel assumption, D-isometry, source sign, or coefficient nonzeroness is used.

## Why the frontier moved

Exact rational structural countermodels already show that generic sign/nonvanishing of `alpha`, `Gamma`, overlap, or source moment cannot close the branch. Scalar-shift covariance also shows that the shift-invariant transfer package cannot determine where the absolute spectral origin lies.

PR #131's active source moment intentionally annihilates scalar identities. Therefore the next theorem must retain absolute canonical normalization rather than further refine the same linear observable.

## Current execution priority

1. **E4-A4b1 — absolute source energy.** Define and decompose `E(v)=Re<Tv,v>` through the actual production pole/arch/prime source, retaining the canonical archimedean scalar correction. Specialize to the cubic shell and zero-shift trial. Prove the exact regular-preimage energy/Schur identity. Do not assume positivity.
2. **E4-A4b2 — canonical one-step domination.** For each parity prove from the actual canonical source

   ```text
   q_c = Re<Tc,c> >= 0
   |<w,b>|^2 <= q_c Re<Aw,w>  for every w in W.
   ```

   This is the decisive finite arithmetic/coercive target.
3. **E4-A4R — log-lift regular-aperture selection, only if useful.** Dense injective predecessor apertures may simplify resonance, but regularity alone does not exclude a negative successor.
4. **Global exclusion and terminal wrapper.** Only after the canonical domination/exclusion theorem is proved.

Parallel E4-B / E3-C / E3-B3 work remains available but should not displace canonical normalization unless it adds independent exclusion information.

## Why one-step domination would close the finite obstruction

With `A>=0`, shell `c`, coupling `b=P_WTc`, and `q_c=Re<Tc,c>`, the domination

```text
|<w,b>|^2 <= q_c Re<Aw,w>
```

implies `w in ker A -> <w,b>=0`, eliminating resonant coupling. In the regular branch, `Ax0=b` gives the zero-shift Schur endpoint `S0>=0`. But the existing first-bad theorem gives `Re S0<0` at the forced negative root. Contradiction.

The unresolved content is therefore source-faithful arithmetic positivity/coercivity for the actual canonical CCM normalization.

## Quantitative source lead

Boundary-flat Taylor algebra suggests first potentially nonzero source-coordinate terms at orders `omega^7` and `omega^9`. High-precision checks support the predicted coefficients. This remains **DERIVED / EXPERIMENTAL** and should only be promoted if it yields a rigorous ingredient for the energy/domination theorem.

## Permanent firewalls

- RH remains OPEN.
- D is algebraic, not unitary/isometric.
- the predecessor correction in `D c+` may not be dropped.
- `ker A` is the projected successor predecessor-block kernel, not the predecessor-size compressed spectrum.
- no `A^-1` at zero.
- `Re S0<0` and `Re sigma0<0` are not root exclusion by themselves.
- the resonant pole is classification, not contradiction.
- `Gamma0*mu(z)=0` does not permit division without a separately proved nonzero factor.
- universal raw source-moment positivity is unavailable for the linear observable.
- factorwise sign/nonzero closure is quarantined by exact rational countermodels.
- shift-invariant transfer data cannot determine absolute spectral sign.
- positive-definite predecessor selection is simplification, not exclusion.
- generic countermodels do not refute the actual canonical arithmetic source.
- numerical precision is not theorem authority.
- no machine claim, negative-root exclusion or RH change follows from research prose.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_134_DELTA.md` — current post-#134 research delta.
- `RESEARCH_LEADS_POST_132_DELTA.md` — historical pre-#134 frontier.
- `OBSTRUCTION_LEDGER.md` — reusable blockers and claim firewalls.
- `DEAD_ROUTES.md` — dead/quarantined routes requiring changed-premise justification.
- `countermodels/POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md` — structural falsification fixtures.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — research-control semantics.
- `CLAIM_REGISTRY.json` / `R003_PROMOTED_BINDINGS.json` — machine promotion surface.

**RH remains OPEN.**
