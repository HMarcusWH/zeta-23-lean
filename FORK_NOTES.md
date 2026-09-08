# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

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

RH = OPEN
```

Live GitHub head + Lean/compiler/CI remain authoritative. PR #132 is documentation/control metadata only. The theorem surface remains exactly through #131.

## Recent theorem packages

```text
#94  canonical finite negative obstruction
#96-#98 constrained canonical algebra + Euclidean sector
#100 exact centered N-flow + fixed-L negative tail
#102-#103 exact reversal/parity geometry + algebraic D-equivalence
#105/#107/#109/#110 least-bad eigenmode, parity normals, KKT, cubic channel
#112/#113 global first bad, intrinsic shell, V=W⊕S, shifted Schur reduction
#115/#118 canonical cubic shell + quotient coordinate
#119 exact secular root/eigenmode equivalence
#121 exact explicit Schur scalar bridge
#122 projected metric/resolvent control + zero-resonance classification
#124/#125 zero-shift kernel/range dichotomy + endpoint + Re S0<0
#127 canonical zero-shift shell response
#128 signed regular response + canonical resonant pole
#129 source-explicit cubic defect + exact cross-parity secular transfer
#131 exact canonical source-moment decomposition
#132 documentation/control synchronization only
```

## Current frontier

```text
E4-A4b0 kernel/source zero-shift transport                         NOW
E4-A4b1 absolute canonical source-energy decomposition            THEN
E4-A4b2 canonical one-step domination/coercivity                  DECISIVE OPEN TARGET
E4-A4R  log-lift dense regular-aperture selection                 FALLBACK SIMPLIFIER
E4-A4d  global first-bad exclusion                                AFTER COERCIVITY

PARALLEL
  E4-B shifted-nullity
  E3-C secular monotonicity / root-count control
  E3-B3 lower-floor deformation
  source-coordinate high-order cancellation formalization when useful

TARGET
  no canonical first-bad negative root
  -> no off-line zero through existing global reduction
  -> explicit terminal Mathlib RH bridge
  RH OPEN
```

## Exact formal state

A hypothetical off-line zero already forces one global-first-bad finite state with:

- a negative exact secular/eigenvalue root;
- both predecessor parity sectors nonnegative;
- canonical one-dimensional shell/KKT geometry;
- zero-shift kernel/range classification;
- `Re S0<0` and regular `Re sigma0<0`;
- a canonical resonant kernel pole;
- exact cross-parity transfer;
- exact pole/arch/prime decomposition of the canonical source moment.

Neither branch is excluded. No negative-root exclusion or RH theorem is proved.

## Post-#132 derived structural target

The next strongest theorem is the denominator-free kernel/source transport. For `z in ker A+`, the audit derives

```text
A-(Dz) = beta(z)d + mu(z)a
<b-,Dz>/rho- = beta(z)+mu(z)
```

and therefore

```text
(||K+b+||^2/rho+) K-d + mu(K+b+) K-a = 0
```

in the full odd predecessor kernel.

Under both regular couplings, the same geometry yields

```text
Gamma0 * mu(z) = 0
```

for every even predecessor-kernel vector. A direct zero-shift transfer is also derivable without pseudoinverse/Laurent machinery:

```text
sigma- = alpha0 sigma+ + Gamma0 * mu(u+0).
```

These are derived targets, not compiled theorem authority.

## Countermodel lesson

Exact rational generic centered-grid fixtures preserve the parity/boundary-flat/KKT/rank-one/transfer package while realizing:

```text
sourceMoment != 0 with Gamma = 0 at a common negative root
Gamma != 0 with sourceMoment = 0 at a common negative root
alpha = 0 at an odd-only negative root with positive even successor
```

Additional fixtures realize negative `Gamma`, negative `alpha`, and either sign of the source moment.

They are not the canonical arithmetic source and not RH counterexamples. They quarantine generic factorwise sign/nonzero closure and any division by those factors without a separate canonical theorem.

## Why absolute energy is now central

The generic covariance

```text
M -> M+tI
lambda -> lambda+t
```

can preserve the trial/transfer package while moving the root relative to zero. Therefore the structural transfer data do not know the absolute spectral origin.

PR #131's normal moment intentionally annihilates scalar identity shifts. The next arithmetic layer must restore the absolute canonical normalization through

```text
E(v)=Re<Tv,v>.
```

The decisive target is the canonical one-step domination theorem. With `A>=0`, shell `c`, coupling `b=P_WTc`, and `q_c=Re<Tc,c>`, prove

```text
q_c >= 0
|<w,b>|^2 <= q_c Re<Aw,w>  for every w in W.
```

If this holds, kernel vectors force the coupling into `range A`, removing resonance. In the regular branch, `Ax0=b` gives `S0>=0`, contradicting the existing `Re S0<0` at the forced negative root.

## Secondary source clue

Boundary-flat Taylor algebra predicts the first potentially nonzero source-coordinate terms at orders `omega^7` / `omega^9`. High-precision diagnostics support the coefficients. This is **DERIVED / EXPERIMENTAL**, not proof, and is useful only if it feeds a rigorous absolute-energy/coercivity estimate.

## Fallback regular-aperture route

If resonance is a proof-engineering obstruction, freeze the prime cutoff and use

```text
M_Q(L)=-log(L)I+B_Q(L),  L=exp(z),
```

with periodic holomorphic remainder to prove determinant nonidentity and dense nonsingularity. Preserve a negative witness by continuity and reselect the least-bad size at a nearby aperture with PD predecessors.

This does not exclude a negative successor. Exact generic fixtures already show PD predecessors can coexist with negative roots.

## Firewalls

- RH remains OPEN.
- D is algebraic, not unitary/isometric.
- predecessor correction in `D c+` must be retained.
- `ker A` is the projected successor predecessor-block kernel.
- no `A^-1` at zero.
- `Re S0<0` and `Re sigma0<0` are not branch exclusion.
- canonical resonant pole is not contradiction.
- no division by `alpha`, `Gamma`, overlap or source moment without theoremized nonzeroness.
- universal raw source-moment positivity is dead by linearity.
- factorwise sign/nonzero closure is quarantined by exact rational countermodels.
- shift-invariant transfer data cannot locate the absolute spectral origin.
- positive-definite predecessors are simplification, not exclusion.
- generic countermodels do not refute the canonical source.
- numerical precision is not theorem authority.
- machine claim promotion and RH status do not change from documentation.

Current research detail: `research/RHRC/RESEARCH_LEADS_POST_132_DELTA.md`.

**RH remains OPEN.**
