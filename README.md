# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after documentation PR #132 = 38f65ce4abf5eec258d51425e7c9c88b63b21ffb
live main tree = 1cc939300fb269f798d25dc88f8eaff4eccc181a

theorem-state anchor = PR #131 merge 436d524d0cdeb5986d76dcbb988f771d19836c55
validated theorem head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
validated theorem tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a
theorem-bearing merged through = PR #131
RHRC #854 = SUCCESS
Permansson #627 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control semantics = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean compiler + CI remain authoritative over prose snapshots. PR #132 synchronized documentation/control metadata only; theorem authority remains exactly at #131.

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
  -> ker(A) cubic-coupling classification                         PROVED / #122
  -> ker/range zero-shift dichotomy + canonical endpoint          PROVED / #124-#125
  -> exact one-dimensional zero-shift shell response              PROVED / #127
  -> Re sigma0 < 0 in regular branch                              PROVED / #128
  -> canonical resonant kernel coordinate and 1/(-lam) pole       PROVED / #128
  -> exact cross-parity secular transfer                          PROVED / #129
  -> cubic defect = canonical quadratic source moment             PROVED / #129
  -> off-line zero -> source-explicit first-bad certificate       PROVED / #129
  -> exact canonical source-moment decomposition                  PROVED / #131

NOW — E4-A4b0 KERNEL/SOURCE TRANSPORT
  theoremize the denominator-free zero-shift kernel identities,
  the full odd-kernel projected compatibility, the direct zero-shift
  cross-parity transfer, and regular-kernel overlap/source annihilation.

THEN — ABSOLUTE CANONICAL SOURCE ENERGY
  restore the pole/arch/prime energy decomposition including the
  scalar normalization term deliberately annihilated by the #131 moment.

DECISIVE TARGET — CANONICAL ONE-STEP DOMINATION
  q_c = Re<Tc,c> >= 0
  |<w,b>|^2 <= q_c Re<Aw,w>  for every predecessor vector w.
  If derived from the actual canonical source, this removes resonance
  and contradicts the already-proved negative zero-shift endpoint.

FALLBACK SIMPLIFIER
  log-lift / analytic dense regular-aperture selection if resonance makes
  the arithmetic estimate unnecessarily difficult. Positive-definite
  predecessors alone are not exclusion.

TARGET
  no canonical first-bad negative state
  -> no off-line zero via the existing global reduction
  -> explicit terminal Mathlib RiemannHypothesis bridge
  RH                                                               OPEN
```

## Exact post-#131 formal state

A hypothetical off-line zero is already reduced to one finite global-first-bad configuration carrying:

- a negative exact secular/eigenvalue root;
- nonnegative predecessor parity sectors;
- canonical `V=W⊕S` and one-dimensional shell geometry;
- safe shifted predecessor resolvents and exact Schur/secular identities;
- the zero-shift regular/resonant branch package;
- `Re S0<0` and, in the regular branch, `Re sigma0<0`;
- the canonical resonant kernel coordinate and exact pole;
- exact cross-parity secular transfer;
- the exact canonical source-moment decomposition into pole-even, reduced arch diagonal/off-diagonal and finite von-Mangoldt source atoms.

This is the strongest theorem-backed finite reduction. It is not negative-root exclusion or RH.

## What the post-#132 audit changed

The next theorem should no longer be merely a source-expanded restatement of #129. The stronger denominator-free target is the kernel/source transport identity. For `z in ker A+`, the derived target is

```text
A-(Dz) = beta(z) d + mu(z) a
<b-,Dz>/rho- = beta(z) + mu(z)
```

and hence, after projection to the entire odd predecessor kernel,

```text
(||K+b+||^2/rho+) K-d + mu(K+b+) K-a = 0.
```

Under both regular couplings, the same geometry yields the derived compatibility

```text
Gamma0 * mu(z) = 0
```

for every even predecessor-kernel vector. These are not yet Lean theorems.

A direct zero-shift transfer is also available without whole-block invertibility, pseudoinverses, or Laurent limits:

```text
sigma- = alpha0 sigma+ + Gamma0 * mu(u+0).
```

## Why generic transfer algebra is essentially exhausted

Exact rational centered-grid countermodels preserve the parity/boundary-flat geometry, predecessor nonnegativity, KKT extraction, rank-one cubic defect, quotient transport, trial reconstruction, overlap formula and full #129 scalar transfer while realizing:

```text
sourceMoment(u+) != 0 with Gamma = 0 at a common negative root
Gamma != 0 with sourceMoment(u+) = 0 at a common negative root
alpha = 0 at an odd-only negative root with positive even successor
```

Additional fixtures realize negative `Gamma`, negative `alpha`, and either sign of the source moment.

These are generic reversal-symmetric diagonal sources, not the canonical arithmetic CCM source and not RH counterexamples. They do show that factorwise sign/nonvanishing and even-only exclusion are not credible structural closure mechanisms.

More importantly, the simultaneous generic shift

```text
M -> M+tI
lambda -> lambda+t
```

can preserve the whole transfer package while moving the spectral root across zero. Therefore the shift-invariant transfer data cannot locate the absolute spectral origin.

## The remaining hard theorem is arithmetic normalization

PR #131's quadratic-normal source moment intentionally annihilates scalar identity shifts. That is ideal for the parity defect but erases precisely the information needed to know where zero lies.

The next source object must retain the absolute normalization:

```text
E(v) = Re<Tv,v>.
```

The decisive target is a canonical one-step domination theorem. For predecessor `A>=0`, shell `c`, coupling `b=P_W T c`, and `q_c=Re<Tc,c>`, prove from the actual pole/arch/prime source that

```text
q_c >= 0
|<w,b>|^2 <= q_c Re<Aw,w>  for every w in W.
```

This is equivalent to positivity of the one-step block extension when `A>=0`.

If it holds, then:

1. `w in ker A` forces `<w,b>=0`, so the resonant coupling disappears;
2. in the regular branch, `Ax0=b` gives `S0>=0`;
3. the existing first-bad theorem gives `Re S0<0` at the forced negative root;
4. contradiction.

A source-faithful proof of this domination is therefore the current central mathematical target.

## Quantitative clue

Post-#132 Taylor algebra and high-precision checks suggest unusually high source-coordinate cancellation under the boundary-flat moment constraints:

```text
odd source-atom energy:        first possible term at omega^7
even source-atom energy:       first possible term at omega^9
even quadratic-normal moment:  first possible term at omega^7
```

This is **DERIVED / EXPERIMENTAL**, not theorem authority. It is relevant only insofar as it can feed a rigorous absolute-energy/coercivity estimate.

## Permanent firewalls

- RH remains OPEN.
- `V=W⊕S` does not imply shell invariance.
- the special `T u0∈S` theorem does not make `u0` an eigenvector.
- D-equivalence is algebraic, not unitary/isometric.
- the predecessor correction in `D c+` must be retained.
- exact cubic factorization is rank at most one, not automatically exact rank one.
- `ker A` is the projected successor predecessor-block kernel, not the predecessor-size compressed-operator kernel.
- no `A^-1` at zero.
- `Re S0<0` and `Re sigma0<0` are not branch exclusion.
- the resonant pole is classification, not contradiction.
- no division by `alpha`, `Gamma`, overlap or source moment without separately proved nonzeroness.
- raw universal source-moment positivity is impossible for the linear observable except in the degenerate zero-functional case.
- shift-invariant transfer data do not determine the absolute spectral origin.
- positive-definite predecessor selection is simplification, not negative-root exclusion.
- generic countermodels refute generic arguments, not the canonical arithmetic source.
- numerical precision is not rigorous enclosure or theorem authority.
- machine claim promotion, negative-root exclusion and RH remain unchanged unless separately theorem-backed.

## Living research records

- `research/RHRC/README.md`
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_132_DELTA.md` — current post-#132 research delta
- `research/RHRC/RESEARCH_LEADS_POST_131_DELTA.md` — historical predecessor delta
- `research/RHRC/RESEARCH_LEADS_POST_129_DELTA.md` — earlier parity/source delta
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/countermodels/POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

Machine claim/binding promotion must not be inferred beyond entries actually present in the registries.

**RH remains OPEN.**
