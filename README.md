# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after theorem PR #134 = 7f1fec480d1ccbff04a456ab937accf7b23cc1af
live main tree = c142efa141036331d139c532d06e7a976c5b50c2

theorem-state anchor = PR #134 merge 7f1fec480d1ccbff04a456ab937accf7b23cc1af
validated theorem head = 753ee53a7fc08bd3be9a5a0f37417629122395f9
validated theorem tree = c142efa141036331d139c532d06e7a976c5b50c2
theorem-bearing merged through = PR #134
RHRC #870 = SUCCESS
Permansson #643 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
Control v2 / FFBBP v1.6 hardened research-control semantics = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact Lean compiler/CI remain authoritative over prose. PR #134 is theorem-bearing; it advances theorem authority beyond #131. The machine claim registries are not automatically promoted merely because supporting theorems exist.

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
  -> denominator-free whole-kernel source transport               PROVED / #134
  -> direct zero-shift cross-parity transfer                      PROVED / #134
  -> Gamma0 * mu(z) = 0 on the full even predecessor kernel       PROVED / #134

NOW — E4-A4b1 ABSOLUTE CANONICAL SOURCE ENERGY
  define and theoremize the exact quadratic energy
    E(v) = Re<Tv,v>
  and decompose it through the production pole/arch/prime source while
  retaining the canonical archimedean scalar identity correction that the
  #131 quadratic-normal moment intentionally annihilates.

NEXT — E4-A4b2 CANONICAL ONE-STEP DOMINATION
  q_c = Re<Tc,c> >= 0
  |<w,b>|^2 <= q_c Re<Aw,w>  for every predecessor vector w.
  This must be proved from the actual canonical arithmetic source; it is the
  decisive source-specific positivity/coercivity target, not a helper assumption.

FALLBACK SIMPLIFIER
  log-lift / analytic dense regular-aperture selection if resonance makes the
  arithmetic estimate unnecessarily difficult. Positive-definite predecessors
  alone are not exclusion.

TARGET
  no canonical first-bad negative state
  -> no off-line zero via the existing global reduction
  -> explicit terminal Mathlib RiemannHypothesis bridge
  RH                                                               OPEN
```

## What PR #134 made formally true

For an even predecessor-kernel vector `z`, with centered-index transport `D`, odd predecessor corrections `d` and `a`, normalized shell-coupling coefficient `beta`, and the exact #131 production source functional `mu`, Lean now proves

```text
A-(Dz) = beta(z) d + mu(z) a
<b-,Dz>/rho- = beta(z) + mu(z).
```

Projecting to the whole odd predecessor kernel gives the exact vector compatibility

```text
beta(z) K-d + mu(z) K-a = 0.
```

For the canonical even cubic-coupling kernel component this specializes to the normalized self-inner coefficient proved in `KernelSourceTransport.lean`.

If the even cubic coupling has a zero-shift preimage, Lean also proves the odd coupling-kernel relation driven by the even zero-shift response and source moment. If both parities have zero-shift preimages, Lean proves the direct zero-shift transfer

```text
sigma- = alpha0 sigma+ + Gamma0 * mu(u+0)
```

and the whole-kernel annihilation law

```text
Gamma0 * mu(z) = 0  for every z in ker A+.
```

`Gamma0` also has its exact trial/full-cubic-generator overlap representation. None of these theorems assumes a zero-shift inverse, pseudoinverse, Laurent limit, one-dimensional kernel, D-isometry, factor nonzeroness, or source sign.

## What changed after #134

The zero-shift transport problem is no longer the active research bottleneck. It is theoremized directly at zero. A Laurent/pseudoinverse route would now recover, at best, weaker shadows of already-proved finite identities.

The remaining obstruction is source-specific and sign-sensitive. Generic structural transfer data cannot locate the absolute spectral origin: exact scalar-shift countermodels preserve the transfer package while moving the spectrum through zero. The #131 source moment likewise discards scalar identity shifts by design.

Therefore the next source object must retain absolute canonical normalization:

```text
E(v) = Re<Tv,v>.
```

## Decisive arithmetic target

For a parity predecessor block `A>=0`, cubic shell `c`, coupling `b=P_W T c`, and

```text
q_c = Re<Tc,c>,
```

the target is

```text
q_c >= 0
|<w,b>|^2 <= q_c Re<Aw,w>  for every w in W.
```

If theoremized from the actual canonical source, this would simultaneously:

1. force `b` to annihilate `ker A`, removing the resonant coupling;
2. give the regular zero-shift endpoint `S0>=0` when `Ax0=b`;
3. contradict the already-proved `Re S0<0` at the forced negative first-bad root.

That is why one-step domination, or an equivalent canonical source-energy coercivity theorem, is now the central finite exclusion target.

## Falsification memory

Exact rational generic countermodels already rule out structural shortcuts based on generic sign or nonvanishing of `alpha`, `Gamma`, overlap, or source moment. They also show that strictly positive predecessors do not by themselves prevent a negative successor root. These fixtures are not canonical CCM sources and are not RH counterexamples.

Boundary-flat Taylor algebra suggests unusually high source-coordinate cancellations (`omega^7` / `omega^9`) that may become useful in the source-energy estimate. This remains **DERIVED / EXPERIMENTAL**, not theorem authority.

## Permanent firewalls

- RH remains OPEN.
- `V=W⊕S` does not imply shell invariance.
- D-equivalence is algebraic, not unitary/isometric.
- the predecessor correction in `D c+` must be retained.
- `ker A` is the projected successor predecessor-block kernel, not the predecessor-size compressed-operator kernel.
- no `A^-1` at zero.
- `Re S0<0` and `Re sigma0<0` are not branch exclusion by themselves.
- the resonant pole is classification, not contradiction.
- no division by `alpha`, `Gamma`, overlap or source moment without separately proved nonzeroness.
- `Gamma0 * mu(z)=0` is a product law, not automatic source annihilation or `Gamma0=0`.
- raw universal source-moment positivity is unavailable for the linear observable.
- shift-invariant transfer data do not determine the absolute spectral origin.
- positive-definite predecessor selection is simplification, not negative-root exclusion.
- generic countermodels refute generic arguments, not the canonical arithmetic source.
- numerical precision is not rigorous enclosure or theorem authority.
- supporting theorem checks do not automatically change machine claim promotion.

## Living research records

- `research/RHRC/README.md`
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_134_DELTA.md` — current post-#134 research delta
- `research/RHRC/RESEARCH_LEADS_POST_132_DELTA.md` — historical pre-#134 frontier
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/countermodels/POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

Machine claim/binding promotion must not be inferred beyond entries actually present in the registries.

**RH remains OPEN.**
