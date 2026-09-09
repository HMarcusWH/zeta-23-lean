# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after theorem PR #137 = fa2f209a6eb8b4059968e8d61239d80588ca256c
live main tree = e3de4dc0377f0124832822b6f97ab5bbd7718640

theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
validated theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
theorem-bearing merged through = PR #137
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
Control v2 / FFBBP v1.6 hardened research-control semantics = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact Lean compiler/CI remain authoritative over prose. PR #137 is theorem-bearing. The machine claim registries are not automatically promoted merely because supporting theorems exist.

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
  -> intrinsic V=W⊕S + shifted Schur/secular machinery            PROVED / #112-#122
  -> zero-shift kernel/range package + endpoint                   PROVED / #124-#125
  -> exact shell response + signed regular/resonant package       PROVED / #127-#128
  -> source-explicit cross-parity transfer                        PROVED / #129
  -> exact canonical source-moment decomposition                  PROVED / #131
  -> denominator-free zero-shift kernel/source transport          PROVED / #134
  -> absolute canonical source energy + channel decomposition     PROVED / #136
  -> exact canonical source pairing                               PROVED / #137
  -> denominator-free one-step determinant Δ(w)                   PROVED / #137
  -> domination => zero-shift regularity + endpoint >= 0          PROVED / #137 (CONDITIONAL)
  -> domination => no safe negative explicit Schur root           PROVED / #137 (CONDITIONAL)
  -> off-line zero => global-first-bad domination failure         PROVED / #137
  -> off-line zero => q_c < 0 OR exists w, Δ(w) < 0               PROVED / #137

NOW — CANONICAL ONE-STEP SIGN THEOREM
  prove, from the actual canonical arithmetic source and under the exact
  first-bad-compatible hypotheses,

    q_c = Re<Tc,c> >= 0
    Δ(w) = q_c q_A(w) - |<w,b>|^2 >= 0  for every predecessor w.

  Equivalently, establish the missing source-specific two-dimensional
  Gram/Schur positivity needed by `canonicalOneStepDomination`.

TARGET
  canonical one-step domination at every forced first-bad state
  -> contradiction with the #137 forced domination-failure certificate
  -> no off-line zero through the existing global reduction
  -> explicit terminal Mathlib RiemannHypothesis wrapper
  RH OPEN
```

## What PR #136 made formally true

PR #136 introduced the scalar-sensitive real quadratic energy

```text
matrixRealEnergy M x = Re(quadraticForm M x)
```

and proved that it remembers real scalar identity shifts. It decomposes the production `canonicalSourceMatrix` energy exactly into pole, reduced archimedean diagonal/off-diagonal, the retained canonical archimedean scalar correction, and the finite von-Mangoldt source-atom sum. It also proves that the canonical regular zero-shift trial energy is exactly `Re S0`, and that a safe negative explicit Schur root forces that trial energy negative.

No source-channel sign or positivity theorem is asserted by #136.

## What PR #137 made formally true

For either parity, predecessor block `A`, cubic shell `c`, coupling `b=P_WTc`, shell energy `q_c`, predecessor energy `q_A(w)` and

```text
Δ(w) = q_c * q_A(w) - |<w,b>|^2,
```

Lean now proves:

- exact production-channel formulas for `q_A`, `b`, and `Δ`;
- `Δ(z) >= 0` on `z in ker A` forces `<z,b>=0`;
- full `canonicalOneStepDomination` puts `b` in `range A`, so a zero-shift preimage exists without an inverse or pseudoinverse;
- with predecessor nonnegativity, domination forces `Re S0 >= 0`;
- therefore domination excludes every safe negative explicit Schur root;
- a hypothetical off-line zeta zero forces one global-first-bad state where domination fails;
- failure is exactly the explicit finite countercertificate

```text
q_c < 0
OR
exists w in W, Δ(w) < 0.
```

This is a reduction, not the missing sign theorem.

## Post-#137 research interpretation

The useful new object is the **explicit sign-failure countercertificate**. A hypothetical off-line zero no longer merely produces a negative eigenvalue or negative Schur endpoint; it produces one of two concrete canonical arithmetic failures.

But the claim firewall matters: with `A>=0` and a one-dimensional shell, proving `q_c>=0` and `Δ(w)>=0` for all `w` is essentially the missing block-positivity content. #137 makes that content exact and source-addressable; it does not make it easy or independent of the central obstruction.

The next research question is therefore not “can we restate positivity again?” It is:

> Does the pole/arch/scalar/prime structure of the actual canonical source force the two sign conditions by a mechanism unavailable in generic first-bad countermodels?

## Highest-leverage next moves

1. Expand `q_c` and `Δ(w)` completely through the #136/#137 production channel formulas and identify cancellations that are exact before inequalities are attempted.
2. Falsify the proposed signs on the smallest exact canonical states satisfying the relevant predecessor/nonnegativity hypotheses. A canonical failure kills this route without affecting RH.
3. Test whether the boundary-flat `omega^7 / omega^9` cancellation lead controls `Δ`, not merely the old linear source moment.
4. Search for a Gram/integral representation of the full canonical source pairing that makes `Δ` a manifest Cauchy-Schwarz remainder.
5. Use the log-lift regular-aperture route only if it simplifies the arithmetic estimate; #137 already shows a proved domination theorem would remove resonance by itself.

## Permanent firewalls

- RH remains OPEN.
- `canonicalOneStepDomination` is a proposition/certificate; no theorem says it holds.
- #137 conditional negative-root exclusion is not unconditional negative-root exclusion.
- the global disjunction `q_c<0 OR exists Δ<0` is forced by a hypothetical off-line zero; neither branch is ruled out.
- source-energy decomposition is bookkeeping until it yields a source-specific inequality.
- termwise positivity of source atoms is not available generically.
- D is algebraic, not unitary/isometric.
- no `A^-1` at zero.
- no division by `alpha`, `Gamma`, overlap or source moment without separately proved nonzeroness.
- generic countermodels refute generic arguments, not the canonical arithmetic source.
- numerical precision is not theorem authority.
- supporting theorem checks do not automatically change machine claim promotion.

## Living research records

- `research/RHRC/README.md`
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_137_DELTA.md` — current post-#137 research delta
- `research/RHRC/RESEARCH_LEADS_POST_134_DELTA.md` — historical pre-#136/#137 frontier
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

Machine claim/binding promotion must not be inferred beyond entries actually present in the registries.

**RH remains OPEN.**
