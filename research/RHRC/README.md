# RHRC — Riemann Hypothesis route-closure control plane

RHRC is the research-side control plane for the HMWH Zeta23 fork.

It does four things without conflating them:

1. **discovery and falsification** — FFBBP-style candidate search, null competition, numerical diagnostics and countermodels;
2. **route governance** — explicit claim boundaries, intervention logging, provenance and dependency closure;
3. **source reconciliation** — pinned literature/source maps and executable oracles that are forbidden from becoming theorem dependencies;
4. **formal promotion** — exact conjecture -> adversarial review -> sorry-free Lean -> axiom audit -> route/claim registration.

The terminal target is unconditional RH. RHRC itself is not evidence for RH.

## Living research-control SSOTs

Two files carry the continuously updated research state above the route-specific level:

- **RESEARCH_LEADS.md** — complete accumulated research inventory. It retains active, testing, blocked, dormant, promoted, refuted and quarantined leads, their formal status, evidence, blockers, composition opportunities and cheapest falsification tests.
- **CURRENT_RESEARCH_PLAN.md** — current execution order from merged theorem truth, including parallel lanes, decision gates, stop conditions and the post-F1 program.

The lead ledger is memory; the plan is priority. Neither is theorem authority.

## Status labels

Use these meanings consistently:

- **PROVED** — exact statement established by Lean/compiler/CI;
- **DERIVED** — straightforward mathematical consequence of proved results, not yet separately formalized;
- **LEAD / HYPOTHESIS** — mathematically motivated direction;
- **EXPERIMENTAL SIGNAL** — numerical/discovery evidence only;
- **OPEN** — not established;
- **REFUTED / QUARANTINED** — failed for a reusable reason.

The machine claim registry uses its own compatible status vocabulary. Never silently upgrade between layers.

## Current route inventory

### R001 — exceptional-zero amplification

The zero-side exposed-pole / filtered-resolvent machinery is formally strong. The route's remaining scalar arithmetic upper-bound target was proved logically equivalent to RH itself.

Consequently R001 is a valuable theorem inventory and obstruction result, not currently an easier terminal route.

See `routes/R001_exceptional_zero/`, OBS-008 and the dead-route ledger.

### R002 — multi-probe / negative-index observables

Block-level off-line-pair negativity and separation from on-line rank-one combinations are proved.

The generic windowed-visibility and arithmetic legs remain open. PR #66 established that the production smooth-taper R002 object is not generically the canonical CCM finite object: the hard-window character relation is a specialization, not a universal identification.

See `routes/R002_multi_probe/`, OBS-009 and D0-R.

### R003 — CCM / finite Weil bridge

This remains the active finite/source route.

Validated theorem state now closes the entire shared function-level front end:

~~~text
W2-A:
  admissible pair
    -> pairwise Wsummand Summable
    -> genuine W(f,g) = literatureRHS(weilTest f g)

W0:
  off-line zero
    -> compact C² pole-neutral h
    -> Re W(h,h) < 0

W1:
  same obstruction
    -> exists L>0, r>0 with L=4r
    -> closed support inside (r,3r) ⊂ (0,L)
    -> pole zeros preserved
    -> Re W(h,h) < 0 preserved.
~~~

The W1 production theorem is
`Zeta23.ExceptionalZero.exists_strictAperture_poleNeutral_negativeWeilTest_of_offLine_zero`.
Its exact Stage-A theorem-green head is
`7abdaaf88f0e157c11049a0e65ebcb2c48fa86e2`, with axiom surface
`[propext, Classical.choice, Quot.sound]`.

The immediate global task is now a **bounded route-comparison pass**, not more route-general infrastructure.

Internal probe:

~~~text
I0 pole zeros of h -> pole zeros of EF.weilTest h h
I1 mu/gamma reflection evenness
I2 weighted gamma-channel integrability
~~~

The weighted integrability condition is independent of symmetry and is required before legal
Bochner integral splitting/averaging.

Source probe:

~~~text
S0 lambda = exp(L/2), 1<lambda, sourceLength lambda = L
S1 exact d*u/L²/kappa/q/PsiSharp/QW premise lock
~~~

If I0-I2 are bounded, continue:

~~~text
W2-B -> W2-C -> F0-B -> G1-A [PROVED] -> F1.
~~~

If the gamma/mu channel balloons while the source interface remains local, continue:

~~~text
G1-B1B -> G1-final -> G23 -> F1.
~~~

Keep both if both close cleanly.

The explicit W1 margin `(r,3r)` is a theorem-backed asset for the boundary-flat F0-B1 fallback.

The preferred post-F1 K0-K3 finite-wall program remains a **planned research route**, not yet a theorem-backed terminal reduction. K1 must first prove that an F1 negative finite value yields a first canonical singular crossing for the same finite sector before crossing exclusion can be composed to RH.

See `routes/R003_ccm_bridge/README.md` and `CURRENT_RESEARCH_PLAN.md`.


### R004 — finite displacement / structural route

The exact rank-at-most-two centered-index displacement law is proved.

The fitted tridiagonal-generator route to eigenvector convergence is quarantined because the recovered finite generators exhibit collapsing spectral gaps. The displacement theorem remains useful and composes with the canonical source matrix because scalar identity shifts commute with the index operator.

See `routes/R004_prolate_v2/`.

## Canonical finite source object

The current source normalization is:

```text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.
```

The historical printed normalization is:

```text
legacyPrintedMatrix = finiteMatrix.
```

Lean proves they differ by a scalar identity term.

Do not use legacy absolute eigenvalues, inertia, PSD, trace, determinant or lower bounds as canonical source spectral data.

## Post-green research law

Every meaningful green theorem/PR/experiment triggers a post-green pass:

- verify the exact head and exact theorem object;
- read the proof and assumptions;
- compare against older attempts and roadmaps;
- inspect upstream simplifications;
- inspect downstream newly reachable claims;
- revisit dead routes whose blockers changed;
- try to falsify promising clues;
- update documentation and registries if the dependency graph changed.

Green infrastructure is not green RH.

## FFBBP / OoL operational boundary

RHRC still preserves the domain-neutral process lessons of FFBBP and OoL-MVS:

- RUN42C is the qualified FFBBP finite-synthetic diagnostic profile; RUN42B is historical development lineage;
- OoL-MVS v2.7.6 contributes evidence/route-governance semantics only;
- neither system can certify a mathematical theorem.

Pinned references live under `ffbbp/` and `ool/`.

## Machine truth

- `CLAIM_REGISTRY.json` — merged theorem/claim state;
- `routes/ROUTE_REGISTRY.json` — route state;
- `BOUNDARY.json` — terminal-claim and governance boundary.

Living research state:

- `RESEARCH_LEADS.md` — complete research option/status memory;
- `CURRENT_RESEARCH_PLAN.md` — current execution order.

These must describe merged repository truth, not merely a green external branch.

## Documentation authority

See `DOCUMENTATION_AUTHORITY.md`.

Short version:

```text
live compiler/CI
  > merged declarations + registries
  > active route README
  > living research leads + current plan
  > current external handover/build plan
  > historical settlements
  > receipts / old plans
```

## Promotion rule

```text
discovery
  -> exact statement
  -> falsification/countermodel pass
  -> dependency/provenance closure
  -> sorry-free Lean
  -> axiom audit
  -> claim/route registration
```

RH remains **OPEN**.
