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

This remains the active finite-obstruction route.

Merged baseline:

~~~text
main = 9e899ca322116e28a56a4412d48aef0052b86fbe
tree = ad636143768dcaa4dbeb23a0ea295d7b2d6b1c9b
merged through = PR #84
PR #83 theorem head = 556be6c2b42e912c58751988c580ab4e0091822d
PR #83 merge = 7b8e0cc9abbaeff97d88ec67ada40734619a8d07
PR #84 final validated head = 1a518c9ebd408fa559c5eff281eafe5ff3b2af48
RH = OPEN
~~~

The theorem-backed function-level chain is now:

~~~text
off-line zero
  -> W0 negative compact C² pole-neutral W witness
  -> W1 strict finite aperture / margin
  -> W2-ZS direct diagonal identity
       W(h,h)=localizedWeilAdditiveRHS(h,h)
  -> strict negative localized additive witness.
~~~

Registered #83 claims:

~~~text
R003_WEIL_LOCALIZED_ADDITIVE_SELF_BRIDGE
R003_STRICT_APERTURE_NEGATIVE_LOCALIZED_ADDITIVE_WITNESS
~~~

The W2-ZS proof is concrete-zeta-specific and uses the actual `rho -> 1-rho` carrier equivalence with multiplicity, exact Fourier reflection and summability-safe zero-sum reindexing. It does not require the old analytic mu/gamma-evenness or weighted gamma-integrability route.

The immediate global internal task is now **F0-B finite approximation / strict-negativity transfer**:

~~~text
F0-B1:
  boundary-flat globally C² finite Fourier approximants
  + W continuity

F0-B2:
  direct localized-additive continuity
  on the existing legal finite vectors

WCONT:
  family-level topology / domination gate
~~~

No candidate is promoted until the bounded topology spike decides it. Individual Summable certificates do not imply a uniform summable majorant.

The previous analytic W2-B route remains a dormant independent cross-check.

Source work remains active in parallel and preserves the #84 sign firewall:

~~~text
S-GEOM L <-> lambda
S-IFACE d*u/L²/kappa/q/PsiSharp/QW
-> G1-B1B -> G1-final

S-NEG or exact W/localized/QW sign composition
-> G23
-> F1
~~~

G1-B1B/G1-final do not themselves transfer the strict negative sign into QW.

The shortest internal continuation is now

~~~text
F0-B -> G1-A [PROVED] -> F1.
~~~

The preferred post-F1 K0-K3 finite-wall program remains planned research, not a theorem-backed terminal reduction.

See `routes/R003_ccm_bridge/README.md`, `CURRENT_RESEARCH_PLAN.md`, `RESEARCH_LEADS.md` and the post-green W2-ZS settlement.


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
