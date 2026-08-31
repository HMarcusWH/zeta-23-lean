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

This remains the active finite/source route. The post-#75 research pass moved the immediate global implementation priority to W2-A/B/C because the existing explicit-formula proof appears to contain the direct W -> literatureRHS bridge almost verbatim. G1-B1B remains the parallel source-faithful lane.

Merged theorem state through the #71-#74 sequence includes:

```text
finite divided-difference/source calculus
  -> finite Guinand-Weil dictionary
  -> literal-tent explicit-formula extension
  -> exact finite zero-side matrix
  -> cutoff-free/canonical source matrix
  -> localized hard-window Fourier basis
  -> actual zero-extended full-complex finite space
  -> additive localized Weil RHS restriction
  -> direct Section-4 source matrix
  -> source-normalization repair
  -> finite kappa/source-sector bridge
```

The remaining source-facing chain on merged main is:

```text
d*u / L2 source interface
  -> PsiSharp / QW pullback
  -> QW_lambda|E_N = canonicalSourceMatrix
  -> source form-core / minimum-eigenvalue transfer if needed
  -> F1 canonical finite obstruction
```

The competing internal lane is:

```text
W2-A direct W/literatureRHS extraction
  -> W2-B reflection/evenization
  -> W2-C W self-value = localized additive RHS
  -> W0/W1 negative test + recentering
  -> F0-B finite additive/Fourier approximation
  -> F1 canonical finite obstruction
```

The current implementation queue is maintained in CURRENT_RESEARCH_PLAN.md. An open green PR is still branch state, not merged theorem state.

See `routes/R003_ccm_bridge/README.md`.

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
