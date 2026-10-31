# Permansson integration

Permansson appears in this repository as an auxiliary formalization, a historical
external reference and a selected policy provider. These have separate sources,
toolchains and claim scopes. **RH and Step 4 remain OPEN.**

Start with the [framework and engine map](../../../docs/FRAMEWORKS.md).
The [integration boundary](../integration/INTEGRATION_BOUNDARY.json) preserves
the separation between research control and mathematical theorem authority.

## Host policy adapter

[opica_composition.py](opica_composition.py) implements a deterministic selector
over a complete, authenticated finite menu. It checks exact source identity,
allowed action IDs, positive costs, budget and trusted attempt counts. Among
affordable actions it chooses least-attempted first, then highest priority,
lowest cost and action ID. An empty or unaffordable menu produces an explicit
stop result.

[Journal](../integration/opica_composition/journal.py) supplies the durable counts
and commits selection and attempt start atomically. Candidate records cannot
invent their history or change the menu within a source generation. Policy
interventions preserve the source, checker, profile, grammar and target inventory.
The [service](../integration/opica_composition/service.py) reconstructs the bounded
search menu before dispatch.

Admitted policy claims are deterministic selection and conditional finite-menu
fairness. The adapter does not establish global theorem-search optimality or a
probability of discovery. Comparisons require the same source, checker, menu,
budget, population and phase. Repeated aliases do not increase the set of
discharged obligations.

## Embedded Theorem 3.1 formalization

The host sources
[GeneralFramework.lean](../../../Zeta23/Permansson/GeneralFramework.lean) and
[Theorem31.lean](../../../Zeta23/Permansson/Theorem31.lean) formalize measurable
joint-process well-posedness. A policy kernel, physical transition kernel and
state-update kernel induce a joint Markov kernel; an initial probability law
then determines a unique trajectory probability law with the stated initial and
transition identities.

This auxiliary result has its own
[formal verification workflow](../../../.github/workflows/permansson-formal.yml).
[FORMAL_VERIFICATION_NOTES.md](../../../Zeta23/Permansson/FORMAL_VERIFICATION_NOTES.md)
preserves its original v0.1.6 verification narrative. Use exact-source CI to
assess current validity; its historical draft wording is not a current run status.
This process theorem supplies no RH premise or theorem-search optimality claim.

## Historical external reference

[FRAMEWORK_REGISTRY.json](../integration/FRAMEWORK_REGISTRY.json) preserves the
v0.1.8 external reference at `c018f79…`, scoped to research regime and intervention
semantics with a bridge-pending label. This historical entry is distinct from the
selected OPICA provider below.

## Selected OPICA provider

The active selection is recorded in
[FRAMEWORK_PROVIDERS.json](../integration/opica_composition/FRAMEWORK_PROVIDERS.json)
and [selected_exports.json](../integration/opica_composition/providers/permansson/selected_exports.json).
At the 28 October 2026 documentation checkpoint it pins
`HMarcusWH/PermanssonLean` commit
`17c315f7df7abf457eb94d393bd526d46da6f6f4`, Lean 4.34 and the
`PermanssonResearch.ReverseSolver.ComputableFiniteMonitor` module.

Only three APIs are selected:

| API | Exact role |
|---|---|
| `computedValue_eq_value` | Executable rational finite-horizon value equals the specification. |
| `leastMaximizingControl_spec` | The fixed-order selected control is admissible and maximizes the score. |
| `computedMaximizer_attains` | The computed controller attains the finite-horizon value under the stated horizon identity. |

[provider.py](../integration/opica_composition/provider.py) checks pinned source,
package and compiler identities, builds a fresh selected source closure, compiles
[independently restated consumers](../integration/opica_composition/providers/permansson/ProviderAudit.lean.in),
audits transitive axioms and repeats the build independently. The host's Lean
4.33.0-rc2 objects and the provider's Lean 4.34 objects never mix.

These are generic finite-control contracts, not a calibrated model of live
theorem search. Admission stays `POLICY_ADAPTER_ONLY`,
`host_theorem_authority: false` and `model_optimality: NOT_ESTABLISHED`.
The host runner still requires its own isolated Lean proof, independent replay,
expected-type consumer and claim-validation gates for a mathematical application.
