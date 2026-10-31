# FFBBP integration

FFBBP supplies typed assurance for research decisions and evidence in this
repository. Its recorded reference title is **FFBBP: A Reference Framework for
Latent-Field Inference and Typed Assurance**. **RH and Step 4 remain OPEN.**

Start with the [framework and engine map](../../../docs/FRAMEWORKS.md).
The [integration boundary](../integration/INTEGRATION_BOUNDARY.json) defines
the common authority limits.

## Active assurance interfaces

[FFBBP_V17_ASSURANCE_REFERENCE.json](FFBBP_V17_ASSURANCE_REFERENCE.json) records
the imported version 1.7 assurance architecture. Profile, protocol and execution
have distinct identities; changing one creates a new qualification object unless
a separately justified equivalence is supplied.

The gate model in [v17_contracts.py](v17_contracts.py) and
[v17_gates.py](v17_gates.py) distinguishes `PASS`, `FAIL`, `NOT_APPLICABLE` and
`NOT_EVALUATED`. Required gates are satisfied only by `PASS`. Structural
nonapplicability must follow the frozen protocol; it cannot waive a failed or
missing required result after observation.

The [OPICA adapter](opica_composition.py) checks complete expected gate sets,
source/run identities and independently replayed raw evidence. It also checks
reduction sufficiency on finite populations, restores full contracts after
retrieval, validates residual-budget interfaces, requires source-compatible
countermodels and deduplicates evidence origins.

In the governed deduction runner,
[journal.py](../integration/opica_composition/journal.py) reconstructs `SOURCE`,
`KERNEL`, `AXIOMS` and `INDEPENDENT_EXPECTED_TYPE` from the independent native
replay before publication. A candidate's own `PASS` label is insufficient.
Lean and the required claim-validation gates remain the mathematical authority.

## RHKG snapshot assurance

[rhkg_assurance.py](rhkg_assurance.py) consumes the Lean-exact candidate receipt
surface under [the v2 configuration](configs/rhkg_candidate_reduction_v2.json).
It tests whether a reduction preserves two declared outputs: the exact visibility
class and the decision whether a candidate is `SOURCE_ONLY_PUBLIC_THEOREM`.

The selected `MODULE_VISIBILITY_SNAPSHOT` reduction supplies post-reference
navigation cohorts. The module-only negative control exposes information lost
when a module contains declarations with different visibility decisions.
Results apply to the exact finite snapshot. They do not establish autonomous
transition closure, future-snapshot sufficiency or mathematical relevance.

The [generated report](generated/RHKG_CANDIDATE_REDUCTION_ASSURANCE.json) records
the input hashes, qualification identities, counterexamples and dispositions.
Its counts belong to that source snapshot. The
[derived-state materializer](../tools/materialize_derived_state.py) owns generation
order; generated reports are not edited by hand.

## Preserved runtime and version history

[FFBBP_REFERENCE.json](FFBBP_REFERENCE.json) and
[IMPLEMENTATION_CLOSURE_OVERLAY.json](IMPLEMENTATION_CLOSURE_OVERLAY.json) preserve
the separate v1.5.1/RUN42C inductive-firewall runtime lineage and its finite
synthetic diagnostic qualification. RUN42B is preserved as superseded development
evidence. These historical qualifications do not certify a real unknown field
or an RH conclusion.

[FFBBP_V16_ASSURANCE_REFERENCE.json](FFBBP_V16_ASSURANCE_REFERENCE.json) preserves
the earlier 1.6 reduction, commutation, horizon and witness overlay. Version 1.7
builds on those assurance distinctions while keeping the runtime qualification
separate. Importing its architecture does not promote RUN46F execution authority
or transfer RUN42C qualification to a new adapter.

FFBBP output remains research control or scoped diagnostic evidence. Discovery
leads return to exact Lean statements and new proof attempts.
