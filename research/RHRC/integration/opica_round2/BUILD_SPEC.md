# OPICA Round 2 — final coding-agent build specification

**Version 3.0 · 25 October 2026 · repository `HMarcusWH/zeta-23-lean`**  
**Deliverable class:** final implementation specification, not an implementation or proof receipt.  
**Mathematical terminal state:** RH OPEN; Step 4 OPEN.  
**New Lean declarations compiled while preparing this package:** zero.

## 0. Mission and non-negotiable outcome

OPICA is the Obstruction-Preservation and Independent-Constraint Architecture. Build mathematics and evidence machinery that preserve the actual zeta-source obstruction, expose precisely what a proposed closing estimate must control, and make source-specific independent estimates testable. Do not optimize for a larger root count or another green wrapper.

The first usable output is the **actual-source fixed-filter four-column regional exclusion theorem**, accompanied by its exact rational certificate and transported zero-witness margin. The full implementation then supplies the remaining original causal/Gram/approximation contracts, supporting consequences, scoped no-go controls and independent native consumers. In parallel, research targets A–D remain available as alternative closing mechanisms. Their independent estimates are not supplied by this specification.

A complete supporting release is possible while RH remains OPEN. A statement `hypothesis → RH` must be registered as that conditional statement, never as proof of the hypothesis. Full core completion and terminal closure are different statuses with different acceptance gates.

## 1. Normative files and precedence

Read `AGENT_START_HERE.md`, this document, `BUILD_MANIFEST.json`, `MODULE_IMPLEMENTATION_GUIDE.md`, `MODULE_DAG.json`, `IMPLEMENTATION_CONTRACTS.json`, `INTEGRATION_PATCH_PLAN.md`, and `ACCEPTANCE_MATRIX.json`. The full mathematical clauses are preserved in `inputs/ROUND2_V2_1.json`; the 25 original records are additionally preserved in `inputs/ROUND2_ORIGINAL_25.json`. Do not rewrite either input to make implementation easier.

Use exact live source/compiler evidence before historical prose. Within this package, a versioned implementation clarification in `AMENDMENTS.md` controls placement, scheduling and ambiguous wording; it does not erase the mathematical clause. An unresolvable mathematical conflict produces `BLOCKED_CONTRACT` with the exact statement and counterexample or missing lemma. It is not permission to prove a weaker statement under the same ID.

`ROOT100_AUDIT.json` contains every original follow-up root, its frozen contract and premises, actual compiled type, transitive axioms, declaration/proof extract, source hash and independent consumers. `ROOT100_AUDIT.md` is its readable companion. `UPSTREAM_SYMBOLS.json` resolves the principal reusable definitions to real files and lines. The inherited research packet under `reference/prior_v2_1/` contains the written proofs, the full original requirement register and historical route evidence. Its older timestamps and statuses stay historical.

## 2. Exact starting object and authority

| Object | Required pin |
|---|---|
| Inspected PR294 head | `416aec21d4d6634675639b5397cc300d1f826e34` |
| Independently reconstructed uploaded tree | `0506bca8ffe613e9cd9ab844650a1141d4494f66` |
| Accepted parent/main at intake | `d53dd70d38b0762af130b1d19b795af259f505f5` |
| PR synthetic merge identifier | `b219d9d4e0eb6b3552c857e0d8f632825fc707d9` |
| Lean | `leanprover/lean4:v4.33.0-rc2` |
| Mathlib | `51e6992efd06126df61a496bebf8f49482a4e129` |
| New namespace | `Zeta23.OPICARound2` |
| Integration directory | `research/RHRC/integration/opica_round2/` |

The ZIP was authenticated by reconstructing its complete Git tree from 4,780 file contents and modes. The fresh current-head aggregate artifact was downloaded, its GitHub SHA-256 verified, all 4,780 receipt source hashes compared, and its command logs/object/exporter checked. The original sealed parser was executed on the raw compiler output and exactly reproduced the declaration, constructor, generated-equation and dependency records. This is a fresh evidence audit, **not a new Lean compilation**.

The receipt verifies 100 original roots, 28 acceptance units, 203 independent consumer queries, 83 canonical definitions, 18 constructors and 3,793 public declarations. The accepted transitive axiom set is contained in `{propext, Classical.choice, Quot.sound}`. The current parent P0 receipt separately verifies its 76-root population. The follow-up receipt still records `release_ready=false`, `full_release_accepted=false` and human review `NOT_ESTABLISHED`. These fields must not be flipped because CI is green.

Refresh live PR/base/head and the job census before implementation. If the head changes, compare exact source/tree and version the lock; do not replace the SHA while retaining old evidence. Start a local/authorized stacked branch from the inspected source. Do not merge PR294, create a remote PR, change repository settings, or rewrite history merely because this specification exists. A future merged base must be read and authenticated, not predicted.

## 3. Scope: minimal milestone, full core and optional extensions

The **full core has 40 contract families**: P01–P23 and S01–S17. The count is a specification count, not a count of new mathematical discoveries or necessarily of individual Lean declarations. A family can require several supporting declarations and clause consumers. P17–P18 are scheduled later but remain required for full core completion.

The **minimal first milestone** comprises P01–P05, S04–S06 and S16. It is explicitly a partial release, not `FULL_CORE_ACCEPTED`. S06 has no P19 dependency: the rational four-column baseline has a direct analytic proof and does not need general Gram inversion, a huge dictionary, multi-zero witnesses or the optional classical necessity theorem.

Optional extensions are P24–P25, O_C2/O_C3/O_C4, and X01. Keep each disabled until its actual prerequisite is proved and its separate expected types/axioms/controls pass. O_C4 may be discharged by exact reuse of the existing stronger native square theorem where the statements match; do not replace it with a weaker growth-restricted task. X01 must not change the native toolchain or import an axiom for an external theorem.

The four terminal targets `OPICA2_T_A` through `_T_D` stay in `OPEN_RESEARCH.json`, not as unproved Lean declarations. Subalternatives within them are alternatives, not a conjunction of four prerequisites. New proposed terminal theorems require their own reviewed statement and full proof; do not place a desired upper/sign in a `NativeCandidate` field and count construction of the wrapper as discharge.

## 4. Exact file footprint

`BUILD_MANIFEST.json` is the machine-readable path authority. It lists **89 required new paths, 12 optional new paths, and 15 existing authoritative edit paths**. It separately enumerates **81 current producer-owned files** that may change only through the canonical materializer. There are no authorized deletions, renames, toolchain updates or ancestor mathematical-source edits.

The mathematical layout is 16 required modules and five optional modules. Each has a separate `Validation/<Module>.lean` consumer. `Zeta23/OPICARound2.lean` is the minimal mathematical facade; `Zeta23/OPICARound2/All.lean` is the complete required-core facade. `Validation.lean` and the compiler exporter are audit-only. OptionalResearch/OptionalValidation do not enter default imports. The existing `lean_lib Zeta23` already covers this namespace: do not add a new library or change defaultTargets.

All new public declarations belong to the new namespace. Reuse actual old definitions directly or provide proved definitional/equational adapters. Do not copy and rename an old source definition into an apparently new “native” object. Any extra tracked helper file requires a versioned manifest and DAG amendment before acceptance. Private helpers within an authorized file are allowed; all public helpers still enter the compiler/axiom census.

## 5. Native objects and conventions to implement first

Use the existing complex causal closed subspace of full-line `Lp ℂ 2 volume`. Its norm is the L² norm and its inner product is conjugate-linear in the first slot. Distinguish pointwise representatives, almost-everywhere equality and equivalence classes. Every convolution-to-operator theorem must pass through the actual Fubini/Bochner identification; an equality of informal integrals is not a construction of the continuous linear map.

Keep `σ = 1/4096` and the literal original even probability source `q`, supported on `[-σ,σ]`. The source is `j=(D²−1/4)²q`, with one copy of the sinc product in its Laplace transform. Define **a new delayed adapter**, `jPlus(t)=j(t−σ)`, supported on `[0,2σ]`; do not redefine `nativeOriginalSource` or pretend its symmetric representative is causal. Retain `JPlus(z)=exp(−σz)J(z)` until its cancellation is proved.

Use the actual kernels

```text
c(t) = 1[t≥0] · (−exp(−t/2) + 2 exp(−3t/2))
a(t) = 1[t≥0] · exp(−3t/2) · floor(exp t) · (floor(exp t)+1−exp t)
T    = nativeDampedCompletionCausalL2Operator 0 (proof of 0≤0)
v    = c * jPlus
w    = a * jPlus = T jPlus
```

The rational transform is `R(z)=(z−1/2)/((z+1/2)(z+3/2))`; the completion transform satisfies `A(z)=R(z)ζ(z+1/2)` on its valid domain **away from the removable point**, while `A(1/2)=1/2`. Lean's totalized multiplication/division must not turn this into zero. `v` is not the old completed input involving `ζ′`.

Represent dictionary indices by positive integers or `Fin N` with explicit `i+1`. Set `u_n=n^(−1/2) D_log(n) jPlus`, `g_n=T u_n=n^(−1/2)D_log(n)w`. Prove delay isometry, causality and the actual dictionary action. The integer completion is locally finite at each time; it is not an L²-convergent ordinary partial sum.

A right-half nontrivial zero uses `λ=ρ−1/2`, `δ=Re λ>0`. The spectral coordinate `κ=ρ(1−ρ)` is a different quantity used by profile modules. Do not share a variable name or adapter that identifies them. The new probe's zeroth-order evaluation gives

`‖v−Tf‖ ≥ √(2δ)|R(λ)JPlus(λ)| > 0`.

Prove this for every actual causal L² input and then its range closure. No simple-zero premise, zeta-derivative lower bound, all-zero uniform constant or finite total spectral mass is required.

## 6. Mathematical build sequence

### Wave 0 — freeze, reconcile and establish the extension boundary

Run the supplied specification checker against the uploaded/exact checkout. Preserve the original 76/100 scopes and all 25 original Round2 objects. Capture actual git source identities, required upstream declarations, old registries and generated-state inventory. Implement the versioned descendant validation described in Section 10 before claiming that new source files are accepted by sealed ancestor gates.

This is an integration gate, not a new theorem. Failed ancestry or stale source receipts must stop registration. Development of local mathematical files may proceed without pretending a full release exists.

### Wave 1 — causal probe

Implement CausalProbe P01–P05. Prove actual source support, smoothness, moments, transforms, L¹/L² representatives, nonzero target and zeroth-order separation. The original inputs specify integral `jPlus=1/16` and `v=−1/24`. Treat nontrivial-zero/reflection assumptions explicitly. Export the conditional range-closure consumer, not the membership premise.

Write independently typed consumers at the same time. They must consume the literal native kernel/source and use arbitrary allowed multiplicity, not a caller-supplied abstract source satisfying the desired conclusion.

### Wave 2 — fixed filter and the first finite output

Implement FixedFilter S04/S16, FilteredClassicalComparison S05 and FiniteFilteredBaseline S06. Use

```text
B(z) = (z+3/2)/(z+1/2)^5
b(t) = 1[t≥0] exp(−t/2)(t^3/6+t^4/24),  ‖b‖₁=48
I(z) = (z−1/2)/(z+1/2)
Bv = I²(qPlus*u0),  Bw = I²(qPlus*h0)
```

Prove the causal all-pass isometry on the stated range; it is not a bounded inverse of B and not a claim that the isometry is onto. Keep the original probability convolution; a contraction upper bound is not equality with the unsmoothed classical Gram.

For exact coefficients `(1,−1,−1,−2/3)`, prove the period-12 step residual and Abel tail, transport its actual-source upper, and compare the correctly filtered witness. Required exact values:

```text
upper = 315384568453197375401 / 4648566756368995059600 < 17/250
lower = 4396431852289 / 49942416588800
upper < lower
region: 3/4 ≤ Re(ρ) ≤ 7/8,  1 ≤ |Im(ρ)| ≤ 2
```

The lower is a **squared** norm lower; compare it with a squared norm upper. The finite theorem excludes this compact rectangle. It is a pipeline acceptance baseline, not a new global zero-free result. The reflected counterpart requires the actual reflection theorem. Keep the region closed exactly as stated; no ordinate extrapolation.

S16 is the conditional global consumer for this **one fixed filter**: finite actual trials with full filtered residual norm tending to zero imply RH. Prove it by a fixed off-line-zero evaluation, not by inverting B. Existence of the sequence remains OPEN.

### Wave 3 — compulsory controls and calibrated evaluation

Implement TruncationControls and the required parts of CertifiedEvaluation. Prove the unconditional divergence of ordinary integer completion partial sums separately from the zero-conditional raw Möbius tail barrier. The exact safe cutoff is a kernel-lag cutoff of the floor kernel. Delay-adjusted output time and the noncompact target tail are separate budgets.

S01 supplies the raw missing-squarefree obstruction through 2047 and the exact activation endpoint/prefix Gram. It rules out residual norm below 6900 for initial raw dictionaries `N≤2046`, not for filtered dictionaries or all N. Do not waste the first computational milestone trying to optimize around this impossibility.

S07 has two distinct evidence obligations. The nonrange proof can use the written case split: exact range implies RH, then a rigorously established source-visible critical mode gives a boundary pole incompatible with L² evaluation. The quantitative input-cost theorem keeps its explicit actual critical-zero multiplicity/source order. A historical numerical zero certificate or a published verification is not an import. Either formalize the counting/visibility route from the supplied proof, or verify an actual bounded certificate inside the accepted proof system. Missing formal visibility blocks the unconditional clause; a conditional helper is useful but does not complete S07.

S08's general absolute error bounds do not require removing the critical-zero hypothesis from its separate asymptotic cost consequence. Prove and test both scopes. A fixed source tolerance must not be reused after coefficient growth.

### Wave 4 — full finite Gram, source approximation and regional certifier

Implement ProbeGram P06–P12/S02, CertifiedEvaluation P19/P23/S08, RegionalCertificates P21/P22 and ClassicalAdapter P20. The exact mixed column is known: with `C=J(3/2)^2/3`, `b_1=q0+C(ζ(2)−1)` and `b_n=Cζ(2)/n²` for `n≥2`. The hard arithmetic information is in the actual w-shift Gram. The simpler v-shift Gram is not a substitute.

Prove strict finite positive definiteness, least-squares minimizer, determinant ratio and innovation identity. `d_N≥0` and monotonicity are not `d_N→0`. Preserve the phase-sensitive spectral cross term and angular-frequency factor `1/(2π)`. Boundary transform identities need a legitimate limiting argument, not substitution beyond the proved half-plane.

P23 must preserve the original finite-box convolution and actual tail law. Prove centered-variance and fourth-moment error budgets in L². The finite source is an approximation with an absolute global error, not the canonical source itself. Retain the stated `M≥12` regularity unless a stronger theorem is actually proved.

P20's compact good kernel is C¹ on the positive half-line, with one-sided regularity at zero. Its explicit nonzero linear behavior near zero does **not** give C¹ regularity of its zero extension across negative x. Use `ContDiffOn`/one-sided derivative or an appropriate extension, prove the required endpoint conditions, and keep P24/P25 out of this adapter.

### Wave 5 — remaining required supporting mathematics

Complete DualCertificates P17/P18; ProfileControls S09/S10/S17; NativeCuts S11; SyntheticControls S12; NativeJumpControls S13; CT1Controls S14; FiniteNeutralApproximation S15. The module guide preserves each exact statement, dependency and countercontrol.

In particular, native rate preservation makes a putative smaller upper decisive but does not provide that upper. S10/S17 give negative positive-test pairings, not a positive arithmetic approximation of them. S14 classifies scalar normalizations of one CT1 family, not arbitrary renormalizations. S15 is an existential legal pole-neutral negative-witness producer under failure of RH; it is not a selected-ground identity or outgoing sign theorem.

Run all required independent consumers and build `Zeta23.OPICARound2.All`. The minimal facade alone is not this gate.

### Wave 6 — optional transfers and independent closing research

Build optional modules only with separate full evidence. Formal classical necessity P24/P25 must be a real theorem under compatible libraries, never a project axiom or hidden approximation premise. Optional C3 uses the corrected smoothing window and mass-one regularizer. X01's external seven-eighths theorem has its own pinned source/toolchain; no incompatible import or global native toolchain upgrade is authorized.

Keep searching A–D after each meaningful green. A conditional wrapper is not the research estimate. A source-preserving transformation that merely transfers the same positive rate or annihilator is useful classification, not contradiction. Record exact failed mechanisms and revisit them only when a relevant premise changes.

## 7. Numerical code and certificate contract

Implement the named Python files in the manifest. The normal path is a rational-complex **primal witness**; do not require a floating inverse or empirical rank threshold. Use exact `Fraction` arithmetic for rational baselines and rigorous outward bounds for transcendental/integral work. Discovery may use floating optimization, but its coefficient output must be rationalized and independently checked from scratch.

For arbitrary rational coefficients x, the analytic theorem uses

`E_x² = q0 − 2 Re(x* b) + x* G x`.

Given actual absolute enclosures, its upper is

`q⁺ − 2 Re(x* b̃) + x* G̃ x + 2‖x‖ ε_b + ‖x‖² ε_G`.

The two-sided optimal-distance bound additionally needs a proved/certified `G≥ell I`, `ell>0`, and the actual residual `b−Gx`. Never substitute an approximate residual without its error. A norm error and a squared-energy error are distinct schema fields; triangle bounds combine norms before squaring.

Let `A_x=Σ|x_n|/√n`. A sufficient raw error budget includes the coefficient-weighted source error, `2 exp(−Tlag/2)‖j‖₂ A_x`, quadrature/enclosure error, and the target tail. For `S≥Tlag+log N+2σ`, the lag-truncated trial has ended, but the target contributes

`‖1_[S,∞) v‖₂=(2/√3)|JPlus(−3/2)| exp(−3S/2)`.

The exact moment tail formula applies to the exact source. An approximate source must use its separately transported global error or its own proved moments. Filtered budgets multiply appropriate operator errors by the actual filter bound; a changing filter requires normalized error-to-witness comparison, not raw norm decay.

Certificates must bind: schema/version, source commit/tree, actual source definition/delay/product copy, kernel/filter identity, coefficient vector, region, source prefix M, kernel-lag and output horizons, precision/backend versions, all absolute error terms, analytical theorem dependencies, exact upper/lower, and producer/checker identities. Integers and rational numerators/denominators use canonical decimal strings; reject duplicates, zero denominators, boolean-as-integer values, NaN/Infinity, negative budgets, unknown fields/versions, invalid regions and omitted tails.

Use separate outcomes:

- `EXACT_FINITE_ARITHMETIC`: the rational comparisons passed; analytic hypotheses are not thereby proved.
- `CERTIFIED_FINITE`: a correctly scoped independent interval certificate passed; this is not automatically a Lean theorem.
- `KERNEL_CHECKED_THEOREM`: the exact native analytic statement and finite checker instantiation compiled with accepted axioms.
- `EXPERIMENTAL_SIGNAL`, `NO_CERTIFICATE`, `UNRESOLVED`, `INVALID_CERTIFICATE`: distinct non-proof outcomes.

`NO_CERTIFICATE` means the rigorous upper did not beat the lower; it is not a counterexample to the criterion. A timeout or exhausted refinement budget is UNRESOLVED. No receipt may carry `RH_PROVED=true` from finite sampling. General numerical enclosures enter a Lean theorem only through proved checker soundness or explicit Lean-proved bounds; untrusted Python output cannot be converted into a proof field.

## 8. Public API and dependency direction

The exact proposed root names are retained in the input contracts and module guide. Use one exported package theorem per contract family if convenient, but also expose named component lemmas needed by consumers. Freeze expected types before implementing bodies. Their full quantifiers, native identities and conclusion conjunctions must match the mathematical contract; names alone do not establish coverage.

Mathematical modules may import earlier mathematical modules and real upstream math. They may **not** import Validation, RHRC exporters, certificate logs, runtime review metadata or optional theorem assumptions. Validation imports mathematics. The audit exporter imports Validation. Registry bindings import only proved mathematical roots. Source-only graph candidates remain discovery-only.

Do not add new imports to ancestor OPICA/OPICAFollowup mathematical facades. Do not make older modules depend on Round2 to advertise a specialization. `MODULE_DAG.json` gives the proposed direct project imports and new-module edges; legitimate helper imports require a reviewed DAG update and a compiled dependency census. No imported ancestor audit module is permitted in the new mathematical closure.

## 9. Registration and deterministic generated state

After actual proofs and independent expected/domain checks pass, append new route-less supporting claims and exact bindings. Preserve every original claim object, route dependency, promotion cap and OPEN status. Conditional consumers are unconditional proofs of conditional propositions, so their statement text must include the antecedent. Do not bind terminal OPEN estimates to a sufficiency wrapper.

In FILE_CLASSES, classify exact audit/Validation/exporter/fixture paths before the broader mathematical namespace. Classify synthetic controls as auxiliary formalization rather than evidence for a native instance. Add semantic roles without enabling graph theorem promotion. Verify all new paths have one intended first-match classification and no UNKNOWN entries.

Prepare the same actual exporter prerequisites that fixed PR294's generated-state failure:

```bash
lake build Zeta23.RHRC.RegisteredClaimBindings \
  Zeta23.RHRC.DeclarationDependencyExport \
  Zeta23.RHRC.SourceCandidateResolution
python research/RHRC/tools/materialize_derived_state.py --write
python research/RHRC/tools/materialize_derived_state.py --check
python research/RHRC/tools/run_suite.py
```

Install the original hash-locked audit dependencies **and** declared RHRC framework requirements in the environment that runs the suite; do not suppress the cryptography-dependent checks. Do not update existing locks without a separate reviewed dependency change.

The materializer's actual order is registered dependency export → graph census → candidate exactification → FFBBP assurance → source-only dependencies → contact-quotient dependency/view → OoL atlas → graph validation. Its transaction restores previous outputs on failure. Preserve that order and rollback behavior. Check committed products **before any write** in CI, then independently regenerate in a disposable worktree and require exact equality. A post-write-only check can launder stale committed data and is not acceptable.

The current 81producer-owned path list is a snapshot, not a promise that future logical streams have the same byte size. Preserve index/shard format and logical digest validation. New or retired shard paths require an explicit amended output inventory. Never return to the oversized monolithic dependency JSON, hand-edit generated reports, or interpret graph reachability as a proof.

## 10. Sealed ancestor integration — required design

The current P0 and P1 validators are exact-source contracts. Adding Round2 files/claims is not accepted automatically, and simply adding a directory exemption would weaken them. Implement the narrowly reviewed descendant mode in `INTEGRATION_PATCH_PLAN.md`.

There are **two compulsory checks**, not interchangeable alternatives:

1. **Frozen ancestor contract replay:** authenticate the 416 baseline from immutable Git objects; validate the entire candidate delta against this new exact manifest; reconstruct an isolated baseline projection and run the original sealed P0/P1 validators/tests there. Preserve their original code, hashes, semantics and result source pins.
2. **Current-tree ancestor compatibility:** compile the original 76 and 100 declarations and independent consumers against the actual Round2 tree, export every transitive type/axiom/dependency channel, and compare their mathematical signatures and source-backed closures with the authenticated baseline. New global registration helpers may extend the exported population; they may not change original roots/definitions/premises or hide differences in private helpers.

Neither check substitutes for the other. Old-tree success does not validate current proofs; new-tree compilation does not authorize altered frozen contracts. Versioned ancestor entrypoint/workflow routing must distinguish these evidence classes explicitly. Unknown extension versions, malformed manifests, unauthorized edits or missing current compatibility evidence fail closed. Before the dispatch is accepted, run the new adversarial tests and the original validators on a deliberately corrupted baseline and deliberately corrupted child.

Do not rewrite the original 100 PUBLIC_ROOTS, PAPER_CROSSWALK, frozen hashes or parent extension objects. Do not set old human-review fields true. The new policy authorizes this exact descendant delta; it does not bless arbitrary future descendants or accept a digest supplied by the same unchecked object it is supposed to verify.

## 11. Compiler receipts and independent consumers

A receipt must bind exact requested/checked commit and tree, checkout kind, clean source manifest, Lean/Mathlib identity, build commands and exit codes, raw-log hashes, exporter source/object hashes, complete public inventory, all required types, constructors/generated equations where applicable, independent consumers and transitive axioms/dependencies. Reject truncated output, duplicate wire records, mismatched kinds/modules, absent completion sentinels, unknown project dependencies, missing TYPE/VALUE/STRUCTURE channels, stale objects and altered sources.

The supplied current 100 audit demonstrates the required pattern: rerun the original parser on raw output and compare parsed records, rather than trusting the receipt's word PASS. New Round2 parser code needs independent negative controls and its own source identity. Use independently written expected statements from the contracts, not mechanically copied source signatures. Compile native-domain consumer examples that actually discharge construction premises. Declaration-existence checks and `#check` are only diagnostics.

Every reachable public and private proof dependency must have an accepted axiom footprint. No `sorry`, `admit`, project `axiom`, assumed terminal estimate, unchecked external oracle or forbidden native evaluation axiom may survive. Do not confuse noncomputable classical choice with an executable algorithm, or require constructive computation where the existing theorem only proves existence.

## 12. CI workflow and command interface to implement

`templates/rhrc_opica_round2.yml` is a design template calling the following **new** CLI, to be implemented—not an assertion those commands already exist:

```bash
python research/RHRC/integration/opica_round2/run_checks.py contract --repo .
python research/RHRC/integration/opica_round2/run_checks.py formal --lane causal --repo .
python research/RHRC/integration/opica_round2/run_checks.py formal --lane filtered --repo .
python research/RHRC/integration/opica_round2/run_checks.py formal --lane gram --repo .
python research/RHRC/integration/opica_round2/run_checks.py formal --lane structural --repo .
python research/RHRC/integration/opica_round2/run_checks.py controls --repo .
python research/RHRC/integration/opica_round2/run_checks.py ancestry --repo .
python research/RHRC/integration/opica_round2/run_checks.py aggregate --repo .
python research/RHRC/integration/opica_round2/run_checks.py generated --repo .
python research/RHRC/integration/opica_round2/run_checks.py harvest --repo .
python research/RHRC/integration/opica_round2/run_checks.py acceptance --scope full-core --repo .
```

Each command exits nonzero for invalid evidence or unmet required coverage. Research outcomes such as UNRESOLVED may be a valid execution result only when explicitly allowed by the workflow contract; they cannot satisfy a mathematical acceptance clause. Optional lanes have explicit enabled/disabled state and cannot make required lanes disappear. The aggregate builds the full All/Validation/exporter surface at a clean current tree even when individual lane caches succeeded.

Use read-only permissions, exact PR-head checkout (record merge checkout separately), pinned actions, fail-fast false for formal matrix coverage, isolated mathlib-only cache reuse, declared finite resource budgets, and upload artifacts even on failed/unfinished scientific work. The fail-closed final summary checks all expected required job results with `always()`; missing/skipped/cancelled/timed-out required jobs are not success. Do not use `continue-on-error` to hide a proof failure.

Harvest all head-associated runs, **both pull_request and push**, additional ready-for-review runs, every attempt and all paginated jobs/artifacts. The GitHub convenience wrapper used during this review listed PR runs only, so a separate push lookup was necessary. Key rows by `(head, event, workflow, run_id, attempt, job_id)`, not job name alone. Expand matrix/conditional jobs from the actual YAML, retaining NOT_INSTANTIATED and legitimate NOT_APPLICABLE distinctions.

## 13. Required controls and tests

`CONTROL_REGISTRY.json` copies all 25 inherited controls with their exact scopes; `ACCEPTANCE_MATRIX.json` adds source/type/provenance/numerical mutations. Every claim must name the controls that test its vulnerable assumptions. All runtime rejection checks must survive Python `-O`; do not rely on `assert` for validation. The inherited finite arithmetic scripts are preserved unchanged as historical references, while the supplied new fixture checker uses explicit exceptions.

Test at least: wrong source copy/delay, removable point, zero dictionary index, v/w Gram swap, missing conjugation/factorials, repeated spectral nodes, raw integer “L² convergence”, omitted source/lag/target tail, updated coefficients with stale errors, negative-time leakage, variable filter scaling, interval endpoint rounding, duplicateJSONkeys/NaN/Infinity, forgedsourcehash, incompletecolumns, copiedtypeconsumer, stalecompileroutput, omittedprivateaxioms, source-onlygraphpromotion, unknownextension and mutationofoldOPENclaims.

Retain the existing meaningful negative results: equal-power causal twins, forced positive Gram/nonreal parameter, native finite quadratic no-repair class, CT1 nonmeasure limit, sharp-gap epsilon/window control, small inverse with growing forcing, high-order contact exits, modified-prime crossings, native gain's negative ordered minor, finite Euler-product divergence and failure of naive no-adjoint iteration. They prohibit only their stated mechanisms; they do not make all arithmetic or spectral routes impossible.

## 14. Historical obligations and research dispositions

Carry forward all 49 requirement IDs and WP0–WP7 from the included exact crosswalk. D2 Full remains distinct from frozen K3 feasibility and requires both parities over the full continuous window with seams and its actual prerequisites. The archived guarded campaign retains35unresolved even intervals; do not erase them with a fresh18/18 frozen-box result. Keep hM51, odd/tie adapters and the originally specified modified-prime K2 control visible.

Preserve all 13 deferred research lanes in OPEN_RESEARCH, including source-specific covariance, Suzuki forcing, corrected prime-prefix residual, boundary amplitude, cardinal/exterior contact, moving sextic, growing spans and alternatives. Exact source models differ: old two-copy-Q B input, logarithmic-derivative completed input and new one-copy delayed stable probe are not interchangeable.

Modern Paths A–D, legacy CI Tracks A–D and historical requirement “Track B” use different naming systems. Each cross-reference must identify its source vocabulary. No generic graph contact supplies a missing independent inequality. A fixed hypothetical witness can be frozen before sending a horizon to infinity; do not impose unnecessary all-zero uniformity, but do retain all same-witness source/phase/complement identities.

## 15. Definition of done and hand-back contract

A **minimal milestone** hand-back must contain the actual compiled native causal/filter/baseline declarations and consumers, exact finite certificate replay, original-scope preservation checks and explicit remaining full-core obligations. It must say MINIMAL_ONLY.

A **full-core implementation** hand-back must discharge every clause of all 40 mandatory families, all required new files, exact integration edits, full facade/consumers/exporter, required controls, both ancestry checks, canonical generated state and every mandatory workflow. Missing formal prerequisites such as an unconditional source-visible critical-mode argument are visible blockers, not dropped subclauses. Optional six families are reported separately as implemented/proved or deferred with their reason.

**Full release** additionally needs the existing independent review/approval process. **RH closure** additionally needs an independently established terminal premise and the literal unconditional RH theorem passing all claim gates. These two statuses do not become true from full-core CI alone.

Return exact final commit/tree, changed-path inventory, implemented/blocked clauses, independent consumer and axiom receipts, original 76/100semantic comparison, complete workflow harvest with scientific outcomes, numerical certificate scope, generated-state hashes and the Post-Green Research Pass. Report what became formally true, workflow results, what changed, upstream/downstream implications, revived routes, new hypotheses, falsification checks and the highest-information next move. Do not stop at “all tests pass.”

## 16. Verification boundary of this specification

This package performs source-tree/receipt validation and executable structural/rational checks. It does not supply a newly compiled Round2 proof, independently reprove every historical argument, replay every numerical campaign locally, or guarantee that every proposed formalization is easy. The inherited written proofs remain labelled as such. The coding agent must produce actual compiler evidence and surface mathematical failures rather than changing the contract. All identified requirements have explicit file, consumer, control, optional or deferred destinations.


---

# Audited implementation amendments v3.1

## A14 — User-controlled merged-base transition

Implementation begins only after observed PR294 merge, as the user requires. Keep416/0506 as immutable historical source/evidence. At merge, record actual merge/main commit, tree, parents and merge evidence; compare source/modes/blobs/toolchain/imports and refresh current compiler/workflow disposition in a separate versioned build-base lock. Static plan PASS never supplies merge evidence.

## A15 — Complete package inventory

Hash every package file except the root manifest itself, including both nested manifests. Verify exact census and digest/size for all records; reject duplicate/missing/unlisted/unsafe paths and disallowed links/modes. Add nested-manifest and extra-file mutations. A manifest establishes integrity only relative to an authenticated root digest; it is not human approval.

## A16 — Bind static metadata to actual authenticated source and compiler evidence

Check exact original100 contract/name sets, audit pins and source/proof hashes against immutable originals; resolve module/kind/type/axioms/consumer records in authenticated compiler output. Resolve upstream full names and source hashes, transitive imports and minimal/full/optional closures. Check all first-match classifications and unchanged old classifications. Preserve the independent raw-log reparse as a distinct compiler-evidence gate. The present independent audit confirms the supplied values are correct; the repair concerns guard coverage.

## A17 — Schema, semantic and early-failure receipt validation

Pin/meta-validate complete schemas and use positive/negative instances. Runtime strict loading and independent recomputation must also enforce canonical rationals, matched index/coefficient arrays, nonnegative complete budgets, valid regions, exact clause/source identities and evidence class. Define a separate failure envelope for stages that fail before exporter/log/type objects exist; never fabricate success fields to serialize an error.

## A18 — Required late dual-certificate slice

Use LATE_REQUIRED_MULTI_ZERO. Preserve mandatory P17/P18 in full-core coverage, facade and workflow lanes. Their omission remains legitimate only for an explicitly labelled MINIMAL_ONLY milestone.

## A19 — Explicit clause-to-control acceptance bindings

Use control_binding_overlay.json as a proposed binding layer:46 families,143 component clauses, expected scientific dispositions and evidence classes, with actual evidence references initially null and acceptance false. Refine the audit-proposed component splits against the complete normative source before freezing expected types. Require scoped review for NOT_APPLICABLE; reject a global controls PASS as coverage. Integrate the mapping into already authorized planned metadata paths, or version the footprint before introducing a new path.

## A20 — Scope the arbitrary-kernel S01e generalization

A causal nonzero w in L²(0,∞), or with local L² regularity on every tested prefix, and an exact finite left support endpoint yields the shifted-prefix Gram positivity result. Support alone does not ensure finite Gram entries: w(t)=1_(0,1)(t)/t is a counterexample. Residual coefficient rigidity additionally requires the actual local relation v=Σμ(n)g_n on that interval. Discharge the relation in the native instance through the source/convolution identities. Keep the inherited source record unchanged and reject an arbitrary target0 used to infer coefficients→μ.

## A21 — S07 prerequisite and semantic-independent consumer evidence

Freeze distinct S07 clauses for conditional boundary-pole/input cost, actual source-visible critical-mode/counting evidence, and unconditional nonrange. Missing visible-mode proof leaves that exact clause and full core unaccepted; the minimal baseline remains separate. Signature/hash mutation checks are provenance checks, not proof of independently reasoned expected types. Record full quantifiers, construction-premise discharge and actual independent review without auto-approving human review or requiring an unconditional off-line zero example.

## A22 — A03/C05 explicit research and control carry-forward

Carry AC01–AC09 from supplemental_foundation_register.json. Add A03_SHORT_COFACTOR_OPEN_S with exact historical two-copy source, cutoff/remainder, complete signed quadratic and native composite-sign/μ²/residue controls; distinguish it from the moving-sextic OPEN-S. Add the original C05 contact source/stable input/advance/domain, exact cumulative exponent and one-contact NQ target. Name finite-local-observation/finite-jet annihilator, renormalized jump-flux and even-completed-divisor lossless-scattering controls with their precise preserved/lost hypotheses. These are PAPER/OPEN or deferred controls, not additional mandatory core Lean families.

## A23 — Later historical alternatives and source-aware failures

Retain separate PAPER/DEFERRED fixed-K2 excursion and Gaussian linear-schedule routes. Fixed-K2 needs eventual all-large-aperture subexponential lower control; cofinal positive values are insufficient. Gaussian tail-negative witnesses permit an appropriate cofinal opposing bound. Preserve cofinal K*=2/zero-predecessor warning, scalar-work observation, native E″(0)>0/memory and small-gain failures, nonzero small Hankel control, causal-boundary G_plus/Hermitian blindness and increasing-aperture non-tightness. BC-1 stays a LEAD requiring actual local/source/domain adapters. Do not transfer old-source failures automatically to the new probe or add these alternatives as conjunctive core obligations.

## A24 — Current requirement aliases and conditional-proof wording

Use the verified49-ID/8-WP current alias map while retaining the historical crosswalk bytes. Section titles and JSON pointers are primary locators; refresh supplemental line locators after edits. Proving P→RH while P remains OPEN is a valid conditional theorem; claiming closure/application requires independent proof of P. Historical4A/4B/4C, modern PathsA–D and legacy CI/requirements tracks remain separately mapped.


The merged base identity is captured separately in ANCESTOR_LOCK; the original416 input identities and all original statement objects stay immutable. The failure-envelope schema and mathematical MultiplicityTail import refinement are recorded in BUILD_MANIFEST.
