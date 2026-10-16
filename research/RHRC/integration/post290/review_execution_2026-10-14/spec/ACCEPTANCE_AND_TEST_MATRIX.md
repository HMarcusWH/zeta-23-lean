# Exact acceptance and test matrix

This is the implementation acceptance contract. The bundled secondary validators test metadata and finite algebra; only the actual repository compiler, source-bound semantic review, native evidence and clean-checkout integration can satisfy the final release gates.

## 1. Typed mathematical contract

Create `Zeta23/RHRC/Step123OutputContractCheck.lean`. Import the final public facade and producer, then check the following through **explicit typed terms** rather than declaration-name searches. Exact identifiers, existing types and source origins are in `API_CROSSWALK.json` and `evidence/DECLARATIONS_BY_MODULE.md`. New names are proposals until compiled.

| Gate | Required typed construction | Reject |
|---|---|---|
| MC01 | Literal fixed density, `k=Pq`, `j=P²q`, their actual support, derivatives, transform and source-only bounds | Alternate bump; transform treated as a density; single-Q source replaced by Q² |
| MC02 | Every requested original phase, actual zero, positive exponent below displacement, and lateness gives the actual padded coefficient vector at `ceil(L^4)` | Assumed finite transport or depth; one common deep time for both phases |
| MC03 | Actual physical realization equals the normalized coefficient realization, with unit norm, endpoint jets and both pole moments | Missing Fourier factor, hard-extension regularity or normalization proof |
| MC04 | Both phase denominators are strictly positive beyond one source-only threshold; the full Gram/native matrices give the real scalar quotient | Lost cross terms; a quotient accepted at a zero denominator |
| MC05 | One retained state from that literal detector supplies its own selected cutoff, ground, branch and inverses | A second chosen selector; copying trial phase or moments onto the ground |
| MC06 | Ground inverse at actual lambda has the 6-budget, detector inverse at minus eta has the 12-budget; both first-cutoff zero spaces handled | Lambda set equal to minus eta; depth substituted for parity gap |
| MC07 | Own-parity neutral residual equals the complete neutral-channel sum and its complex Gram sum | Old legal residual used as a neutral residual; omitted scalar/normal channels |
| MC08 | Strict-even, strict-odd and tied identities hold for the actual stored ground | An existence-only tie vector silently substituted; singular full inverse |
| MC09 | Actual compact L2 inverse has weak derivatives, clamped traces, uniqueness, norm 4 and AE-source compatibility | Free inverse field; pointwise uniqueness presented as all-representative invariance |
| MC10 | Actual mixed Weil response, four original histories and finite projected forcing equality | Prime-only response; assumed explicit formula; omitted conjugation or reflection |
| MC11 | Actual approximation error controls the projected forcing error in the specified norm and parameters | Unsupported uniform eta bound; a pointwise error used as an operator norm |
| MC12 | Original exterior record retains its nonzero interior and compact history | Relabelling the original trial as a continuous contact/null vector |
| MC13 | Actual physical Y transform has the required zero order and nonzero witness pairing in the same causal Hilbert space | Analytic-expression jet without the physical identity; wrong damping/conjugation |
| MC14 | Native output has no rho/closing-law dependency and contains all N01–N40 groups from constructed data | Metadata strings inhabiting proof fields; arbitrary source/response field |
| MC15 | Generated extension fills G01–G04 from the actual zero and the one native state | Caller-supplied visibility, correction, forcing, exterior, inverse or output-existence hypothesis |
| MC16 | Exactly A-X, B-Y and C-Schur are the unresolved premises in their respective RH sufficiency wrappers | An unconditional RH label; hidden Step 1–3 premise; A-X inserted into C-Schur |

The typed checks must consume the actual constructors. A theorem name with a stronger premise does not pass merely because its conclusion matches. Definitions and structures require correct-kind checks; `#print axioms` alone does not expose a structure's semantic obligations. Retain full binder types, including `NativeCompactPoleH2 s f` in the existence-and-uniqueness theorem.

## 2. Exact command sequence for every owned proof task

1. `lake build <each-new-or-changed-active-module> <its-direct-consumer>`; preserve all exits and logs with `set -euo pipefail`.
2. `python research/RHRC/closure_batch/check_lean_proof_escapes.py --scope promoted` from repository root; zero-file scope fails.
3. `lake build Zeta23.RHRC.Step123OutputContractCheck Zeta23.RHRC.Step123OutputBindings` after their source dependencies exist.
4. `lake env lean Zeta23/RHRC/Step123OutputContractCheck.lean` and the existing bindings execution/export.
5. Preserve exact checked head/tree, toolchain, source blobs, fully typed declarations, compiler logs and axiom lists. All new formal roots use only the approved standard axiom footprint.
6. Run the owned regression tests in ordinary Python and under `python -O`. Test functions must not disappear under optimization.

The new complete-output mode of the existing receipt builder must fail until MC01–MC16, every API and every field group is satisfied. The current downloaded component receipt is a mandatory negative release fixture: it must remain valid as component evidence and be rejected as a full output release.

## 3. Mandatory adversarial mutations

Preserve all existing controls and add the following source/convention tests. A test success records a falsified inference, not a proof of RH.

| Mutation | Expected disposition |
|---|---|
| Replace J by the correlation transform with Q² | SOURCE_MISMATCH |
| Pair at conjugate(w), or omit epsilon from p=w+epsilon | WRONG_TRANSFORM_POINT |
| Use order m instead of m−1 for physical Y | WRONG_ZERO_JET_ORDER |
| Insert an extra factorial or omit the parity sign | WRONG_JET_COEFFICIENT |
| Evaluate the zeta-pole point with totalized products instead of the proved limit | EXCEPTIONAL_POINT_MISMATCH |
| Swap the 6 and 12 inverse budgets | WRONG_SHIFT_BUDGET |
| Set lambda=−eta or parityGap=D/3 | UNSUPPORTED_SPECTRAL_IDENTIFICATION |
| Drop D0 inverse from the even shifted-ray residual equation | WRONG_CARRIER_MAP |
| Drop the strict-odd minus sign or replace D0* by D0 inverse | WRONG_ADJOINT_IDENTITY |
| Apply the even residual bound to an odd vector | INAPPLICABLE_BRANCH |
| Set the neutral continuum defect to zero | OMITTED_NORMAL_TERM |
| Replace the complete detector complement by the ground's one-dimensional shell | WRONG_SCHUR_SPACE |
| Delete a reflected prime history or the original interior response | INCOMPLETE_FORCING |
| Replace an actual pole-neutral residual by the legal residual | WRONG_COMPRESSION |
| Use positivity/real-root data from the original source for a selected finite ground | UNPROVED_PROPERTY_TRANSPORT |
| Promote a finite inverse iteration to infinite range membership | MISSING_DOMAIN_LIMIT_THEOREM |
| Mark unrun/unresolved/skipped numerical geometry complete | INCOMPLETE_NUMERICAL_COVERAGE |
| Stale source tree/type hash, duplicate root, missing API or wrong declaration kind | EVIDENCE_INTEGRITY_FAILURE |
| Set completion flags without the source-bound semantic review and typed contract | INCOMPLETE_PRODUCER |
| Count a successful diagnostic UNRESOLVED disposition as positivity | SCIENTIFIC_DISPOSITION_MISMATCH |

Use the retained modified-prime, degenerate tie, arbitrarily small parity-gap, coincident product-zero and finite-shift controls at their original hypotheses. Do not change their old bytes to reflect a later theorem about another object.

## 4. Artifact contract

Use the original filenames from the accepted build: `STEP123_FORMAL_OUTPUT.json`, `SOURCE_LINEAGE.json`, `CONSTRAINTS.json`, `NATIVE_OBSERVATIONS.jsonl`, `RESIDUAL_CHANNELS.jsonl`, `COUNTERMODEL_SURVIVAL.json`, `D2_CONTINUUM_RECEIPT.json`, `STEP4_CUTS.json`, `WORKFLOW_HARVEST.json/.md`, `STEP4_RESEARCH_HANDOFF.md`.

Every record must distinguish:

- execution state and exit code;
- integrity/source identity;
- mathematical object and carrier;
- parameters, source scale, cutoff, phase, normalization and shifted operator;
- theorem/type/axiom receipt or bounded numerical evidence;
- scientific disposition and resolution;
- current versus inherited authority;
- input/source transformations and any lost properties.

Resolution is one of `SYMBOLIC_FORMAL`, `RATIONAL_EXACT`, `CERTIFIED_INTERVAL`, `FLOAT_DIAGNOSTIC`, `UNRESOLVED`, `NOT_APPLICABLE`. Conditional theorem-selected states stay symbolic. The existing 44-pair/176-row native observations stay a separate unconditional finite panel; they do not inherit a hypothetical zero, detector or selected-ground claim.

For mathematical fields, consume `OUTPUT_FIELD_CONTRACT.json` and verify every listed producer and consumer. The full original API list is mandatory: no automatic deletion of aliases just because a stronger theorem exists elsewhere. Record actual origins and explicit reviewed compatibility.

## 5. Full release acceptance

Release is a conjunction of separate obligations, not one green job:

1. Complete mathematical producer and all three conditional consumers, with the independent Step 4 laws still OPEN.
2. Exact final-tree all-root compiler, type, axiom and proof-escape evidence.
3. Source-bound independent semantic review of all 44 field groups and the fully typed contract.
4. Existing and new adversarial controls, plus complete native panel reconstruction at its finite scope.
5. Full approved D2 result: all unique children, final fresh 768-bit all-layer no-search validation and NON-PARTIAL gate, with exact source equivalence.
6. Entire existing graph/claim/derived-state stack fresh in a clean checkout before generators run.
7. Every attached workflow/job harvested with its precise scientific result; running, skipped, unresolved and failed cases never silently passed.
8. A post-green mathematical comparison on the same source and norm; no claim that more complete infrastructure supplies the missing opposing Step 4 estimate.
9. Separate user decision before merge.

No universal paper argument, finite symbolic fixture, artifact upload or metadata validator replaces its corresponding Lean or numerical soundness obligation.
