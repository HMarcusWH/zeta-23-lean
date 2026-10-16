# Coding-agent execution brief — PR #292 continuation

**Goal:** finish the accepted source-faithful Step 1–3 output and its three explicitly conditional Step 4 consumers. Do not conduct a new proof-discovery campaign. Do not claim RH. Do not merge.

## 0. Read order

1. `AUDIT_REPORT.md`.
2. `spec/BUILD_SPEC.md`.
3. `spec/EXECUTION_MANIFEST.json` and `spec/OUTPUT_FIELD_CONTRACT.json`.
4. `spec/PROOF_RECIPES.md` for the mathematical task being implemented.
5. `spec/API_CROSSWALK.json` for every public name you touch.
6. `spec/REVIEW_DECISIONS_50.md` and `spec/D2_CONTINUATION_AND_RELEASE.md`.
7. `evidence/DECLARATIONS_BY_MODULE.md` for exact existing types; then open the actual pinned source and nearby definitions in the repository.

The original user contract, manifest, amendment and original mathematical packets are preserved under `inputs/`. Their status words are historical. None of the package's new proposed modules has been compiled by this review.

## 1. Pin and workspace

Repository `HMarcusWH/zeta-23-lean`; continue `research/post290-step123-output` at:

```
efa6ceea7bba2b34ff453a70a32a0800fee98b82
```

Expected tree:

```
511f6dc182d9a02b54e9404e93c32eb614fbff34
```

Keep Lean 4.33.0-rc2 and Mathlib 51e6992efd06126df61a496bebf8f49482a4e129. Read the live remote PR before writes. If its source has changed, stop with a delta report. Do not reset a dirty worktree, delete another agent's files, force-push, rebase against main, upgrade Mathlib or open a replacement PR by default.

Run the included read-only preflight against the checkout. It does not fetch or write Git refs:

```bash
bash /path/to/this/package/tools/preflight.sh /path/to/zeta-23-lean
```

## 2. Execute the ready tasks

Task dependencies and file owners are fixed in `EXECUTION_MANIFEST.json`.

- Native analytic owner starts **T01** (actual Y jet), then **T02** (A-X/B-Y wrappers).
- Source owner completes **T03–T04** (norm/scaling, aliases, physical normalization, rates, real phase quotient, odd equality).
- Finite owner completes **T05–T07** (public branches, actual neutral residual, AE-source inverse use).
- Native analysis owner completes **T08–T12** using the exact R5/R6 response and history formulas.
- Integration owner alone completes **T13–T19** after those producers exist.
- Numerical owner **T20** only reconciles/finishes the already approved D2 execution within its existing rules. This document authorizes no new dispatch, retry or budget.
- **T21** is final exact-tree acceptance and user merge review.

Shared-file edits belong to integration; independent owners supply completed modules and verified export lists. No two owners edit the same file concurrently.

## 3. Compiler loop (per task)

1. Implement the listed mathematical definitions and proofs, retaining every stated hypothesis and source identity.
2. Build every changed active module and its direct consumer with `lake build <Module> ...`.
3. On failure, preserve the exact error, source, Lean version and type. Repair elaboration without changing the mathematical statement. If the fixed proof recipe has a mathematical gap, STOP that task and its consumers with the precise gap.
4. Run the promoted proof-escape scanner from repository root; empty scope is a failure.
5. Add correct-kind source-origin bindings and print axioms/types. Definitions and structures are not theorem claims. Where pretty printing hides witness types, emit the full typed form.
6. Keep the task incomplete until its acceptance theorem actually compiles. A file, alias or metadata flag is not a substitute.

Do not convert failed proofs to `.lean.txt` and still count their original obligation complete. The pre-existing archived candidates remain historical; active replacement files need fresh evidence.

## 4. Exact output production

Native definitions do not receive rho or a closing law. The generated extension receives only the actual zero, its off-line exponent gap, requested original phase and lateness. Call the existing padded admissible retained-state producer once; use that exact detector/state for every view.

Emit symbolic formal expressions and theorem references for the hypothetical generated packet. Preserve the 44-pair native fixed-probe panel as the numerical product. Do not invent numeric off-line-zero coordinates or a numerical value for a noncomputable selected threshold. Preserve all unresolved and inapplicable numeric states.

The three final wrappers expose **A-X**, **B-Y**, **C-Schur** as unresolved sufficient premises. They are not tasks to assume or to mark PROVED. Do not build a fourth terminal criterion or a new contact hierarchy during this continuation.

## 5. Graph/release sequence

After all intended source and binding changes compile, run the existing complete freshness checker BEFORE any generator writes and record any intentional-source-drift failures:

```bash
python research/RHRC/tools/materialize_derived_state.py --check
```

Only after source/claim-classification updates are complete, regenerate the ENTIRE existing stack transactionally:

```bash
python research/RHRC/tools/materialize_derived_state.py --write
python research/RHRC/tools/materialize_derived_state.py --check
```

Stage intentional deletions before source census. Commit the intended source/generated changes only after local acceptance. In a genuinely clean checkout of that candidate commit, the same `--check` must pass before any `--write`. Do not mask stale committed products by regenerating first in CI.

Run the existing exact controls, new convention/evidence mutations, native-panel higher-precision checker and full final type/axiom contract. Join the separately source-bound D2 result only after all 460 children, fresh 768-bit checks of all 30 layers and NON-PARTIAL acceptance reconcile.

Current component mode must remain available for historical replay but cannot satisfy complete-output mode. Never flip `producer_complete` or `independent_assumption_review_pass` by hand. The latter requires the separately recorded semantic review of all 44 field groups on the final source.

## 6. Deliverables and stop rules

Deliver all original final output artifacts plus a final mathematical comparison, all-job workflow harvest and source-bound audit. Keep exact external compiler/run/tree IDs separate from committed source manifests to avoid self-referential hashes.

STOP instead of improvising when: the source pin changes; a new premise is needed; a detector/source/metric would change; a parity or tie branch is missing; a current source result contradicts its claimed scope; a required numeric interval remains unresolved; a D2 child cannot be recovered within its original allowance; the complete graph is stale; or a theorem's typed constructor does not fill the original contract.

The user decides whether to merge. This brief does not authorize a merge, source-replacing workaround, new expensive campaign, or unconditional RH claim.
