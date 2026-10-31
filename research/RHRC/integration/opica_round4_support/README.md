# OPICA Round 4: source-locked mathematical support add-on

**Status: supporting-code candidate; consult the source-bound preparation receipts.** Authoring-session evidence below is historical. Fresh descendant and full Round 4 acceptance remain required. This package is **not** the full OPICA v1.1 composition implementation; it is an additive, narrow supporting-code package for the *next descendant PR after PR #297 is accepted and merged*. Step 4 and RH remain OPEN.

## Why this package exists

The v1.1 build kit is an independently validated implementation specification, not an executed host deployment. This add-on supplies new, separately staged Lean and Python files targeting missing mathematical connections while respecting the kit's F001–F078 plan. Do not unzip the full kit into a live RH checkout. Review these new files, then explicitly add their additional paths to the descendant file-class/manifest migration before staging them.

- `WitnessNorms.lean`: physical Pythagorean shell norm, nonunit Schur witness norms, unit-shell Rayleigh costs.
- `NativeRayConsumer.lean`: uses the EXACT existing even corrected-source and odd adjoint shifted-ray `...eq_one` theorems with a **visible independent bound hypothesis**. Not a proof of that bound.
- `ScalarShift.lean`: shift invariance countercontrols; not permission to change the canonical source.
- `Validation.lean`: independently restated consumers and transitive axiom printouts.
- Python: strict context metadata comparisons (NOT a proof adapter), deterministic tagged priority selection (NOT theorem-success probabilities), pinned blob preflight and normal/-O unit tests.
- `verify_support.py`: source-fail-closed local compilation and test runner for the new trusted-source add-on. It is NOT an untrusted candidate sandbox or a repository-wide acceptance replacement.

## Pinned reference

- Repository `HMarcusWH/zeta-23-lean`.
- Original inspected PR297 head `8109728135135a58eb98920180e03f77439c1da4`.
- Tree `5442650eb749576e4a82e2d57460a4b97e19b5a9`.
- Lean toolchain `leanprover/lean4:v4.33.0-rc2`.
- Mathlib pin `51e6992efd06126df61a496bebf8f49482a4e129`.
- Upstream Git blob identities are in `SOURCE_REFERENCES.json` and are checked rather than only documented.

## Coding-agent integration sequence

1. Read the **included unchanged upstream v1.1 kit** in `inputs/` (`START_HERE.md`, `specs/01_MIGRATION.md`, `CODE_TASKS.md`, `manifests/FILE_PLAN.json`, `CORRECTIONS_v1_1.md`). Its instructions take precedence for the composition-system build.
2. **Do not edit or push PR297.** Recheck whether PR297 has accepted merge and a complete appropriate scoped source/head check. If not, leave this overlay external. Reconcile accepted merge/tree/source bytes against the inspected head; if there are changes, update the new register and review every affected theorem.
3. Independently classify the new overlay paths. The original kit authorizes 49 ADD, 7 EDIT, 22 PRESERVE; this add-on introduces additional paths and therefore needs an explicit **reviewed descendant extension** to the exact file plan, source-classification and root manifests. Do not change existing protected rows.
4. In a fresh disposable checkout, COPY (do not run `git add` before the pinned-parent verifier) **only** files under `overlay/` at corresponding repository-relative paths. Reject collisions; do not blindly overwrite a source file. Do not install the v1.1 reference implementation under production package names without implementing its service contracts.
5. Run `python -B research/RHRC/integration/opica_round4_support/run_python_tests.py` and `python -O -B ...`.
6. Run `python -B research/RHRC/integration/opica_round4_support/verify_support.py --repo . --evidence /ABS/NEW/EVIDENCE/DIR` on the **exact original inspected parent** for initial proof engineering. This wrapper rejects a different HEAD; after a validated merge, the coding agent must record the reviewed source/tree reanchor and update this verifier to the accepted parent *before* its first successful downstream acceptance run.
7. Investigate and repair any Lean/compiler errors before claiming these files PROVED; do not add `sorry`, `admit`, project axioms, loose assumptions or cache substitutions. Build a fresh type/axiom/consumer receipt and run semantic stronger-statement controls.
8. Integrate the new accepted supporting lemmas into kit stages S1/S2 and their independent consumers, regenerate official graph/registry outputs, and execute the full production acceptance defined by the v1.1 kit. The kit's 117 production cases are not executed by this add-on.
9. Perform the Post-Green Research Pass, including source-bound theorem inventory and all research-producing workflow dispositions.

## Local verified / unverified boundary

**Verified in authoring environment:** original kit checksum/schema checks and reference Python tests; new Python test suite normal and -O; local source-blob matches; ZIP CRC and manifest (see evidence). **NOT VERIFIED:** fresh native Lean compilation (Lean toolchain unavailable in this environment), independent semantic mutation, v1.1 host integration, full workflows, mathematical Step 4 closure.

## Explicit known risks for the coding agent

- Imported Lean code may need proof-engineering adjustment after real pinned compilation. It is intentionally shipped with **no placeholders**; failures must remain failures.
- The The original parent HEAD and TREE are locked into the verifier and cannot be
changed using CLI flags. A descendant merge requires a separately reviewed
versioned source register/verifier; do not edit these constants to bypass the
policy.
- A metadata context fingerprint or scheduler tag does not discharge a logical premise. The new source bound is still OPEN.
- A runtime artifact receipt without raw trusted compiler evidence is not proof; final acceptance requires independent replay.
- The package's direct `lake build` uses the ordinary existing library import mechanism and must run only in a disposable checkout to protect active caches.

## Corrected V3 verification contract

- Lean Pythagoras uses the complex `mem_orthogonal'` orientation and the
  pinned `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` with `pow_two`.
- Six new separately typed consumer statements ensure that norms, Rayleigh
  depths, and scalar-shift controls were not silently weakened.
- Axiom evidence requires exact full declaration names and the approved
  transitive axiom footprint; similarly named suffixed declarations do not pass.
- The CLI no longer accepts an arbitrary `--expected-head`: require the exact
  original parent HEAD and TREE. A reviewed new descendant is a distinct mode.
- Before and after Lean, recheck source blobs and complete overlay inventory.
- The mutation failure must be the intended type error, not missing imports.
- The fresh evidence directory must be outside the checkout and absent on entry.
- This is NOT independent Lean compilation in the authoring environment:
  execute `verify_support.py` using the pinned project's `lake` to establish it.
