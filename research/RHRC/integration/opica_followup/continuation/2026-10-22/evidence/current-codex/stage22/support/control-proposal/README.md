Prepared on2026-10-24 for code commit `2440dcde7607baa7bcff2ce9626effa1ae9f3f07`, tree `dee5bc2fa3148ad42e3ef1fef17c4acf6a408f99`.

This proposal contains31 Lean source controls:27 expected compiler rejections and4 positive falsification theorems. It preserves all21 Stage21 source files byte for byte. The10 additions comprise3 canonical action/recovery mutations,3 actual square-measure domain omissions,1 unrestricted tempered-lattice compact-compatibility omission,2 CT1.3 normalization/slope mutations and1 omitted common total-variation bound for continuous compact tests. `CONTROL_PLAN.json` gives every source hash, scope and provenance. Adaptations to sealed scratch sources change only module imports; the square examples are split without changing their proof bodies.

Run while the owner repository and build cache have no writers. The owner explicitly authorized overlap with its read-only44-consumer replay after completing the broad build. Keep sources and shared cache quiescent until completion. The clean pin and full tracked-source bytes must match the plan; a changed pin requires a freshly reviewed plan, never editing this receipt into a pass.

From the project workspace, using the bundled native Python:

```powershell
& 'work/tools/python-3.13.5-embed-amd64/python.exe' -B `
  work/opica-stage22-control-proposal/run_controls.py `
  --output-dir work/opica-stage22/clean-controls `
  --workers 2
```

The result directory must be new and outside the owner checkout. Each compiler command uses the pinned native `lake env lean`, the original strict implicit settings and800000-heartbeat cap, an explicit external source root, and an external object output. The runner performs no `lake build` and requests no shared-cache outputs. It checks clean HEAD/tree before each command, full tracked-source hashes before and after the suite, and shared build-cache file sizes/timestamps before and after. The cache guard is a write detector, not a cold-object provenance certificate. This is a warm contract-mutation replay; the separate full100 cold export remains a separate obligation.

Positive files must compile with fully qualified requested axiom audits and only `propext`, `Classical.choice`, `Quot.sound`. Negative files must fail with the intended source-specific diagnostic; import errors, unknown identifiers/modules, resource failures and unrelated diagnostics fail the control. Both `error:` and `error(lean...):` are recognized. The legitimate `Invalid field choose` diagnostic on a function still awaiting its `LinearIndependent` premise is preserved. Lean can print `sorryAx` after recovery in a rejected named mutation; this is recorded as rejected output and grants no theorem authority. A positive control containing `sorryAx` fails.

`test_runner.py` checks the classifier against all historical actual logs at their own original source states, adversarial forged/wrong-name/resource diagnostics, standard-axiom coverage and source/cache guards. Those parser tests are protocol evidence only. They are not a Stage22 Lean replay. The planned31 controls are marked PREPARED until the native runner creates a successful exact-pin `CHECK_RESULT.json`.

`PASS_CONTROLS_ONLY` means only that these31 controls had their expected dispositions. It does not set independent review, source-register authority, parent-extension approval, aggregate acceptance, RH or Step4. All those acceptance claims remain governed by their original gates; RH and Step4 remain OPEN.
