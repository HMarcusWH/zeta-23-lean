# Repaired three-module local verification

All three exact repaired sources compiled successfully and saved genuine isolated `.olean` artifacts. All three unchanged independent consumer files then passed against those saved imports. The 14 printed declaration closures contain only `propext`, `Classical.choice`, and `Quot.sound`. There were no Lean errors, no consumer warnings, and no reviewer source or consumer repairs.

The complete machine-readable receipt, artifact/log hashes, and axiom lists are in `STATUS.json`. Input provenance is in `INPUT_PROVENANCE.json`; mathematical and scope review is in `SEMANTIC_REVIEW.md`.

| Module | Source SHA256 | Source / imported consumer exits | Source warnings | Primary candidate roots |
|---|---|---|---|---|
| MaskedNativeRate | `3fcb70e2fa504b5ef14d44c5a9d862f9bac4c8853556ed6e64a6f7e1066545c4` | 0 / 0 | 8 | 2 |
| ComplexLocalMeasures | `43d96d5474819b79c29853a81f8b4398f16d298470c2100fdade3fcada3a25b8` | 0 / 0 | 4 | 1 |
| AuxiliaryCompletions | `4dd849389b193ec3fbdbe718c30d62c7212b2d9e4b369437640d8b81804746dd` | 0 / 0 | 9 | 3 |

The warnings are linter/deprecation notices and redundant tactic warnings; they are preserved in the logs. This is not a warning-free claim. The source/consumer hashes still match the canonical latest zip entries; each module also matched its explicitly identified loose Downloads file byte-for-byte before copying.

The isolated base is `9b6a9a3a2badb4cff62a56c1158d9cef8759d30d`. Toolchain: `leanprover/lean4:v4.33.0-rc2`; each direct leaf used `lake env lean -DmaxHeartbeats=800000`, `LEAN_NUM_THREADS=1`. Source saves used `-o` for only the corresponding isolated module. No broad dependency build ran during this task. The warmed parent imports were read as cached dependencies. Other old unchecked files in the isolated checkout were not compiled or promoted.

The initial serial Mask save completed successfully. Its wrapper and started consumer were stopped at the orchestration boundary to prevent redundant writes while launching the two remaining modules in parallel. The authoritative Mask consumer rerun is `ExpectedMasks-imported-02.log`, exit0. `ComplexLocalMeasures-module-save-01.log` / `ExpectedComplex-imported-01.log` and `AuxiliaryCompletions-module-save-01.log` / `ExpectedAuxiliary-imported-01.log` are the other authoritative pairs. All owned compiler processes have exited; the writer slot is released.

## What became formally true locally

PROVED in the exact tested overlay: both full scheduled-mask roots, the full faithful complex-local-measure root, and all three auxiliary-completion roots have the independently stated consumer types. Constants remain outside all moving horizons/palettes and, for auxiliary ratios, outside all orders k. Actual native fields, genuine local complex variation, the endpoint atom, negative/zero Fourier frequencies, the extended convergent transform domain, and the filled half-point value survive the checks.

The six declarations are `log_slack_both_low_masks_subexp`, `log_slack_masked_energy_rate_difference`, `complex_local_measure_embedding_faithful`, `aux_completion_actual_transform`, `aux_completion_uniform_decay`, and `aux_completion_ratio_bounds` in namespace `Zeta23.OPICAFollowup`.

## Workflow harvest and acceptance boundary

This subtask ran local exact-source formal checks only. It did not run, inspect, or pass any remote CI job, complete release gate, aggregate independently bound root inventory, or committed-tree declaration-DAG export. A draft may carry this work with honest local-green/aggregate-pending labels. The integrating owner must bind the exact adopted bytes to the source register and run the broader gates before promoting root counts. The original100 roots remain required. No global proof-count promotion is made by this reviewer. RH remains OPEN.

## What changed and implications

The previous partial-kit review failed to elaborate the older auxiliary source and did not accept its new roots. These repaired bytes now pass the exact-source and imported-consumer gates without new assumptions or weakened statements. The independent checks replace external receipts for this narrow local result. The more general coordinate-level auxiliary ratio helper may be reused upstream, while its actual-zero specialization discharges the coordinate exclusions.

DERIVED: once the actual full physical rate is proved, the retained-mask rates can inherit it from their proved vanishing difference. The mask theorem itself gives no Theta equality or signed retained upper.

LEAD: the genuine beta/endpoint/Poisson and uniform-ratio package removes a prerequisite bottleneck for the all-multiplicity terminal-memory route. The next substantive missing work is actual top-moment, stable-input, finite-residual and terminal-memory control. A Laguerre normalization alone does not discharge those obligations.

LEAD: the complex common-growth tail theorem is reusable for genuine co-Poisson and zero-jet limits. Actual local-TV convergence and one common growth budget remain input obligations to prove for those native families. Native co-Poisson construction and positivity/sign conclusions are not obtained from the measure API alone.

Falsification checks: omitting the k=0 endpoint atom breaks the compact-profile identity; replacing the filled half-point value by the raw totalized product gives the wrong value; allowing constants to depend on the limiting horizon/order would invalidate the rate arguments; local convergence without a common growth bound does not invoke the Schwartz result. These checks were retained in the tested domains/consumers. None implies exclusion of an off-critical zero.

Highest-leverage next moves are the exact source-bound aggregate audit for publication, followed by the actual multiplicity-tail proof chain. Keep failed or unverified heat/spectral candidates explicitly WIP. Reconcile stale source prose saying `UNCHECKED` or that later roots are absent when integrating; this is a documentation issue, not a request to change any theorem type or normative requirement.
