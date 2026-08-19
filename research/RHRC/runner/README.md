# RHRC one-command terminal runner

The runner is designed to **finish with a legally bounded answer**, not merely a plot or score.

```bash
python research/RHRC/runner/run_all.py \
  --zeros 100 --grid 5400 --aperture-max 300 \
  --output-dir rhrc_final_output
```

It runs RHRC regression/claim checks, executes the cached/vectorized R001 finite diagnostic, optionally builds `Zeta23.ExceptionalZero` when `lake` is installed, and writes:

- `R001_RESULT.json`
- `FORMAL_BUILD_STATUS.json`
- `FINAL_ANSWER.json`
- `FINAL_ANSWER.txt`

`FINAL_ANSWER` is deliberately fail-closed. A finite diagnostic PASS can produce `RH_OPEN` with a research signal, but it cannot produce `RH_PROVED_TRUE`. The latter is emitted only when `C_RH` and every theorem-relevant dependency are registered `PROVED_UNCONDITIONAL` through the Lean/comparator promotion path.

For larger Colab/HPC runs the R001 runner first attempts to bootstrap verified finite zero ordinates from Andrew Odlyzko's public `zeros1` table (first 100,000 zeros, stated accuracy 3e-9), caches them locally, and falls back to `mpmath.zetazero` if that source is unavailable. The zero source is recorded in `R001_RESULT.json`.
