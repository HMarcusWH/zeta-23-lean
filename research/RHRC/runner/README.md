# RHRC terminal-status runner

This directory contains the original one-command RHRC status runner.

It is **not** an executor for the current R003 CCM/source critical path.

Its role is narrower:

- run RHRC registry/regression checks;
- execute the retained R001 finite diagnostic;
- optionally build selected Lean targets;
- emit a fail-closed terminal status.

```bash
python research/RHRC/runner/run_all.py \
  --zeros 100 --grid 5400 --aperture-max 300 \
  --output-dir rhrc_final_output
```

Outputs include:

- `R001_RESULT.json`;
- `FORMAL_BUILD_STATUS.json`;
- `FINAL_ANSWER.json`;
- `FINAL_ANSWER.txt`.

## Claim firewall

A finite diagnostic PASS can never emit `RH_PROVED_TRUE`.

The terminal result may become proved only when `C_RH` and every theorem-relevant dependency are registered `PROVED_UNCONDITIONAL` through the formal promotion path.

The active CCM/G1 route is developed and validated through Lean/CI and the R003 route machinery, not through this runner.

For current route state see:

- `../README.md`;
- `../routes/R003_ccm_bridge/README.md`;
- `../CLAIM_REGISTRY.json`;
- `../routes/ROUTE_REGISTRY.json`.
