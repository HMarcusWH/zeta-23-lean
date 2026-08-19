# R001 — Exceptional-zero amplification

Target decomposition:

1. **Zero-side growth:** prove that one off-line zero of depth `delta > 0` forces a rigorously defined multi-scale residual norm to have positive upper exponential rate.
2. **Prime-side upper bound:** prove unconditionally that the same residual norm has nonpositive upper exponential rate.
3. Combine the two exact theorems to rule out every off-line zero.

Current theorem status: both substantive steps are `OPEN`. The logical closure is easy; the analytic content is not.

## First live discovery run — 2026-08-19

The first executable R001 pass instantiated the R6 zero-sum residual

`Z_a(xi) = sum_rho exp(2a(rho-s))/(rho-s)`, with `s = 1/2 + i xi`,

on a finite numerical set of 200 zeta-zero ordinates and compared an on-line double control with functional-equation/conjugation-symmetric injected off-line pairs.

Bounded experimental result: `PASS / VALID` under `EXPERIMENTAL_EVIDENCE`, claim cap `FINITE_NUMERICAL_SYNTHETIC_DIAGNOSTIC_ONLY`.

For the local multi-aperture probe, the late fitted log-RMS slopes were approximately:

- on-line double: `4.97e-5`;
- delta = 0.005: `0.00146` (predicted asymptotic `0.01`);
- delta = 0.010: `0.00732` (predicted `0.02`);
- delta = 0.020: `0.03106` (predicted `0.04`);
- delta = 0.050: `0.09923` (predicted `0.10`);
- delta = 0.100: `0.19998` (predicted `0.20`).

The delta=0.05 signal transferred across four widely separated ordinates with local slopes `0.09910–0.09921`. Candidate-aligned ablation `delta -> 0` removed essentially the full growth slope. A 100-zero vs 200-zero fidelity replay changed the main delta=0.05 local slope by only `2.79e-5`.

### Cancellation lesson

The adversarial scan found the hardest tested two-pair configuration at ordinate spacing `0.02`. It produced strong aperture-dependent destructive/constructive interference: the sparse-grid late slope fell to about `0.077` for a predicted asymptotic rate `0.10`, while dense longer-aperture replay recovered an upper-envelope rate near `0.11`.

This materially sharpens the mathematical target. We should **not** seek a theorem asserting monotone pointwise growth at every aperture. The route should instead target a limsup / upper-envelope invariant, e.g. a rigorously defined quantity of the form

`Gamma = limsup_{a -> infinity} (1/a) log ||Z_a||`,

for which finite phase cancellation cannot erase an exceptional-zero exponential envelope.

The additional information channel relative to `ZeroSide/TightMult` is explicit: **multi-aperture evolution of the residual norm**, not another scalar function of the same single-compression trace/Frobenius/index data.

Machine-readable receipt: `research/RHRC/receipts/r001_discovery_run_002_2026_08_19.json`.

## Non-claims

- This finite numerical run is not RH evidence.
- It does not prove `R001_ZERO_GROWTH`.
- It does not prove `R001_PRIME_UPPER`.
- It does not justify finite-to-infinite transfer.
- The attempted 400-zero and 250-zero replays exceeded the available runtime; they were recorded as incomplete rather than substituted.
- Mathematical promotion remains Lean/comparator-only.
