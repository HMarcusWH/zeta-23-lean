# R001 — Exceptional-zero amplification

Target decomposition:

1. **Generic zero-side detector:** prove `R001_FILTERED_ZERO_POLE`: for an absolutely summable spectral filter, an off-line zero with nonzero filter coefficient forces the filtered zero family to fail `Subexponential`.
2. **Concrete zero-side growth:** instantiate that theorem with an admissible Weil filter and the exact claim-bearing arithmetic residual to prove `R001_ZERO_GROWTH`.
3. **Prime-side upper bound:** prove unconditionally that the same residual is `Subexponential`, establishing `R001_PRIME_UPPER`.
4. Combine the two exact concrete theorems to rule out every off-line zero.

Current theorem status (2026-08-20, all Lean, sorry-free, standard axioms only):

- `R001_FILTERED_ZERO_POLE` — **PROVED_UNCONDITIONAL**, in the corrected right-sided form:
  `Zeta23.ExceptionalZero.not_subexponential_filteredZeroFamily_of_right_zero`
  (`Zeta23/ExceptionalZero/ExposedPole.lean`). Subexponentiality would make the Laplace
  transform holomorphic on `Re z > 0`; meromorphic identity propagation from the safe
  half-plane seed forces it to match the filtered resolvent at the nonremovable target pole.
- `R001_WEIL_BRIDGE` — **PROVED_UNCONDITIONAL**:
  `Zeta23.ExceptionalZero.filteredZeroFamily_weilZeroFilter_eq_literatureRHS`
  (`Zeta23/ExceptionalZero/WeilFilter.lean`). The filtered family of the natural Weil filter at
  center `1/2` *is* the literature explicit-formula RHS of the translated test `k(· − 2a)`.
- `R001_ZERO_GROWTH` — **PROVED_UNCONDITIONAL**, in the adaptive pole-killed form:
  `Zeta23.ExceptionalZero.exists_poleKilled_test_not_subexponential_of_right_zero`.
- `R001_PRIME_UPPER` — **OPEN**, and now proved **RH-equivalent** in its scalar form:
  `Zeta23.ExceptionalZero.arithmeticSideSubexponential_iff_criticalLine`
  (`Zeta23/ExceptionalZero/ArithmeticReduction.lean`). See OBS-008 and
  `PRIME_SIDE_FEASIBILITY_2026_08_20.md`. Terminal state of the route: `RH_OPEN` with this one
  sharply defined remaining theorem.

### Route-specification adaptation — 2026-08-20 (DISCOVERY phase, logged)

The earlier specification said "one frozen Weil-admissible filter". That created an unnecessary
visibility obstruction: a single fixed compactly supported test may have
`paperFT k (gammaOf ρ₀) = 0` at the very zero it must see. The route now uses the logically
weaker but sufficient **target-adaptive** family: under the contradiction hypothesis that a
particular right-side zero exists, a complex-modulated smooth bump `q` is visible at it
(`exists_contDiff_visible_test`), and the pole-killer `k = q'' − q/4` (which multiplies the
transform at `gammaOf ρ` by exactly `ρ(ρ−1) ≠ 0` in the open strip) kills both deterministic
explicit-formula pole terms at every aperture. Generic filters are never assumed
reflection-symmetric; the left half-strip is excluded by the zeta reflection `ρ ↦ 1 − ρ̄` at the
final assembly (`criticalLine_of_arithmeticSideSubexponential`). This adaptation weakened the
required specification without weakening the target; the claim registry entries record it.

### Formal route correction — 2026-08-20

The original discovery language below used a positive limsup / upper-exponential-rate target. That remains useful intuition, but it is no longer the claim-bearing formal target. The frozen analytic target is the weaker and safer statement

`¬ Subexponential (fun a => ‖filteredZeroFamily phi c a‖)`.

This avoids overclaiming an eventual pointwise exponential lower bound and is exactly what the Laplace-pole contradiction can support.

The formal route also keeps the following seams separate:

- continuity/measurability of the filtered time family before Laplace integration;
- safe-half-plane Laplace equality versus analytic continuation into `Re z > 0`;
- local nonremovable target-pole / anti-cancellation theorem;
- concrete Weil-filter nonvanishing and exact same-filter arithmetic bridge;
- Archimedean growth control;
- finite-sum closure of subexponential bounds;
- the terminal unconditional prime/operator estimate.

No claim is promoted merely because these seams are named or partially formalized.

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

This materially sharpened the mathematical target. We should **not** seek a theorem asserting monotone pointwise growth at every aperture. The discovery-stage limsup quantity

`Gamma = limsup_{a -> infinity} (1/a) log ||Z_a||`

remains useful intuition for why aperture evolution exposes an exceptional zero, but the formal detector now uses a nonremovable Laplace pole to prove failure of subexponentiality directly.

The additional information channel relative to `ZeroSide/TightMult` is explicit: **multi-aperture evolution of the residual norm**, not another scalar function of the same single-compression trace/Frobenius/index data.

Machine-readable receipt: `research/RHRC/receipts/r001_discovery_run_002_2026_08_19.json`.

## Non-claims

- This finite numerical run is not RH evidence.
- It does not prove `R001_FILTERED_ZERO_POLE`.
- It does not prove `R001_ZERO_GROWTH`.
- It does not prove `R001_PRIME_UPPER`.
- It does not justify finite-to-infinite transfer.
- The attempted 400-zero and 250-zero replays exceeded the available runtime; they were recorded as incomplete rather than substituted.
- Mathematical promotion remains Lean/comparator-only.
