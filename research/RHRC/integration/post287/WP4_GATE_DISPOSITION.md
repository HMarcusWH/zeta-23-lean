# WP4 Full K3 frozen feasibility gate — historical test receipt

> **SECOND AUTHORITY CORRECTION — 2026-10-13:** later artifacts expose a
> distinct nan-curvature bug: Python min(0,nan.lower()) silently drops an
> unknown Taylor remainder. The first full campaign (run 38326458483) was
> stopped. Its affected tile passes are invalidated. The old frozen summary
> omits leaf curvature diagnostics and needs a fresh finite-guard replay.
> See `NUMERICAL_AUTHORITY_CORRECTION.md`; no complete K3 positivity is accepted.

> **AUTHORITY CORRECTION — 2026-10-12:** The older frozen-Q14 evaluator
> used the centre values of (a,b,d,a',b',d') when constructing the
> **second derivative of the determinant over a whole interval**.
> This does *not* enclose the genuine (Delta''(x)) throughout that
> interval. Therefore its "10 positive / 2 unresolved" subdivisions
> and the subsequent **18/18 PASS** on head
> `518c4fd00641e98ccbe26a33af7d7154ca068358` (run
> `38311427064`, artifact `11774767416`) are HISTORICAL
> EXECUTION OUTPUTS, **not rigorously certified positivity**.
> The old figures remain below for reproducibility, not authority.
> A corrected evaluator now uses full-interval values, first jets and
> second jets for (Delta''), and must pass a fresh exact-head
> GitHub run. Until then the corrected frozen gate is **PENDING VALIDATION**,
> and continuous K3 positivity is OPEN. No RH implication follows.


**Claim status:** UNRESOLVED, **RH OPEN**. This is a rigorous Arb *enclosure-method feasibility test*, not a theorem or a negative-eigenvalue finding.

- Candidate source head: `a7ace814928645dea86f1303807339387896e32e`.
- GitHub Actions: [run 38303390350](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/38303390350), job `wp4-k3-frozen-feasibility` (`114991486061`), artifact `post287-wp4-k3-gate` (`11773165754`).
- Exact source: `wp4_k3_frozen_q14_gate.py`, canonical 7×7 pole+arch+prime, 2D parity carriers, 384-bit Arb, Q14 frozen #176 centres, three frozen radii, both parities.
- Count: 12 prescribed boxes, 10 with separately positive a and determinant lower bounds, **two even determinant boxes unresolved**.

| Q14 coordinate t | Halfwidth | Parity | Certified lower bound for `a` | Computed determinant **lower bound** | Disposition |
|---|---:|---|---:|---:|---|
| `4071598118066347/10^16` | `2^-12` | even | `+2.2885530e-8` | `-5.5134964e-16` | UNRESOLVED |
| `2033825479935501/5*10^15` | `2^-12` | even | `+2.2906650e-8` | `-5.5197223e-16` | UNRESOLVED |

The **lower-bound values are negative**, not the actual canonical determinant. There is no certified negative eigenvalue. Both even determinants at `2^-16` and `2^-20` were positively certified; all six odd boxes passed.

The original second-order enclosure method therefore fails the **specified full-radius gate**. Per Marcus's D2=Full rev4 rule, **do not** increase precision/subdivision/derivative order on the same representation. A *separate, predeclared fourth-order Taylor model* (exact centre coefficients through three and a fourth-order interval remainder) is the only authorized method change. No fourth-order rigorously checked derivative evaluator has yet been produced. If that alternative fails, publish exact unresolved boxes and stop. WP4 all-interval both-parity positivity remains OPEN.

The workflow itself completed success because a **research gate records failure as a valid disposition**. It is not a green mathematical positivity claim.
