# Post-#287 WP0–WP7 integrated build (single draft PR)

**Baseline:** `main` commit `bb7c9c9d54fa2d1f82ad5b682c31148539a8f78c`; exact tree `e492714b5d5db02b6fc4ed2e10d0c81ef66d9087` (PR #288 merged).  
**Specification:** user-approved `POST287_NEXT_THREAD_PLAN_2026-10-11`, rev4; D2 = **Full K3**, both parities, over `[1/512, log 16]`.  
**Claim firewall:** `RH_OPEN`. This research PR must not merge by merely making a code/build gate green. User controls merge.  
**Intent:** one PR; incremental, reviewable commits and checked data products, with no hidden strengthening/weakening of theorem statements.

## Execution graph, commitments and independent gates

| Package | Build target | Exact deliverable | Required authority/stop |
| --- | --- | --- | --- |
| WP0 | Source/CI authority | Pin live SHA/tree; compile claims; reconcile #287/#288 receipts and historical obligations, canonical vs legacy matrix | No unverified assumptions; halt on normalization mismatch |
| WP1 | Reciprocal aperture | Prove second derivative `G''(s)=L^4(E''(L)+2E'(L)/L)` and strict concavity; transfer fixed-vector bounds to even Rayleigh infimum under a proved radius | Lean theorem + axiom audit; no claim for radius above M66 |
| WP2 | K2 even hybrid | Lean glue `(0,1/512]` to M51 `[1/400,log 16]` through WP1, M51 as **explicit hypothesis**; exact Python↔Lean normalization map; one record per Arb interval; independent cover checker | Never promote Python interval evidence to Lean theorem; stop on missed cell, failed controls, or mismatch |
| WP3 | #247/#287 strict-even adapter | Same selected negative `groundTrial=c·canonicalShiftedRay`, `H(x)=1`, `P(x)+Budget(x)=-λ‖x‖²>0`, explicit `λ<bottomOdd` | Lean theorem on actual state; not an RH obstruction; ties require a different map |
| WP4 | **D2 = Full** K3 | Frozen full 7×7 canonical source, legal 2D even/odd carriers; certifiable `a>0` and `Δ=ad-|b|²>0` for all `L∈[1/512,log16]`; K2 odd prerequisite; all seams; independent checker and all controls | Mandatory 384-bit Q14 frozen-box depth-40 gate. If failed, report UNRESOLVED and attempt the **single** predefined order-four Taylor model. If both fail, publish both dispositions; NEVER claim all-L positivity. Only a checked transcript could confer INTERVAL_EVIDENCE, not Lean unconditional theorem authority |
| WP5 | Modified-prime falsifier | Arb certificate for opposite K2 even signs at rational `L=1.295,1.296`, with positive odd at sample endpoints and true-zeta controls; consistent q4/q2 weights | Labels `INTERVAL_EVIDENCE`; not actual ζ and not a global first contact |
| WP6 | One bounded signed probe | At the #247-shifted ray keep M50 vs M59/M61 weights distinct; use #262 endpoint jets; test K2/Q14/Pair-D/cubic/modified-prime/planted witnesses | Report **one** source-dependent candidate disposition (no conjecture promotion); stop on circularity/falsification. D1 default INCLUDE, report-only |
| WP7 | Single PR integration | Append new modules to `Zeta23/CCM.lean`; explicit Lean/axiom workflow targets; independent test receipts; manifest+sha256; RHKG rebuild with 16 shards; review every workflow/job and post-green research | No `sorry`, `admit`, new axioms, RH claim registration, or premature successful status; user merges |

## Commit boundaries (all on this branch)

1. `WP0`: source/CI pin, audit, this contract, normalization/claim firewall.
2. `WP1`: generic reciprocal calculus with exact theorem signatures, proof escape/axiom tests.
3. `WP3`: same-negative-ground shifted secular adapter (parallel to independent certificates).
4. `WP2`: K2 gluing, M51 per-interval transcript and checker, controls.
5. `WP4`: feasibility gate, frozen Q14 report, and **either** complete continuous two-parity transcript **or** faithfully recorded failure and predeclared fallback result.
6. `WP5`: modified-prime interval control, with true ζ comparator.
7. `WP6`: bounded signed-correlation report with adversarial outcomes.
8. `WP7`: imports/CI, exact-head status and post-green graph+research review. Open draft until all accepted build goals are demonstrated; user merges.

## Source normalization and witness firewalls

- Work with `canonicalSourceMatrix`, **not** legacy `finiteMatrix`; archimedean `wCorrection` exactly once.
- At q=p^j use `Λ(q)=log p`; derivative source physical weight `Λ(q)(log q)^2/sqrt q` belongs to M50, not M59/M61.
- The parity index map `D` is **not unitary**. Compressed Rayleigh spaces and shifted negative vs zero-contact rays are different.
- For WP3 keep `s.aligned.evenShiftedTrial` and the selected negative shift `s.aligned.lam`; do not substitute a separate contact witness.
- WP4 uses the exact 2×2 Sylvester determinant, NEVER division by `a`. UNRESOLVED is not negative.
- External Zhu/Liu/Groskin positivity is never imported as an axiom or asserted verified here. T1 hard-window domain transfer is a distinct later project.

## Scientific stop conditions

The original rev4 plan's mandatory D2 gate can prevent completion of a full-K3 certificate. If it does, this PR must remain transparently partial with a reproducible **UNRESOLVED** report, not replace the full continuous requirement by M76 grid samples. The eventual report must distinguish code compilations, positive Arb interval coverage, pointwise probes, exact falsifiers and open RH obligations.

**Environment correction (2026-10-13):** the initial checkout lacked Lean and
python-flint. The repair session installed the pinned Lean 4.33.0-rc2 and
python-flint 0.9.0 in isolated workspace tools, enabling local compiler and
independent Arb checks. Final authority still requires exact-object completed
compiler/workflow receipts. This file is a build specification, not an executed
certificate.
