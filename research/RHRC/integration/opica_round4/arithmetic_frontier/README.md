# Arithmetic frontier: guide to the final source

This entry page describes the arithmetic-frontier material included in the
[21 November 2026 snapshot](../../../../../docs/CURRENT_STATE.md). The dated
[build specification](BUILD_SPEC.md) is preserved as its original contract.
Later source and handovers record work beyond that initial increment.

## Read the results by question

| Question | Source and interpretation |
| --- | --- |
| How does growth of a fixed moment slice relate to zero-free strips? | [ZeroFreeFloor.lean](../../../../../Zeta23/OPICARound4/ArithmeticFrontier/ZeroFreeFloor.lean) contains the even/odd fixed-rate equivalences and the rate ladder. Rates above one half are supplied; the required independent bounds at every positive rate remain open. |
| Which formulations would close the attempt? | The same source gives the RH equivalences labelled C1, SB, PG and SE, with separate conditional delay/scale variants. Read the hypotheses and quantifier order, not just the labels. |
| Why is a small value along a subsequence insufficient for the C2 route? | [C2GrowthClosure.lean](../../../../../Zeta23/OPICARound4/ArithmeticFrontier/C2GrowthClosure.lean) requires its bound at all sufficiently late times. |
| What finite numerical kernel is formalized? | [FiniteCertificateSoundness.lean](../../../../../Zeta23/OPICARound4/ArithmeticFrontier/FiniteCertificateSoundness.lean) proves a positive-shift/Frobenius-residual criterion for exact real data. The native Arb/transcendental enclosure bridge is a separate open obligation. |
| Can a smaller source core stand in for the full matrix? | [SourceColumnCore.lean](../../../../../Zeta23/OPICARound4/ArithmeticFrontier/SourceColumnCore.lean) retains the complement-leakage cost and physical Gram metric. |
| How do parity slices fit together? | The later [Round 5 bridge](../../../../../Zeta23/OPICARound5/ParityMomentBridge.lean) proves a fixed-moment short exact sequence and dimension relations. Its namespace remains `Zeta23.OPICARound4.ArithmeticFrontier`; its charts are nonunitary. |

Read the [12 November handover](HANDOVER_2026-11-12.md) for the final local
checkpoint and its evidence boundaries. Earlier [7 November](HANDOVER_2026-11-07.md)
and [8 November](HANDOVER_2026-11-08.md) handovers retain their own source scopes.
The later [Round 6 guide](../../opica_round6/README.md) follows finite signed
charges, complete shells, paid removals and stopping cuts. Its independent
arithmetic upper bounds and full growing-horizon transfer remain distinct open
inputs.

## Reuse and verification

The [result crosswalk](../../../../../docs/RESULTS_AND_FORMALIZATION.md) links
theorems, papers and evidence. The [reuse catalogue](../../../../../docs/REUSABLE_COMPONENTS.md)
separates abstract finite algebra from source-specific statements; the
[examples](../../../../../docs/EXAMPLES.md) show the certificate and its sign
hypothesis. Use the [reproduction recipes](../../../../../docs/REPRODUCIBILITY.md)
for an explicit module or consumer. The default `lake build` has a narrower
import surface than this research package.
