# OPICA Step 4 — where the graph calculations leave the proof

19 November 2026. **Step 4 and RH remain OPEN.** This handover supersedes the earlier 19 November graph checkpoint. It covers the merged repository at commit c867a8f15320ad6ac69177e0a498de4cb9d744f9, tree 573cda1f06d2d7a0e61349a53183311e4ba621fc. The archive includes the source code, local compiler receipts, analytic derivations and finite arithmetic runs. [Merged repository](https://github.com/HMarcusWH/zeta-23-lean/tree/c867a8f15320ad6ac69177e0a498de4cb9d744f9) · Drive research folder

## The shortest remaining arithmetic statement

For every sufficiently large integer \(L\), take the prescribed native site \(n_L=\lfloor 21L/20\rfloor\). In the distributed calibration, all denominators \(24L/25<q\le L\) coprime to 6 have full divisor coefficient \(-\mu(q)/q\). Corrections drop out of those individual coefficients by divisibility. The conjugate pair with numerators \(1,q-1\) contributes the genuine signed subgraph
\[
 T_L=\sum_{\substack{24L/25<q\le L\\(q,6)=1}}
       \frac{\mu(q)\cos(2\pi n_L/q)}{2q\sin^2(\pi/q)}.
\]
**DERIVED on paper.** If \(B\) is the supremum of the real parts of nontrivial zeta zeros, both the positive and negative parts of \(T_L\) have limsup exponent \(1+B\). The Mellin multiplier is nonzero at *every* shifted zero, including those at unknown heights. This follows from a strictly positive decreasing density on the actual frequency interval. A one-sided arithmetic estimate \(T_L\ll_\epsilon L^{3/2+\epsilon}\) for every positive \(\epsilon\), at **every sufficiently large** integer \(L\), would therefore be enough to establish RH. Either sign can be chosen and fixed. I have no independent proof of this estimate. The source supplies \(|T_{L+1}-T_L|\ll L\), and both signs recur. In consequence \(|T_L|\ll L\) infinitely often even if there is an off-line zero. Selecting successful cutoffs on this scalar cannot close Step 4. Phase calculation, Mellin proof and quantifiers

Both groups of individual summands, grouped by Möbius sign, have an explicit identical leading term of order \(L^2\). Ordinary PNT proves this leading cancellation. The desired estimate would additionally control the difference to relative precision \(L^{-1/2+\epsilon}\). Signed mass calculation

## The complete-source alternative

For the full arithmetic source the quantifier is more favorable. The finite positive native residue statistic has exponent \(B-1\) as \(L\) tends to infinity through **all integers**. The complete-period mean square meets the critical power, while the actual starting point is in an exponentially rare class for its first difference. Combining the large sieve with cancellation among genuinely shared numerator coefficients controls all but the explicit large-denominator, small-numerator ranges. With site scale \(N<n\le2N\), the remaining sum includes precisely the dyadic rectangles satisfying both \(D^5L>N^5K^3\) and \(D^4L>N^4K^4\), after the initial \(L^{5/6}\) sites. The signed contributions are added before taking each absolute value. Positive residue criterion · Period covariance and native phase · Bounds by denominator and numerator

The remaining frequencies have distance less than \(2L^{1/4}/N\) from an integer. This makes their signed sum smooth between adjacent native sites. Across the full native range one can reconstruct its weighted absolute mass \(H_L\) with additive error \(O(L^{-6})\) from \(O(L^{1/4}\log^2 L/\log\log L)\) deterministically specified integer observations. Here a proof of \(H_L\le L^{-1/2+\epsilon}\) at **arbitrarily large integer cutoffs for each \(\epsilon>0\)** suffices. The sample count reduces the number of observations. Each one retains the total signed divisor contribution, whose independent bound is missing. Sampling and error proof

## What was actually computed

| Calculation | Result | Scope |
|---|---|---|
| First nonempty native residual | \(L=205793\), one site; \(H_L=1.7930229066\times10^{-10}\). The exact complete Möbius knot at this site is \(-2315070\). | Exact integer cutoff scan and certified intervals covering 8,479,102 signed frequencies including conjugates. Receipt |
| Full native residual on a longer interval | At \(L=262144\), the remaining signed response was positive on all 2,066 sites. \(H_L=3.8358500752\times10^{-8}\). The independently computed full knot mass on the identical interval is \(3.4467851195\times10^{-8}\). | All 13,833,038 remaining frequencies including conjugates, 16 full signed interpolation samples and an independently evaluated endpoint. Uniform pointwise interpolation error below \(1.632\times10^{-9}\). This bound covers the entire stated interval. Receipt |
| Genuine first numerator at \(L=67108864\) | Positive contributions \(1.220319\times10^{12}\), negative magnitude \(1.221260\times10^{12}\). The signed row is \(-941235915.331083721041010141018\); \(T_L/L^{3/2}=-0.00171209815622\). | Every one of 894,784 eligible denominators accounted for. All Möbius values independently checked. The selected site is beyond the controlled prefix. Receipt |

**PROVED in local pinned Lean.** Two divisor-strip declarations and four factorial-ramp declarations compiled and passed object-level axiom inspection. These include the exact identity connecting the original integer ramp to the residue graph. Only propext, Classical.choice and Quot.sound occur. The exponent theorems and sampling arguments above are paper results. This pass added no repository commit or production CI qualification. Core evidence with both formal receipts

The traversal of all 16 repository graph shards covered 22,198 declarations and 1,236,174 distinct directed declaration-value dependencies. It identified the integrability premise on the route from the exact divisor identity and the eventual lower on the original Round 4 signed long term. The new scalar criterion reaches the same zeta zeros by an independent analytic derivation. Using it to certify the original Step 4 entry point would require verifying the transfer under the project's proof and claim gates. The completed CI harvest and all earlier attempts are linked in the core archive's handover. Graph audit · [Round 4 entry point](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICARound4/ActualSourceHyperbola.lean#L1560) · Earlier handover
