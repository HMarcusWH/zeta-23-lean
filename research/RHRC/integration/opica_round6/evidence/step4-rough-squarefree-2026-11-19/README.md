# Step 4 evidence guide

19 November 2026. **Step 4 OPEN. RH OPEN.** This archive accompanies the rough squarefree paper, based on the merged research map and previous aperture analysis.

| File | What it establishes |
| --- | --- |
| STEP4_ROUGH_SQUAREFREE_RESIDUAL.md | Paper derivation for the original K5 aperture integral. The full sieve background costs \(\exp(O(T/\log T))\) times a polynomial. The composites with two and with at least three large prime factors contribute opposite leading terms. Equation (5) identifies the outstanding one-sided lower bound. |
| lean/WeightedPrimeBalance.lean | Exact finite prime balance, for every finite input set and real weight. All proper powers and residuals are present. |
| UNCONDITIONAL_RESIDUAL_BOUND.md | Transfers the explicit Vinogradov–Korobov prime estimate through the actual kernel, giving an unconditional signed residual bound with the published constant 0.1853 in its exponent. |
| lean/RoughSquarefree.lean and lean/SquareDivisorMask.lean | Finite divisor decomposition and squarefree indicator identities supporting the arithmetic interpretation. |
| lean/VERIFICATION.json, compiled objects and logs | Three local Windows compilations using the pinned Lean 4.33.0-rc2 and existing Mathlib imports. Nine declaration axiom reports use only propext, Classical.choice and Quot.sound. The receipts give invocation, input, output and log hashes. |
| check.py and finite-checks.json | Independent exact checks of the sieve, the original signed drive coefficients after restricting Möbius divisors, the finite signed balance and three endpoint polynomial moments. Run with Python 3. |
| ROUGH_RESPONSE_OBSTRUCTION.md | Paper argument on the distinct fixed universal-sinc prime field. Its source with the small-prime smooth factor retained detects every visible off-line zero. At the cutoff \(y=T^2\), a polynomial upper is already impossible under RH. A cofinal upper at every positive exponential rate would suffice. |
| MARKED_ARITHMETIC.md | A separate paper sensitivity check. Marking Möbius rows by their number of large prime factors yields an explicit derivative of order \(e^{T/2}/T^2\). This quantifies the error introduced by modifying genuine weights. |

**Evidence boundary.** The analytic estimates and growth predictions have paper status. The finite Lean identities were compiled locally with the project pin. A repository commit, a production CI run for these new notes, and a closing arithmetic inequality are outside the verified results. The earlier native lower and its hypotheses are available in the [merged Lean source](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICARound4/QuarticErrorReduction.lean#L414).
