# Post-284 source-inertia campaign — research report

**Terminal status: `RH_OPEN`.** Nothing in this campaign proves RH, F04,
OBS-060O, or any branch exclusion.

Authority precedence: Lean compiler results for the exact PR head > this
ledger > the v0.4 handoff (execution plan only). Machine-readable companions:
`BASELINE.json`, `SOURCE_CLOSURE_AUDIT.json`, `CLAIM_MIGRATION_MATRIX.json`,
`PROOF_ROOTS.json`, `WORKFLOW_HARVEST.json`, `EXPERIMENT_DISPOSITIONS.json`,
`OPEN_OBLIGATIONS.json`.

## 1. What became formally true (pending exact-head CI)

Exact Lean theorems with their full hypotheses (no `sorry`, no project axioms;
each root carries a `#print axioms` receipt line):

| Package | Module | Headline |
|---|---|---|
| M05 | `CanonicalRegularizedEnergyIdentity` | `quadraticForm (canonicalSourceMatrix L N) u = ∫₀ᴸ f_L W − ∫₀ᴸ (f_L − c_u e^{−t/2}) ρ − c_u·wCorrection L − Σ_q Λ(q)/√q f_L(log q)` for every `L > 0` and complex `u`; sesquilinear version for the mixed dictionary test. No zero-at-origin and no F04 premise. |
| M17 | `SourceParityExactInertia` | At `ω = 1/2`, for **every** `K ≥ 2`: exact inertia of the elementary source on the even carrier `(K/2, (K−1)/2, 0)` and on the odd carrier `((K−1)/2, K/2, 0)`, with an explicit orthogonal splitting, nondegeneracy and maximality of the definite dimensions. |
| M17 | `SourceParityPolynomialCoordinates` | Lattice operators `cos`, `i sin`, `1 ± cos` with box adjointness, sign-operator anticommutation, injectivity on finitely supported sequences, and the carrier parametrizations `u = (1−cos)²q` (even) and `u = (i sin)(1−cos)q` (odd). |
| M15 | `SourceMomentVandermondeFiltration` | Complex Vandermonde separation by `M_0..M_{2K}`; exact codimension `finrank F_r = 2K+1−r`; rank-one first jet `2(−(2π)²)^r|M_r|²` on `F_r`; first surviving jet order `4j+1` (`2 ≤ j ≤ K`, strictly positive) on the even carrier and `4j+3` (`1 ≤ j ≤ K−1`, strictly negative) on the odd carrier. |
| M04 | `SourceFourierConvolution` | `S_nm(ω) = π⁻¹∫₀^{2πω} cos(nt + m(2πω−t)) dt` for every real `ω`, and the complex convolution formula for `quadraticForm (sourceMatrix ω N) u`. |
| M04/M15/M18 | `SourceSignCountermodels` | `(1,−4,7,−8,7,−4,1)`: `M₀..M₃ = 0`, `M₄ = 48`, `e(1/2) = −4`; exact K2/K3 moment witnesses; fourth-moment firewall (both strict signs with `M₄ ≠ 0`) for every `K ≥ 3`. |
| M04 | `SourceLatticeCoordinates` | `sourceMatrix (1/2) = Diag((−1)^n)`; centered zero extension preserves every moment and the source form at every `ω`. |
| M11 | `StrictEvenPrimeSeamDichotomy` | Abstract LOW/HIGH classification from explicit degree-9 expansion premises (CONDITIONAL). |
| M19 | `ContactNinthJumpGapBound` | `∑|u|² ≤ (2K+1)∑n²|u|²` when `∑u = 0`; conditional `|M₄| ≥ δ/((2K+1)B)` and `Δ₉ ≤ −κδ²/((2K+1)²B²)` from explicit premises (CONDITIONAL on M10 and the M19 identity). |

Claim registry: `R003_COMPRESSED_PRODUCTION_C2` and
`R003_INHERITED_FIRST_VARIATION_RESTRICTION` promoted individually to
`PROVED_UNCONDITIONAL` (premise-free relative to the claim text; merged-green
PR #284). The two F04-conditional post-282 claims stay OPEN with corrected
notes.

## 2. External 7/8 theorem

Provenance only (`SOURCE_CLOSURE_AUDIT.json`): 2,924-module, ~486k-line
closure on Lean v4.34.1 / Mathlib `d13f23…`, plus patched PrimeNumberTheoremAnd
and Rellich–Kondrachov. Incompatible with the Zeta23 toolchain; no adapter was
written.

## 3. Falsification results (research, not theorem authority)

* M05 candidate formula: independent mpmath canonical channels agree to
  quadrature precision at six `(L,K)` cases with complex vectors; re-adding
  `canonicalArchScalarCorrection` is detected (residual ≈ 3.9). Now backed by
  the M05 Lean theorem.
* Inertia samples `K = 2..9`, `ω ∈ {0.05, 0.25, 1/3, 0.45, 0.5}` agree with
  `(⌈d/2⌉, ⌊d/2⌋)` / `(⌊d/2⌋, ⌈d/2⌉)`; Andréief leading-minor signs
  `(−1)^{r(r−1)/2}` at `a ∈ {2π·0.05, π/2, π}`.
* Moving vectors: `−23/(660660π)a¹³` (even) and `+19/(24948π)a¹¹` (odd);
  the mixing ratios `3/11` and `5/18` are exactly the critical points of the
  beta-integral quadratic.
* **New signal (spectral flow):** on `(1/2, 1)` the negative count of the
  elementary source falls from `⌊d/2⌋`/`⌈d/2⌉` to `0`, but for `K ≥ 4` the
  201-point grid shows more sign changes than the lower bound — the passage
  is not monotone (e.g. K=4 odd: 0.695, 0.775, 0.8875, 0.9275). Not certified.
* **New signal (index mass):** the true minimum of `‖Dz‖²` under
  `∑z = 0, ‖z‖ = 1` is ≈ 0.27–0.30 for `K = 2..8`, so the M19 constant
  `1/(2K+1)` is far from sharp; a `K`-uniform constant looks available.

## 4. Change in assumptions and implications

* M05 removes the "normalization hard stop": the candidate whole-form
  identity is exact with the repository's `wCorrection`, and the reduced
  scalar `canonicalArchScalarCorrection` must not be added again. F04 work can
  now start from a theorem, not a candidate.
* M17 at `ω = 1/2` plus the fourth-moment firewall make every elementary
  source-sign route on carriers of dimension ≥ 2 indefinite; M15 shows signs
  are vector-dependent and the moving-vector controls show fixed-vector
  arguments cannot be made uniform. Any exclusion must use contact-specific
  canonical structure, not elementary source positivity.
* The M11 dichotomy is a classification, not an exclusion: the entering prime
  makes the HIGH case negative to the right.

## 5. Highest-information next moves

1. F04 (M06): differentiate the M05 identity cell-by-cell in `L` (prime cells,
   pole upper endpoint with `f_L(L) = 0`, regularized arch integral with local
   uniform domination near `t = 0`).
2. M17 interior: the Andréief signed-minor lemma for `0 < ω < 1/2`.
3. M18: filtered inertia via `(1 − cos)^s` (the shift-operator identity
   `B = ±⟪q, (1 − cos²)^s R q⟫` already holds) and the filtered-carrier
   dimension identification.
4. Sharpen the M19 index-mass constant; certify the spectral-flow passages.
5. OAI 7/8 import as a sibling PR on a v4.34.1 toolchain.

## 6. Workflow harvest at the final head

Recorded after CI in `WORKFLOW_HARVEST.json` (`post284_branch_harvest`).
