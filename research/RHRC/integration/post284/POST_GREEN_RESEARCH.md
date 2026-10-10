# Post-284 source-inertia campaign — research report

**Terminal status: `RH_OPEN`.** Nothing in this campaign proves RH, F04,
OBS-060O, or any branch exclusion.

Authority precedence: Lean compiler results for the exact PR head > this
ledger > the v0.4 handoff and the Steps 49–107 follow-up (execution plans
only). Machine-readable companions: `BASELINE.json`, `SOURCE_CLOSURE_AUDIT.json`,
`CLAIM_MIGRATION_MATRIX.json`, `PROOF_ROOTS.json`, `WORKFLOW_HARVEST.json`,
`EXPERIMENT_DISPOSITIONS.json`, `OPEN_OBLIGATIONS.json`,
`FOLLOWUP_REGRESSIONS.json`.

## 1. What became formally true (pending exact-head CI)

Exact Lean theorems with their full hypotheses (no `sorry`, no project axioms;
each root carries a `#print axioms` receipt line, all locally
`[propext, Classical.choice, Quot.sound]`):

| Package | Module | Headline |
|---|---|---|
| M05 = F-M52/F-M64 | `CanonicalRegularizedEnergyIdentity` | `quadraticForm (canonicalSourceMatrix L N) u = ∫₀ᴸ f_L W − ∫₀ᴸ (f_L − c_u e^{−t/2}) ρ − c_u·wCorrection L − Σ_q Λ(q)/√q f_L(log q)` for every `L > 0` and complex `u`, `f_L(t) = e_u(1 − t/L)`, `c_u = e_u(1)`; sesquilinear version for the mixed dictionary test. No zero-at-origin and no F04 premise. The repository `wCorrection` is term-by-term the follow-up's `w(L)`. |
| M17 | `SourceParityExactInertia` | At `ω = 1/2`, for **every** `K ≥ 2`: exact inertia of the elementary source on the even carrier `(K/2, (K−1)/2, 0)` and on the odd carrier `((K−1)/2, K/2, 0)`, with an explicit orthogonal splitting, nondegeneracy and maximality of the definite dimensions. |
| M17 | `SourceParityPolynomialCoordinates` | Lattice operators `cos`, `i sin`, `1 ± cos` with box adjointness, sign-operator anticommutation, injectivity on finitely supported sequences. |
| M18 | `SourceMomentFilteredInertia` | At `ω = 1/2`: the even filtered carrier (`M₀..M_{2s−1} = 0`) on `K = m+s` splits with exact definite dimensions `(m/2+1, (m+1)/2)`, the odd filtered carrier on `K = m+s+1` with `((m+1)/2, m/2+1)`; both indefinite for `m ≥ 1`. |
| M15 | `SourceMomentVandermondeFiltration` | Vandermonde separation by `M_0..M_{2K}`; `finrank F_r = 2K+1−r`; first jet `2(−(2π)²)^r|M_r|²`; first surviving order `4j+1` (positive, even) / `4j+3` (negative, odd). |
| M04 | `SourceFourierConvolution` | `S_nm(ω) = π⁻¹∫₀^{2πω} cos(nt + m(2πω−t)) dt`; convolution formula for the source form. |
| M04/M15/M18 | `SourceSignCountermodels` | `(1,−4,7,−8,7,−4,1)`: `M₀..M₃ = 0`, `M₄ = 48`, `e(1/2) = −4`; fourth-moment firewall for every `K ≥ 3`. |
| M04 | `SourceLatticeCoordinates` | `sourceMatrix (1/2) = Diag((−1)^n)`; centered zero extension preserves moments and the source form. |
| M11 | `StrictEvenPrimeSeamDichotomy` | Abstract LOW/HIGH classification from explicit degree-9 premises (CONDITIONAL). |
| M19 | `ContactNinthJumpGapBound` | `(2K+1)` index-mass inequality; conditional ninth-jump algebra (CONDITIONAL on M10). |
| F-M35/M40/M54 | `CanonicalSourceWeightedIntegral` | `∫₀¹ S = P₀`; `∫₀¹(1−ω)S_nm = −(1/(2π²))(1/(nm) + δ_nm/n²)`; for `u₀ = 0`: `∫₀¹(1−ω)e_u = −(1/(2π²))(Σ|u_n|²/n² + |Σu_n/n|²) ≤ −‖u‖²/(2π²K²)`; `= −‖z‖²/(2π²)` for `u = Dz`, `Σz = 0`; every nonzero `u` with `u₀ = 0` has a negative source coordinate and a zero of `Re e_u` in `(0,1)`. |
| F-M20/M24/M26/M30 | `SecularDeterminantKernel` | Over any field, from `BD − DA = g⊗h`: `det A = det B(1 − T)`, `A x = (1−T)D⁻¹g`, `ker A ⊆ span x`, `T = 1 ⇔ ker A ≠ 0`; shifted version at every `μ`; matched update `(1−T')(1+tγ) = 1−T`; exact `2×2` crossing control with `T(h) = 1 + h³/(12+3h³−4h⁶)` and a surviving negative even eigenvalue. |
| F-M46 | `CanonicalCenteredIndexCoercivity` | `‖z‖² ≤ C_K‖Dz‖²` for `Σz = 0`, `C_K = 1 + Σ_{0<|n|≤K} n⁻² ≤ 5 − 4/(K+1) < 5`, `C_K ≤ 2K+1`; at an even ground eigenvector with odd–even gap `δ ≥ 0`: `δ‖v‖² ≤ C_K |H(v)| |M₄(v)|` (from the existing parity-gap theorem). |
| F-M42 | `CanonicalPrimeFreeSecondTest` | For `Σz = 0`, `0 < L ≤ log 2`: `Q_N(L,z) = ∫₀ᴸ t²(W−ρ) Re e_{Dz}(1−t/L) dt ≥ L²‖z‖²[1/(4π²) − L(2N+1)N²/2]`, hence `Q > 0` for `z ≠ 0`, `0 < L < 1/(2π²(2N+1)N²)`. Built from `|S_nm(ω)| ≤ 2ω`, `|t²(W−ρ)+t/2| ≤ 3t²` on `(0, log 2]` and the compiled M40 identity. Fixed-vector test only; its identification with `E″ + (2/L)E′` (M65) is OPEN. |
| F-M47/M48 | `CanonicalK2SourceSignInterval` | `K = 2`: `Re e_u(ω) < 0` for every nonzero legal odd `u` and `Re e_{Dz}(ω) < 0` for every nonzero legal even `z`, `0 < ω ≤ 3/4` (convolution on `(0,1/2]`, explicit trigonometric form on `[1/2,3/4]`); `e_{u₀}(1) = 20`. For `0 < L ≤ log 16` every sample `2 ≤ q ≤ e^L` has `ω_q ∈ [0,3/4]`, so every K=2 prime term `−β_q e_{Dz}(ω_q)` with `β_q ≥ 0` is nonnegative (source side only). |

Claim registry: `R003_COMPRESSED_PRODUCTION_C2` and
`R003_INHERITED_FIRST_VARIATION_RESTRICTION` promoted individually to
`PROVED_UNCONDITIONAL` (premise-free relative to the claim text; merged-green
PR #284). The two F04-conditional post-282 claims stay OPEN with corrected
notes. The new roots above are research-ledger roots, not registered claims.

## 2. External 7/8 theorem

Provenance only (`SOURCE_CLOSURE_AUDIT.json`): 2,924-module, ~486k-line
closure on Lean v4.34.1 / Mathlib `d13f23…`, plus patched PrimeNumberTheoremAnd
and Rellich–Kondrachov. Incompatible with the Zeta23 toolchain; no adapter was
written.

## 3. Falsification results (research, not theorem authority)

v0.4 suite (`post284_source_falsifier_suite.py`):

* M05 candidate formula agrees with independent mpmath canonical channels at
  six `(L,K)` cases; re-adding `canonicalArchScalarCorrection` is detected.
* Inertia samples `K = 2..9` agree with the exact half-aperture counts;
  Andréief leading-minor signs `(−1)^{r(r−1)/2}`.
* Moving vectors: `−23/(660660π)a¹³` (even) and `+19/(24948π)a¹¹` (odd).
* Spectral flow on `(1/2, 1)` is not monotone for `K ≥ 4` (uncertified).
* Index mass: true minimum of `‖Dz‖²` is ≈ 0.27–0.30 for `K = 2..8`; the new
  `C_K < 5` theorem (bound `> 0.2`) confirms a `K`-uniform constant.

Follow-up suite (`post284_followup_regressions.py`, `FOLLOWUP_REGRESSIONS.json`):

* **M30 (exact):** rank-one identity, `det D = −1`, `T(0) = 1`, `T' = T'' = 0`,
  `T''' = 1/2`, λ-slopes `+1/12`, `−1/6`. Mirrors the Lean control.
* **M24 (exact):** `T₊ − T₋ = d h⁹ − c h¹⁰ + O(h¹¹)`.
* **M41 (interval evidence):** `Q_{2,z}(L)` for `z = (1,−4,6,−4,1)`:
  enclosures with signs `+ + + − −` at `L = 0.1, 0.4, 0.5, 0.6, 2/3`
  (e.g. `Q(0.5) ∈ [0.0380, 0.0407]`, `Q(0.6) ∈ [−0.0654, −0.0606]`): a
  prime-free sign change in `(0.5, 0.6)`, strictly before `log 2`. Simpson
  values reproduce the handoff table to ~10⁻¹².
* **M43 (interval evidence):** `Q_{3,z₋}(2/3) ∈ [−0.181, −0.174]`,
  `Q_{3,z₊}(2/3) ∈ [0.248, 0.351]`; both vectors legal (`M₀ = M₁ = M₂ = 0`).
  The prime-free second-order physical form is indefinite on fixed vectors.
* **M42 (numeric sanity, now also a Lean theorem):** at `L = 0.9 ε₂` the test
  is positive and above the proved lower bound.
* **M67 (attached log3 script, interval evidence):** `H(log 3, z) ∈
  [0.0344, 0.0483]`; falsifies only a universal nonpositive source-pairing
  claim on arbitrary legal vectors.

Enclosures use mpmath outward rounding with an analytic bound on the origin
cell (`|t²(W−ρ)| ≤ 3t² + t e^{t/2}/2`, `|S_nm(ω)| ≤ 2ω` from the compiled
cosine-integral form); they are not Lean/Arb certificates.

## 4. Change in assumptions and implications

* **M05 = M52 = M64 hard gate met at matrix level.** The full fixed-vector
  energy `E_z(L)` is a theorem about the actual `canonicalSourceMatrix`, with the
  repository `wCorrection`; F04 work (M53/M65) starts from a theorem.
  `canonicalArchScalarCorrection` must not be added again.
* **Averaged source structure (M35/M40/M54) is negative-definite on `u₀ = 0`**
  while the pointwise half-aperture form is indefinite (M17/M18). Any fixed
  `u` with `u₀ = 0` changes sign in `(0,1)`: the sign question is about the
  location of the sampled coordinates, not about the source operator.
* **Rank-one geometry does not exclude crossings (M30).** The secular
  algebra (M20/M26) gives `T = 1 ⇔ ker A ≠ 0` and simple kernels, but the
  exact 2×2 model has `T − 1 = O(h³)` with a surviving negative eigenvalue.
  Any exclusion must use canonical arithmetic input.
* **K-uniform coercivity (M46) upgrades the M19 premise.** At even ground
  eigenvectors the inequality form of the M19 identity follows from an
  existing theorem; with `C_K < 5` the moment lower bound is
  `|M₄| ≥ δ‖v‖²/(5|H(v)|)`. The M10 ninth-order premise stays OPEN.
* **K = 2 is sign-controlled through `log 16` on the source side (M47/M48)**,
  but only the *possibility of adverse prime signs* is removed, not the
  older-prime sum; the F04-conditional contact statement `P = −F ≤ 0` stays
  OPEN.
* **Prime-free counterexamples (M41/M43)** kill any proposed all-vector
  second-order positivity before the first prime; the M32 Grönwall route must
  be contact-conditioned or resolvent-based.

## 5. Highest-information next moves

1. **M65 prime-free F04:** differentiate the M05 identity in `L` on
   `0 < L < log 2` (`t = Lx`, removable singularity of the arch integrand,
   `w'(L) = e^{−L/2}ρ(L)`), giving `E'' + (2/L)E' = −(2π)²Q/L⁴`.
2. **M66 after M65:** the positive side `Q_K(L,z) > 0` below `ε_K` is now a
   Lean theorem (M42); combined with a proved prime-free F04 identity it would
   give (Q-NEG-EULER) and the conditional local exclusion. Until M65 is
   proved, no contact statement follows.
3. Instantiate M20/M26 on the actual compressed `A_L, B_L, D, g, H_L` and export
   `⟨g, Dz⟩ = M₄(z)` (M21/M58 phase lock).
4. M17 interior (`0 < ω < 1/2`): Andréief signed minors.
5. Certify the spectral-flow passages and the M41 root by a formal interval
   library; OAI 7/8 import as a sibling PR on a v4.34.1 toolchain.

## 6. Workflow harvest at the final head

Recorded after CI in `WORKFLOW_HARVEST.json` (`post284_branch_harvest`).
