# Post-285 falsification report (M38, M55, M65–M76)

Terminal claim: **RH_OPEN**. Everything below is regression or experimental
evidence. Theorem authority comes only from the Lean roots listed in
`PROOF_ROOTS.json`.

**Endpoint correction (2026-10-13, PR #290).** The historical M51 receipt below
reported `[1/400, log 16]`, but its producer clips every cell at the exact rational
`U = 2772588722239781/10^15 < log 16`. Its 1,310-interval evidence covers only
`[1/400, U]`; `(U, log 16]` remains OPEN for that receipt. The original receipt
and observations are retained below as history, with this correction governing
their scope. The live ledgers now record the rational domain and the explicit
`M51_K2_EXACT_LOG16_ENDPOINT` obligation. This legacy receipt does not validate
the invalidated unguarded post287 transcript. See
[the migration record](../post287/LEGACY_M51_ENDPOINT_MIGRATION.md).

## Scripts

All nineteen scripts live in `research/RHRC/routes/R003_ccm_bridge/post285/` and
run in the `source-falsifier-research` job of
`.github/workflows/rhrc_post284_source_inertia.yml`. Each one runs in seconds.

| Script | Packages | Result |
|---|---|---|
| `post285_m74_secular_falsifier.py` | M74, M30 | Pass, with both negative controls failing as they should |
| `post285_gate_a_d_falsifier.py` | M70, M73, M75 | Pass, with negative controls |
| `post285_m76_secular_margin.py` | M76 | Experimental signal (see below) |
| `post285_f04_falsifier.py` | F04 (M65), M66 | Pass, with both negative controls failing as predicted |
| `post285_m55_abel_falsifier.py` | M55, M38 | Pass, with both negative controls failing as predicted |
| `post285_m71_andreief_falsifier.py` | M71 | Pass (Arb-certified signs), with both aperture controls failing as predicted |
| `post285_m27_root_slope_falsifier.py` | M27 | Pass, with both negative controls failing as predicted |
| `post285_m08_cubic_schur_falsifier.py` | M08 | Exact pass, with all three controls behaving as predicted |
| `post285_m09_weighted_remainder_falsifier.py` | M09, M12 (Step 28) | Pass at 30 digits, with all three controls failing as predicted; Step 28 values Arb-certified |
| `post285_m45_odd_endpoint_falsifier.py` | M45 | Arb-certified at 232 cells, with all four controls failing as predicted |
| `post285_m49_near_edge_probe.py` | M49 | Experimental signal; the proved chain holds at every sample checked |
| `post285_m50_older_prime_budget_probe.py` | M50 | Experimental signal; both proved ingredients hold at every sample checked |
| `post285_m61_source_balance_falsifier.py` | M59, M61 | Pass, with all three controls failing as predicted |
| `post285_m34_remainder_oscillation_probe.py` | M33, M34 | Pass on the proved statements; experimental signal on the oscillation room |
| `post285_m44_entering_prime_jet_probe.py` | M44 | Pass, with both controls failing as predicted |
| `post285_m29_source_resolvent_derivative_probe.py` | M29 | Pass, with all three controls failing as predicted |
| `post285_m51_k2_even_bottom_certificate.py` | M51 | Certificate passes; both controls fail and the positive control holds as predicted |
| `post285_m63_route_comparison_probe.py` | M63 | Experimental signal; the control fails as predicted |
| `post285_m76_arb_resolution.py` | M76 | Arb-certified at all 96 grid points, with all three controls failing as predicted |

## M74: canonical secular resolvent

The script checks 200 random complex instances. In each one `B` is Hermitian
positive definite, `D` is a general invertible matrix (not unitary), and
`A := D⁻¹(BD − g hᵀ)`. Every identity proved in
`CanonicalSecularResolvent.lean` holds to below `1e-6` relative error:

- the rank-one relation;
- the ray formula `A x = (1 − T) D⁻¹ g`;
- `det A = det B (1 − T)`;
- `γ = ⟨g, B⁻¹g⟩` is real and positive;
- the gauge `⟨g, D x⟩ = γ`;
- the Ward identity `γ H(v) = ⟨g, Dv⟩ − ⟨r, D A v⟩` for complex `v`;
- the approximate bound `|γH(v) − ⟨g, Dv⟩| ≤ ‖r‖‖DAv‖`.

**Contact.** Forcing `H(x) = 1` gives a one-dimensional kernel in every trial.
On that kernel line, `Re(conj(Hz)⟨g, Dz⟩) = γ|Hz|²` holds for complex phases.

**Negative controls.**
- Replacing Mathlib's sesquilinear pairing with a bilinear one breaks the Ward
  identity.
- Using `D*` instead of `D⁻¹` breaks the ray identity, because `D` is not unitary.

**M30 crossing.** The PR #285 2×2 cubic crossing satisfies every M74 identity
for all `s`, yet `A(s)` has a negative eigenvalue for `s > 0`. The secular
algebra cannot exclude a crossing by itself. A sign input independent of
contact is still needed, and `H(x) = 1` is not such an input because it is
equivalent to contact.

## M70: source excursions (Step 108)

Over random nonzero zero-sum `z` with `K ≤ 6`, on a 2001-point grid:
- the smallest observed `π² min e_{Dz}/‖z‖²` is −5.59, below −1 as required;
- the smallest observed `π² max e_{Dz}/‖z‖²` is 10.56, above 1 as required.

**Control.** Drop the zero-sum hypothesis and take `z = e₀`. Then `Dz = 0` and
`e ≡ 0`, so no strict excursion occurs.

## M73: Poincaré constant `1/4` (Step 115)

The telescoped mass `∑_{0<|n|≤K} 1/(n² − 1/4) = 4 − 4/(2K+1)` is exact to
4e-16 for `K ≤ 60`.

The optimal constant on the whole zero-sum carrier was computed for each `K`:

| K | constant |
|---|---|
| 1 | 0.3333 |
| 2 | 0.2958 |
| 3 | 0.2816 |
| 5 | 0.2695 |
| 10 | 0.2599 |
| 20 | 0.2550 |
| 40 | 0.2525 |
| 80 | 0.2513 |

It decreases toward `1/4`. **Control:** the constant `1/4 + 0.01` fails at
`K = 80`.

Sharpness is a **numerical signal only**. The constant is not claimed for the
narrower even legal carrier.

## M75: negative window (Steps 119–120)

- **Derivative bound.** By central differences, the entry derivative
  `|dS_nm/dω|` reaches at most 0.934 of the proved bound `2 + 4πK`.
- **Window.** For every random trial, the window `[ω₋ − η_K, ω₋ + η_K]` lies
  inside `(0,1)`, and `e ≤ −‖z‖²/(2π²)` holds on it.
- **Crudeness of η_K.** The true negative run around `ω₋` is at least about 198
  times `2η_K`. So `η_K` is very conservative.
- **Prime threshold.** The threshold `L ≥ π²M_K log 2` is about 3.7·10³ at
  `K = 2`. That is far beyond any aperture computed in this repository.

## M76: actual-canonical secular margin

This probe uses the production canonical float matrices for `K = 2..5` and
`L = 0.25..6` in steps of 0.25.

- **Rank-one relation.** `B_L D − D A_L = g H_L` holds to 2e-15 on every grid
  point. This is an independent numerical check that the Lean rank-one theorem
  matches the executable canonical matrix.
- **Resolved points.** 46 grid points have `λ_min` above `1e-10 × ‖S‖`. On all
  of them, `B > 0`, `A > 0`, and the secular margin `1 − T(L)` is positive. The
  smallest margin is 4.4e-4, at `K = 3, L = 2.75`. The identity
  `det A / det B = 1 − T` holds to 3e-9.
- **Channel split.** `T` decomposes over the pole, signed arch, signed prime and
  scalar channels. The pole and prime contributions are huge and opposite. The
  pole term reaches up to 7e9 times the net `T`, so a sign argument has to
  control a cancellation, not a dominant term.
- **`CanonicalShiftedSecular` regressions on the same matrices.**
  - At all 46 resolved even eigenvalues `a` below the odd floor, `T(a) = 1`
    holds to 3e-9.
  - At the same eigenvalues, the shifted overlap identity
    `⟨v_a, D⁻¹g⟩ H(D⁻¹(B − a)⁻²g) = ‖v_a‖²` holds to 5e-8.
  - Where `A > 0`, `det B / det A = 1 + H(A⁻¹D⁻¹g)` holds to 5e-8 relative.
  - The script fails if any of these residuals exceeds 1e-5.
- **Unresolved points.** 50 grid points (larger `K` and `L`) fall below float64
  resolution. Their apparent negative eigenvalues are at the 1e-15 level and are
  **not** reported as signs. `post285_m76_arb_resolution.py` resolves them in
  Arb (see "M76 in Arb" below).

## F04 (M65) and M66

`post285_f04_falsifier.py` checks the F04 identities at matrix level on the
even boundary-flat carrier `P` (orthonormal columns), against the executable
canonical matrix `M(L)` (which carries the single `2 cCorrection(L)` repair).
`M'(L)` and `M''(L)` come from 5-point finite differences. The physical side is
Gauss–Legendre quadrature of `(t/L²) S'(1 − t/L)(W − ρ)` and
`(t²/L⁴) S''(1 − t/L)(W − ρ)`, minus the exact prime sums.

- **Identities.** For `K = 2..5`:

  | Where | Apertures | First identity | Euler identity |
  |---|---|---|---|
  | Prime-free | `L = 0.08, 0.2, 0.35, 0.5, 0.62` | ≤ 3e-12 | ≤ 1.4e-8 |
  | Prime cells | `L = 0.9, 1.3, 1.5` | ≤ 5e-8 | ≤ 1.4e-7 |
  | Exactly at seams | `L = log 3, log 4, log 5` | ≤ 2e-8 | ≤ 1.2e-6 |

  The seam rows are the numerical counterpart of the Lean gluing step: an
  entering prime atom has zero value and slope at its seam.
- **Control: nonzero coefficient sum.** For `z = e₀` (so `e'_z(0) = 2 ≠ 0`) the
  Euler identity misses by 2.07530, against the predicted boundary term
  `e'_z(0)(W(L) − ρ(L))/L = 2.07530`. Zero coefficient sum is exactly what
  kills that term.
- **Control: correction added twice.** With `M + 2 cCorrection(L) I`, the first
  identity misses by 0.449461, against the predicted
  `2 cCorrectionIntegrand(L)|z|² = 0.449461`.
- **M66 bound.** At `L = 0.25, 0.5, 0.9 ε_K` for `K = 2..5`, the largest
  eigenvalue of the Euler form lies below the proved bound
  `−(1/L²)(1 − 2π²L(2K+1)K²)`.
- **Signal: the true Euler radius.** The Euler form stays negative definite on
  the even carrier up to about `L = 0.553` (K = 2), 0.425 (3), 0.379 (4),
  0.355 (5), 0.350 (6), 0.328 (8), 0.316 (10, 12) and 0.305 (16). The proved
  radius `ε_K` is `2.5·10⁻³` at `K = 2`.
- **Signal: no even contact below `log 2`.** On `(0.001, log 2)` the even
  compressed ground stays positive for `K = 2..16`. Its minimum is always at the
  right end and falls from 0.096 (K = 2) to 0.003 (K = 16). So no generated
  strict-even contact is seen in the prime-free window, and M66 is likely
  vacuous there for these `K`.

No numerical regression is run for the `CanonicalContactOverlapSign` sign: no
synthetic family with a Hermitian rank-one intertwining at a contact is at
hand, and the executable canonical grid has no contact. The proof is exact
linear algebra plus one limit.

## M55 and M38: weighted Chebyshev partial summation and remainder extrema

`post285_m55_abel_falsifier.py` uses an exact von Mangoldt table up to
`N = 20000`. `R` is a step function minus `2√t`, so `∫₁ˣ R(t)/√t dt` is
evaluated exactly cell by cell rather than by quadrature.

- **(96.1).** `ψ(x) − x = 1 + √x R(x) − ½∫₁ˣ R/√t` holds to 4e-11 relative at
  79997 points: every integer up to `N` and three interior points per cell.
  At `x = 1` both sides are `−1`, and `R(1) = −2`.
- **Conventions.** Left limits on both sides at an integer also satisfy the
  identity, since `ψ` and `√n R(n)` both drop by `Λ(n)`. **Control:** mixing
  conventions (`ψ(n−)` against `R(n)`) misses by exactly `Λ(n)`.
- **Transfer bound.** `|ψ(x) − x − 1| ≤ 2M√x` with `M` the running maximum of
  `|R|`. The worst ratio is 0.5, at `x = 1`.
- **M38 extrema.** For `X` just below, at and just after
  2, 3, 4, 5, 8, 9, 16, 25, 27, 32, 49, 97, 128 and 500, the finite supremum
  formula matches dense sampling exactly, and the finite infimum formula is
  approached from above (a left limit). **Control:** dropping the cut
  `min(m+1, X)` undershoots the infimum at non-integer `X`.

## M71: Andréief interior inertia (Steps 44, 109)

`post285_m71_andreief_falsifier.py` builds the even and odd carrier Gram
matrices in the cosine-power bases from exact rational lattice coefficients and
the elementary source entries, in python-flint Arb balls.

- **Certified signs.** For `K = 2..9` and 14 apertures
  `ω ∈ {1/1000, 1/200, 1/50, 1/20, 1/10, 1/8, 1/6, 1/5, 1/4, 1/3, 2/5, 9/20, 49/100, 1/2}`,
  every leading minor has the proved sign: `(−1)^{r(r−1)/2}` (even) and
  `(−1)^{r(r+1)/2}` (odd). That is 224 cells at 512-bit precision, none
  unresolved, with minors as small as about `10^{-488}` at `ω = 1/1000`.
- **Inertia.** The Jacobi counts equal the proved inertia, and an independent
  120-digit eigenvalue count agrees for `K = 2..7` at `ω = 1/20, 1/5, 1/3, 1/2`.
- **Gram identity.** The carrier Gram entries equal the Andréief convolution
  integrals `±π⁻¹ ∫_0^a w(t) cos^k t · w(a−t) cos^l(a−t) dt` to `10^{-40}`.
- **Controls.** For `ω ∈ (1/2, 1)` the certified signs break the pattern (for
  example `K = 3` at `ω = 4/5` and `9/10`), and at `a = 3π/2` a pair factor is
  positive. Both fail as predicted, so the hypothesis `ω ≤ 1/2` is needed.

## M27: alternating root slopes (Step 59)

`post285_m27_root_slope_falsifier.py` uses the same float canonical source
matrices as the M76 probe (`K = 2..5`, `L = 0.5..6` in steps of `0.5`).

- **Slope formula.** At all 22 resolved even eigenvalues below the odd floor,
  the resolvent derivative `H(D⁻¹(B − a)⁻² g)` matches
  `∏_{i≠j}(a_i − a_j)/∏_k(b_k − a_j)` to a relative `7·10⁻⁹`. A central
  difference of `T`, with its step scaled to the distance to the nearest root
  or odd eigenvalue, agrees to `2·10⁻⁵`.
- **Sign.** The rule `(−1)^{#{i : a_i < a_j}}` holds at every root.
- **Determinant form.** `1 − T(λ)` equals the eigenvalue-product ratio to
  `4·10⁻¹⁵` at a point below every root.
- **Coverage.** No sampled row has more than one even eigenvalue below the odd
  floor. Only the first slope, which is positive, is exercised. The alternation
  at later roots is proved in Lean and not seen numerically on this grid.
- **Controls.** C1 perturbs `B_L` off the rank-one relation `BD − DA = g Hᵀ`
  while keeping `H`: the product formula then misses the resolvent derivative
  by up to a relative `4.6·10⁸`. C2 counts larger eigenvalues instead of smaller
  ones (Mathlib's decreasing order): that sign rule fails at 7 roots. Both fail
  as predicted.

## M08: abstract cubic Schur (Step 34)

`post285_m08_cubic_schur_falsifier.py` works in exact SymPy rationals. It
expands `H(t)⁻¹` by the Neumann series around `H(t₀)` and reads `s'''(t₀)` off
the exact third Taylor coefficient of `s = a − b* H⁻¹ b`.

- **Formula.** On 18 seeded families the general, symmetric and response forms
  all equal the exact `s'''(t₀)`. The families are real symmetric with
  complement dimension 1 to 4, where dimension 1 is the 2×2 Schur toy model, and
  complex Hermitian with dimension 1 or 2, using the real-part form.
- **Controls.** C1 uses coefficient 3 instead of 6 on `⟪b', R H' R b'⟫` and
  fails on all 18 families. C2 lets `b(t₀) ≠ 0` and breaks the formula on all
  12 real families. C3 builds `s = s' = s'' = 0` with `s''' = ±1`: `s` is
  positive just to the right for `+1` and negative for `−1`, as the necessary
  sign predicts.

## M09: zero-endpoint weighted remainder identity (Step 32)

`post285_m09_weighted_remainder_falsifier.py` works at 30 digits with mpmath. It
computes `A_L[h]` directly from its pole, archimedean and prime channels and
compares it with `∫ R(e^t) h' + ∫ (e^{−t/2} − ρ) h`, integrating the staircase
cell by cell.

- **Identity.** 50 cases agree to a relative residual below `1e−28`. The tests
  are complex polynomial tests `t(L − t)p(t)` and the contact form
  `t² e(1 − t/L)` with the derivative used in Lean. The ten apertures include
  `L < log 2`, the seam `log 2`, and points just past `log 4` and `log 7`. A
  synthetic smooth `e` with `e(0) = 0` stands in for `e_{Dz}`, since the
  identity uses only `C¹` regularity and `e(0) = 0`.
- **Controls.** C1 keeps `h(0) = 0` but lets `h(L) ≠ 0`, and misses by exactly
  `R(e^L) h(L)`. C2 drops the main term `2√x` and misses by exactly
  `−∫ e^{t/2} h`. C3 drops the chain-rule factor `−1/L` in the contact derivative
  and misses by a nonzero amount.

The contact-weighted sign `A_{L*}[t² e_{Dz}] = −2 L*⁴ C/(2π)² ≤ 0` is a
theorem about generated contacts. No generated contact is known, so it is not
exercised numerically.

**Step 28 replay, certified.** The same script encloses the two historical Step
28 float values with Arb at 128 bits (`K = 2`, `L = 1.2`, `z = (1,−4,6,−4,1)`,
`Dz = (−2,4,0,−4,2)`):

- `E(Dz) ∈ [0.2154944559 ± 4e−11]`, certified positive. This is the M05
  regularized value, which a theorem equates with the canonical energy. On
  `[0, 1e−12]` the archimedean integrand is bounded through `|N(t)| ≤ t sup|N'|`.
- `A_L[t² e_{Dz}(1 − t/L)] ∈ [−0.52241962817044517287 ± 2e−21]`, certified
  negative.

Both historical 8-digit values lie inside `5e−9` of these enclosures. The vector
`z` is not an actual contact. The pair certifies only that positive ordinary odd
energy does not force a positive weighted value (gate G-WEIGHTED). The post-284
row X12 recorded these values as not replayed.

## M45: quantitative odd endpoint source bound (Step 82)

`post285_m45_odd_endpoint_falsifier.py` evaluates the elementary source energy
in Arb at 256 bits.

- **Bound.** For 29 Gaussian-integer legal odd vectors (`K = 2..8`, including
  the `K = 2` generator `(−1,2,0,−2,1)`), at eight rational apertures each up to
  the angle `(1/2π)√(5|M₃|/B(u))`, Arb certifies
  `−Re e_u(ω) − (π⁶/90)|M₃|²ω⁷ > 0` at all 232 cells. The aperture hypothesis
  is certified too. The smallest ratio `−e/((π⁶/90)|M₃|²ω⁷)` is 1.996.
- **Ingredients.** At 40 digits: the sine bound
  `|sin x − x + x³/6| ≤ |x|⁵/120`, the remainder bound
  `|T_u(t) + M₃t³/6| ≤ B(u)|t|⁵/120`, the integral `∫₀ᵃ t³(a−t)³ = a⁷/140`, and
  `B(u) ≤ A_K‖u‖` with `A_K² = 2Σn¹⁰`.
- **Sharpness.** The ratio tends to `16/7` as `ω → 0`. So `π⁶/90` is sharp up to
  the factor `16/7` that the `7/16` product bound costs.
- **Controls.** C1: the constant `(16/7)(1 + 10⁻³)π⁶/90` fails at `ω = 10⁻⁴`.
  C2: without the angle the bound fails, since the `K = 2` generator has
  `e(1) = 20 > 0` (certified). C3: dropping oddness while keeping `M₁ = 0` and
  `M₃ = 12` (an even part with `M₂ = 4` added) makes `Re e > 0` at small `ω`.
  C4: with `M₃ = 0` (the `K = 3` fifth-moment witness), `−e/ω⁷ → 0`, so no
  positive `ω⁷` bound exists without `m > 0`.

This is an elementary source statement. It is not a sign of the canonical
arithmetic test, and the contact angle `θ_*` (M46) is not checked here.

## M49: is the near-edge angle populated? (Steps 84, 90)

`post285_m49_near_edge_probe.py` uses the float canonical matrices for
`K = 2..6` and `L = 0.25, 0.5, …, 6`. At each point it takes the even ground
state `v`, which is not a contact. It computes the parity gap `δ`, `H(v)` from
the rank-one relation, and the angle `θ_* = (1/2π)√(5δ/(A_K|H(v)|√c))`.

- **Proved chain.** The parity-gap input `δ‖Dz‖² ≤ H(v)M₄` holds to float
  rounding. At all 329 prime samples inside `θ_*`, the chain
  `−e_{Dz}(ω_q) ≥ (π⁶/90)M₄²ω_q⁷ ≥ (π⁶/90)(δ/(c|H(v)|))²ω_q⁷` holds, with the
  energies taken at 50 digits.
- **Size of the angle.** With `c = 4`, `θ_*` is 0.084 for `K = 2` and at most
  0.052, 0.037, 0.028 and 0.022 for `K = 3, 4, 5, 6`.
- **Population.** Prime samples fall inside `θ_*` in 20 of 24 `K = 2` rows and
  6 of 24 `K = 3` rows. For `K = 4..6` none do on this grid, so the near-edge
  benefit is vacuous there. This answers the plan's question about the growth
  of `A_K` for this grid only.

12 rows have parity gap 0 to float resolution and are skipped.

## M50: the older-prime budget on the canonical grid (Step 91)

`post285_m50_older_prime_budget_probe.py` evaluates the M50 quantities on the
float canonical matrices for `K = 2..6` and `L = 0.25, 0.5, …, 6`. It uses the
even ground state, which is not a contact, and splits the samples at
`θ = θ_*(c = 4)` from the M49 probe. `P` is computed by Gauss–Legendre
quadrature with 400 nodes, and the sample energies at 50 digits.

- **Proved ingredients.** The size bound `|e_{Dz}(ω_q)| ≤ 2ω_q(2K+1)K²` holds
  at every sample of all 120 rows. The M49 near-edge bound
  `β_q e_{Dz}(ω_q) ≤ −bβ_qω_q⁷` holds at every near sample of the 108 rows
  with a positive parity gap.
- **Cancellation.** `P` and the prime sum nearly cancel. For `L ≥ 2`,
  `|V| = |P − ∑_q β_q e_{Dz}(ω_q)| ≤ 6.6·10⁻⁴|P|`. The sign of `V` is resolved
  (`|V| > 10⁻⁹ max(1, |P|)`) in 71 rows: negative in 54, positive in 17.
- **Finite form.** Wherever older samples exist,
  `2(2K+1)K² ∑_O β_q ω_q ≥ 114|P|`. So (91.2) holds with a wide margin and
  says nothing on this grid. The six rows with negative slack are prime-free
  (`L = 0.25` for every `K`, and `L = 0.5` for `K = 2`): there `O` is empty and
  `P > 0`. Those ground states have a positive even eigenvalue, so they are
  not contacts in any case.

A useful older-prime estimate (M51) has to keep the cancellation between `P`
and the primes; bounding each older term by its size cannot work. 12 rows have
parity gap 0 to float resolution: their size checks run, and the split is
skipped.

## M59/M61: source-moment kernel and the exact older-prime balance (Steps 98, 99)

`post285_m61_source_balance_falsifier.py` uses the float canonical matrices for
`K = 2..5` and `L = 0.25, 0.5, …, 6`. At each point it takes three legal even
vectors: the even ground state and two complex random vectors. None is a
contact. `h_v` is the mixed quadratic-normal atom on the elementary source
matrix, `β_q = Λ(q)/√q`, and the integrals use Gauss–Legendre quadrature with
400 nodes.

- **Kernel (98A).** `∫₀ᴸ h_v(1 − t/L)(W − ρ) − Σ_q β_q h_v(ω_q)` equals `H(v)`
  read off the rank-one relation `B D − D A = g H` to `5·10⁻¹⁴` at all 288
  vectors.
- **Real pairing (98B) and partition (99B).** `I − Σ_q β_q p_v(ω_q)` equals
  `Re(conj(M)H(v))`, and `I − O + N` equals the same value at
  `θ = 0.05, 0.2, 0.5`, both to `5·10⁻¹³`. At a contact the right side is the
  proved `|M|²/γ`.
- **Ward.** `γH(v) = M₄(v) − ⟨B⁻¹g, D A v⟩` holds to `3.5·10⁻¹¹` on the 81
  vectors with `λ_odd ≥ 10⁻⁶`. Below that the float odd block is the small net
  of large pole and prime channels, so `B⁻¹g` is not resolved and those
  vectors are not counted.
- **Gap.** `γ ≤ ‖g‖²/λ_odd` at every point.

Controls: C1 uses the M50 weights `Λ(q)(log q)²/√q` and misses the kernel value
by at least `1.3·10⁻³` (relative) for `L ≥ 1`. C2 drops the archimedean
integral and misses by at least `5·10⁻⁴`. C3 uses the energy `e_{Dz}` in place
of `h_z` and misses by at least 0.98.

This is a regression of the identities only. It says nothing about the sign
of `I + N − O` at a contact, which is the OPEN opposite side (99C).

## M33/M34: sign reversal and remainder oscillation (Steps 68, 70, 71)

`post285_m34_remainder_oscillation_probe.py` uses the float canonical matrices
for `K = 2..5` and `L = 1, 1.25, …, 6`, at the even ground state, which is not
a contact. `h(t) = t² e_{Dz}(1 − t/L)` and `R(x) = Σ_{n≤x} Λ(n)/√n − 2√x`.

- **Step 70.** The M09 identity on the actual source energy,
  `P − Σ_q β_q e(ω_q) = ∫ R(eᵗ) h' + ∫ (e^{−t/2} − ρ) h`, holds to `7·10⁻¹⁴`.
  `∫ R h'` is integrated piecewise between the breakpoints `log n`.
- **Step 71.** `|∫ R h'| ≤ (Ω/2) ∫ |h'|` holds at all 84 rows, with
  `Ω = sup R − inf R` on `[1, e^L]` (sup over integers, inf over left limits).
- **Step 68.** At the 10 rows where the explicit `θ` of the Lean theorem is at
  least `10⁻⁶`, `e_{Dz} < 0` at `θ/100, θ/10, θ/2, θ` (50 digits, with `Dz`
  projected onto the legal odd carrier) and `e_{Dz}(1) = 2‖Dz‖² > 0`. Elsewhere
  `θ` is below `10⁻⁶` and the `O(ω⁷)` energy is under the 50-digit floor, so
  those rows are not counted. `θ` is at most 0.0039 (`K = 2`) and 0.00017
  (`K = 5`).
- **Room in the budget.** The ground states use at most 30% of the oscillation
  room for `∫ R h'` and 13% for `∫ (e^{−t/2} − ρ) h`. So (71.2) with `C = 0`
  would hold with a margin of at least 7.8 on this grid: the crude oscillation
  `Ω` is far from an obstruction.

## M44: entering-prime physical jet (Step 81)

`post285_m44_entering_prime_jet_probe.py` works at 60 digits for `K = 2..5`,
with six legal even vectors per `K` (the even ground states of the float
canonical matrices at `L = 1, 2, 3, 4`, and two random vectors), at the seams
`q = 2, 3, 4, 5, 7, 8, 9, 11, 13`. That is 216 rows. `ΔQ_z(log q + h) =
−β_q e_{Dz}(h/(log q + h))` and `a = 2Λ(q)(2π)⁶|M₄(z)|²/(7!√q (log q)⁵)`.

- `M₃(Dz) = M₄(z)` to `10⁻⁵⁹`.
- `ΔQ/(a h⁷)` is within `10⁻³` of 1 at `h = 10⁻⁴` at every row.
- `|ΔQ − a h⁷|/h⁸` agrees within a factor 2 between `h = 10⁻³` and `10⁻⁴`.
- Inside the odd-endpoint angle of `Dz`, `ΔQ ≥ (π⁶/90) β_q |M₄|² ω_h⁷` and
  `ΔQ > 0` at all 1108 grid points.
- **Signal.** `|ΔQ − a h⁷|/h⁸` tends to `7a/log q`: it is 0.991 to 1.0002 of
  that value at `h = 10⁻⁴`. This is the next term predicted by
  `ω_h⁷ = (h/log q)⁷(1 − 7h/log q + …)`, since `e_u` is odd in `ω` and has no
  `ω⁸` term.
- **Control C1.** Using the even energy `e_z` in place of `e_{Dz}` gives a
  negative jump at all 216 rows. This is the ninth-order seam term of Step 56,
  a different observable.
- **Control C2.** Using `(log q)⁷` in place of `(log q)⁵` in `a` misses the
  ratio by at least 0.2.

## M29: source-resolvent derivatives (Steps 61, 62)

`post285_m29_source_resolvent_derivative_probe.py` uses the float canonical
matrices for `K = 2..5` and `L = 0.3, 0.55, …, 5.8`. It keeps the 27 points with
`λ_odd ≥ 10⁻⁶` and skips 65 where the float odd block is not resolved. With
`R = B_L⁻¹`, `r = R g` and `x = D⁻¹ r`:

- `T = H_L(x_L)` agrees with `1 − det A_L/det B_L` to `1.5·10⁻¹¹`.
- `T' = H'(x) + H(x')` and `T'' = H''(x) + 2H'(x') + H(x'')` agree with
  central differences of the determinant ratio to `5.2·10⁻⁵` and `3.0·10⁻⁴`.
  Where `λ_odd ≥ 10⁻²` the agreement is `1.9·10⁻⁷` and `2.5·10⁻⁶`. The operator
  jets are central differences of the matrices, with one Richardson step for
  the second jets.
- **Control C1.** Dropping `H(x')` from `T'` misses by at least 0.99 at every row.
- **Control C2.** Flipping the sign of `x'` misses by at least 0.99.
- **Control C3.** Counting `H'(x')` once in `T''` misses by at least 0.97.

The third derivative (Step 63) is not checked.

## M51: the K = 2 even bottom on `[1/400, log 16]` (Step 92)

Historical endpoint label: read `log 16` in this certificate claim as
`U = 2772588722239781/10^15`; the exact-log16 gap stays OPEN as explained above.

For `K = 2` the legal even carrier is spanned by `z = (1, −4, 6, −4, 1)`, so the
even compression is the scalar `λ(L) = ⟨z, S_L z⟩/⟨z, z⟩` and a contact is
`λ(L) = 0`. `post285_m51_k2_even_bottom_certificate.py` works in Arb at 128 bits.

- **Certificate.** `λ(L) > 0` for every `L ∈ [1/400, log 16]`. Each closed cutoff
  cell `[log Q, log(Q + 1)]` is covered by intervals on which
  `λ ≥ λ(c) − |λ'(c)| r + ½ min(0, inf λ'') r²`, with `inf λ''` from an Arb ball
  over the whole interval. It takes 1310 intervals; the smallest certified
  lower bound is `4.4·10⁻¹²`.
- **Closest approach.** After `L = 1.2` the local minima are `1.36·10⁻⁶`,
  `4.55·10⁻⁹`, `8.79·10⁻⁹` and `3.22·10⁻¹⁰`, at `L = 1.3339`, `1.7784`,
  `2.2230` and `2.6682`. These are `L γ₁/(2π) = 3.0008, 4.0008, 5.0008, 6.0025`,
  with `γ₁` the first zeta zero.
- **F04 at the minima.** The physical second test `V` matches
  `−(L⁴/(4π²))(λ'' + 2λ'/L)` from the Arb jets to `10⁻¹²`.
- **Zero side.** `λ` equals the sum of the first 100 single-zero terms
  `c_L(γ_k)`, each `≥ 0`, to `3·10⁻⁹` relative. At the minima the `γ₁` term
  nearly vanishes, so the margin is the higher-zero remainder. This uses the
  known zeros and is not independent of them.
- **Control C1.** Scaling every von Mangoldt weight by `1 + 10⁻⁶` makes `λ`
  negative at `L = 2.6682` (certified `−6.4·10⁻⁷`); the primes contribute
  `−0.645` there.
- **Control C2.** The same covering rejects `λ − 5·10⁻¹⁰` on the cell of the
  deepest minimum.
- **Positive control C3.** Scaling by `1 − 10⁻⁶` keeps `λ` positive.

`(0, 1/400)` is not certified; there `λ ≈ −log L − 0.90`. This is interval
evidence for `K = 2` only.

## M63: the two contact identities at the `K = 2` near-contacts (Step 100)

`post285_m63_route_comparison_probe.py` evaluates both routes at the four
minima above, with `v = z/|z|`.

- **Route A (F04 curvature).** At a stationary generated contact `V = −κC`, and
  `C = 0` for `K = 2`. At the minima `V/|P| = −1.7·10⁻²`, `−7.1·10⁻⁴`,
  `−7.3·10⁻⁵`, `−1.4·10⁻⁵`. `V` matches the F04 form to `5·10⁻⁹`.
- **Route B (source moment).** At any even contact
  `I − Σ β_q p_v(ω_q) = |M₄|²/γ`. At the minima the relative defect is `0.027`,
  `0.0096`, `0.0099`, `0.0054`, equal to `λ/λ_odd` to three digits (the Ward
  form of (98B)).
- **Control C1.** Route B with the M50 weights `Λ(q)(log q)²/√q` misses by a
  factor of at least 2900.

## M76 in Arb: the secular-margin grid certified (Step 113)

`post285_m76_arb_resolution.py` recomputes all 96 points of the M76 grid
(`K = 2..5`, `L = k/4 ≤ 6`) in Arb at 256 bits. It uses the canonical matrix at
the exact rational aperture, with the cutoff certified inside its cell, and the
exact integer parity carriers.

- **Certified signs.** `λ_min(A_L) > 0`, `λ_min(B_L) > 0` and
  `1 − T(L) = det A_L / det B_L > 0` at every point, the 50 float-unresolved
  points included. Float64 had shown negative bottoms at 13 of those 50 (9 even,
  4 odd); all are positive.
- **How small.** The margin falls to `2.2·10⁻⁹` (`K = 5`, `L = 6`) and
  `λ_min(A_L)` to `9.7·10⁻²⁵`. The even bottom is certified below the odd bottom
  at every point (ratio `0.49` down to `1.1·10⁻³`).
- **Consistency.** `T = H_L(x_L)` matches the determinant ratio to `10⁻⁴¹`. Each
  channel (pole, arch, prime, scalar) satisfies the rank-one relation on its own
  to `10⁻⁶⁸`, and the pole channel cancels at up to `2·10¹⁶` times `T`. On the 46
  resolved points the float64 margins agree to `1.9·10⁻³` relative; the error
  grows with the cancellation.
- **Where the dips are.** Every `K = 2` grid minimum of `λ_min(A_L)` is the grid
  point nearest some `2πk/γ₁` (`k = 4, 5, 8, 9, 10, 12, 13`). `K = 3` and `K = 4`
  dip deepest at `L = 4`, where `L γ₁/(2π) = 8.998`.
- **Control C1.** Every von Mangoldt weight times `1 + 10⁻⁶` makes `λ_min(A_L)`
  negative (certified) at the smallest-margin point of each `K`.
- **Control C2.** Times `1 − 10⁻⁶` makes `λ_min(B_L)` negative (`K = 2`), or both
  bottoms (`K = 3..5`). Positivity at these points depends on the exact prime
  weights to one part in a million, in both directions.
- **Control C3.** Adding `canonicalArchScalarCorrection` twice lifts both bottoms
  by exactly `2c(L) ≈ 0.87`, which would hide every near-contact.

This is pointwise evidence at 96 apertures: nothing between grid points, nothing
for `K ≥ 6`, and no contact is excluded.

## Inherited regressions kept running

These still run unchanged in the same job:
- the post-284 suite F01–F12;
- the exact SymPy falsifier;
- the M24/M30/M47 exact regressions;
- the M41/M43 interval enclosures;
- the attached log3 `K = 2` certificate.
