# Post-285 falsification report (M38, M55, M65–M76)

Terminal claim: **RH_OPEN**. Everything below is regression or experimental
evidence. Theorem authority comes only from the Lean roots listed in
`PROOF_ROOTS.json`.

## Scripts

All eight scripts live in `research/RHRC/routes/R003_ccm_bridge/post285/` and
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
  **not** reported as signs. Resolving them needs the Arb path
  (`canonical_source_arb.py`).

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

## Inherited regressions kept running

These still run unchanged in the same job:
- the post-284 suite F01–F12;
- the exact SymPy falsifier;
- the M24/M30/M47 exact regressions;
- the M41/M43 interval enclosures;
- the attached log3 `K = 2` certificate.
