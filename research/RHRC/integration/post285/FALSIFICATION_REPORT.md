# Post-285 falsification report (Steps 108–120, M70–M76)

Terminal claim: **RH_OPEN**. Everything below is regression or experimental
evidence. Theorem authority comes only from the Lean roots listed in
`PROOF_ROOTS.json`.

## Scripts

All three scripts live in `research/RHRC/routes/R003_ccm_bridge/post285/` and
run in the `source-falsifier-research` job of
`.github/workflows/rhrc_post284_source_inertia.yml`. Each one runs in seconds.

| Script | Packages | Result |
|---|---|---|
| `post285_m74_secular_falsifier.py` | M74, M30 | Pass, with both negative controls failing as they should |
| `post285_gate_a_d_falsifier.py` | M70, M73, M75 | Pass, with negative controls |
| `post285_m76_secular_margin.py` | M76 | Experimental signal (see below) |

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
- **Unresolved points.** 50 grid points (larger `K` and `L`) fall below float64
  resolution. Their apparent negative eigenvalues are at the 1e-15 level and are
  **not** reported as signs. Resolving them needs the Arb path
  (`canonical_source_arb.py`).

## Inherited regressions kept running

These still run unchanged in the same job:
- the post-284 suite F01–F12;
- the exact SymPy falsifier;
- the M24/M30/M47 exact regressions;
- the M41/M43 interval enclosures;
- the attached log3 `K = 2` certificate.
