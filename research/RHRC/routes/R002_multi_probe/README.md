# R002 — Multi-probe tomography → Gram/operator observables

Search over a predeclared family of apertures/test functions/probes rather than
one compression. The candidate must identify information absent from the
TightMult certificate and survive the G03/G04/G05 sanity fixtures.
Promotion condition: an exact separation theorem, not a classifier score.

## Locked objects

- **Probe family:** the taper grid `τ_k = T + 2πk/L`, `k < d ≈ LT/2π`, with
  `φ` supported in `[−L/2, L/2]`, `L = λ·l`, `l = log(T/2π)`, `X = e^L`.
- **Observable:** the *spectrum* of the windowed Gram `G̃(T)`, whose zero-side
  and prime-side expressions are unconditionally equal
  (`ZeroConfig.Gz_eq_Gp` + `paperInputs_zeta`). The retained channel is the
  **eigenvalue sign / forbidden direction**, i.e. the negative index `n₋`,
  which the paper's certificate never uses.
- **Block object:** `ZeroSide.ZeroBlockData.pair_term`'s exact off-line pair
  block `2m(xxᵀ − yyᵀ)`, `u = x + iy`, with `y = 0` exactly for on-line zeros.

## Proof-search ladder

| step | statement | status |
|---|---|---|
| P0 | off-line pair block has a strictly negative direction, with an explicit witness and an exact value | **CLOSED** (`dotProduct_pairBlock_orthoWitness`, `..._neg`) |
| P1 | on-line configurations and the TightMult mock have no such direction | **CLOSED** (`dotProduct_nonneg_of_onLineCombination`) |
| P2 | the two are therefore not equal — block-level separation | **CLOSED** (`not_onLineCombination_of_pairBlock`) |
| P3 | windowed visibility: the negative direction survives the PSD on-line bulk | **OPEN** — masking; visible iff `δL ≳ √(6/λ)`, and unconditionally at `λ > 1` where the grid oversamples (§3 of the feasibility certificate) |
| P4 | arithmetic leg: `∫\|W\|²ν_X ≥ −θ` for all band-limited `W` | **OPEN and RH-equivalent** in the `∀(T, λ>1)` limit (Weil's criterion) — see OBS-009 |
| P5 | CCM identification: `M_{λ,N}` is the same Weil–Gram object | **OPEN, partially verified** — see R002-D below |

P0–P2 are proved in `Zeta23/ExceptionalZero/ProbeGramNegativity.lean`
(sorry-free, standard axioms only). P3–P5 are not claimed.

## Feasibility certificate

`MULTI_PROBE_GRAM_OPERATOR_FEASIBILITY_2026_08_21.md` — six candidate families,
scalar-collapse audit against OBS-008, every-δ bookkeeping with numerical
validation, online-double adversary, named unconditional mechanisms, ranking,
decision token `PROMOTE_ONE_CANDIDATE_TO_FORMALIZATION`.

Killed there, with decisive reasons: **R002-B** (odd moment `tr G̃³` — needs
ternary Λ-correlation to relative precision `1/N`), **R002-E** (L² aperture
coherence — collapses to OBS-008 by linearity plus Cauchy–Schwarz), **R002-F**
(full-diagonal majorization — δ-insensitive at leading order). Both kills are
recorded as DR-006.

## R002-D — the CCM ≡ Weil–Gram bridge: conjecture refuted, gap localized

Numerical result obtained 2026-08-21 (claim cap
`FINITE_NUMERICAL_DIAGNOSTIC_ONLY`, script `check_ccm_weil_bridge.py`): for the
even two-sided test `K_{nm}(y) = q_basis(n,m,|y|,L)` attached to R004's CCM
matrix, two of the three explicit-formula channels match **exactly**, to 10
digits, with a uniform factor 2:

```
h_{nm}(i/2) + h_{nm}(−i/2)              = 2 · pole_component(n,m,L)
Σ_k Λ(k)k^{−1/2}(K(log k) + K(−log k))  = 2 · prime_component(n,m,L)
```

The archimedean channel does **not**: the ratio to `arch_component` is
consistent with `−2` on the off-diagonal entries (−1.90 … −1.97, within the
quadrature truncation tail) but clearly not on the diagonal (−1.59 at `(0,0)`,
−0.75 at `(1,1)`, stable across λ). The assembly test agrees: off-diagonal
`(1,0)` matches the Weil zero-side sum within the zero tail, both diagonals are
off by a near-constant ≈ 1.064.

**So `M_{λ,N} = ½·(Weil Gram)` is FALSE as stated — and the gap is localized to
the diagonal archimedean term**, which is exactly where R004 uses a separate
formula (`2γ_L(n) − 2β_L(n)`) instead of the off-diagonal divided difference,
and exactly the part of `M` that the displacement identity leaves unconstrained
(`[D,M]` vanishes on the diagonal identically).

Sharpened R003 question, now well posed: *is there a diagonal normalization
making `M_{λ,N}` exactly `½·(Weil zero-side Gram)` in this basis?* An
affirmative answer turns `[D,M] = g1ᵀ − 1gᵀ` into an exact explicit-formula
statement (R004 ladder step **J5**). Obstacles: a higher-accuracy archimedean
quadrature is needed to assert (rather than merely observe) the off-diagonal
match; and `K_{nm}` is only piecewise `C¹`, so it is not a legal `C_c²` test for
`EF_lit` — formalization would need a mollified family and a limit.

## Dumbassery checks

- The block-level separation is **not** a windowed-visibility theorem: the
  on-line bulk can mask the negative direction (P3).
- `n₋ ≥ 1` at block level does **not** imply RH; the arithmetic leg (P4) is
  RH-equivalent, per OBS-009.
- The `λ > 1` every-δ result buys detection at the price of `X > T`, i.e. a
  longer Dirichlet polynomial — the difficulty is exchanged, not removed.
- Numerical `λ_min < 0` in the synthetic diagnostic is a finite computation on a
  synthetic zero lattice; it is not evidence about ζ.
- The R002-D factor-2 match is numerical at one `(λ, N)`; it is not an identity
  until the archimedean channel is verified and the whole thing is proved.

## Route-specification adaptation — 2026-08-21 (DISCOVERY phase, logged)

The route previously named only "a predeclared multi-probe family" with no
observable fixed. It is now specialized to the **negative-index channel of the
windowed Gram**, and claim `R002_MULTI_PROBE_SEPARATION` is restated to the
block-level statement actually proved (with its transversality hypothesis
`gramDet x y ≠ 0` explicit) rather than the earlier open-ended wording. The
claim registry carries the corresponding `adaptation_note`.

## Non-claims

- No RH evidence, no RH route closure, no promotion of `C_RH`.
- No windowed-visibility theorem, no arithmetic upper bound.
- No CCM identity — only a partial numerical channel match.
- Finite numerical diagnostics have no theorem authority; Lean/comparator
  remains the promotion gate.
