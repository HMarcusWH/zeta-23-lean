# R001 prime-side feasibility certificate — 2026-08-20

This is the required feasibility gate (predeclared in the route instructions) for
`R001_PRIME_UPPER`, produced **after** the zero-side chain closed in Lean and **before** any
further terminal prime-side Lean coding. Conclusions here are research assessments except where
a Lean theorem is explicitly cited; the cited Lean theorems are theorem-authoritative.

## 1. Exact observable

The claim-bearing observable, fixed by the now-closed zero-side chain, is

    F_k(a) = ‖ literatureRHS (translateRight k (2a)) ‖,

for admissible tests `k = q'' − (1/4)q`, `q ∈ C_c⁴(ℝ)` (so `k ∈ C_c²`), with both
explicit-formula pole transforms killed:

    paperFT k (±i/2) = 0        (Lean: paperFT_poleKilled_I_half / _neg_I_half).

By `literatureRHS_translateRight_poleKilled_eq` (Lean, unconditional), at every aperture

    literatureRHS (translateRight k (2a))
      = −Σ_n Λ(n)/√n · [k(log n − 2a) + k(−log n − 2a)]
        + (1/2π) ∫ paperFT(k_t)(r)·[Re ψ(1/4+ir/2) − log π] dr.

The Archimedean integral is uniformly bounded in `a` (profile decay ≪ (1+r²)^{-1} against a
log-growth bracket), so the growth question is exactly the translated prime sum.

## 2. Zero-side exceptional exponent

For a hypothetical zero ρ = 1/2 + δ + iγ, δ > 0, the Laplace pole of the family sits at
2δ + 2iγ; failure of subexponentiality is forced for every δ > 0
(Lean: `not_subexponential_weilLiteratureRHS_of_right_zero`,
`exists_poleKilled_test_not_subexponential_of_right_zero`). No pointwise exponential
lower-growth is claimed; the claim is exactly `¬ Subexponential`.

## 3. Prime-side trivial exponent

Support localization: for `a > Λ/2` (Λ = test support radius) only `log n ∈ [2a−Λ, 2a+Λ]`
contributes, i.e. `n ≍ X = e^{2a}`. Chebyshev gives

    Σ_{n≍X} Λ(n)/√n ≍ √X = e^a        →  trivial exponential rate exactly 1.

## 4. Effect of pole killing on the PNT main term

Writing the prime sum as a Stieltjes integral against ψ(x),

    main term (dx-part) = e^a · ∫ k(u) e^{u/2} du = e^a · paperFT k (−i/2) = 0

for pole-killed k. **The pole-killer removes the PNT main term of the prime sum identically.**
The residual is the pure fluctuation

    P_k(a) = ∫ k(log x − 2a) x^{−1/2} d(ψ(x) − x).

## 5. Strongest unconditional input and resulting exponent

With the strongest unconditional zero-free-region bound (de la Vallée Poussin form,
ψ(x) − x ≪ x·exp(−c√(log x)); the repository's own Chebyshev–Mertens layer is weaker),

    P_k(a) ≪ e^{a − c'√a}    →  exponential rate 1 − o(1).  NOT subexponential.

Under RH, ψ(x) − x ≪ √x log²x gives P_k(a) ≪ a², subexponential.

## 6. Formal status of the gap: THE SCALAR TARGET IS RH

This is no longer an estimate-versus-estimate assessment. It is a Lean theorem:

    Zeta23.ExceptionalZero.arithmeticSideSubexponential_iff_criticalLine :
      ArithmeticSideSubexponential ↔ ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1/2

(`Zeta23/ExceptionalZero/ArithmeticReduction.lean`, sorry-free, standard axioms only).
The forward direction is the closed zero-side chain plus reflection; the converse holds because
on the critical line every filtered mode has unit modulus. Consequently `R001_PRIME_UPPER`
in the scalar observable class is **exactly equivalent to RH**. It cannot be closed by "more
PNT", and any unconditional theorem implying it is an RH-strength theorem by definition.

## 7. ξ-averaging / Montgomery–Vaughan route: exponent bookkeeping (REJECTED)

Modulated family `P_a(ξ) = Σ c_n n^{−iξ}`, `c_n = Λ(n)/√n·k(log n − 2a)`, window `|ξ| ≤ T`,
`T = e^{2βa}`:

- diagonal mass: `Σ|c_n|² ≍ Σ_{n≍X} Λ(n)²/n ≍ a`;
- MV off-diagonal penalty: `Σ n|c_n|² ≍ Σ_{n≍X} Λ(n)² ≍ X·a = e^{2a}·a`;
- provable L² bound: `∫_{|ξ|≤T}|P_a|² ≪ T·a + e^{2a}·a`; RMS ≪ max(√a, e^{(1−β)a}√a);
- exceptional zero at depth δ: localized spectral bump of L² mass `e^{4δa}·O(1)`;
  RMS `≍ e^{(2δ−β)a}`.

Detection requires `2δ − β > 1 − β` (β < 1) or `2δ − β > 0` with `β ≥ 1`, i.e. **δ > 1/2 in
every regime**; the dilution deficit is `e^{(2δ−1)a}` independent of the window length. Since
RH permits δ arbitrarily close to 0, the route fails the mandatory every-δ test. Structural
reason: MV's `δ_n ≳ 1/n` spacing penalty at `n ≍ X` is exactly the unconditional inability to
certify cancellation below the `√X` energy barrier; removing the additive `Σ n|c_n|²` term for
`T ≪ X` would itself be zero-density/RH-strength information. Recorded as DR-004.

## 8. Operator / Gram / multi-probe channels (14.A–14.C assessment)

Generic constraint: any exact observable `O` satisfying both route legs — (i) off-line zero ⇒
`¬Subexponential O`, and (ii) unconditional arithmetic ⇒ `Subexponential O` — proves RH
outright; hence once (i) is proved for a class, every candidate (ii) for that class is exactly
RH-strength (for the scalar class this is now the Lean equivalence above, not an inspection).
Observable-engineering can therefore only *reorganize* where the RH-strength difficulty sits —
e.g. Weil positivity `W(g⋆ĝ) ≥ 0` is verbatim RH by Weil's criterion — it cannot weaken the
total requirement. A "better observable" search is a search for a more provable reorganization
of RH, and must be evaluated as such, never as an independent arithmetic target.

## 9. R003/R004 status

Not advanced this session. The exact finite displacement identity `[D,M] = g1ᵀ − 1gᵀ`
(rank ≤ 2) remains finite-matrix algebra with no theorem-authoritative finite-to-infinite
bridge; the fitted prolate generator's spectral-gap collapse stands. R003 remains OPEN.

## 10. Certificate verdict

- Exceptional exponent: `2δ` for every δ > 0 (proved, Lean).
- Trivial prime exponent: `1`.
- Best unconditional exponent: `1 − o(1)`.
- Averaging dilution: fatal (`e^{(2δ−1)a}` deficit, every window).
- Is the required estimate RH-equivalent? **YES — proved in Lean.**

Therefore: do **not** attempt terminal Lean coding of `R001_PRIME_UPPER` as an arithmetic
estimate. The route's honest terminal state is `RH_OPEN` with the single remaining theorem
`ArithmeticSideSubexponential` (equivalently RH), and any future attack must present a named
new information channel together with a *new* zero-side leg (i) for its observable.
