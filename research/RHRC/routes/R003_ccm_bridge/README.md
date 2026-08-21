# R003 — CCM / Weil / aperture bridge

The earlier finite-prime CCM program remains a separate finite-validation lane.

A formal `CCMBridge.lean` should not be created merely because two constructions look similar. Promotion requires an exact identity, intertwiner, or quantitatively controlled convergence/limit theorem sufficient for the claim being consumed.

## Sharpened bridge question — 2026-08-21

The R002 campaign compared R004's finite CCM matrix `M_{λ,N}` directly against
the Weil literature form, using the even two-sided test
`K_{nm}(y) = q_basis(n,m,|y|,L)` and `h_{nm}(z) = ∫K_{nm}(y)e^{izy}dy`
(diagnostic: `routes/R002_multi_probe/check_ccm_weil_bridge.py`; receipt:
`receipts/r002_negindex_masking_2026_08_21.json`; claim cap
`FINITE_NUMERICAL_DIAGNOSTIC_ONLY`).

Result: the pole and prime channels match **exactly**, to 10 digits, on every
tested entry and both tested λ, with a uniform factor 2 —

```
h_{nm}(i/2) + h_{nm}(−i/2)              = 2 · pole_component(n,m,L)
Σ_k Λ(k)k^{−1/2}(K(log k) + K(−log k))  = 2 · prime_component(n,m,L)
```

— and the archimedean channel matches off-diagonally (ratio −1.90…−1.97,
consistent with −2 within the quadrature truncation tail) but **not** on the
diagonal (−1.59 at `(0,0)`, −0.75 at `(1,1)`, stable in λ). So

> `M_{λ,N} = ½ · (Weil zero-side Gram in this basis)` is **false as stated**,
> and the entire discrepancy is localized to the **diagonal archimedean term**.

This is the part of `M` that R004 builds with a separate formula
(`2γ_L(n) − 2β_L(n)`, not the off-diagonal divided difference), and also exactly
the part that the exact displacement identity `[D,M] = g1ᵀ − 1gᵀ` leaves
unconstrained (its diagonal is identically `0 = 0`).

**The R003 question is therefore now well posed:** is there a choice of diagonal
normalization for which `M_{λ,N}` is exactly `½ ·` the Weil zero-side Gram in
this basis? An affirmative answer would convert the displacement identity into
an exact statement about the explicit formula — R004 ladder step **J5** — and
would satisfy this route's "exact identity or intertwiner" promotion bar.
A negative answer bounds how close the CCM construction can come to a Weil form.

Prerequisite before any Lean work: `K_{nm}` is continuous but only piecewise
`C¹` (kink at `y = 0`), so it is not a legal `C_c²` test for `EF_lit`; a
mollified family plus a limit would be required.
