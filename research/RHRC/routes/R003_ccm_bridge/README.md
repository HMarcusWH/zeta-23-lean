# R003 — CCM / Weil / aperture bridge

The earlier finite-prime CCM program remains a separate finite-validation lane.
A formal `CCMBridge.lean` should not be created merely because two constructions
look similar. Promotion requires an exact identity, intertwiner, or
quantitatively controlled convergence/limit theorem sufficient for the claim
being consumed.

## Locked objects

- **CCM matrix** (R004): `M_{λ,N}(n,m) = Pole − Arch − Prime` over Fourier
  indices `n,m ∈ [−N,N]`, `L = 2 log λ`, prime powers `k ≤ e^L`.
- **Index operator**: `D = diag(−N,…,N)`; R004's algebraically closed
  displacement identity is `D M − M D = g 1ᵀ − 1 gᵀ`, hence
  `rank(DM − MD) ≤ 2` (sympy-certified, float-verified to 1.75e-15).
- **Weil object**: the explicit-formula zero-side sum `Σ_ρ m_ρ h_{nm}(γ_ρ)` for
  the even two-sided truncated-character correlation
  `K_{nm}(y) = q_basis(n,m,|y|,L)`, `supp K = [−L,L]`.

## The reduction that makes the comparison exact

The literature explicit formula is
`WeilGram = [h(i/2)+h(−i/2)] − PrimeSum + ArchLit`. The pole and prime channels
match the CCM construction exactly with a uniform factor 2, so in
`WeilGram − 2M` they cancel identically and

```
WeilGram(n,m) − 2·M(n,m)  =  ArchLit(n,m) + 2·arch_component(n,m).
```

This is a purely **archimedean** statement — no zero sums, hence no slowly
converging zero tail. `check_diagonal_shift.py` measures it directly.

## Closed form for `h` (derived, and validated to 1e-16)

With `a = 2πm/L`, `b = 2πn/L` (so `aL, bL ∈ 2πZ`):

```
n ≠ m :  h(r) = (2/(π(n−m))) (1 − cos rL) [ a/(a²−r²) − b/(b²−r²) ]
n = m :  h(r) = (2/L) (1 − cos rL) [ 1/(b+r)² + 1/(b−r)² ]
```

Both are even and entire (the apparent poles are removable: `1 − cos rL` has a
double zero there). Specializing to `r = i/2` reproduces
`h(i/2) + h(−i/2) = 2·pole_component(n,m,L)` **analytically** — the pole channel
is now a derivation, not just a numerical match.

## Why the diagonal is special (structural explanation of the shift)

For `n ≠ m`, `K_{nm}(0) = 0`, so `∫K_{nm}·ρ` converges outright and
`arch_component` off-diagonal is exactly that integral, with no added constant.
For `n = m`, `K_{nn}(0) = 2 ≠ 0`, the archimedean density
`ρ(x) = e^{x/2}/(e^x−e^{−x}) = e^{−x/2}/(1−e^{−2x})` (the classical kernel) makes
the integral logarithmically divergent at `0`, and R004 regularizes it with the
**index-independent** constants `c_correction(L) + w_correction(L)` inside
`gamma_L`. Every non-cancelling term is therefore proportional to `K(0)`, which
vanishes off the diagonal — so the CCM/Weil discrepancy *must* be a multiple of
the identity. That is hypothesis **H**, and it is structural rather than
accidental.

## Proof-search ladder

| step | statement | status |
|---|---|---|
| J1-D | exact finite displacement identity `[D,M] = g1ᵀ − 1gᵀ` | CLOSED (R004, algebraic) |
| B0 | closed form for `h_{nm}`, and the pole channel `2h(i/2) = 2·pole_component` | **DERIVED + validated to 1e-16** |
| B1 | prime channel `PrimeSum = 2·prime_component` | verified to 10 digits (even-extension convention) |
| B2 | `WeilGram − 2M = ArchLit + 2·arch` (pole/prime cancel) | **exact reduction** |
| B3 | H: the residual is `c(L)·δ_{nm}` | **numerically confirmed** (diag spread 4.5e-9 … 2.1e-10); structurally explained above |
| B4 | closed form `c(L) = 4·c_correction(L)` | **numerically confirmed to machine precision**, four λ (table below) |
| J5 | transfer: `[D, WeilGram] = 2(g1ᵀ − 1gᵀ)`, rank ≤ 2 | **algebra proved in Lean**, conditional on B3 as an explicit hypothesis |
| J6 | finite→infinite normalization / limit | OPEN |

Lean: `Zeta23/ExceptionalZero/DisplacementTransfer.lean` proves the transfer
algebra — `displacement_add_scalar`, `displacement_eq_of_eq_smul_add_scalar`,
`rank_displacement_le_two_of_eq_smul_add_scalar` — sorry-free, standard axioms.
Every statement carries the CCM/Weil relation as an **explicit hypothesis**;
none of them asserts it.

## Measured result

`confirm_closed_form.py`, `mp.dps = 20`. `c_raw` is the mean diagonal residual;
`offdiag sys` is the mean off-diagonal residual, which H predicts to be exactly
zero and which is a common systematic of the archimedean quadrature tail, so
subtracting it removes that systematic from both:

| λ | `c_raw` (diagonal) | off-diag systematic | `c` corrected | `4·c_correction(L)` | \|diff\| | diag spread |
|---|---|---|---|---|---|---|
| 2 | 1.076281434379 | 2.48e-07 | 1.076281186271 | 1.076281186271 | 5.6e-15 | 4.5e-09 |
| 3 | 1.408303228758 | −1.05e-07 | 1.408303333375 | 1.408303333375 | 1.3e-15 | 1.1e-09 |
| 5 | 1.616560903218 | 4.93e-08 | 1.616560853940 | 1.616560853940 | 2.2e-16 | 3.6e-10 |
| 7 | 1.681430174226 | −5.57e-08 | 1.681430229916 | 1.681430229916 | 2.2e-16 | 2.1e-10 |

So, numerically and at machine precision on four values of λ:

```
WeilGram(n,m)  =  2 · M_{λ,N}(n,m)  +  4·c_correction(L) · δ_{nm},
c_correction(L) = ∫₀^L (1 − e^{−x/2}) / (e^x − e^{−x}) dx.
```

Because `[D, c·I] = 0`, this is exactly the shape that transfers R004's
displacement identity — see `DisplacementTransfer.lean` and step J5.

## The remaining obstacle to a Lean identity

`K_{nm}` is continuous but only piecewise `C¹` (a corner at `y = 0`), so it is
**not** an admissible `C_c²` test for `EF_lit`. Formalizing B1–B3 therefore needs
a mollified family plus a limit, or an EF strengthened to `C¹`-with-bounded-
variation tests. Until then B3/B4 remain numerical and `R003_CCM_BRIDGE` stays
OPEN.

## Dumbassery checks

- B3/B4 are numerics at finitely many `(λ, n, m)`; they are not the identity.
- The Lean transfer theorems are conditional; reading them as establishing the
  bridge would be exactly the "module A passes, module B passes" error the OoL
  discipline forbids.
- `rank ≤ 2` for a finite matrix says nothing about any infinite operator; J6 is
  untouched.
- No RH consequence is claimed anywhere in this route.

## Reproduction

```
pip install -r requirements.txt
python3 check_diagonal_shift.py --lambdas 2 3 5 --ns -3 -2 -1 0 1 2 3
```

## Non-claims

- No CCM identity, no intertwiner, no limit theorem.
- No RH evidence, no RH route closure.
- Finite numerics have no theorem authority; Lean/comparator is the gate.
