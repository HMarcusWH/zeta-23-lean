# R003 — CCM / Weil / aperture bridge

Status: **DISCOVERY**.  RH remains open.

The finite CCM matrix is now theorem-authoritative in `Zeta23.CCM`, and PR #30 proved its exact
finite index-displacement identity in Lean.  The remaining R003 bridge is deliberately split into
two different mathematical obligations:

1. **deterministic RHS identity** — prove the literature explicit-formula RHS evaluated on the CCM
   kernel equals the formal finite CCM matrix up to the observed scalar shift;
2. **explicit-formula regularity extension** — prove that the actual zeta zero-side sum equals that
   literature RHS for the continuous, compactly supported but non-`C_c²` CCM kernel.

These arrows must not be conflated:

```text
formal CCM matrix M
    |
    |  R003_CCM_RHS_IDENTITY
    v
EF.literatureRHS(K)
    ^
    |  R003_KERNEL_EF_EXTENSION
    |
actual zeta zero-side matrix G
```

Only when both arrows are proved may `R003_CCM_BRIDGE` be promoted.

## Locked objects

- **CCM matrix**: `Zeta23.CCM.finiteMatrix L N`, with source-level wrapper
  `finiteMatrixOfLambda lam N` using the exact conversion `L = 2 log lam`.
- **Index operator**: `Zeta23.CCM.indexMatrix N`.
- **Formal finite displacement theorem**:
  `Zeta23.CCM.finiteMatrix_displacement` and
  `Zeta23.CCM.rank_finiteMatrix_displacement_le_two`.
- **CCM/Weil test**:
  `Zeta23.CCM.kernel n m L y = qBasis n m |y| L` on `|y| <= L`, zero outside.
- **Deterministic target object**: `EF.literatureRHS (kernel n m L)`; this is not yet called the
  zero-side Weil Gram because `kernel` is not an admissible `C_c²` test for the current `EF_lit`
  theorem.

## Exact finite displacement result now closed

For positive aperture `L`, the formal CCM entry satisfies

```text
(n-m) M_nm = g_n - g_m,
```

with the exact formal sequence

```text
g_n = poleSeq n L + alphaL n L + primeSeq n L.
```

Consequently, on the centered finite grid,

```text
[D,M] = g 1^T - 1 g^T,
rank([D,M]) <= 2.
```

This is now compiler-checked Lean mathematics for the actual formal CCM matrix, not merely a
Python/SymPy identity.  It is registered as `R004_CCM_DISPLACEMENT_FORMAL`.

## The deterministic scalar-shift target

The literature RHS is

```text
RHS(K) = PoleLit(K) - PrimeLit(K) + ArchLit(K).
```

The working candidate, supported by the finite diagnostics, is

```text
RHS(K_nm) = 2*M_nm + 4*cCorrection(L)*delta_nm.
```

Equivalently, after exact pole and prime cancellation, the only nontrivial identity is

```text
ArchLit(n,m,L) + 2*archComponent(n,m,L)
  = 4*cCorrection(L)*delta_nm.
```

This statement is purely deterministic analysis.  It can be proved before the non-`C_c²`
regularity seam is solved.

## Why the diagonal is special

The formal kernel already satisfies

```text
K_nm(0) = 2*delta_nm.
```

Off diagonal, `K_nm(0)=0`, so the singular archimedean contact channel is cancelled by the test
itself.  On the diagonal, `K_nn(0)=2`, and the finite CCM formula carries index-independent
regularization constants through `gammaL`.

This gives a structural mechanism for a scalar diagonal shift, but it is **not itself a proof**
that the full gamma-side residual equals `4*cCorrection(L)*I`.  That exact identity remains the
central analytic theorem of `R003_CCM_RHS_IDENTITY`.

## Closed form for the transform — discovery evidence

With `a = 2πm/L`, `b = 2πn/L`, the diagnostic derivation gives

```text
n != m:
  h(r) = (2/(π(n-m))) (1-cos(rL))
         * [a/(a^2-r^2) - b/(b^2-r^2)]

n = m:
  h(r) = (2/L) (1-cos(rL))
         * [1/(b+r)^2 + 1/(b-r)^2].
```

The apparent poles are removable.  Specialization to `r = +/- i/2` reproduces the factor-two pole
channel numerically and by paper derivation; the next formalization wave will turn the pole and
prime channels into Lean theorems before attacking the archimedean channel.

## Numerical scalar-shift diagnostic

`confirm_closed_form.py`, `mp.dps = 20`:

| lambda | c_raw | offdiag systematic | corrected c | `4*cCorrection(L)` | abs diff | diag spread |
|---|---:|---:|---:|---:|---:|---:|
| 2 | 1.076281434379 | 2.48e-07 | 1.076281186271 | 1.076281186271 | 5.6e-15 | 4.5e-09 |
| 3 | 1.408303228758 | -1.05e-07 | 1.408303333375 | 1.408303333375 | 1.3e-15 | 1.1e-09 |
| 5 | 1.616560903218 | 4.93e-08 | 1.616560853940 | 1.616560853940 | 2.2e-16 | 3.6e-10 |
| 7 | 1.681430174226 | -5.57e-08 | 1.681430229916 | 1.681430229916 | 2.2e-16 | 2.1e-10 |

This is discovery evidence only.  The corrected machine-precision agreement is not theorem
authority and is not used as a proof premise.

## Proof-search ladder

| step | statement | status |
|---|---|---|
| J1-D-formal | exact `[D,M] = g1^T - 1g^T`, rank <= 2 for formal CCM matrix | **PROVED IN LEAN** |
| K0 | continuity/compact support/integrability of CCM kernel | **IN FORMALIZATION** |
| B0 | exact pole-channel identity | OPEN |
| B1 | exact prime-channel identity | OPEN |
| B2 | deterministic reduction to the archimedean channel | OPEN until B0+B1 are Lean-closed |
| B3 | exact archimedean scalar-shift identity | OPEN |
| B4 | `RHSMatrix = 2*M + 4*cCorrection(L)*I` | OPEN |
| E1 | extend zeta `EF_lit` from `C_c²` approximants to the CCM kernel | OPEN |
| J5 | actual zero-side matrix `G = 2*M + 4*cCorrection(L)*I` | OPEN |
| J5-D | exact `[D,G] = 2(g1^T - 1g^T)`, rank <= 2 | OPEN |
| J6 | finite-to-infinite operator/normalization seam | OPEN |

## Regularity seam

The current zeta literature explicit formula is already proved for every `C_c²` test.  The CCM
kernel is continuous and compactly supported but has the `|y|` corner at zero, so the intended route
is downstream approximation, not modification of the trusted `EF_lit` theorem:

```text
K_epsilon in C_c²
EF_lit(K_epsilon)
limits of zero / pole / prime / arch channels
-------------------------------
EF identity for K
```

The current intended approximation is a normalized compactly supported smooth mollifier, with a
uniform transform bound strong enough to justify zero-side and archimedean dominated convergence.

## Claim boundary

- `R003_CCM_RHS_IDENTITY`: OPEN.
- `R003_KERNEL_EF_EXTENSION`: OPEN.
- `R003_CCM_BRIDGE`: OPEN and depends on both claims above.
- `R003_WEIL_DISPLACEMENT`: OPEN.
- RH: OPEN.

No finite-to-infinite theorem, RH implication, or new prime-side upper bound is claimed.

## Reproduction

```bash
pip install -r research/RHRC/routes/R003_ccm_bridge/requirements.txt
python research/RHRC/routes/R003_ccm_bridge/check_diagonal_shift.py --lambdas 2 3 5 --ns -3 -2 -1 0 1 2 3
python research/RHRC/routes/R003_ccm_bridge/confirm_closed_form.py
```
