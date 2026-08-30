# D0-C — cutoff-free CCM finite matrix map — 2026-08-30

Status: **THEOREM IMPLEMENTED / FINAL PR VALIDATION REQUIRED**.

Repository: `HMarcusWH/zeta-23-lean`

Base:

```text
ff878f010318273ebb740f5f523ce7f57e6517c6
```

PR: **#65**

Branch:

```text
research/d0c-cutoff-free-matrix-map-20260830
```

## Objective

Remove the remaining finite representation ambiguity between the
project's theorem-authoritative zeta zero-side matrix and the pinned
cutoff-free CCM/CvS source convention.

The target is a finite matrix-formula identity only:

```text
zeroSideMatrix hs N L = cutoffFreeMatrix L N
```

for every finite `N` and positive aperture `L`.

This document does **not** promote the stronger operator statement that the
finite matrix is the restriction of a named infinite localized Weil form to a
Hilbert/form-domain Galerkin subspace.  That is a separate downstream G0/G1
obligation.

## Pinned external source

The convention audited in PR #33 remains pinned to:

```text
repository: HMarcusWH/connes-cvs-
commit:     5a66d0cd177ef8b8ad1c2c93165b8d56ca40292c
source blob:90576ea92835fff2f9dd2e3aa63ad99829bd17e5
```

The external Python implementation remains an oracle/falsifier only and is
forbidden as a Lean dependency.

## Primitive convention map

PR #33's independent normalization audit isolated:

```text
alpha_reference = alpha_ours
beta_reference  = beta_ours
gamma_reference = gamma_ours - cCorrection(L)
pole_reference  = pole_ours
```

The corresponding finite target was:

```text
Q_inf = M + 2*cCorrection(L)*I.
```

Before PR #65 this relation was source-formula/numerical-audit evidence, not a
Lean theorem.

## Independent Lean object

PR #65 defines, without using `finiteMatrix`, `dictionaryMatrix`, or
`zeroSideMatrix` in the definition:

```text
cutoffFreeGammaL
cutoffFreeArchComponent
cutoffFreeEntry
cutoffFreeMatrix
```

on the full centered Fourier index set `-N,...,N`, dimension `2N+1`.

The matrix is **not** defined as an alias of the desired target.

## Theorem ladder

The implemented theorem surface is:

```text
cutoffFreeArchComponent_eq_archComponent_sub_two_correction
cutoffFreeEntry_eq_entry_add_two_correction
cutoffFreeMatrix_eq_dictionaryMatrix
cutoffFreeMatrix_eq_finiteMatrix_add_correction
zeroSideMatrix_eq_cutoffFreeMatrix
```

Thus the intended exact composition is

```text
actual zeta zero sum
    = zeroSideMatrix
    = cutoffFreeMatrix
    = dictionaryMatrix
    = finiteMatrix + 2*cCorrection(L)*I.
```

## Parameter lock

The pinned cutoff-free source uses

```text
L = log c,
```

while the fork-owned historical lambda wrapper uses

```text
L = 2*log(lambda).
```

PR #65 therefore defines both wrappers and proves, for positive `lambda`,

```text
cutoffFreeMatrixOfCutoff (lambda^2) N
  = cutoffFreeMatrixOfLambda lambda N.
```

This records the convention map

```text
c = lambda^2
```

inside Lean rather than leaving another factor-two convention in prose.

## Full matrix versus even sector

The promoted D0-C theorem concerns the full centered `2N+1` matrix.

The pinned source also exposes a reversal-even `N+1` compression.  No
full-to-even isometric compression/conjugacy theorem is claimed by PR #65.
That map may be formalized later if required by the spectral route.

## Claim firewall

**PROVED only after exact final CI passes:**

- the independently defined finite cutoff-free source matrix has the exact
  scalar-diagonal normalization above;
- the actual finite zeta `zeroSideMatrix` equals that finite source matrix;
- the cutoff/lambda parameter wrappers agree under `c=lambda^2`.

**OPEN:**

- identification with a named infinite Hilbert-space operator or quadratic
  form restriction;
- form-domain inclusion;
- nestedness/density/form-core density;
- Rayleigh-Ritz bottom-of-spectrum convergence;
- positivity;
- R002 taper-grid masking;
- Bombieri truncation correspondence;
- finite-to-infinite closure;
- RH.

## D0 continuation

After final green settlement:

1. **D0-R:** test whether the generic R002 taper-grid/windowed-probe object has
   an exact change-of-basis, compression, or congruence map to the canonical
   CCM finite object.  A clean negative classification is an acceptable
   result.
2. **D0-B:** extract the exact Bombieri finite truncation conventions and prove
   or refute an exact map to the canonical finite object.
3. If D0-C remains green after those audits, move to **G0/G1**: define the
   actual finite function subspace and prove the matrix is the restriction of
   the localized Weil form.
4. Only then attack the decisive **form-core / Rayleigh-Ritz** finite-to-infinite
   seam.

RH remains **OPEN**.
