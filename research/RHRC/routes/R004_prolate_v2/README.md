# R004-v2 — finite displacement / structural route

> **Current normalization authority**
>
> The canonical direct-source finite object is
>
> ```text
> canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix.
> ```
>
> The Python `build_ccm_matrix` executable and Lean `finiteMatrix` use the historical printed normalization. They differ from the canonical matrix by a scalar identity shift.
>
> R004 conclusions are therefore split:
>
> **shift-invariant and transportable:** commutators, displacement, eigenvectors/eigenspaces, eigenvalue gaps/order;
>
> **shift-sensitive and canonical-only:** absolute eigenvalues, PSD/positivity, inertia, lower bounds, trace, determinant.
>
> No R004 numerical output may be used as canonical spectral-sign evidence unless the canonical normalization is computed or an explicit scalar-shift theorem is applied.

Status: **DISCOVERY**. The fitted commutator/null results remain finite numerical diagnostics. The
index-displacement formula is now an **exact theorem-authoritative Lean identity for the formal
finite CCM matrix**. It is not a finite-to-infinite theorem and not RH evidence.

## Purpose

R004-v1 found that finite CCM/Weil matrices admit a real symmetric traceless tridiagonal matrix `J`
with an anomalously small normalized commutator relative to eigenvalue-preserving random-basis nulls.
That was a useful signal, but it left two dangerous alternative explanations open:

1. the normalization `||[M,J]||_F / (||M||_F ||J||_F)` might improve only because `||M||_F` grows;
2. a small commutator is not perturbatively useful if the recovered `J` has collapsing spectral gaps.

R004-v2 therefore reports absolute and gap-normalized metrics, adds a locality-preserving null, and
audits the index-displacement structure of the CCM matrix.

## Locked finite object

The source matrix is the Route-A CCM construction

`M_{lambda,N} = W_{0,2} - W_R - sum_p W_p`,

including prime powers through the von Mangoldt weight.

Source notebook SHA-256:

`aa6004b432f8baa3c9dc5c919b0f8df78621a84747f45bfda9fffc79a1d2e24d`

The formal port is now owned by `Zeta23.CCM`:

- `Zeta23.CCM.entry` — exact scalar finite CCM entry;
- `Zeta23.CCM.finiteMatrix` — aperture-level finite matrix;
- `Zeta23.CCM.finiteMatrixOfLambda` — source-level wrapper with `L = 2 log lambda`;
- `Zeta23.CCM.indexMatrix` — centered Fourier index operator.

The source mapping is frozen in `CCM_FORMAL_PORT_MANIFEST.json`.

## Candidate generator

As before, search the finite-dimensional space of real symmetric traceless tridiagonal matrices:

`min_J ||[M,J]||_F / (||M||_F ||J||_F)`.

The minimizer is obtained from the generalized Rayleigh problem for the commutator Gram matrix.

## New diagnostics

For the recovered `J`, v2 records:

- absolute `||[M,J]||_F`;
- `||M||_F` and `||J||_F`;
- Frobenius-normalized commutator;
- operator-norm commutator and operator-normalized ratio;
- minimum adjacent eigenvalue gap of `J`;
- `||[M,J]||_F / gap(J)`;
- `||[M,J]||_F / (||M||_F gap(J))`.

These metrics explicitly test whether the v1 signal can support a perturbative eigenvector argument.

## Null ensembles

### Eigenvalue-preserving random basis

`M_null = Q diag(eig(M)) Q^T`.

This preserves the exact spectrum and destroys the CCM basis structure.

### Band-profile-preserving null

For every diagonal offset `d`, independently permute the values on the `d`-th upper diagonal and
restore symmetry. This preserves the empirical value multiset on every matrix band while destroying
coherent index alignment.

## Exact theorem-authoritative index displacement identity

Let

`D = diag(-N, ..., 0, ..., N)`.

For Fourier indices `n,m`, the formal CCM matrix has

`M_nm = Pole_nm - Arch_nm - Prime_nm`.

The Lean development defines the exact scalar sequence

`g_n = poleSeq n L + alphaL n L + primeSeq n L`

and proves, for positive aperture `L`,

`(n-m) M_nm = g_n - g_m`.

Therefore on the centered finite grid:

`[D,M] = g 1^T - 1 g^T`

and

`rank([D,M]) <= 2`.

The theorem-authoritative sources are:

```text
Zeta23.CCM.entry_displacement
Zeta23.CCM.finiteMatrix_displacement
Zeta23.CCM.rank_finiteMatrix_displacement_le_two
```

The Python/SymPy certificate `derive_exact_displacement.py` remains an independent reproduction aid,
not theorem authority.

This result is theorem-relevant finite algebra, but it does **not** establish operator convergence,
identify a limiting Jacobi/prolate operator, or transfer finite spectral information to Xi.

## RUN 002 finite result

Grid:

- `lambda in {2,3,5,7,10}`;
- `N in {5,8,12,20}`;
- 10 eigenvalue-preserving nulls per case;
- 10 band-profile-preserving nulls per case;
- seed `20260820`.

Summary:

- maximum candidate / eigenvalue-null-median normalized residual ratio: about `3.29e-2`;
- maximum candidate / band-profile-null-median normalized residual ratio: about `7.37e-2`;
- maximum relative residual after rank-two approximation of `[D,M]`: about `1.76e-15`.

Thus the fitted tridiagonal commutant signal survives the stronger band-profile null on the tested
finite grid.

However, the perturbative spectral-gap story fails badly for the fitted generator in many tested
cases. Examples:

- `lambda=2, N=20`: `gap(J) ~ 1.39e-17` while `||[M,J]||_F ~ 1.45e-2`;
- `lambda=5, N=20`: `gap(J) ~ 1.34e-12` while `||[M,J]||_F ~ 2.63e-3`;
- `lambda=10, N=20`: `gap(J) ~ 1.88e-14` while `||[M,J]||_F ~ 1.43e-3`.

Therefore the v1 route `small normalized commutator -> spectral-gap estimate -> eigenvector
convergence` is **not supported by this recovered generator** without a different analytically
identified operator and a separate gap theorem.

## Revised proof-search ladder

`J0` — anomalous finite tridiagonal commutant relative to eigenvalue and band-profile nulls.
**NUMERICAL PASS.**

`J1-D` — exact finite displacement identity
`[D,M] = g 1^T - 1 g^T`. **CLOSED.**

`J1-D-formal` — bind the exact identity to a theorem-authoritative formal definition of the CCM
matrix. **CLOSED / PROVED IN LEAN** by `Zeta23.CCM.finiteMatrix_displacement` and
`Zeta23.CCM.rank_finiteMatrix_displacement_le_two`.

`J1-J` — derive an analytically specified Jacobi/prolate generator from the displacement identity or
another exact CCM identity. The numerical minimizer by itself is not an identification theorem.
**OPEN.**

`J2` — prove an absolute commutator estimate for that explicit generator, not merely a residual
normalized by `||M||`. **OPEN.**

`J3` — prove a theorem-relevant simple/uniform spectral-gap estimate for the analytically specified
generator. **OPEN; current fitted-generator finite gaps are a warning signal.**

`J4` — only after J2+J3, derive eigenspace convergence by a self-adjoint perturbation theorem. **OPEN.**

`J5` — connect the exact finite CCM structure to an actual zeta zero-side object.
**CLOSED / PROVED IN LEAN on the production object by #62/#63.** The theorem-authoritative
production identities are

```text
zeroSideMatrix = finiteMatrix + 2*cCorrection(L)*I
[indexMatrix, zeroSideMatrix] = g 1^T - 1 g^T
rank([indexMatrix, zeroSideMatrix]) <= 2.
```

PR #64 additionally settles the historical doubled R002-D raw-`qBasis/kernel` convention:

```text
rawKernelZeroSideMatrix = 2*finiteMatrix + 4*cCorrection(L)*I
[indexMatrix, rawKernelZeroSideMatrix] = 2*(g 1^T - 1 g^T)
rank([indexMatrix, rawKernelZeroSideMatrix]) <= 2.
```

Sources: `Zeta23.CCM.zeroSideMatrix_eq_finiteMatrix_add_correction`,
`Zeta23.CCM.zeroSideMatrix_displacement`,
`Zeta23.CCM.rawKernelZeroSideMatrix_eq_two_finiteMatrix_add_four_correction`, and
`Zeta23.CCM.rawKernelZeroSideMatrix_displacement`. This does not identify the
general R002-A taper-grid `G̃(T)`, prove positivity, or address J6.

`J6` — close the finite-to-infinite normalization and limit-identification seam. **OPEN.**

## Dumbassery checks

- The identity direction is excluded by the traceless fitted-generator space.
- Eigenvalue-preserving nulls preserve the exact candidate spectrum.
- Band-profile nulls preserve each matrix diagonal's value multiset.
- Absolute commutator values are reported; normalized decay is not called convergence.
- Gap-normalized quantities are reported; small commutator alone is not called eigenvector control.
- The recovered tridiagonal generator is not called prolate.
- The exact displacement theorem is finite-dimensional; rank <= 2 does not imply an infinite
  operator theorem.
- No numerical trend is promoted to an asymptotic theorem.
- This route is not RH evidence or proof.

## Reproduction

Numerical gauntlet:

```bash
pip install -r research/RHRC/routes/R004_prolate_v2/requirements.txt
python research/RHRC/routes/R004_prolate_v2/run_commutator_gauntlet_v2.py \
  --lambdas 2 3 5 7 10 \
  --Ns 5 8 12 20 \
  --nulls 10 \
  --seed 20260820 \
  --output r004_v2_result.json
```

Exact symbolic displacement reproduction:

```bash
python research/RHRC/routes/R004_prolate_v2/derive_exact_displacement.py
```


## Normalization repair after PR #71

The old `finiteMatrix` theorem remains mathematically valid but is now explicitly
classified as the historical literal printed-(4.14) normalization.  The direct
source authority is

```text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix
  = finiteMatrix + 2*cCorrection(L)*I.
```

Therefore the exact displacement law and its rank-at-most-two consequence are
now promoted on `canonicalSourceMatrix`.  The legacy theorem remains available
for history and because scalar identity shifts leave the commutator unchanged.

Absolute eigenvalues, positivity, lower bounds, trace, determinant, and inertia
are not scalar-shift invariant and must use the canonical source normalization.
No external `QW_lambda` restriction identification is claimed here.
