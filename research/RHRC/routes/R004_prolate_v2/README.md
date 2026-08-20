# R004-v2 — commutator stress test and displacement-structure audit

Status: **DISCOVERY**. The commutator/null results remain finite numerical diagnostics. The index-displacement formula below is now an **exact symbolic identity for the implemented finite CCM entry formula**, but it is not a finite-to-infinite theorem and not RH evidence.

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

No source matrix formula is changed relative to R004-v1.

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

This is a substantially harsher locality control than a fully randomized eigenbasis.

## Exact index-displacement identity

Let

`D = diag(-N, ..., 0, ..., N)`.

For Fourier indices `n,m`, the implemented CCM matrix has

`M_nm = Pole_nm - Arch_nm - Prime_nm`.

Write

`kappa = 16*pi^2`,

`C_L = 32*L*sinh(L/4)^2`,

`d_n = L^2 + kappa*n^2`.

The pole entry is

`Pole_nm = C_L * (L^2 - kappa*m*n) / (d_m*d_n)`.

For `n != m`, direct algebra gives

`(n-m) Pole_nm = C_L * (n/d_n - m/d_m)`.

Indeed,

`n*d_m - m*d_n = (n-m)(L^2 - kappa*m*n)`.

The off-diagonal archimedean channel is

`Arch_nm = (alpha_m - alpha_n)/(n-m)`,

so

`(n-m)(-Arch_nm) = alpha_n - alpha_m`.

The prime channel is a weighted sum of divided differences. Define the scalar prime sequence

`prime_n = sum_k Lambda(k) k^(-1/2) sin(2*pi*n*log(k)/L) / pi`

over the same finite prime-power range used by the matrix construction. Then

`(n-m)(-Prime_nm) = prime_n - prime_m`.

Therefore, with

`g_n = C_L*n/d_n + alpha_n + prime_n`,

we obtain the exact entrywise identity

`(n-m) M_nm = g_n - g_m`.

On the diagonal both sides are zero. Hence for every entry,

`[D,M]_nm = g_n - g_m`,

or in matrix form

`[D,M] = g 1^T - 1 g^T`.

Consequently

`rank([D,M]) <= 2`

**exactly for the implemented finite CCM formula**.

The symbolic certificate `derive_exact_displacement.py` verifies the only nontrivial rational
algebra independently of the numerical matrix builder. This explains the `~1e-15` rank-two residual
seen in RUN 002: that residual was floating-point roundoff around an exact displacement structure.

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
`[D,M] = g 1^T - 1 g^T`. **ALGEBRAICALLY CLOSED FOR THE IMPLEMENTED FINITE FORMULA.**

`J1-D-formal` — bind the exact identity to a theorem-authoritative formal definition of the CCM
matrix (Lean or equivalent comparator-grade source), rather than the Python implementation alone.
**OPEN.**

`J1-J` — derive an analytically specified Jacobi/prolate generator from the displacement identity or
another exact CCM identity. The numerical minimizer by itself is not an identification theorem.
**OPEN.**

`J2` — prove an absolute commutator estimate for that explicit generator, not merely a residual
normalized by `||M||`. **OPEN.**

`J3` — prove a theorem-relevant simple/uniform spectral-gap estimate for the analytically specified
generator. **OPEN; current fitted-generator finite gaps are a warning signal.**

`J4` — only after J2+J3, derive eigenspace convergence by a self-adjoint perturbation theorem. **OPEN.**

`J5` — connect the limiting concentrated mode to the exact R001 / localized Weil observable.
**OPEN.**

`J6` — close the finite-to-infinite normalization and limit-identification seam. **OPEN.**

## Dumbassery checks

- The identity direction is excluded by the traceless fitted-generator space.
- Eigenvalue-preserving nulls preserve the exact candidate spectrum.
- Band-profile nulls preserve each matrix diagonal's value multiset.
- Absolute commutator values are reported; normalized decay is not called convergence.
- Gap-normalized quantities are reported; small commutator alone is not called eigenvector control.
- The recovered tridiagonal generator is not called prolate.
- The exact displacement identity is explicitly limited to the implemented finite CCM formula.
- No finite-to-infinite theorem follows from rank-two displacement alone.
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

Exact symbolic displacement derivation:

```bash
python research/RHRC/routes/R004_prolate_v2/derive_exact_displacement.py
```
