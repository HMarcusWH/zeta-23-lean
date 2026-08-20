# R004-v2 — commutator stress test and displacement-structure audit

Status: **DISCOVERY / FINITE NUMERICAL DIAGNOSTIC ONLY**.

## Purpose

R004-v1 found that finite CCM/Weil matrices admit a real symmetric traceless tridiagonal matrix `J`
with an anomalously small normalized commutator relative to eigenvalue-preserving random-basis nulls.
That was a useful signal, but it left two dangerous alternative explanations open:

1. the normalization `||[M,J]||_F / (||M||_F ||J||_F)` might improve only because `||M||_F` grows;
2. a small commutator is not perturbatively useful if the recovered `J` has collapsing spectral gaps.

R004-v2 therefore reports absolute and gap-normalized metrics, adds a locality-preserving null, and
audits the exact index-displacement structure of the CCM matrix.

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

## Displacement audit

Let

`D = diag(-N, ..., 0, ..., N)`.

R004-v2 computes the singular values of

`[D,M] = D M - M D`

and reports the Frobenius residual after the best rank-two approximation.

This is motivated by the divided-difference form of the CCM entries: an exact rank-two displacement
identity would be theorem-relevant algebra, unlike visual resemblance of recovered Jacobi coefficients.

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

The rank-two displacement diagnostic is much more rigid: across every tested case, `[D,M]` is
numerically rank two to floating-point precision. This elevates the exact displacement identity to
the primary analytic target.

## Revised proof-search ladder

`J0` — anomalous finite tridiagonal commutant relative to eigenvalue and band-profile nulls.
**NUMERICAL PASS.**

`J1-D` — derive the exact displacement identity for `[D,M_{lambda,N}]` from the CCM entry formula,
including the explicit two generating vectors. **PRIMARY OPEN TARGET.**

`J1-J` — derive an analytically specified Jacobi/prolate generator from `J1-D` or another exact CCM
identity. The numerical minimizer by itself is not an identification theorem. **OPEN.**

`J2` — prove an absolute commutator estimate for that explicit generator, not merely a residual
normalized by `||M||`. **OPEN.**

`J3` — prove a theorem-relevant simple/uniform spectral-gap estimate for the analytically specified
generator. **OPEN; current fitted-generator finite gaps are a warning signal.**

`J4` — only after J2+J3, derive eigenspace convergence by a self-adjoint perturbation theorem. **OPEN.**

`J5` — connect the limiting concentrated mode to the frozen R001 translated pole-killing prime
statistic / localized Weil minimizer. **OPEN.**

`J6` — close the finite-to-infinite normalization and limit-identification seam. **OPEN.**

## Dumbassery checks

- The identity direction is excluded by the traceless generator space.
- Eigenvalue-preserving nulls preserve the exact candidate spectrum.
- Band-profile nulls preserve each matrix diagonal's value multiset.
- Absolute commutator values are reported; normalized decay is not called convergence.
- Gap-normalized quantities are reported; small commutator alone is not called eigenvector control.
- The recovered tridiagonal generator is not called prolate.
- Rank-two displacement is a finite numerical observation here until derived symbolically.
- No numerical trend is promoted to an asymptotic theorem.
- This run is not RH evidence or proof.

## Reproduction

```bash
pip install -r research/RHRC/routes/R004_prolate_v2/requirements.txt
python research/RHRC/routes/R004_prolate_v2/run_commutator_gauntlet_v2.py \
  --lambdas 2 3 5 7 10 \
  --Ns 5 8 12 20 \
  --nulls 10 \
  --seed 20260820 \
  --output r004_v2_result.json
```
