# R004 — hidden Jacobi / prolate commutator route

Status: **DISCOVERY / FINITE NUMERICAL DIAGNOSTIC ONLY**.

## Motivation

Connes' 2026 RH survey reports that the finite-prime minimizer of the localized Weil quadratic form is numerically well approximated in a prolate-spheroidal basis, and identifies prolate/Slepian structure as a central bridge in the proposed finite-to-infinite convergence strategy. A 2026 matched-generator theorem (M. A. Thornton, arXiv:2607.08788) gives a general variational mechanism for recovering a hidden commuting tridiagonal/Jacobi generator by minimizing a double-commutator residual.

This route asks a narrower falsifiable question before making any prolate identification:

> Does the finite CCM/Weil matrix possess an anomalously good traceless tridiagonal approximate commutant, compared with matrices having exactly the same eigenvalues but randomized eigenvectors?

## Finite object

The source matrix is the locked Route-A CCM construction

`M_{lambda,N} = W_{0,2} - W_R - sum_p W_p`,

with prime powers included through the von Mangoldt weight and cutoff `1 < k <= lambda^2`.

Source notebook SHA-256:

`aa6004b432f8baa3c9dc5c919b0f8df78621a84747f45bfda9fffc79a1d2e24d`

## Generator search

Let `B` be the finite-dimensional space of real symmetric traceless tridiagonal matrices. We solve

`min_A ||[M,A]||_F / (||M||_F ||A||_F)`, `A in B`, `A != 0`.

This is the generalized Rayleigh problem for the Gram matrix of the commutators. The identity direction is explicitly removed so the trivial exact commutant cannot win.

### Adversarial null

For each finite CCM matrix `M`, construct random orthogonal conjugates

`M_null = Q diag(eig(M)) Q^T`.

These nulls preserve the **exact eigenvalue multiset** of the CCM matrix and destroy only its basis/eigenvector structure. The same tridiagonal-generator search is then rerun.

## RUN 001 finite result

Grid:

- `lambda in {2,3,5,7,10}`
- `N in {5,8,12,20}`
- 30 eigenvalue-preserving randomized-basis nulls per case
- seed `20260820`

Result:

- every tested CCM candidate residual was below the best tested randomized-basis null;
- median candidate/null-median residual ratio: about `8.16e-3`;
- worst candidate/null-median residual ratio: about `3.23e-2`.

Selected examples:

- `lambda=5, N=20`: candidate about `2.76e-4`, null median about `1.14e-1`;
- `lambda=10, N=20`: candidate about `1.39e-4`, null median about `6.20e-2` (exact value is in the receipt).

This says the tested finite CCM matrices contain strong **Jacobi-commutant structure** that is not explained by their spectrum alone.

It does **not** yet identify the recovered generator with the prolate operator.

## Proof-search ladder

`J0` — finite diagnostic: anomalously small tridiagonal commutator residual. **NUMERICAL PASS**.

`J1` — derive the recovered Jacobi coefficients analytically from the CCM/Weil entries, or identify a closed-form candidate `J_{lambda,N}`. **OPEN**.

`J2` — prove a quantitative commutator bound

`||[M_{lambda,N},J_{lambda,N}]|| <= epsilon_{lambda,N}`

with an explicit regime `epsilon_{lambda,N} -> 0`. **OPEN**.

`J3` — prove a uniform/simple spectral-gap estimate for the relevant Jacobi/prolate eigenvalue(s). **OPEN**.

`J4` — convert J2+J3 into eigenvector/eigenspace convergence by a self-adjoint perturbation argument. **OPEN**.

`J5` — identify the limiting Jacobi/prolate eigenvector with the minimizer of the localized Weil form strongly enough to control its lowest eigenvalue / regularized determinant. **OPEN**.

`J6` — close the CCM finite-to-infinite convergence/normalization/limit-identification seam. **OPEN**.

Only after those steps may a theorem-level implication toward RH be considered.

## Dumbassery checks

- A small commutator caused by the identity matrix is forbidden by using the traceless generator space.
- Nulls preserve the exact CCM eigenvalues, so the finite signal cannot be attributed merely to spectral clustering.
- No statement that the generator is 'prolate' is made from visual coefficient shape.
- No numerical commutator trend is promoted to an asymptotic theorem.
- No eigenvalue or determinant result is promoted to RH evidence.

## Reproduction

```bash
pip install -r research/RHRC/routes/R004_prolate_commutator/requirements.txt
python research/RHRC/routes/R004_prolate_commutator/run_commutator_gauntlet.py \
  --lambdas 2 3 5 7 10 \
  --Ns 5 8 12 20 \
  --nulls 30 \
  --seed 20260820 \
  --output r004_result.json
```
