# D0-B Bombieri / CCM finite-object audit — 2026-08-30

Status: **SETTLED — DISTINCT FINITE TRUNCATIONS / NO DIRECT CCM MAP ESTABLISHED**

Claim class: **route classification**, not a new Lean theorem.

RH status: **OPEN**.

## Question

Does Bombieri's finite truncation in *Remarks on Weil's quadratic functional in the theory of prime numbers, I* coincide with, or give an immediate equality/congruence/compression map to, the theorem-authoritative finite CCM matrix

```text
zeroSideMatrix
  = cutoffFreeMatrix
  = finiteMatrix + 2*cCorrection(L)*I
```

on the centered deterministic basis `-N,...,N`?

## Answer

**No direct finite-object map is present in Bombieri's construction.**

The two finite truncations are indexed in fundamentally different ways:

```text
Bombieri:
  Gamma_N = {gamma from rho=1/2+i*gamma : |gamma| <= N}
  matrix  = H(Gamma_N;t)
  size    = #Gamma_N, with zero multiplicities
  indices = zeta-zero parameters gamma

CCM:
  indices = -N,...,N
  matrix  = cutoffFreeMatrix(L,N)
  size    = 2*N+1
  indices = deterministic Fourier-character modes
```

Bombieri's `N` is a **height cutoff in zero space**. CCM's `N` is a **Fourier-mode cutoff in a deterministic finite test-function dictionary**. The shared letter `N` must not be treated as a parameter map.

## Source evidence

The primary source lock is `research/RHRC/external/bombieri/SOURCE_MAP.md`.

The load-bearing source facts are:

1. §7 writes `rho = 1/2 + i*gamma`, introduces `Gamma`, defines `H(x,y;t)` in (7.3), and writes the eigenvalue problem over `gamma in Gamma` in (7.4).
2. The matrix is explicitly `H(Gamma;t)`.
3. Theorem 6 defines finite truncations by `Gamma_N = {gamma in Gamma : |gamma| <= N}`.
4. §8 obtains the finite approximation by taking a finite multiset of the `rho/gamma` points.
5. Theorem 8 counts negative eigenvalues of that zero-indexed finite matrix.
6. §10 passes to the limit through the height truncations `Gamma_N`.

That settles B0: Bombieri is **not truncating the same coordinate family** as the centered CCM construction.

## Why an entrywise comparator would be fake work

A numerical `compare_bombieri_ccm.py` was considered and deliberately not created.

There is no canonical same-size matrix pair to compare:

- `dim H(Gamma_N;t) = #Gamma_N`;
- `dim cutoffFreeMatrix(L,M) = 2*M+1`.

Choosing `M` only so dimensions happen to agree would manufacture a comparison rather than derive one. Sorting zero ordinates and matching them to centered integer modes would likewise invent the coordinate map.

The correct falsifier was therefore the source-level index/truncation audit.

## Why no Lean bridge is created

A `Zeta23/CCM/BombieriBridge.lean` module would only be justified after a mathematically defined map between the zero-coordinate finite space indexed by `Gamma_N` and the deterministic CCM Fourier-coordinate space indexed by `Fin(2*M+1)`.

Bombieri's paper does not supply such a map, and D0-B did not derive one.

Creating an existential change-of-basis matrix after forcing equal dimensions would be vacuous and would not identify the underlying finite objects.

Therefore:

```text
NO BombieriBridge.lean
NO ClaimBindings promotion
NO CLAIM_REGISTRY theorem claim
NO RHRC numerical comparator
```

## Spectral-transfer firewall

Bombieri's finite negative-inertia theorem remains mathematically interesting, but it applies to `H(Gamma;t)`. It is **not** a theorem about the project's canonical finite CCM matrix.

D0-B does not establish any of:

```text
inertia(H(Gamma_N;t)) = inertia(cutoffFreeMatrix(L,M))
lambda_min(H(Gamma_N;t)) = lambda_min(cutoffFreeMatrix(L,M))
H(Gamma_N;t) = C^* cutoffFreeMatrix(L,M) C
H(Gamma_N;t) = C^T cutoffFreeMatrix(L,M) C
H(Gamma_N;t) = compression(cutoffFreeMatrix(L,M))
```

The distinction between transpose congruence and Hermitian `conjTranspose` congruence remains object-dependent; #66's R002 `ExactResponseMap` theorem is not imported or reused here.

## What Bombieri still contributes

### DERIVED historical/structural lesson

Bombieri supplies a second finite-to-infinite program for Weil's quadratic functional:

```text
zero-indexed finite matrices
  -> exact finite inertia
  -> control of limiting negative eigenvalues / limiting relations.
```

The project CCM route currently has:

```text
deterministic finite test-function dictionary
  -> exact zeta zero-side matrix
  -> OPEN localized-form restriction
  -> OPEN form-core / Rayleigh-Ritz closure.
```

These are complementary, not identical.

### LEAD

A future connection would have to be an **operator-level duality** between truncation in spectral/zero coordinates and Galerkin restriction in deterministic test-function coordinates. That is a G0/G1-or-later question, not D0-B.

## D0-B classification

```text
CLASSIFICATION: DISTINCT_TRUNCATIONS
DIRECT_EQUALITY: NOT ESTABLISHED
CONGRUENCE: NOT ESTABLISHED
COMPRESSION: NOT ESTABLISHED
PARAMETER_MAP: NOT REQUIRED / NOT ESTABLISHED
INERTIA_TRANSFER_TO_CCM: NOT AUTHORIZED
```

This is not an impossibility theorem saying no relation can ever exist. It closes the roadmap ambiguity: Bombieri's published finite truncation is not the same finite object as the project's CCM centered band.

## Downstream decision

B1 — direct Bombieri inertia transfer to CCM — is **not opened**.

The next CCM critical-path task is:

```text
G0/G1 — localized Weil restriction
```

Define the actual ambient localized quadratic form and named finite test-function subspace, then prove or falsify that the theorem-authoritative `cutoffFreeMatrix` is its exact matrix in the centered basis.

Only after such an operator/restriction theorem exists should Bombieri be revisited for a possible dual/operator-level comparison.

## Claim firewall

D0-B proves no new RH-facing theorem. Localized Weil-form restriction, form-domain membership, form-core density, Rayleigh-Ritz convergence, finite negative persistence, positivity, and RH remain **OPEN**.
