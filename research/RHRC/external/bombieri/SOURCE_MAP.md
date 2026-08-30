# Bombieri finite-truncation source map

Status: **D0-B source extraction / external literature authority only**.

This file records the exact literature object used by the D0-B Bombieri/CCM representation audit. Nothing in this directory is a Lean dependency.

## Primary source

Enrico Bombieri, **Remarks on Weil's quadratic functional in the theory of prime numbers, I**, *Rendiconti Lincei. Matematica e Applicazioni*, Serie 9, vol. 11 (2000), no. 3, pp. 183-233.

Stable records:

- Bibliographic record: https://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0
- PDF endpoint: https://www.bdim.eu/item?fmt=pdf&id=RLIN_2000_9_11_3_183_0
- EuDML record: https://eudml.org/doc/252338
- MR1841692; Zbl 1008.11034.

The exact PDF checksum is **not pinned in this PR** because the repository does not vendor the external PDF. Equation/page references below are therefore the source lock.

## Supplementary source

Enrico Bombieri, **A variational approach to the explicit formula**, *Communications on Pure and Applied Mathematics* 56 (2003), 1151-1164.

- DOI: https://doi.org/10.1002/cpa.10089
- Wiley record: https://onlinelibrary.wiley.com/doi/10.1002/cpa.10089

This follow-up is background for the variational viewpoint. The D0-B finite-object classification below is determined from the 2000 memoir.

## Source conventions relevant to D0-B

### Ambient support parameter

Bombieri works with functions supported on a fixed multiplicative interval `[M^{-1},M]`, then writes `M = exp(t)` with `t > 0`; see §6-§7 and the change of variables before equations (7.1)-(7.4).

Thus Bombieri's aperture variable in the finite spectral problem is `t`. D0-B does **not** identify `t` with the CCM aperture `L`; no such map is needed for the object-mismatch classification.

### Spectral index set

Bombieri writes each relevant point as `rho = 1/2 + i*gamma` and denotes by `Gamma` the corresponding multiset of `gamma` values, including multiplicities and zeta symmetries; see §7-§8.

### Infinite matrix / eigenvalue problem

After the change of variables, Bombieri defines a kernel `H(x,y;t)` in (7.3), then rewrites the dual eigenvalue problem in (7.4) as

```text
w_gamma = Lambda * sum_{gamma' in Gamma} H(gamma,gamma';t) w_{gamma'}.
```

The corresponding infinite matrix is `H(Gamma;t) = (H(gamma,gamma';t))_{gamma,gamma' in Gamma}` and the resolvent determinant is `D(Lambda;t) = det(I - Lambda H(Gamma;t))`; see (7.5).

**Key D0-B fact:** Bombieri's matrix coordinates are indexed by zero parameters `gamma`, not by a deterministic Fourier-mode index `n=-N,...,N`.

### Finite truncation

Bombieri truncates the zero-index multiset by

```text
Gamma_N = { gamma in Gamma : |gamma| <= N }.
```

The finite determinant is the matrix `delta_{gamma,gamma'} - Lambda H(gamma,gamma';t)` restricted to `gamma,gamma' in Gamma_N`; see Theorem 6 / equations around (7.5)-(7.9), and §10.

Consequences:

- dimension is `#Gamma_N`, including multiplicity;
- dimension depends on the zero multiset below height `N`;
- coordinate labels are the actual `gamma` values;
- entries are `H(gamma,gamma';t)`.

This is not the project CCM truncation `Fin(2*N+1) <-> -N,...,N`, whose size is deterministic and whose coordinates are Fourier-character indices.

### Finite-set theorem

Section 8 studies a finite multiset of points with the zeta symmetries. Theorem 8 states that for the finite matrix `H(Gamma;t)`, the number of negative eigenvalues equals the number of distinct complex-conjugate pairs in `Gamma` (with multiplicity handled in the preceding lemma).

### Passage to zeta truncations

Section 10 again defines `Gamma_N` by `|gamma| <= N`. If the multiset has finitely many but at least one complex pair and `N` contains all complex pairs, Bombieri obtains a negative eigenvalue for `H(Gamma_N;t)` and studies the limiting eigenvectors.

Theorem 10 assumes zeta has only finitely many non-trivial zeros `1/2+i*gamma` with `gamma` non-real, and at least one such zero. Section 11 gives the analogous second eigenvalue problem; Theorem 11 carries the same finite-off-line-zero hypothesis.

## D0-B extraction table

| Question | Bombieri 2000 answer | Source |
|---|---|---|
| Ambient support | multiplicative `[M^-1,M]`, `M=e^t` | §6-§7 |
| Finite coordinates | zero parameters `gamma` from `rho=1/2+i gamma` | §7-§8 |
| Infinite matrix | `H(Gamma;t)` | (7.3)-(7.5) |
| Finite truncation | `Gamma_N={gamma: |gamma|<=N}` | Theorem 6, §10 |
| Finite dimension | `#Gamma_N`, multiplicity included | §7 |
| Deterministic Fourier band? | **No** | index definition |
| Parity split | separate even/odd second eigenvalue problem | §9 |
| Negative-inertia theorem | Theorem 8 for finite `Gamma`; limiting zeta results §§10-11 | §§8-11 |
| Zeta limiting hypothesis | finitely many off-critical non-trivial zeros, at least one | Theorems 10-11 |

## Claim firewall

The source does **not** provide an equality, change of basis, parity compression, parameter identity `t=L`, or inertia-transfer theorem from `H(Gamma_N;t)` to `Zeta23.CCM.cutoffFreeMatrix`. Those would require additional mathematics and are not promoted here.
