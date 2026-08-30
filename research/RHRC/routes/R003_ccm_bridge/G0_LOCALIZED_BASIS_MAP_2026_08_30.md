# G0-A localized Fourier basis map — 2026-08-30

Status: **REACHED — COMPILER-VALIDATED G0-A BASIS/CORRELATION MAP**

RH status: **OPEN**.

## Objective

Install the concrete finite Hilbert-space geometry underneath the theorem-authoritative CCM kernel before attaching the localized Weil quadratic form.

The pinned external Connes/CvS source describes a Galerkin band on Fourier modes indexed by `-N,...,N` and gives the exact hard-window character correlation formulas used by the finite matrix. The repository already has the closed formula as `qBasis`; this PR formalizes the normalized hard-window correlation integral and proves that it is exactly `qBasis`.

## Production objects added

`Zeta23/CCM/LocalizedBasis.lean` introduces:

- `localizedMode L n x`: normalized Fourier character `L^(-1/2) exp(2π i n x/L)`;
- `localizedFiniteFunction L N u x`: the finite centered character combination using the existing `centeredIndex` map;
- `hardWindowCharacterCorrelation n m y L`: the real symmetrized normalized overlap integral over the surviving interval `[0,L-y]`;
- `integral_cos_affine`: a neutral affine-cosine interval integral helper;
- `hardWindowCharacterCorrelation_eq_qBasis`: exact diagonal/off-diagonal identification for `0 <= y <= L` and `L>0`;
- centered-index wrapper for `Fin(2N+1)` coordinates;
- `two_mul_dictionaryBasisTest_eq_kernel`: explicit factor-two firewall between the full hard-window kernel and the production half-normalized dictionary entry test.

## Exact target

For positive `L` and `0 <= y <= L`:

```text
hardWindowCharacterCorrelation n m y L
  = qBasis n m y L.
```

The diagonal branch is

```text
2*(1-y/L)*cos(2*pi*n*y/L),
```

and the off-diagonal branch is

```text
(sin(2*pi*n*y/L)-sin(2*pi*m*y/L)) / (pi*(m-n)).
```

These are exactly the pre-existing production formulas in `Zeta23/CCM/Kernel.lean`.

## Why this is G0, not G1

This PR identifies the finite character geometry only. It does not define the localized Weil form, a Friedrichs operator, a form domain, or a finite-to-infinite theorem.

The next G1 theorem must attach the actual localized Weil functional to this basis and prove that the resulting matrix is `cutoffFreeMatrix` / `zeroSideMatrix` under the exact production normalization.

## Normalization firewall

The existing production basis test is

```text
dictionaryBasisTest n m L = (1/2) * kernel n m L.
```

Accordingly this PR theorem-locks

```text
2 * dictionaryBasisTest n m L y = kernel n m L y.
```

G1 must not silently identify `dictionaryBasisTest` with the full character correlation.

## Green checkpoint

The repaired theorem checkpoint compiled on the exact PR tree. The promoted endpoints report only `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or project axiom remains. The full CCM build, ExceptionalZero build, RHRC regression suite, R003 normalization audit and Permansson verification all passed before claim promotion.

The proof revealed that the interval identity is algebraic in the shift; the `0 <= y <= L` assumptions are retained in the public theorem because they are the physical hard-window overlap regime used by G0/G1.

## Claim firewall

This PR does not establish:

- localized Weil-form restriction;
- positivity;
- form-core density;
- Rayleigh-Ritz convergence;
- finite negative persistence;
- RH.

RH remains **OPEN**.
