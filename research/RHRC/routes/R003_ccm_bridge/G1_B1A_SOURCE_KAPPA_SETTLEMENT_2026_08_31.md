# G1-B1A finite source kappa settlement — 2026-08-31

Status: **IN PR #72; proof-bearing status depends on the current post-#73 CI head.**

RH remains **OPEN**.

## Source statements being ported

Primary source: Connes--Consani--Moscovici, *Zeta Spectral Triples*,
arXiv:2511.22755v1.

For `lambda > 1`, Proposition 3.2(i) sets

```text
L = 2*log(lambda)
kappa(f)(u) = f(log(lambda*u))
```

and states that this is the coordinate isometry from the additive interval
`[0,L]` to the multiplicative interval `[lambda^-1,lambda]`.

Equation (3.21) defines

```text
V_n(u) = U_n(log(lambda*u)) = kappa(U_n)(u).
```

Section 5.1 then defines the finite space `E_N` as the span of the
`V_n`, `|n| <= N`; the test-function convention used by the paper extends
these interval functions by zero outside `[lambda^-1,lambda]`.

## What PR #72 is intended to prove

The PR theorem-locks the finite coordinate/function part of that source map:

- `sourceLength lam = 2*log(lam)` and positivity for `lam > 1`;
- `sourceLogCoordinate lam u = log(lam*u)`;
- the endpoint and interval map
  `[lam^-1,lam] -> [0,sourceLength lam]`;
- the explicit reverse coordinate
  `sourceExpCoordinate lam x = lam^-1*exp(x)`;
- the two coordinate inverse identities and reverse interval map;
- smoothness of the repository formula-level finite Fourier functions;
- the equation-(3.21) convention `V_n = kappa(U_n)`;
- arbitrary-complex centered finite-coefficient transport;
- the distinction between formula-level source functions and the actual
  zero-extended source finite vectors;
- support/compact-support certificates for the latter;
- the production identity
  `sourceKappaFiniteVector = sourceFiniteVector` on the full complex
  centered finite sector.

## Important correction to the original draft

The original draft described `sourceMultiplicativeMode` as independent of
`kappa` while proving the basis equality by `rfl`.

That prose was too strong.  The source itself defines `V_n=kappa(U_n)` in
equation (3.21), so the definitional equality is faithful to the source rather
than an independent convention check.

The actual semantic hole was different: the draft's
`IsSourceFiniteFourierVector` classified a global formula on all real
arguments, while the paper's source space lives on the positive multiplicative
interval and its test functions are localized/zero-extended.  PR #72 now
separates these objects explicitly.

## Post-#73 normalization firewall

No source finite-matrix label in this PR may identify the historical printed
`finiteMatrix` as canonical.

The current source convention is

```text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.
```

PR #72 does not need the legacy printed equation-(4.11)/(4.14) normalization.

## What remains open after G1-B1A

This PR does **not** theorem-lock the multiplicative-Haar measure `d*u` or
the bundled L2 isometry part of Proposition 3.2(i).  That interface may be
ported at the beginning of G1-B1B if required by the formal statement of the
external form.

Most importantly, this PR does not prove Proposition 3.2(ii):

```text
QW(kappa f,kappa g) = PsiSharp(F),
F(u) = q(f,g)(log u).
```

Therefore it does not prove

```text
QW_lambda restricted to E_N = canonicalSourceMatrix.
```

Form-core/Rayleigh-bottom convergence, Suzuki, positivity, finite-negative
persistence, and RH remain open.

## Dependency order

```text
#73 canonical source normalization
  -> #72 G1-B1A finite kappa/source-sector map
  -> G1-B1B d*u / QW / PsiSharp source correspondence
  -> actual QW_lambda|E_N = canonicalSourceMatrix
  -> T22
  -> G2/G3
  -> Suzuki fixed aperture
```

## Claim firewall

**PROVED only after current-head CI is green:** finite coordinate/source-sector
transport represented by the exact Lean declarations in `SourceKappa.lean`.

**OPEN:** multiplicative-Haar L2 isometry unless separately theorem-locked.

**OPEN:** `QW/PsiSharp` source identity.

**OPEN:** actual `QW_lambda|E_N` matrix identification.

**OPEN:** form-core/Rayleigh-bottom convergence.

**OPEN:** Suzuki fixed-aperture obstruction.

**OPEN:** RH.
