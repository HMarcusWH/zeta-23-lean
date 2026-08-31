# G1-A additive localized Weil restriction settlement — 2026-08-31

Status: **PROVED for the repository additive half-correlation RHS.**

External CCM `QW_lambda` source identification remains **OPEN (G1-B)**.

RH remains **OPEN**.

## Exact proof-bearing validation

Proof-bearing PR #70 head:

```text
e2c4b80f40f1d811e1cd8041ab920a0c433c8a08
```

Base/main:

```text
dce12c288c696c63bfe46559444a83032a27a954
```

Synthetic merge at the proof-bearing checkpoint:

```text
dbbd443dcecadd2bacf4aa439832e46dd524c711
```

The complete validation family passed:

- CCM formalization build;
- ExceptionalZero build;
- forbidden-placeholder scan;
- RHRC claim/regression suite;
- R003 normalization audit;
- external finite-dictionary/oracle guards;
- separate Permansson verification workflow.

All new printed endpoints use only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`.

No project-specific axiom.

## Source firewall that motivated this PR

Connes--Consani--Moscovici, *Zeta Spectral Triples* (arXiv:2511.22755), defines for zero-extended additive functions

```text
q(f,g)(y) = (f* * g)(y) + (f* * g)(-y)
```

and gives, for `lambda > 1` and `L = 2*log(lambda)`, the logarithmic-coordinate isometry

```text
kappa : L2([0,L],dx) -> L2([lambda^-1,lambda],d*u)
```

together with Proposition 3.2:

```text
QW(kappa(f),kappa(g)) = PsiSharp(F),
F(u) = q(f,g)(log u),
```

for smooth `f,g` on `[0,L]`.

The same source states the evenization identity

```text
Psi(h) = PsiSharp(h + h o inversion).
```

G0-B already proves that the repository's actual symmetrized localized correlation is the exact source-style even correlation on the finite Fourier space, with production normalization

```text
localizedWeilCorrelation(f_u,f_u) = 2 * dictionaryTest(N,u,L).
```

However, the repository does not yet contain a formal multiplicative `kappa` / `PsiSharp` / `QW_lambda` source object. Therefore this PR deliberately does not define its additive functional to be `QW_lambda`.

## What became formally true

This PR defines

```lean
localizedWeilHalfTest f g
```

as one half of the actual symmetrized localized correlation and

```lean
localizedWeilAdditiveRHS f g
```

as `EF.literatureRHS` applied to that half-correlation.

For every positive `L`, finite `N`, and arbitrary complex coefficient vector

```lean
u : Fin (2 * N + 1) -> C
```

Lean proves globally:

```lean
localizedWeilHalfTest
  (localizedFiniteVector L N u)
  (localizedFiniteVector L N u)
=
dictionaryTest N u L.
```

It then consumes the already-proved arbitrary-complex theorem

```lean
dictionaryRHS_dictionaryTest_eq_quadraticForm
```

and the independently defined source normalization

```lean
cutoffFreeMatrix_eq_dictionaryMatrix
```

to prove the G1-A endpoint:

```lean
localizedWeilAdditiveRHS
  (localizedFiniteVector L N u)
  (localizedFiniteVector L N u)
=
quadraticForm (cutoffFreeMatrix L N) u.
```

The source-facing wrapper additionally proves the exact parameter convention

```text
L = 2 * log(lambda),  lambda > 1.
```

## Remaining source-identification gate

The file defines

```lean
MatchesLocalizedWeilAdditiveRHSOnFiniteSpace Q
```

and proves:

```lean
finiteRestriction_eq_cutoffFreeQuadraticForm_of_matches
```

Thus any ambient pullback form `Q` that is subsequently theorem-identified with the repository additive RHS on the actual finite vectors automatically has finite restriction matrix `cutoffFreeMatrix`.

This is the intentional compression:

```text
all finite algebra / normalization
        CLOSED
             |
             v
one source-identification gate
QW_lambda pullback = localizedWeilAdditiveRHS
             |
             v
actual QW finite restriction = cutoffFreeMatrix
```

## What changed

Before #69, the project lacked actual full-complex finite functions.

After #69, it had those functions and their exact inherited correlation semantics, but not the finite Weil-functional matrix.

After this PR, the entire repository-side finite functional calculation is closed.  No new prime, pole, archimedean, zero-side, matrix-completion, or normalization analysis remains in G1.

The remaining G1 question is semantic/source-facing rather than finite-algebraic.

## Upstream implications

The factor-half normalization is now theorem-locked rather than inferred from source conventions:

```text
full actual q correlation = 2*dictionaryTest
=> half q = dictionaryTest
=> additive RHS = cutoffFree quadratic form.
```

No extra real-coefficient or coefficient-sum-zero condition appears.

## Downstream implications

The next PR should not build form-core or Rayleigh--Ritz machinery.

It should answer only:

> Is the pullback of the genuine external `QW_lambda` through the source `kappa` map equal to `localizedWeilAdditiveRHS` on the finite Fourier sector?

The source Proposition 3.2 is unusually well matched to the objects already present:

- `localizedFiniteFunction L N u` is a finite Fourier combination and is smooth;
- `localizedFiniteVector L N u` is exactly its zero extension to the additive real line;
- G0-B already computed the required even correlation `q`;
- the parameter lock `L=2*log(lambda)` is already present.

If that source identification closes, the actual external localized Weil-form finite restriction will be a short consequence of the theorem proved here.

## Resurrected routes

No dead route is reopened by G1-A itself.

The result does, however, strengthen the reason to revisit the published form-core theorem immediately after G1-B rather than constructing an independent G2/G3 theory.

## New RH-relevant clues

**LEAD:** G1 has compressed from a potentially large analytic/form-theoretic layer to one source-coordinate identity.

**LEAD:** once G1-B closes, the published claim that the Fourier span is a form core may replace much of the planned bespoke G2/G3 implementation.

Neither statement is RH evidence.

## Falsification checks

G1-B must fail closed if any of the following occurs:

1. the repository `EF.literatureRHS` normalization does not match the source full Weil functional `Psi`;
2. the half/evenization relation does not exactly produce `PsiSharp`;
3. the logarithmic coordinate direction or translation is mismatched;
4. the source uses a different Fourier normalization;
5. the finite source functions do not land in the stated smooth/source domain;
6. the `L=2*log(lambda)` map is inconsistent.

The purpose of the G1-A firewall is that none of these potential source mismatches can be hidden by redefining `QW_lambda`.

## Highest-leverage next move

Implement G1-B as a source-correspondence PR, not as a spectral PR.

Minimal target:

```text
source QW pullback on the actual finite Fourier functions
=
localizedWeilAdditiveRHS
```

then compose with

```lean
finiteRestriction_eq_cutoffFreeQuadraticForm_of_matches
```

to obtain the actual external QW finite restriction theorem.

Only after that promotion should the project consume the form-core / Rayleigh-bottom theorem.

## Claim firewall

**PROVED:** repository additive half-correlation RHS finite restriction = `cutoffFreeMatrix`.

**OPEN:** identification with external CCM `QW_lambda`.

**OPEN:** form-core/Rayleigh-bottom source port.

**OPEN:** Suzuki fixed-aperture finite obstruction.

**OPEN:** RH.
