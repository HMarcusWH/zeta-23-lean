# G0-B localized finite-space settlement — 2026-08-31

Status: **PROVED / SETTLED FOR THE FINITE FUNCTION-CORRELATION LAYER.**

RH remains **OPEN**.

## Authority

The theorem-bearing source head validated by the full PR #69 compiler/CI gate is:

- proof-bearing head: `fd49db84fb7aa851ace695b953798b86b7fb3a30`
- base/main: `2907b03c4c291d12da684a5eaee062fd8907ed5b`
- exact synthetic merge tested at that checkpoint: `812125e3ebd94c50ad5148e78d7b53390bb8265b`

The later commits on PR #69 only bind/promote the already-validated theorem surface and add this settlement record; they do not change `Zeta23/CCM/LocalizedFiniteSpace.lean`.

The authoritative PR #69 validation completed:

- CCM formalization build: green;
- ExceptionalZero build: green;
- RHRC claim/regression suite: green;
- R003 normalization audit: green;
- external-oracle/dependency guards: green;
- forbidden-placeholder scan: green;
- Permansson verification workflow: green.

## What is now formally true

For every positive aperture `L`, every finite `N`, and every arbitrary complex coefficient vector

```lean
u : Fin (2 * N + 1) → ℂ
```

the repository now has an actual zero-extended finite function

```lean
localizedFiniteVector L N u : ℝ → ℂ
```

built from the centered Fourier indices

```text
-N, ..., 0, ..., N.
```

The source interval is exactly `[0,L]`.  Outside this interval the function is zero.

Lean proves:

- exact indicator representation by the formula-level finite Fourier combination;
- pointwise support containment in `[0,L]`;
- compact support;
- `MemLp ... 2 volume`;
- the inherited `EF.weilTest` positive- and negative-shift overlap formulas;
- evenness of the symmetrized localized correlation;
- actual basis correlation = the hard-window character correlation;
- actual basis correlation = `qBasis`;
- arbitrary-complex finite-vector correlation = the correct sesquilinear contraction of the actual basis correlations;
- direct vanishing beyond the aperture from support separation;
- the global production identity
  ```lean
  localizedWeilCorrelation
      (localizedFiniteVector L N u)
      (localizedFiniteVector L N u)
    =
    fun y => 2 * dictionaryTest N u L y
  ```
  under only `0 < L`;
- the zero-shift endpoint
  ```lean
  localizedWeilCorrelation
      (localizedFiniteVector L N u)
      (localizedFiniteVector L N u) 0
    =
    2 * coefficientMass N u.
  ```

## Exact convention firewall

The inherited repository convention is

```lean
EF.weilTest f g = f ⋆ tilde g
```

with the actual argument order used in `localizedWeilCorrelation` fixed by the theorem implementation.

The production dictionary is half-normalized relative to the full hard-window/source correlation:

```text
actual symmetrized localized correlation = 2 * dictionaryTest.
```

This factor is theorem-authoritative and must not be silently removed.

## No hidden coefficient restriction

The load-bearing theorem is valid for the full complex coefficient space.

It has **no** assumption of:

- real coefficients;
- even coefficients;
- coefficient-sum zero;
- positivity;
- form-core membership beyond the proved finite L2 statement;
- RH.

This matters because the conjugation/order in the finite sesquilinear contraction was checked by Lean rather than inferred from a real sector.

## Axiom surface

The load-bearing endpoints print exactly the standard expected surface:

```text
[propext, Classical.choice, Quot.sound]
```

including:

- `localizedWeilCorrelation_basis_eq_hardWindow`;
- `localizedWeilCorrelation_basis_eq_qBasis`;
- `localizedWeilCorrelation_finiteVector_eq_basis_sum`;
- `localizedWeilCorrelation_finiteVector_eq_two_mul_dictionaryTest`;
- `localizedWeilCorrelation_finiteVector_zero`.

No `sorryAx`.

No project-specific axiom.

## What G0-B does not prove

G0-B does **not** prove that `cutoffFreeMatrix` is the restriction of the external Connes–Consani–Moscovici localized Weil form `QW_lambda`.

In particular it does not yet formalize:

- the multiplicative `kappa` map;
- the source `PsiSharp` functional;
- the identity `QW(kappa f,kappa g)=PsiSharp(q(f,g))`;
- form-domain inclusion for the external source form;
- form-core density;
- Rayleigh–Ritz/bottom convergence;
- positivity;
- Suzuki's fixed-aperture implication;
- any RH conclusion.

The next PR must therefore preserve a source-identification firewall: composing the repository half-correlation with `EF.literatureRHS` is useful and expected to recover the finite matrix, but defining that composition does not by itself prove equality with the external source `QW_lambda`.

## Post-green implications

### Upstream

At zero shift, the theorem gives the exact coefficient-mass normalization.  This strongly suggests the finite Fourier energy/isometry statement can be packaged cheaply without a separate orthogonality development.  That packaging remains downstream unless separately proved.

### Downstream

The shortest next composition is now:

```text
actual finite function
  -> actual global correlation
  -> half correlation = dictionaryTest
  -> existing complex dictionary RHS identity
  -> dictionaryMatrix
  -> cutoffFreeMatrix.
```

This should be isolated as an additive source-functional theorem first.

Only after a separate source theorem identifies that additive functional with the actual CCM `QW_lambda` may the project promote a genuine localized Weil-form Galerkin restriction.

### Resurrected route

The detector-to-CCM approximation question now targets an actual function space rather than matrix coordinates.  It remains a lead, not part of the immediate execution spine.

## Claim firewall

**PROVED:** actual full-complex localized finite space and global inherited autocorrelation semantics.

**OPEN:** actual external localized Weil-form restriction.

**OPEN:** finite-to-infinite closure.

**OPEN:** RH.
