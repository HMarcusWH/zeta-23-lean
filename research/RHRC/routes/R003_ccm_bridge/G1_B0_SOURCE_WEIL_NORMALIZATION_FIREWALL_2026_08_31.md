# G1-B0 source Weil normalization firewall — 2026-08-31

Status: **PROVED FOR DIRECT EQUATION-(4.4) FINITE SOURCE MATRIX + NORMALIZATION FIREWALL.**

RH remains **OPEN**.

## Exact proof-bearing state

PR #71 proof-bearing head:

```text
d5ab979772a4a4b2e1b3904222f312c6f5f22729
```

Base/main:

```text
9d3304050caf6c6bef874373aa2d91a03c956064
```

Synthetic merge at that checkpoint:

```text
a62695c37ee3b9457fd931810fde76861b45eeee
```

The exact proof-bearing head passed:

- CCM formalization build;
- ExceptionalZero build;
- forbidden-placeholder scan;
- RHRC claim/regression suite;
- R003 normalization/oracle audit;
- Permansson verification.

Every promoted G1-B0 theorem prints exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`.  No project-specific axiom.

## Why G1-B0 changed during implementation

The initial implementation attempted to identify a direct equation-(4.4)
source matrix with `cutoffFreeMatrix`.

The source audit falsified that promotion path before it was registered.

The Connes--Consani--Moscovici paper gives:

- equation (4.4): the archimedean Weil contribution directly from
  `omega=q(U_n,U_m)`;
- `rho(x)=exp(x/2)/(exp(x)-exp(-x))`;
- equation (4.11): a rewrite from the `(cos-exp(-x/2))*rho` diagonal
  integrand to the `(cos-1)*rho` integrand plus a displayed correction
  `c(L)`;
- equation (4.14): a gamma definition using the equation-(4.11) left-hand
  integral plus another explicit `c(L)+w(L)`.

Taken literally, the correction forced by subtracting the two rho-weighted
integrands is not the displayed `c(L)` integrand.  It contains an additional
factor `exp(x/2)`.

The PR was therefore rewritten to fail closed.

## What became formally true

The printed equation-(4.11) RHS cos-minus-one integrand is named

```lean
sourceEq411RhsCosMinusOneIntegrand
```

and the equation-(4.11) left-hand integrand is named

```lean
sourceEq411LhsIntegrand.
```

Lean proves the exact pointwise decomposition

```lean
sourceEq411LhsIntegrand n L x
  =
sourceEq44CosMinusOneIntegrand n L x
  + sourceEq411DerivedCorrectionIntegrand x.
```

The decisive firewall theorem is

```lean
sourceEq411DerivedCorrectionIntegrand x
  =
Real.exp (x / 2) * cCorrectionIntegrand x.
```

Thus the rho-weighted algebra itself exposes the extra factor.

The equation-(4.11)-left-hand primitive, before adding the printed correction
again, is theorem-identified with the independent cutoff-free convention:

```lean
sourceEq411LhsGammaL n L = cutoffFreeGammaL n L.
```

The historical printed-(4.14) repository primitive satisfies

```lean
gammaL n L
  =
sourceEq411LhsGammaL n L + cCorrection L.
```

This then lifts entrywise:

```lean
sourceEq411LhsArchComponent = cutoffFreeArchComponent
sourceEq411LhsEntry         = cutoffFreeEntry
sourceEq411LhsMatrix        = cutoffFreeMatrix.
```

## What remains deliberately open

The direct equation-(4.4) objects are named:

```lean
sourceEq44GammaL
sourceEq44ArchComponent
sourceEq44Entry
sourceEq44Matrix.
```

After correcting the post-green source transcription, Lean now proves:

```lean
sourceEq44GammaL = cutoffFreeGammaL
sourceEq44ArchComponent = cutoffFreeArchComponent
sourceEq44Entry = cutoffFreeEntry
sourceEq44Matrix = cutoffFreeMatrix.
```

Thus the direct primary Section-4 finite formula is now theorem-locked to the production cutoff-free matrix.

The printed equation-(4.11) integrated correction is represented by the
unproved proposition

```lean
SourceEq411CorrectionIdentity.
```

No theorem proves this proposition.

Therefore G1-B0 identifies the direct Section-4 finite source formula with `cutoffFreeMatrix`, but it still does not formalize the ambient external `QW_lambda` / `kappa` / `PsiSharp` correspondence.

## Executable-source evidence

The pinned external cutoff-free implementation uses a combined `c_w()`
closed-form term in its `gamma_L`.

Independent oracle checking shows that this executable convention tracks the
correction forced by the rho-weighted algebra, not the displayed correction
integrand taken literally.

This is **EXPERIMENTAL/SOURCE SIGNAL**, not Lean theorem authority.

## What changed

Before G1-B0, the remaining G1 problem was described as primarily a
`kappa/PsiSharp` source-map port.

After the corrected post-green pass, the intended direct Section-4 finite matrix is no longer ambiguous: equation (4.4) lands on `cutoffFreeMatrix`. The printed equation-(4.11)/(4.14) simplification remains internally inconsistent but is no longer load-bearing. The remaining source provenance obligation is the ambient `kappa/PsiSharp/QW_lambda` correspondence.

## Upstream implications

The historical `cCorrection` object should now be treated as the literal
printed correction convention, not automatically as the correction algebraically
forced by `rho`.

The theorem-authoritative `cutoffFreeMatrix` remains internally valid and
independently source-audited, but its final semantic label as the actual
`QW_lambda|E_N` matrix is still open.

## Downstream implications

Do not start form-core, Rayleigh--Ritz, Suzuki, or finite-negative persistence until the ambient `QW_lambda` pullback is theorem-identified with the already-settled direct finite source formula. The suspect printed (4.11)/(4.14) rewrite should remain documented and non-load-bearing.

## Resurrected routes

No dead RH route is resurrected by this result.

The result does resurrect **source archaeology as a load-bearing task**,
which had previously been considered largely closed after PR #65.

## New RH-relevant clues

**LEAD:** the pinned executable appears to use the rho-derived correction and
may encode the intended correction of the manuscript formulas.

**LEAD:** if the source seam resolves in favor of the equation-(4.11)-left-hand
convention, `cutoffFreeMatrix` remains the natural finite source object and
the fixed-aperture route can resume with only a thin source correspondence.

These are not RH results.

## Falsification checks

Fastest checks:

- inspect the actual TeX/source around equations (4.11) and (4.14);
- derive the diagonal of equation (4.4) independently from Lemma 2.3;
- compare that derivation against the pinned executable closed form;
- test the two correction integrals numerically over several apertures;
- do not infer equality merely because both conventions give numerically
  similar matrices.

## Highest-leverage next move

G1-B1 should now be the **kappa/PsiSharp/QW source-correspondence PR**. The direct finite Section-4 matrix is already settled. The next target is to theorem-lock `QW(kappa f,kappa g)=PsiSharp(q(f,g))` with `L=2*log(lambda)`, specialized first to the existing finite Fourier sector.

## Claim firewall

**PROVED:** direct equation-(4.4) finite source matrix = `cutoffFreeMatrix`.

**PROVED:** exact printed equation-(4.11) normalization firewall and equation-(4.11)-left-hand convention = `cutoffFreeMatrix`.

**OPEN:** printed equation-(4.11) integrated correction identity.

**OPEN:** ambient external `QW_lambda` / `kappa` / `PsiSharp` finite restriction correspondence.

**OPEN:** form-core/Rayleigh-bottom port.

**OPEN:** Suzuki finite-aperture obstruction.

**OPEN:** RH.
