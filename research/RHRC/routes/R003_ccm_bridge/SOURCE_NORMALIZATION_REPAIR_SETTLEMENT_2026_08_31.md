# CCM source-normalization repair settlement — 2026-08-31

## Status

**STOP-THE-LINE REPAIR.**

PR #71 established that the direct Section-4 equation-(4.4) finite source
formula agrees with the independently audited `cutoffFreeMatrix`.  The later
printed equation-(4.11)/(4.14) normalization chain does not agree with that
direct formula if read literally.

This repair preserves every historical definition and theorem while changing
which object is allowed to carry the canonical source label.

## Primary-source seam

The source defines

```text
rho(x) = exp(x/2) / (exp(x)-exp(-x)).
```

Equation (4.11) prints

```text
∫ (cos-exp(-x/2))*rho
  = ∫ (cos-1)*rho + c(L)
```

with printed correction integrand

```text
(1-exp(-x/2)) / (exp(x)-exp(-x)).
```

Subtracting the two rho-weighted cosine integrands instead forces

```text
(1-exp(-x/2))*rho(x)
  = exp(x/2) * cCorrectionIntegrand(x).
```

PR #71 theorem-locks that pointwise factor.  This repair adds the integrated
corrected rewrite using `sourceEq411DerivedCorrection`.

Equation (4.14) then prints the left-hand `(cos-exp(-x/2))*rho` integral with
an additional `+c(L)`.  The direct equation-(4.4) diagonal primitive instead
uses that left-hand integral plus `w(L)`, with no re-addition of the printed
correction.

## Frozen historical objects

The following definitions are intentionally unchanged:

```text
cCorrectionIntegrand
cCorrection
gammaL
entry
finiteMatrix
```

Semantic aliases expose their role:

```text
legacyPrintedCorrectionIntegrand
legacyPrintedCorrection
legacyPrintedGammaL
legacyPrintedMatrix
```

No old theorem statement silently changes meaning.

## Canonical direct-source objects

```text
canonicalSourceGammaL := sourceEq44GammaL
canonicalSourceMatrix := cutoffFreeMatrix
```

Lean target equalities:

```text
canonicalSourceMatrix = sourceEq44Matrix
canonicalSourceMatrix = dictionaryMatrix
canonicalSourceMatrix
  = legacyPrintedMatrix + 2*legacyPrintedCorrection(L)*I
```

Under the existing zeta seam hypotheses, previous theorems also give

```text
zeroSideMatrix = dictionaryMatrix = canonicalSourceMatrix.
```

## R004 damage control

Scalar identity shifts leave commutators unchanged:

```text
[D, M + aI] = [D,M].
```

The canonical source matrix therefore inherits the exact existing displacement
law and rank-at-most-two theorem.  These are promoted as

```text
canonicalSourceMatrix_displacement
rank_canonicalSourceMatrix_displacement_le_two
```

The old `finiteMatrix` displacement theorem is not withdrawn; its source label
is historical.

A deterministic numerical audit
`check_normalization_shift_invariants.py` checks both normalizations
side-by-side.  Its claim cap is finite numerical regression only.

Invariant under the scalar shift:

- eigenvectors/eigenspaces,
- eigenvalue gaps and ordering,
- centered-index commutator,
- displacement rank structure,
- fitted commutator minimizers.

Shift-sensitive:

- absolute eigenvalues,
- trace,
- determinant,
- matrix norms,
- positive semidefiniteness/inertia in general,
- absolute spectral lower bounds.

## Closed-form discrepancy — DERIVED, not yet a promoted Lean theorem

Writing `a = exp(L/2)`, direct calculus gives

```text
sourceEq411DerivedCorrection(L) - legacyPrintedCorrection(L)
  = log(2*(a^2+1)/(a+1)^2)
  = log(2*(exp(L)+1)/(exp(L/2)+1)^2).
```

For `L>0`, this is positive because

```text
2*(a^2+1) - (a+1)^2 = (a-1)^2 > 0.
```

This closed form is recorded here as **DERIVED** only until separately
theorem-locked in Lean.  The semantic repair does not depend on it.

## Claim firewall

**PROVED:** direct equation-(4.4) finite source matrix equals the canonical
cutoff-free/dictionary matrix; legacy printed normalization differs by the
known scalar identity; canonical R004 displacement survives unchanged.

**OPEN:** ambient external `QW_lambda / PsiSharp / kappa` finite-restriction
identification.

**OPEN:** form-core / Rayleigh-bottom convergence.

**OPEN:** positivity/lower-bound consequences.

**OPEN:** Suzuki fixed-aperture closure.

**OPEN:** RH.

## Dependency order

```text
#71
  -> source-normalization repair
  -> rebase #72
  -> finite kappa/QW/PsiSharp correspondence
  -> form-core/Rayleigh bottom
  -> Suzuki fixed aperture
```

Do not bypass the normalization repair when interpreting absolute finite
eigenvalues.
