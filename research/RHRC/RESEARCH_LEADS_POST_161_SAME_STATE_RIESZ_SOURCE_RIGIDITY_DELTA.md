# Post-#161 same-state Riesz/source rigidity research delta

> **Claim firewall:** RH remains OPEN.

This delta records the required Post-Green Research Pass after merged green theorem-bearing PR #161.

## Exact validated state

```text
merged theorem-bearing PR = #161
merged main = ef29b45de683962122c1e898ed31bf9417757125
validated theorem head = 188407fb02a37de2e380ede3b60e140953b01441
validated theorem tree = b080572e87068889a72b4e612f99ddf0bd67f482
RHRC #1026 = SUCCESS
Permansson #799 = SUCCESS
control-plane semantic anchor = PR #117
RH = OPEN
```

The #161 theorem files are:

```text
Zeta23/CCM/FirstBadSpectralInterfaces.lean
Zeta23/CCM/SecularRootRieszBoundary.lean
Zeta23/CCM/RegularFirstBadCrossParityRiesz.lean
Zeta23/CCM.lean
```

No machine claim promotion or ExceptionalZero theorem wrapper changed in #161.

# What became formally true

## PROVED — spectral/ancestry interfaces

```text
parityBad_of_negative_eigenmode
RegularCellMinimalFirstBadCertificate.predecessorNonnegative_anyParity
```

A genuine nonzero compressed eigenmode with negative eigenvalue is enough to construct `ParityBad`, and whole-cell first-bad ancestry gives predecessor nonnegativity at the retained predecessor size for either reversal parity.

This removes two proof-packaging gaps that previously complicated cross-parity composition.

## PROVED — shifted secular-root energy/Riesz interface

At a genuine secular root `lam < 0`:

```text
parityCanonicalSourceEnergy_cubicSecularTrialVector_eq_lam_normSq_of_root
parityCanonicalSourceEnergy_cubicSecularTrialVector_neg_of_root
canonicalSourceChannelEnergy_cubicSecularTrialVector_neg_of_root
```

For the even sector:

```text
canonicalRieszSourceChannelEnergy_eight_neg_of_even_secular_root
canonicalRieszSourceChannelEnergy_nine_lt_neg_momentFourBoundary_of_even_secular_root
```

Thus the same canonical shifted secular trial that realizes the negative root has exact negative complete source-channel energy, strict complete Riesz-8 negativity, and the exact #159 Riesz-9 / `M4` boundary inequality.

No sign of the Riesz endpoint scalar is assumed or proved.

## PROVED — opposite-parity nonroot interface

```text
cubicSecularScalar_ne_zero_of_not_parityBad
```

If the successor parity sector is not bad, its secular scalar cannot vanish at a negative shift.

## PROVED — retained same-state cross-parity/Riesz composition

For a retained `RegularCellMinimalNegativeEnergyCertificate` whose selected parity is even, #161 defines the canonical shifted trial

```text
evenShiftedTrial
```

and proves:

```text
evenSecularRoot_of_even
evenShiftedRieszEightNeg
evenShiftedRieszNine_lt_neg_momentFourBoundary
oddSecularScalar_eq_gamma_mul_explicitSource_of_even
explicitSourceMoment_ne_zero_of_even_of_not_oddBad
oddBad_or_explicitSourceMoment_ne_zero_of_even
```

The headline forced-state fork is therefore

```text
ParityBad .odd L (Nstar + 1)
OR
explicitCanonicalSourceMoment L (Nstar + 1) evenShiftedTrial != 0.
```

Crucially, the Riesz defect and the cross-parity arithmetic source defect now live on the **same shifted negative canonical state**.

# What changed

Before #161, the project had theorem-backed pieces in neighboring stacks:

```text
negative first-bad state
Riesz 8 / Riesz 9 + M4 boundary
a shifted cross-parity source transfer
```

but the exact same-state composition was still an open proof-engineering and mathematical interface problem.

After #161 that composition is closed.

The bottleneck has therefore moved from

```text
Can the exact structures be aligned on one state?
```

to

```text
What independent canonical arithmetic restriction makes that jointly constrained state impossible?
```

That is a genuine narrowing of the RH attack surface.

# Upstream implications

## DERIVED — parity badness has a canonical negative-eigenmode characterization

The repository already had the forward existence direction from `ParityBad` to a negative eigenmode. #161 supplies the converse. A future cleanup theorem may package

```text
ParityBad p L N
  <-> exists lam < 0, exists v != 0,
       parityCompressedCanonical p L N v = lam • v.
```

This is dependency compression, not new RH content.

## PROVED interface should become default

`predecessorNonnegative_anyParity` should be the default first-bad ancestry interface in cross-parity work. It avoids adding unnecessary simultaneous zero-shift regularity hypotheses.

# Downstream implications

## FB-04B is closed

The following is no longer open:

```text
same-state shifted Riesz x cross-parity source composition.
```

It is PROVED / #161.

## FB-04C becomes the live theorem frontier

The highest-information next theorem target is the exact mixed quadratic-normal source observable.

Conceptually define

```text
h_v(omega)
  = <centeredQuadraticNormal, sourceMatrix(omega) v>
      / <centeredQuadraticNormal, centeredQuadraticNormal>.
```

The expected even-boundary-flat identity is

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v).
```

Status: **DERIVED / OPEN IN LEAN**.

This is not a type-level corollary of #159's self-energy odd-jet theorem. It is a distinct complex linear mixed pairing with its own conjugation and normalization obligations.

If theoremized, combine it with #159/#161:

```text
B8(v) = 2*(2*pi)^8*S8(L)*|M4(v)|^2
```

to obtain the derived rewrite

```text
B8(v) = S8(L)/(2*(2*pi)^4) * |h_v^(7)(0)|^2.
```

That would put a linear mixed source jet and the quadratic Riesz boundary defect into one formal observable chain.

# Derived consequences

## DERIVED — odd-good forces Gamma nonzero as well

In the retained even-selected branch, assume

```text
not ParityBad .odd L (Nstar + 1).
```

#161 proves the odd secular scalar is nonzero and also

```text
F_odd(lam) = Gamma(lam) * explicitCanonicalSourceMoment(...).
```

Therefore, without division:

```text
Gamma(lam) != 0
AND
explicitCanonicalSourceMoment(...) != 0.
```

This is a straightforward consequence but is not yet separately theorem-locked.

## OPEN — source moment and M4 are not interchangeable

#161's nonzero source theorem does **not** imply

```text
M4(evenShiftedTrial) != 0.
```

`explicitCanonicalSourceMoment` is a global canonical arithmetic linear functional containing pole, reduced archimedean diagonal/off-diagonal, and finite prime-source contributions. `M4` is a local centered coefficient moment.

Conversely, `M4 != 0` does not imply nonzero explicit source moment without a theorem.

Any decisive bridge must spend additional canonical-state structure.

# Resurrected routes

## Simultaneous parity badness

The left branch of #161's fork is

```text
ParityBad .odd L (Nstar + 1)
```

while the retained selected branch is already even-bad.

This makes the simultaneous-bad branch worth re-examining with the existing parity-compression rank-at-most-one / cubic-defect machinery.

Status: **LEAD / HYPOTHESIS** only.

Do not theorem-invest before exact generic/rational countermodel tests determine whether simultaneous even+odd badness is structurally easy. If generic rank-one parity models realize it, arithmetic must enter here too.

## Odd-selected first-bad branch

#161 is explicitly conditional on the retained selected parity being even.

There is no `WLOG even` theorem:

```text
D is algebraic, not unitary/isometric,
and parity compressions are not spectrally identified.
```

The odd-selected branch remains open coverage debt. A reverse-transfer or separate odd rigidity mechanism may eventually be necessary.

# New RH-relevant clues

## LEAD — three representations of one forced state

On the same retained even shifted negative state `u_lam`, the project now has

```text
spectral negativity:
  R8(u_lam) < 0

local moment boundary structure:
  R9(u_lam) < -2*(2*pi)^8*S8(L)*|M4(u_lam)|^2

global arithmetic source structure:
  F_odd(lam) = Gamma(lam)*mu_L(u_lam)
```

with

```text
odd bad OR mu_L(u_lam) != 0.
```

This is the strongest current structural clue: several inequivalent representations constrain the **same** forbidden candidate state.

The likely decisive theorem, if this route succeeds, is therefore a rigidity relation across those representations rather than a standalone generic positivity lemma.

# Falsification checks

Before building a strong source/M4 claim, test:

1. canonical even boundary-flat vectors with `explicitCanonicalSourceMoment != 0` but `M4 = 0`;
2. vectors with `M4 != 0` but explicit source moment zero;
3. actual shifted secular trials near small cutoff/prime-threshold cells for whether those separations persist;
4. simultaneous even+odd badness in exact rational generic rank-one parity models;
5. mixed seventh-jet sign and `(2*pi)^6` normalization at `K=2` and `K=3`;
6. conjugation convention for the complex mixed pairing;
7. modified-source controls: if the proposed rigidity survives unchanged in non-arithmetic systems, it is not sufficient;
8. normalization/scaling: source moment is linear while the Riesz boundary is quadratic.

# Highest-leverage next moves

1. Synchronize documentation/control state to #161. This delta is part of that synchronization.
2. Theoremize the mixed quadratic-normal source observable and its seventh `M4` jet if the direct production derivative algebra survives exact normalization checks.
3. Specialize the mixed jet to `evenShiftedTrial`.
4. Theoremize the easy odd-good conjunction `Gamma != 0 AND explicitSourceMoment != 0` only if it simplifies composition.
5. In parallel, falsify simultaneous-parity badness as a generic contradiction route before Lean investment.
6. After the mixed bridge is green, perform another full Post-Green pass asking whether the canonical secular equation or explicit source decomposition imposes a relation between the nonzero global source moment and the local `M4` jet that generic vectors do not satisfy.

# Standing questions

Given everything now formally true, what becomes possible that was not possible before?

**Answer:** exact Riesz negativity, exact `M4^2` boundary information, and exact cross-parity arithmetic source information can now be compared on one canonical shifted negative state.

If this contains a clue toward RH, where does it propagate?

**Answer:** downstream into a possible source/M4 rigidity theorem; sideways into simultaneous-parity badness; upstream into a cleaner negative-eigenmode/ParityBad interface.

What experiment or lemma most efficiently tells us whether the clue is real?

**Answer:** theoremize/falsify the mixed quadratic-normal seventh-jet -> `M4` bridge and test whether the canonical shifted secular state enforces a non-generic relation between that local jet and `explicitCanonicalSourceMoment`.

**RH remains OPEN.**
