# RHRC post-#163 mixed-source / Riesz arithmetic-frontier delta

> **Claim firewall: RH remains OPEN.**

This delta records the exact mathematical state after merged-green PR #163 and identifies what became possible only after its mixed-source/Riesz coupling was theoremized.

## Exact validated authority

```text
merged theorem-bearing PR = #163
merged main = bd3fa1aafa7df2aa35873df532bdb6f17ddd2bbd
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS
control-plane semantic anchor = PR #117
terminal claim = RH_OPEN
```

The exact #163 head passed the aggregate CCM build, ExceptionalZero build, no-placeholder/project-axiom gate, R003 normalization/source checks, Control-v2 regression/smoke checks and Permansson verification.

## What became formally true

### PROVED — mixed quadratic-normal source jet

For even boundary-flat `v` and `K >= 1`, define

```text
h_v(omega) = quadraticNormalSourceAtom K v omega.
```

Lean proves

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v).
```

This is the direct mixed-pairing theorem. It is not imported from #159's self-energy jet by type or analogy.

### PROVED — squared-jet form

Lean proves

```text
|h_v^(7)(0)|^2 = 4*(2*pi)^12*|M4(v)|^2.
```

Thus the phase/sign of `M4` disappears from the exact quadratic boundary term.

### PROVED — the production source moment samples the same observable

Lean rewrites `explicitCanonicalSourceMoment` so that its finite-prime contribution is a weighted sum of

```text
quadraticNormalSourceAtom K v (primeSourceCoordinate q L).
```

Pole and archimedean pieces remain. This is an exact shared-observable interface between the global production source moment and the local mixed jet.

### PROVED — exact Riesz-8/Riesz-9 mixed-jet boundary

Lean proves

```text
2*(2*pi)^4*(R8(v)-R9(v)) = S8(L)*|h_v^(7)(0)|^2,
```

where

```text
S8(L) = canonicalPolePrimeRieszEndpointScalar L 8.
```

No sign or nonvanishing theorem for `S8(L)` is used or obtained.

### PROVED — retained first-bad specialization

The same exact identities hold on the retained even shifted trial from #161. In the even-selected branch Lean additionally proves

```text
R8 < 0
```

and therefore

```text
2*(2*pi)^4*R9 < -S8(L)*|h^(7)(0)|^2.
```

This strict inequality requires no sign assumption on `S8(L)`.

### PROVED — cross-parity Gamma nonvanishing under odd-good

On the retained even-selected branch with the odd successor good, #163 theoremizes

```text
crossParityGamma != 0.
```

This follows without division from the #161 nonzero odd secular scalar and exact transfer identity.

## What changed

Before #163, `M4` was present in the Riesz boundary but the proposed linear quadratic-normal source observable and its seventh jet were only a derived research calculation.

After #163, the dependency graph is compressed to an exact theorem-backed chain:

```text
quadraticNormalSourceAtom
       |
       +--> finite-prime samples inside explicitCanonicalSourceMoment
       |
       +--> seventh jet at zero
               |
               +--> M4
                       |
                       +--> exact R8-R9 boundary
```

This is a genuine structural improvement. The missing theorem is no longer the local analytic coupling.

## What did not change

The following remain OPEN:

```text
explicitCanonicalSourceMoment != 0 -> M4 != 0
M4 != 0 -> explicitCanonicalSourceMoment != 0
finite prime samples determine h^(7)(0)
S8(L) >= 0
S8(L) != 0
simultaneous even/odd bad exclusion
odd-selected first-bad closure
independent contradiction-producing arithmetic restriction
negative-root exclusion
RiemannHypothesis
```

A finite weighted sum of samples does not generically determine a local derivative. #163 does not supply the missing interpolation/uniqueness theorem.

## Upstream implications

The mixed rank-two derivative transport is now validated deeply enough to support a production theorem, not merely a local calculation. The quadratic normal is also canonical in the headline coefficient: after normalization, the seventh jet collapses exactly to `M4` with coefficient `-2*(2*pi)^6`.

A broader normal-degree / jet / moment hierarchy is therefore plausible, but it should only be formalized if it compresses later arithmetic work. Generalization for its own sake is lower priority than testing FB-05.

## Downstream implications

The sign-bearing uncertainty in the Riesz increment is isolated into the witness-independent arithmetic scalar `S8(L)`. If a theorem eventually gives a useful sign or nonvanishing property of `S8(L)`, it immediately constrains the R8/R9 evolution of every legal even boundary-flat carrier and in particular the retained first-bad state.

Separately, the exact prime-source sampling theorem makes a sampling/interpolation route well-posed: the global source obstruction and the local jet now share one concrete analytic function.

Neither route is solved by #163.

## Resurrected routes

### Cross-parity source fork

The #161 fork

```text
odd successor bad
OR
explicitCanonicalSourceMoment != 0
```

is more informative after #163 because the source moment's prime term samples the same function whose seventh jet controls `M4` and the Riesz boundary. The missing bridge has moved from “different observables” to “global weighted samples versus local jet.”

### Moment-square boundary route

Earlier `M4^2` arguments can now be reframed through a manifest squared analytic jet. This removes phase/sign ambiguity in `M4` itself and exposes the endpoint scalar as the remaining sign-bearing factor.

## New RH-relevant clues

### LEAD / HYPOTHESIS — endpoint-scalar rigidity

If `S8(L)` has a fixed sign or a sufficiently controlled sign pattern on the production range, the squared-jet recurrence becomes a monotonicity/rigidity statement for Riesz order. This must be falsified before formalization.

### LEAD / HYPOTHESIS — canonical sample-to-jet rigidity

One finite weighted sample sum is insufficient generically. But the production prime coordinates, weights, cutoff-cell structure and multiple compatible identities may collectively constrain the analytic function enough to control its seventh jet. Search for a divided-difference, interpolation, recurrence, or uniqueness mechanism.

### LEAD / HYPOTHESIS — hierarchy of squared-jet Riesz increments

If higher centered normals produce analogous source jets and successive Riesz increments, transformed energy may admit a hierarchy of arithmetic scalars times squared analytic data. This could convert FB-05 into a monotonicity or rigidity problem rather than an opaque sign estimate.

### LEAD / HYPOTHESIS — cross-parity + squared-jet squeeze

Compose the #161 odd-secular/source identity with #163's squared-jet boundary on the same retained state. A new arithmetic relation may squeeze the allowed state space even if neither ingredient alone has a sign.

## Falsification checks

Fast failure tests for the new clues:

1. Sweep the exact Lean-normalized `S8(L)` for zeros and sign changes across cutoff cells and prime-power thresholds.
2. Construct legal/generic analytic controls where the same finite weighted sample sum is nonzero but the seventh jet vanishes, and conversely.
3. Test whether the canonical shifted state actually narrows those generic degrees of freedom.
4. Search exact generic/rank-one parity models for simultaneous even+odd badness.
5. Verify every retained-state composition uses the same shifted trial and does not substitute the zero-shift witness.
6. Test modified-source analogues where the mixed-jet identity survives but the desired RH-directed conclusion fails; if so, the identity is structural infrastructure rather than decisive arithmetic.
7. Preserve normalization: the Riesz discrepancy is in the repository's source-coordinate normalization, not an informal physical-coordinate rewrite.

## Highest-leverage next moves

1. **Endpoint-scalar falsification pass.** Derive the exact piecewise/cellwise representation of `canonicalPolePrimeRieszEndpointScalar L 8` and search for sign changes/zeros before proposing a theorem.
2. **Production sample-to-jet falsification pass.** Reuse R003 exact/Arb infrastructure to look for separation between the global source moment and the seventh mixed jet on theorem-aligned states.
3. **Simultaneous-parity falsification.** Determine whether the left branch of #161 is generic or arithmetically constrained.
4. **Choose the next theorem PR only after those tests.** If endpoint-scalar positivity/nonvanishing survives, formalize the weakest true result. If it fails, pivot immediately to sample-to-jet or parity arithmetic rather than proving a false global sign claim.
5. **Keep odd-selected coverage explicit.** No WLOG-even shortcut is available.

## Claim firewall

```text
#163 mixed source jet green != sourceMoment<->M4 theorem
#163 squared-jet boundary green != endpoint-scalar positivity
same analytic observable in prime samples != interpolation theorem
retained R8<0 != contradiction
strict R9 upper bound != negative-root exclusion
supporting theorem authority != machine claim promotion
negative-root exclusion != terminal Mathlib RH wrapper
```

## Standing questions

Given everything that is now formally true, what becomes possible that was not possible before?

The global production source obstruction and local Riesz boundary can now be studied through the same exact analytic observable.

If this contains a clue toward RH, where does that clue propagate?

It propagates into endpoint-scalar arithmetic, sample-to-jet rigidity, cross-parity composition, and the admissible space of retained first-bad states.

What experiment, lemma, reformulation, or connection would most efficiently tell us whether that clue is real?

The fastest discriminator is a theorem-aligned falsification sweep of `S8(L)` and of global-source / local-jet separation before any larger Lean investment.

**RH remains OPEN.**
