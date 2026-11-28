# Direct arithmetic windows to native literal energy

This route extracts an arithmetic bound before the original zero-exclusion
consumer, then feeds the bound into the existing native spectral construction.
Its terminal is
`Zeta23.RHReference.riemannHypothesis_direct_arithmetic_windows`.

**Verification status:** implementation candidate. The new supplier and combined
terminal require a fresh common-environment build, declaration-dependency audit,
and independent exported-proof checks. The earlier verified
[`CompactEnergyAdapter`](../Zeta23/RHReference/CompactEnergyAdapter.lean) is a
separate route with its own receipts. Its successful checks do not certify this
new composition.

## Exact arithmetic boundary

The source is the existing native literal function, including all prime powers:

\[
G(x)=\sum_{n=1}^{\lfloor x\rfloor}\Lambda(n)(x/n-1)
      -x\log x+(1+\gamma)x.
\]

The extracted theorem supplies

\[
\forall t>0\;\forall B\in\mathbb R\;\exists Y\ge\max(B,2)\;
\forall x\in[Y,Y^{3/2}],\quad G(x)\le x^{1/2+t}.
\]

This is a complete real window at arbitrarily late scales. It places no
requirement on the intervals between the supplied windows. The coefficient is
exactly one; the original family exponents are fixed before choosing the small
positive exponent that produces the requested `t`.

The supplier uses the original archive at
[`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`](https://github.com/CocoSgt/riemann-hypothesis-lean/tree/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4).
It assembles `TopG` and `VWin` from the proved row and local-correspondence inputs,
the `HypsAlt` theta/covolume construction, and the Green/shape construction.
It then applies `level_gm_le_on_family_scales` before any zero-free endpoint.

At the principal character of modulus one, `Level.cyc PChar.one` retains only
`PChar.one`. Erasing that character removes every additional summand, so
`Level.Gm = Formalism.Gz`. The original literal formula then equals native
`literalG` definitionally. This normalization does not replace the source with
a truncated prime-only model.

## Paper calculation

The native positive-part energy is

\[
E(Y)=\int_Y^{Y^{3/2}}\frac{\max(G(x),0)^2}{x^2}\,dx.
\]

On one supplied window, an upper bound `G(x) <= A*x^(1/2+t)` with `A >= 0`
and `t > 0` implies

\[
E(Y)\le\frac{A^2}{2t}\bigl(Y^{3t}-Y^{2t}\bigr)
     \le\frac{A^2}{2t}Y^{3t}.
\]

The existing `window_energy_bound` provides this integration step. A one-sided
upper bound suffices because the energy uses the positive part. Continuity on
the positive compact interval follows from the existing literal-to-ramp identity.

The native `bothParityPowerComparison_proved` supplies a fixed `delta > 0` and
eventual full even and odd slice bounds with error `E(Y)/Y^delta`. Fix

\[
t=\min(\delta/12,1/8),\qquad C=1/(2t),\qquad a=\delta-3t>0.
\]

For each integer `n >= 1`, request a good window beyond the comparison threshold,
`exp (n+2)`, and a threshold where `C/Y^a <= 1/n`. Such a window exists by
cofinality. With `L = log Y`, the resulting full slice bound has the unchanged
`originalDetectorQuarticCutoff L`, error `1/n`, and `L >= n+2`. This is C1,
`CofinalMomentSliceVanishingErrorBounds`.

The explicit model power is eventually small. The arithmetic upper bound itself
remains cofinal throughout the proof. In particular,
`eventually_scaled_energy_small` is applied only to the function
`fun Y => C * Y^kappa` with its reflexive upper bound. An actual arithmetic window
is selected after the model threshold is known.

Finally, the existing actual generated even/odd trial pair eventually excludes
the full slice bound for every sufficiently small positive error under an
off-critical zero. Choose `n` so that `1/n` is below that fixed margin and
`n+2` is beyond its aperture threshold. The C1 witness gives the contradiction.
`riemannHypothesis_of_c1_through_generated_pair` is the terminal consumer.

The native comparison retains its attributed original Landau-window and pole
analysis. The earlier handoff concerns the arithmetic upper-bound input; it does
not assert that the native consumer is independent of all original analysis.

## Source and theorem map

| Module | Responsibility |
| --- | --- |
| [`ProvedInputs`](../Zeta23WindowArithmetic/ProvedInputs.lean) | Assemble `arithmeticInputs : TopG ∧ VWin` from original theorem bodies. |
| [`PrincipalNormalization`](../Zeta23WindowArithmetic/PrincipalNormalization.lean) | Prove the original principal singleton and `Gm = Gz` identities. |
| [`WindowExtraction`](../Zeta23WindowArithmetic/WindowExtraction.lean) | Extract complete windows from the arithmetic inputs, keeping their quantifier order. |
| [`PrincipalWindowSupply`](../Zeta23WindowArithmetic/PrincipalWindowSupply.lean) | Expose `principal_original_windows` with no arithmetic premise. |
| [`DirectWindowContract`](../Zeta23/RHReference/DirectWindowContract.lean) | Define the complete-window, cofinal-energy, and normalized-smallness contracts. |
| [`DirectWindowSource`](../Zeta23/RHReference/DirectWindowSource.lean) | Identify `Formalism.Gz` with `literalG` and prove `principal_literal_windows`. |
| [`DirectWindowEnergy`](../Zeta23/RHReference/DirectWindowEnergy.lean) | Integrate a supplied window and preserve cofinality. |
| [`CofinalEnergyClosure`](../Zeta23/RHReference/CofinalEnergyClosure.lean) | Obtain normalized smallness, C1, and the conditional generated-pair consumer. |
| [`DirectWindowAdapter`](../Zeta23/RHReference/DirectWindowAdapter.lean) | Bind the supplier to the exact unconditional terminal. |

The conditional consumer can be built independently of `ProvedInputs`. Checking
that smaller boundary is useful development evidence, but does not verify the
unconditional supplier or terminal.

## Common source environment and ownership

The isolated verification environment uses Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The repository's default compiler
and the historical strict verifier remain unchanged.

The original archive owns duplicated original analytic declarations. The
[`ownership map`](../verification/direct-arithmetic-window/OWNERSHIP.json) binds
all 27 known module pairs to exact hashes. Twenty-five native bodies match the
original after import relocation. The original `CharFamily` and
`LandauZeroFreeCriterion` files additionally contain definitions; their shared
declarations agree. Only staged native copies become import-only shims.

Any compatibility change must have an explicit old-source hash, replacement
hash, path, and reason. The stage and audits must reject an unrecorded duplicate
or an uninspectable proof edge. Neither a blanket namespace rewrite nor a broad
path exception establishes ownership.

## Size and execution requirements

A source import walk at the recorded original commit found **175,173 original
modules** in the extracted supplier's closure, about **17.37 million source
lines**. The cut is mathematically earlier, but its module imports still cover
almost the whole original archive. Declaration-dependency audits are therefore
essential: a mixed module may import or define a later endpoint without the
selected proof depending on it.

The original verification notes report a full build taking hours on a machine
with hundreds of GB of RAM. They also report a 61.6 GB solution export and an
exporter peak near 163 GB. These are measurements of the original terminal,
not measurements of this new terminal. Lake's temporary `.setup.json` files can
occupy substantial disk unless completed-module setup files are reclaimed.
See the pinned [original verification notes](https://github.com/homeowmorphism/riemann-hypothesis-original/blob/cfabf56cd40776cf3f46d6d462f1c5e09dcfe607/verification/NOTES.md).

The new workflow runs source/native checks and checker preflight automatically.
A full run uses an explicitly selected sufficiently large runner. It can be
requested by workflow dispatch or, before merge, by applying the label
`direct-window-full-verification` to the same-repository PR whose exact head is
`research/direct-arithmetic-window-20261128`. The PR route uses fixed large-runner
labels; the existence of a suitable registered runner is not assumed.
A missing, skipped, or failed
full run does not produce full acceptance. The resource probe is an operational
precondition, not a mathematical result or an estimate of the eventual proof's
precise resource use.

## Reproduction and acceptance

Use the commands in the [verification README](../verification/direct-arithmetic-window/README.md).
The source lock records the exact original and native baselines. Staging records
every copied source, original-owner shim, compatibility overlay, and selected
entry module. A development stage using uncommitted files is labelled explicitly
and cannot be promoted into an acceptance receipt.

The supplier and terminal receive separate declaration-dependency audits.
The supplier must not depend on native energy/C1/RH consumers or completed
upstream zero-exclusion endpoints. The terminal must contain the actual supplier,
normalizations, window-energy proof, cofinal closure, native comparison, and
generated-pair consumer. Its closure must exclude the earlier compact
fixed-strip/Perron terminal route. Both audits inspect types and values, including
opaque values and inductive/constructor/recursor dependencies.

Allowed logical axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
The final proposition is Mathlib's stock `RiemannHypothesis`, with no additional
explicit or implicit premise. The trusted challenge imports only Mathlib and is
built separately from the untrusted solution.

Exports are produced with `lean4export` at
`15f6055e299ad5b89345e533cc2192f4cc00f659`, built with Lean `v4.33.1`.
The judge uses official Lean `v4.36.0`, its default and paranoid kernel modes,
and Nanoda. The original archive's published successful pipeline is a tooling
precedent; the new composition needs a fresh export and fresh receipts. The
aggregate binds all required results to the same candidate, source pins, and
export identity.

## Attribution and distribution

The arithmetic input is credited to Levent Alpöge's original development with
Claude and Anthropic. The adapter files explain the extraction and normalization;
the workflow obtains the pinned original source externally. The original source
is not vendored by this change. Its stated provenance does not supply the compact
edition's Apache-2.0 license, and that separate license is not reassigned to it.

Historical manuscripts, claim registries, canonical producers, and prior proof
receipts retain their dated scopes. This document describes only the direct
arithmetic-window candidate and the evidence required for its acceptance.
