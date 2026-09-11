# Post-PR #148 parameter-holomorphy green delta

> **Claim firewall: RH remains OPEN.**

## Exact green object

```text
PR #148
merge commit = fcd301ae4c1b58196ff7fca18128243f1d35a87b
merge tree = 91d537ee64b8f613bebdcf12110deba486276d35
validated theorem head = 77c2d14511004ba380b080e08b4943b267ebd863
validated theorem tree = 91d537ee64b8f613bebdcf12110deba486276d35
RHRC #930 / run 34619665717 = SUCCESS
Permansson #703 / run 34619665725 = SUCCESS
```

Compiler/CI evidence on the exact validated head is authoritative. PR #148 is theorem-bearing and advances the merged theorem anchor beyond #146.

## What became formally true

**PROVED / #148:**

- `complexArchSafeStrip = {z : ℂ | |z.im| < pi}` is open, convex, preconnected and connected.
- every real aperture lies in the strip, and multiplication by `t ∈ [0,1]` preserves the strip;
- `complexArchSinhSlope` is zero-free on the strip;
- `complexRegularizedArchScale` is differentiable/analytic throughout the strip;
- the exact fixed-unit parameter cores `complexAlphaCore`, `complexBetaCore` and `complexGammaCore` are differentiable/analytic throughout the strip;
- each core therefore has real-axis analyticity corollaries without requiring positivity of the real parameter.

The proof uses genuine parameter differentiation under the fixed `[0,1]` interval with local compact domination. It does not infer holomorphy from translation/deck identities.

## What changed

The old FB-01 "prove genuine parameter holomorphy of the fixed-unit production cores" is closed.

The next analytic task is now **assembly on one common source domain**. The full frozen source/predecessor still contains source channels not discharged merely by alpha/beta/gamma holomorphy:

- the production scalar/principal-log branch;
- pole denominators;
- elementary/frozen prime-source terms;
- fixed finite matrix assembly and intrinsic projection;
- the logarithmic-cover predecessor as an analytic family on a connected lifted domain.

Therefore #148 does **not** prove holomorphy of `complexFrozenCanonicalSourceRemainder` or `complexFrozenIntrinsicPredecessorRemainder`.

## Upstream implications

The fixed-unit dominated-differentiation proof pattern is now reusable infrastructure. It should not be abstracted further unless another downstream source integral actually needs it.

The strip `|Im z|<pi` is a canonical common archimedean domain. It is strong enough to avoid the nonzero periodic zeros of the divided sinh factor while containing the full positive real axis.

## Downstream implications

The immediate source-assembly target can now treat the archimedean cores as closed inputs. The next route should prove:

```text
common punctured source domain
  -> scalar branch control
  -> pole denominator zero-freeness
  -> finite prime/source analyticity
  -> complex frozen source holomorphy
  -> complex frozen intrinsic predecessor holomorphy
  -> lifted predecessor holomorphy on a connected logarithmic-cover domain.
```

Only after that should determinant analyticity become load-bearing.

## Resurrected route: deck-shift determinant nonidentity

The exact #144 law

```text
Ahat(z + 2*pi*i) = Ahat(z) - (2*pi*i) I
```

becomes more useful now that the parameter-integral obstruction is gone.

**LEAD / HYPOTHESIS:** iterate the deck law at one base point. If the lifted determinant were identically zero, then one fixed finite operator would have too many distinct scalar shifts as eigenvalues. A characteristic-polynomial root count should prove nonidentity. This algebraic nonidentity argument is distinct from holomorphy; holomorphy is then used to obtain isolated zeros / dense regularity.

Special case firewall: predecessor dimension zero (`N=1`) should be handled directly rather than forcing a positive-degree characteristic-polynomial argument.

## New scalar lead

For `z=x+iy`, the production scalar factor can be rewritten as

```text
z * (exp z + 1) / (exp z - 1) = z * coth(z/2)
```

and formally one expects

```text
Re(z*coth(z/2)) = (x*sinh x + y*sin y) / (cosh x - cos y).
```

On `|y|<pi`, both numerator contributions are nonnegative and the denominator is positive away from `z=0`; the numerator should be strictly positive away from zero. This suggests:

```text
Re(complexApertureScalarFactor z) > 0
```

throughout the punctured arch strip.

**Status: LEAD / HYPOTHESIS.** If proved, it gives a clean principal-log branch on the same common source domain.

## Cell-minimal route survives the post-green check

The preferred quantifier order remains:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Then every `K<K*` is good in both parities at **every** aperture of that physical cutoff cell. This is essential: minimizing only at one aperture and then moving the aperture would lose predecessor nonnegativity.

After dense regularity is proved, #142 same-witness persistence only needs one regular point inside the persistent-negative open set at predecessor size `N*=K*-1`.

## Zero-shift compression lead

At a regular selected state, existing theorems already give the unique `x0` with

```text
A x0 = b.
```

Because `A` is symmetric/self-adjoint, the coupling `inner x0 b = inner x0 (A x0)` should be real. If theoremized, the one-step determinant at `x0` compresses to

```text
Delta(x0) = q_A(x0) * (q_c - q_A(x0)).
```

**Status: DERIVED/LEAD until exact complex realness is separately proved in Lean.**

This suggests a potentially narrower closing certificate than universal domination:

```text
q_c >= 0
and
Delta(x0) >= 0
```

only on the exact forced zero-shift preimage. The zero-energy case must be handled explicitly; `Delta(x0) >= 0` alone does not imply the endpoint sign when `q_A(x0)=0`.

## Falsification checks

- #148 does not establish full frozen-source/predecessor holomorphy.
- The source parameter `z=0` remains special because prime/source coordinates contain `1/z`; the natural common source domain is expected to be punctured.
- The pole channel has its own complex denominator and needs a separate zero-free proof.
- Translation/deck identities still do not imply holomorphy; `F(z)=-z+Re z` remains the negative control.
- Holomorphy does not imply determinant nonidentity.
- Determinant nonidentity does not imply the arithmetic Schur-energy sign.
- Generic regularization countermodels remain active against any attempt to derive the contradiction from persistence/minimality/regularity alone.
- The final Mathlib `RiemannHypothesis` wrapper still needs an explicit formal seam from the strip-zero exclusion to Mathlib's nontrivial-zero statement, including the outside-strip/trivial-zero bookkeeping.

## Highest-leverage next moves

1. Prove the scalar right-half-plane theorem on the punctured arch strip, or falsify it quickly.
2. Assemble holomorphy of the exact complex frozen source and intrinsic predecessor on a common punctured strip.
3. Prove a connected lifted domain for the logarithmic-cover family and lifted predecessor holomorphy.
4. Prove determinant nonidentity by the deck-shift / characteristic-polynomial argument, with the zero-dimensional predecessor case split off.
5. Use the one-variable analytic identity theorem to derive dense real regular apertures on each physical cell.
6. Production-package the cell-minimal regular first-bad state and the exact negative zero-shift energy certificate.
7. Attack the exact canonical arithmetic sign on that one forced state.

## Formal status

```text
parameter-integral holomorphy of alpha/beta/gamma       PROVED / #148
assembled frozen source holomorphy                       OPEN
assembled frozen predecessor holomorphy                  OPEN
lifted determinant analyticity/nonidentity               OPEN
dense regular fixed-cell apertures                       OPEN
cell-minimal regular first-bad packaging                 OPEN
forced regular negative zero-shift energy                OPEN / downstream composition
independent canonical nonnegative sign                   OPEN / decisive arithmetic gap
terminal Mathlib RiemannHypothesis                       OPEN
```

**RH remains OPEN.**
