# Post-#227 research delta — one-coefficient transfer and mixed-resolvent frontier

> **Claim firewall: RH remains OPEN.**
>
> Evidence precedence: exact merged GitHub object and compiler/CI first; this document records the post-green mathematical interpretation without upgrading any claim beyond Lean.

## What became formally true

**PROVED — PR #226.**
`oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul` establishes
```text
a_N = -kappa_N d_N
kappa_N = (2N-1)/6.
```

**PROVED — PR #227.**
- every complex-linear construction carries the same correction collapse;
- safe negative-shift coefficients satisfy
  `Gamma_lambda = 1 + kappa_N(1-alpha_lambda)`;
- `6*Gamma_lambda + (2N-1)*alpha_lambda = 2N+5`;
- the safe cross-parity secular transfer has one free transfer coefficient;
- the direct zero-shift transfer has the same one-coefficient collapse;
- predecessor-kernel correction directions collapse to one;
- the selected-even bi-regular retained state admits a denominator-free one-coefficient zero-shift normal form.

Exact validated head: `b8d29733167a95e16f5721eddfced6b650a3b641`.
Merged commit: `7aace87a5644f837e2c8b64bdcf5e66b2dc0b020`.
Tree: `1dd1cdefcf4f4f7929b310697fdd1615a861ca1a`.

## What changed

Before #226/#227, alpha and Gamma appeared as two independent cross-parity correction channels. They are now affine-dependent because their underlying predecessor correction vectors are exactly collinear.

The retained selected-even transfer is reduced from
```text
sigmaMinus = alpha*sigmaPlus + Gamma*mu
```
to a one-coefficient identity of the form
```text
6*sigmaMinus =
  alpha*(6*sigmaPlus-(2N-1)*mu) + (2N+5)*mu.
```

One transfer degree of freedom has disappeared. The remaining problem is to understand the canonical geometry of alpha, not to discover another relation between alpha and Gamma.

## Upstream implications

The existing proof of `crossParitySecularGamma_eq_trial_cubic_overlap_div` internally derives a mixed-resolvent formula for the correction functional evaluated on the cubic-generator predecessor correction. The proof pattern is not specific to that vector.

The natural upstream theorem is therefore the generic Riesz representation
```text
chi(y) = <R b, y> / <c,c>
```
for arbitrary predecessor direction `y`, where `R` is the safe predecessor resolvent, `c` the odd cubic shell and `b` its shell-to-predecessor coupling.

This abstraction should replace repeated scalar-specific calculations.

## Downstream implications

Specializing the generic representation to
`d = oddIndexCubicShellPredecessorPart N`
would give
```text
1-alpha_lambda = <R_lambda b,d> / <c,c>.
```

The existing safe-resolvent norm bounds and Cauchy-Schwarz can then give magnitude control on `1-alpha_lambda`. This is theoremically safer than attempting a sign result immediately.

The #209/#211/#213 complete-source functional stack can then be compared with the Riesz representative `R b` on the same retained state.

## Resurrected routes

The full-space source/M4 sign and proportionality routes remain consumed by #215. They are not revived.

A narrower dual/Gram route becomes worth reconsidering: the new object is the retained-state resolvent-transformed vector/covector `R b`, which was not the full-carrier object tested in #215.

The pre-bi-regular kernel route is cleaner after #227 because the two correction kernel directions are collinear, but it remains secondary because bi-regularity already kills the relevant kernel coordinate.

## New RH-relevant clues

**LEAD / HYPOTHESIS.** A decisive canonical condition may be an angle, phase, Gram determinant, or extremal relation between
```text
R b,
d,
and the complete source-functional covectors.
```

**LEAD / HYPOTHESIS.** If actual canonical arithmetic forces sufficient alignment between `R b` and `d`, the one remaining coefficient alpha may enter a restricted half-plane or magnitude region strong enough to contradict the retained first-bad scalar equation.

No such alignment theorem is currently proved.

## Falsification checks

1. `<R b,d>` is a mixed pairing, not the positive quadratic value `<R b,b>`; resolvent positivity alone does not imply alpha is real or signed.
2. Do not identify `d` with the shell coupling `b`; they have different definitions and dependencies.
3. PR #216 forbids silently substituting a safe negative-shift state for the zero-shift retained state.
4. PR #205 shows generic reversal/parity/shell/displacement geometry does not exclude simultaneous badness; any decisive constraint must use actual canonical arithmetic.
5. Selected-even remains an explicit hypothesis; no WLOG theorem exists.
6. Check boundary and low-N cases before using any denominator or nonzeroness argument.

## Highest-leverage next moves

1. Create `Zeta23/CCM/CrossParityCorrectionFunctionalRiesz.lean`.
2. Prove the generic correction-functional Riesz representation for arbitrary predecessor `y`.
3. Derive the exact alpha mixed-resolvent formula as a corollary.
4. Derive Cauchy-Schwarz and safe-resolvent magnitude bounds.
5. Search for a canonical `b` versus `d` alignment/Gram theorem; try to falsify it immediately.
6. Compose any surviving constraint with the #209/#211/#213 source-functional stack.
7. Mirror or eliminate the odd-selected branch before any parity-complete finite claim.
8. Keep the terminal Mathlib RH seam explicit.

Standing question: given the one-coefficient collapse, the fastest information-gain experiment/theorem is whether the generic mixed-resolvent representation exposes a canonical relation between `R b` and `d`. If it does not, the current route should pivot before investing in alpha sign formalization.
