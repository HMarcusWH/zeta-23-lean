# Post-#249 research delta — remainder/budget ratio scout

Status: **POST-GREEN RESEARCH PASS / EXPERIMENTAL SIGNAL / RH OPEN**

## What became formally true

Nothing new became a Lean theorem in PR #249. Theorem authority remains PR #247. The exact arithmetic identity being explored remains PR #246:
`canonicalSourceChannelEnergy = -canonicalPrimeRemainderEnergy - canonicalPrimeFreeBudget`.

PR #249 is research-producing tooling and frozen Arb evidence only.

## Workflow harvest

Exact PR #249 research head:
- head: `1758ed7fd1fd0bbae6b6929b3793fa8e97288b55`
- merge: `caec6773664458bde0eac55cf1ad60446c385efd`
- merge tree: `6c5e363e4477cc075ac3779dabc4ce8d27e69674`
- attached workflows: **11/11 completed successfully**

The main RHRC workflow passed the Python claim/regression suite, R003 normalization audit, #249 scope checker, Arb result replay, quick ratio grid, Lean build and anti-circularity/firewall jobs. Historical regression workflows preserved their prior dispositions.

## What changed

### EXPERIMENTAL SIGNAL — sharp finite cancellation

Across 96 tested real points, `A` and `B` are positive definite on the exact even/odd boundary-flat carriers, while `E=A-B` remains positive. Their eigenvalues are order-one on the fixture, but the smallest certified `λ_min(E)` reaches about `3.49e-82` and the smallest generalized slack about `6.8e-83`.

This strongly disfavors proof strategies that only deliver a coarse fixed-factor comparison. It establishes no asymptotic decay law.

### EXPERIMENTAL SIGNAL — low-rank zero-side signature

The synthetic zero-side perturbation gives a rank-one PSD on-line response and signature `(1,1)` off-line response in each tested parity block. 82/90 tested off-line cases become canonically bad. Near `δ=0`, the negative increment has a leading-order quadratic response.

### Interpretation repair

The original #249 prose overstated finite-grid decay as asymptotic, a coarse-grid separation as an exact first-zero switch, a local quadratic response as an exact global `δ²` law, and narrow sign-change brackets as globally minimal thresholds. Those points are repaired and CI-locked.

## Upstream implications

The #246 split should be treated as an exact cancellation problem, not a large-margin domination problem. The unconditional ground-spectrum atlas remains the correct mathematical spine, and the #249 perturbation should be used as an adversarial test for any proposed structural law.

## Downstream implications

The Glasses-v2 order remains: unconditional ground spectrum/eigenspace -> carrier min-max/interlacing -> unconditional prime-test-weight interface -> multiplicity-safe fixed-cell dynamics -> exact prime-power seam -> positive base -> first-crossing exclusion.

A useful experimental follow-up is a dense fixed-`K` sweep in `L` around `2πK/L≈γ₁`.

## Resurrected routes

No dead global-monotonicity route is resurrected. The experiment strengthens exact-factorization/positivity-identity searches, low-rank signature analysis, ground-space/test-weight structure, and first-crossing work where exact seam identities matter.

## New RH-relevant clues

The useful “divide by turtle” interpretation is that subtracting the two exact #246 families isolates an extremely small zero-sensitive residual on some legal extremal directions. The structurally sharper clue is the on-line PSD versus off-line indefinite low-rank response.

The next question is whether genuine arithmetic structure forces admissible zero contributions into the PSD type without merely restating Weil positivity.

## Falsification checks

Do not infer an asymptotic `K` law, a hard cutoff at `2πK/L`, monotonicity in `δ`, global minimality of the sign-change brackets, or a globally consistent alternate zeta function from PR #249. Do not rule out analytic-number-theory methods as a class.

## Highest-leverage next moves

1. Keep the next theorem PR focused on **unconditional ground-spectrum atlas + N-flow monotonicity**.
2. Add a dense first-zero-scale transition scout before promoting any resolution-threshold story.
3. Use the #249 perturbation as an adversarial test for candidate exact positivity/factorization laws.
4. Build a globally prime/Euler-product-consistent planted model only if a candidate theorem genuinely needs that stronger falsifier.

## Standing questions

What exact algebraic feature makes an on-line planted contribution PSD but an off-line quartet indefinite on these carriers?

Can that feature be expressed on the unconditional ground eigenspace without assuming RH or residual-state nonexistence?

Does the first-zero-scale separation sharpen under a dense sweep, or disappear?

Can the codimension-three boundary-flat restriction convert a full-space positive/low-rank identity into a nonvacuous canonical theorem?

**RH remains OPEN.**
