# Astra external research review — post-#150 arithmetic frontier assessment

Date: 2026-09-12

> **Authority firewall:** this file preserves an external-model research assessment for provenance. It is not Lean theorem authority, machine claim promotion, interval proof, or RH evidence. Statements below are classified explicitly. **RH remains OPEN.**

## Audited state

The review was requested after merged theorem PR #150, covering the #144-#150 analytic/regularization tranche and its interaction with the older Schur/source machinery.

Repository theorem authority for this review is independently anchored by the project to:

```text
PR #150 merge = fb92d5749d6f7a65cfc9129d49d8213219c059db
validated theorem head = b1be9eca5f544d4356ea88089c0f7264f75d2220
validated theorem tree = 999ef44d44855cdffd5be5843e9f072867c0a7a8
RHRC #971 / run 34690959720 = SUCCESS
Permansson #744 / run 34690959699 = SUCCESS
```

The review itself does not create that authority.

## Principal assessment

The regular-aperture/log-cover programme has done its intended job: a hypothetical off-line zero can now be pushed into an exact finite state where the selected predecessor is regular and the canonical zero-shift trial has strictly negative exact source-channel energy.

Therefore the immediate research bottleneck is no longer analytic continuation or determinant nonidentity. It is the arithmetic sign of the selected regular residual.

The review recommends avoiding broad universal positivity targets unless they are derived from genuinely new canonical arithmetic information.

## Strongest proposed reduction — pole/prime discrepancy

**Classification: EXTERNAL DERIVED / repository theoremization pending.**

The review rewrites the pole-minus-prime part of the canonical energy in a cancellation-preserving form. In the notation used by the audit:

```text
g_u(omega) = <sourceMatrix(omega) u, u>

D(t) = 4*sinh(t/2)
       - sum_{q <= exp(t)} Lambda(q)/sqrt(q)
```

and the proposed exact identity is

```text
E_pole(u) - E_prime(u)
  = (1/L) * integral_0^L D(t) * g_u'(1-t/L) dt.
```

The research significance is the order of operations: combine the pole and finite-prime channels exactly first, then estimate their discrepancy. This is better aligned with the observed strong cancellation than bounding the channels separately.

No sign conclusion for the integral was established by the review.

## Full-state retention recommendation

**Classification: RESEARCH DESIGN RECOMMENDATION.**

The review notes that the #150 construction knows more than the outermost negative-energy endpoint exports. Valuable information includes:

```text
cell-minimal bad size K*
all smaller sizes good throughout the physical cell
both parity sectors nonnegative at smaller sizes
open persistence of the selected negative witness
selected predecessor regularity
negative explicit root
unique zero-shift preimage equation
exact negative canonical energy.
```

The recommendation is to retain this ancestry in the next theorem interface instead of repeatedly projecting it away.

A stronger simultaneous-regularity certificate for both parities / finitely many predecessor sizes is suggested as worth testing, but is not claimed as proved.

## Numerical / falsification findings reported in the review

The following are discovery signals, not theorem authority.

### Raw aperture Loewner monotonicity

**EXPERIMENTAL SIGNAL:** tested canonical aperture derivatives show mixed spectral signs rather than a uniform positive- or negative-semidefinite derivative. This argues against a global Loewner monotonicity shortcut.

### Minimizing-trial Schur monotonicity

**EXPERIMENTAL SIGNAL:** the aperture derivative of the regular zero-shift Schur value changes sign in tested canonical cases. This argues against a simple scalar monotonicity proof.

### Elementary source-atom energy

**EXPERIMENTAL SIGNAL:** the tested elementary source-atom quadratic energy changes sign. A universal positive atom kernel is therefore not a credible default representation.

### Channel conditioning

**EXPERIMENTAL SIGNAL:** the final regular Schur endpoint can be a very small residue of much larger pole/arch/scalar/prime channel terms. This reinforces the earlier post-#138 warning that independent coarse channel majorants may destroy the relevant cancellation.

The project should reproduce any numerical fixture needed for decision-bearing use and prefer interval certification before treating a sign pattern as reliable.

## Recommended next work from the review

1. Preserve/export the full #150 first-bad certificate.
2. Reproduce the exact pole integral and pole-minus-prime discrepancy identity in repository-native notation.
3. Test the discrepancy kernel numerically on actual canonical selected trials before formal sign work.
4. Use the exact boundary-flat moment constraints when simplifying the discrepancy kernel.
5. Prefer cancellation-preserving paired-channel estimates over independent absolute bounds.
6. Keep universal one-step domination as a broad fallback rather than the primary reduction.

## What the review does not establish

The review does **not** prove:

```text
Ecanonical(c-x0) >= 0
q_c >= 0
Delta(x0) >= 0
universal one-step domination
negative-root exclusion
finite-to-infinite closure
outside-strip/trivial-zero closure
RiemannHypothesis
```

It also does not promote any numerical or symbolic calculation to Lean theorem status.

## Project interpretation

The value of the review is obstruction compression: it identifies a smaller cancellation-preserving arithmetic observable after #150 and records several tempting monotonicity/positive-kernel shortcuts that should be attacked rather than assumed.

For the project-maintained synthesis and the subsequent Riesz-smoothing derivation, see:

`../RESEARCH_LEADS_POST_150_REGULARIZATION_CLOSED_ARITHMETIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**
