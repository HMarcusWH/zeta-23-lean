# Post-green research: first weighted mixing root

## Exact state

The complete external `WeightedMixing.lean` candidate, including original root
`weighted_mixture_exists_fourier`, passed the pinned Lean compiler with exit 0
and no warnings (`foundation-11.log`). Its source SHA256 is
`5b0d86adcf72167a45b3922689911a5591da4c3ecab7fd19ceb246de5f00998a`.
The narrow saved-module and eight independent imported consumer checks also
passed, warning-free, with only the standard three axioms. Exact hashes and
gate results are recorded in `STATUS.json`.

This is local compiler evidence for a new partial module, based on Stage1
checkpoint `96dfba7082fb0cc7a93f7b25e31d449951ee9e4d`. It is not a GitHub workflow
result, full100 receipt, or parent acceptance. No remote workflow was rerun or
harvested by this proof lane.

## What became formally true

For every genuine complex locally finite parameter measure sigma satisfying
the actual true-variation exponential moment, at every strict `a > 1/2`, the
actual weighted product-pushforward over the full integer lattice defines a
locally finite linear-growth complex mixture. Its Schwartz pairing equals the
literal parameter integral. The Fourier transform is the mixture of the
reflected parameter measure, retaining the original complex coefficients. Its
origin atom is exactly the integral of `exp(t/2)` against sigma. Absolute product
integrability is proved for all four Jordan coordinates, so the transport is
genuine Fubini rather than a totalized integral identity without integrability.

No positivity or compact-support premise is introduced. No finite whole-line
mass premise is imposed on the output.

## What changed upstream

The construction and growth estimate can precede uniform Schwartz estimates.
Once the actual positive mixture has linear growth, parent temperateness gives
Schwartz integrability. Pullback through the actual map and density then gives
the absolute product integrability required for Fubini. This compresses a
potentially separate family of parameter-uniform seminorm estimates.

The complex-coordinate argument uses a proved global control inequality
`variationControl <= totalVariation + totalVariation`, obtained from compact
coherence and exhaustion. The Euclidean complex total variation is never
relabelled as the sum of real and imaginary variations.

Supporting construction lemmas allow `a >= 1/2`. The original theorem retains
the paper's strict threshold. The endpoint improvement belongs only to this
existence/Fourier part.

## Downstream and resurrected routes

LEAD: the actual logarithmic pushforward can now be developed on top of a
constructed locally finite mixture, rather than an abstract desired mixture
packet. Compact log intervals correspond to compact positive x-intervals bounded
away from zero; this is the natural local finiteness proof for the next
`positiveLogMeasure` construction.

LEAD: the previously compact weighted-convolution route may extend through
absolute Fubini once the exact log identity and the true weighted Möbius norm
are proved. The latter requires the actual absolute Möbius Dirichlet series,
not merely the signed identity `sum mu(n)/n^s = 1/zeta(s)`.

DERIVED, not separately registered: reflection-invariant parameter measures
give self-dual mixture distributions by the proved Fourier reflection law.
This is sufficient only within the stated exponential moment class.

## Falsification and limits

Independent consumers test the full arbitrary complex input type, actual
measurable-set construction, arbitrary parameter atoms, exact origin,
imaginary coefficient sign, and an output with infinite whole-line mass.
The last case rules out silently replacing the output by a globally finite
complex measure.

The existence endpoint does not establish the Möbius inverse or sharp-gap
endpoint: the inverse norm involves the divergent boundary series at
`a + 1/2 = 1`. A conditional or critical-tail parameter profile does not acquire
the exponential moment merely because its renormalized distribution exists.

## Highest-leverage next moves

1. Construct the actual positive-axis logarithmic pushforward with its weight;
   prove local finiteness directly on compact log intervals.
2. Prove the exact `eta = N * sigma` transport with absolute product Fubini.
3. Establish absolute Möbius norm and genuine measure-algebra inversion before
   using cancellation to infer the sharp-gap conclusion.

The inverse, sharp-gap and leakage roots remain absent and OPEN. RH, Step4,
independent closing inequalities and full100 release remain OPEN.
