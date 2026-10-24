# Weighted mixing Stage 2 — final handover

## Current integrated state

One original root, `Zeta23.OPICAFollowup.weighted_mixture_exists_fourier`, is
complete at the full frozen scope and integrated in the main working tree after
the owner's Stage1 commit signal. The source is
`Zeta23/OPICAFollowup/WeightedMixing.lean`, SHA256
`5b0d86adcf72167a45b3922689911a5591da4c3ecab7fd19ceb246de5f00998a`.
External, main and audit28 source bytes are identical.

The independent consumer is integrated at
`research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedWeighted.lean`,
SHA256 `e137ed312f799cd589126a89281470c9f45293bcccf1386598dd66de30639bad`.
Its external and integrated bytes are identical. All expected consumers are
theorem declarations; every axiom query uses its fully qualified name.

Work is based on Stage1 commit `96dfba7082fb0cc7a93f7b25e31d449951ee9e4d`, tree
`c7a86500bcb1fb9fee009cb4b4500ed8927aae82`. This lane makes no commit or push.
The root agent owns the final source audit, ledger, dependency amendment,
manifest refresh, aggregate acceptance and publication.

## Completed gates

- `foundation-11.log`: exact full source leaf, exit 0, no warnings/errors.
- `genuine-save-02.log`: exact planned module saved to its own audit28 `.olean`,
  exit 0, no warnings/errors. No broad dependency build.
- `imported-consumers-02.log`: genuine import of that saved module, exit 0,
  no warnings/errors; primary plus eight independent consumer theorem queries
  print only `propext`, `Classical.choice`, `Quot.sound`.
- Independent mathematical read-only review by `parent_harvest` found no
  material gap against BUILD_SPEC lines1304–1308. The real-source consumer
  makes the real specialization explicit.

The eight consumer theorems check the full arbitrary-complex-input statement,
the actual measurable-set constructor, arbitrary parameter Dirac atoms,
infinite unweighted output mass, exact positive origin, imaginary coefficient
sign, full product absolute integrability, and arbitrary real signed input
producing zero imaginary output. The infinite mass case prevents substituting
a globally finite output carrier.

All compiler checks used pinned Lean 4.33.0-rc2 via audit28, one thread. This is
local compiler evidence, not a fresh GitHub workflow result or all100 receipt.
No compiler/check process from this lane remains running.

## Exact mathematical scope

The first original root is proved for arbitrary genuine complex locally finite
parameter measures with finite **true complex total-variation** exponential
moment and strict `a > 1/2`. No positivity or compact-support premise is added.

The actual positive mixture is the weighted product-pushforward of the parameter
measure and counting measure on all integers under `(t,n) ↦ exp(t)n`, with
weight `exp(t/2)`. The complex mixture is assembled from all four actual Jordan
coordinates. Local finiteness and linear variation growth are derived;
whole-line finite output mass is not imposed. Its exact atom is evaluated using
the true compact complex restriction to `{0}`.

The theorem exposes actual constructor equality, the literal Schwartz pairing,
Fourier reflection, exact origin and absolute product integrability of every
Jordan coordinate. Reflection retains complex coefficients without conjugation.

Supporting construction lemmas work at `a >= 1/2`. The original root retains
the strict threshold. No inverse or sharp-gap endpoint conclusion follows.

## APIs and import inventory

Canonical definitions present: `weightedVariation`, `weightedDilationMixture`.
Canonical `positiveLogMeasure` is absent because its actual log construction
belongs to the unfinished inverse lane; no dummy definition is supplied.

Useful proved supporting groups include actual positive mixture evaluation,
origin, local finiteness, growth and absolute Fubini; global
`variationControl_le_twice` from compact exhaustion; coordinate exponential
moments; actual complex mixture growth/pairing; actual reflected Jordan measures
and preserved moment finiteness; complex Fourier reflection; finite signed
compact atom transport and exact complex origin.

The sole direct project import is `Zeta23.OPICAFollowup.DilatedComb`.
The planned `Zeta23.CCM.NativeIntegerPrimeConvolution` edge is deferred because
none of the first-root proof uses arithmetic convolution; it is needed by the
future inverse lane. No broad unused import is introduced.
Mathlib imports are Integral.Prod, Measure.WithDensity,
Integral.Bochner.ContinuousLinearMap and Tactic.

Direct foundation hashes match main and audit28:

- DilatedComb: `6fd8a4016305e8898b58c64c38807b50d417e5a763487d5ccad5c6cabd4ecfc1`.
- ComplexLocalMeasures: `43d96d5474819b79c29853a81f8b4398f16d298470c2100fdade3fcada3a25b8`.

## Explicitly unfinished

The following three original root names remain absent and OPEN:

- `weighted_mobius_inverse`: actual log pushforward and measure convolution,
  absolute Möbius/divisor Fubini, exact absolute Möbius norm
  `ζ(a+1/2)/ζ(2a+1)`.
- `weighted_mixture_sharp_gap`: actual complex measure injectivity, reflection,
  gap support transport and scalar integer-comb conclusion without positivity.
- `weighted_gap_leakage`: true weighted total-variation leakage and continuous
  density supremum, retaining endpoint supremum versus stricter measure
  integrability exponents.

Highest leverage next is the actual positive-axis logarithmic weighted
pushforward, locally finite because compact log intervals pull back to compact
positive intervals bounded away from zero. Then prove `eta=N*sigma` with
absolute Fubini and the true absolute Möbius norm before invoking inversion.

## Diagnostics retained

`WeightedMixing-foundation03.lean` is an earlier genuinely green positive-only
snapshot, SHA256 `35a99332dbb03a0d1949e48f8244439a62e6332dc536fb710d5299dc9fbdc5d8`.
It is superseded by the integrated full first-root source.

Failed `foundation-04.log` through `foundation-09.log` are diagnostic evidence,
not formal passes. Corrections were API/coercion issues, an explicit map
SFinite instance, explicit Fourier target type, true singleton restriction
simplification and a real-to-complex integral cast annotation. Later passes
10,11 and final imported checks are green. Initial `genuine-save.log` was only
a wrong relative copy path before any module save; corrected by absolute copy
and the green `genuine-save-02.log`. Fragments are historical development aids;
the integrated source and final consumer are the authority.

## Claim firewall

No full module/all100 completion, parent acceptance, or RH claim is made.
RH, Step4 and independent closing inequalities remain OPEN. A fresh aggregate
source-bound compiler receipt and semantic review are separate root-owned gates.
