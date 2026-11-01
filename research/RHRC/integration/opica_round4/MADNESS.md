# Madness? — the exact arithmetic boundary

This closing attempt starts from merged PR #298, commit
`09ac22e48bb0683437572509abdf2ddec520b7ac`, tree
`f9e19310c2281af1609ae005a76cab40c913380f`.
It uses the supplied [research folder](https://drive.google.com/drive/folders/1howQ2e7wiynZef8GNlYkVd5Mc0B3Hta1),
including Pass 8 added during the investigation. **Step 4 and RH remain OPEN.**
The new proofs remove finite arithmetic and source-identification gaps. They do
not prove the independent cancellation estimate.

## What the new proofs establish

[MobiusHyperbola.lean](../../../../Zeta23/OPICARound4/MobiusHyperbola.lean)
uses Mathlib's genuine Möbius and von Mangoldt arithmetic functions. For a test
vanishing above an integer cutoff it proves the exact Dirichlet hyperbola
identity `U = 2 E - T`. Expanding `Λ = μ * log` retains every prime power.
The logarithmic test vanishes beyond `N/2`: the only exceptional factor would
be one, and `log 1 = 0`. The finite boundary therefore uses `sqrt(N/2)`.

[ActualSourceHyperbola.lean](../../../../Zeta23/OPICARound4/ActualSourceHyperbola.lean)
instantiates this algebra with the unchanged original kernel `H = κ * κ`, at
scale `1/4096`. Its cutoff follows from actual compact support. The existing
`originalDetector_correlationField_eq_sourceConvolution` supplies the literal
bridge to the native prime source. No arbitrary coefficient sequence replaces
von Mangoldt; no all-vector positivity condition replaces the actual signs.
The logarithmic test is also the delayed actual integer drive, with its
square-root normalization retained. The literal correlation-source integer drive
is proved equal to the positive density convolved with the original integer
drive. Its already proved decay faster than every fixed exponential transfers,
with the exact radius-dependent constant and threshold. The entire normalized short term
`E` also decays faster than every fixed exponential: its cutoff gives
`a <= exp(t/2 + s0)`, so every delayed argument is late together. The proof
uses only `abs(mu(a)) <= 1`, counts the finite terms, and fixes its threshold
before selecting any summation index. It requires no cancellation premise.
Consequently, the complete actual prime observable plus the normalized long
term decays at every fixed exponential rate. This estimates their sum, not
either summand separately.

[HyperbolaDiagonal.lean](../../../../Zeta23/OPICARound4/HyperbolaDiagonal.lean)
proves that a remainder bounded by `M` on `[1/T, infinity)` has genuine-Möbius
diagonal bounded by `M sqrt(T) sqrt(x)`. It splits the complete quadratic into
the rank-one term (nonnegative when `I >= 0` and `x >= 0`), the signed
off-diagonal and the diagonal, and proves
equivalence of the two eventual square-root lower-bound targets. Constants and
thresholds precede the observation scale. This proves neither lower bound.
The literal analytic remainder and its regularity still require their own
formal adapter; a generic bounded function is not substituted for that source.

## The remaining arithmetic statement

For the paper's fixed flat test `F`, write `P_F(y) = sum_k F(k/y)`,
`I_F = integral F > 0`, `R_F(y) = P_F(y) - I_F y`,
`Y = floor(sqrt(T x))`, and `L_Y = sum_(a<=Y) mu(a)/a`.
The exact surviving target, after the bounded diagonal is removed, is

```text
there exist C, X0 > 0 such that for every real x >= X0,

I_F * x * L_Y^2
  + sum_(1 <= a,b <= Y, a != b) mu(a) mu(b) R_F(x/(a*b))
    >= -C * sqrt(x).
```

The nonnegative rank-one term belongs in this inequality. Bounding the off-diagonal
alone is a stronger task. At Pass 8's exact samples `x = N^2/T`, the paper-level
condition is `H_N >= -C N`. This is a useful discrete target, not a proven bound.

Normalization matters: the repository proves that its finite logarithmic test
at `t`, with `x = exp(t)`, is `actualFlatMobiusTest(a/x)/sqrt(x)`. Identification
with the paper's `F` still needs the even-source orientation and periodization
adapters. At paper level, its normalized `hyperbolaT` therefore needs an
eventual **constant** lower bound. One cannot apply an unnormalized
`sqrt(x)` estimate to it without transporting that factor.

## What the accumulated constraints do and do not supply

The exact divisor law fixes the arithmetic coefficients. The source convolution
bridge fixes which observable is being studied. Rapid integer-drive decay
controls late arguments; inversion still samples early history at large divisors.
Type I and low-mask bounds remove easy regions. Full multiplicity, parity,
ground, jet and complement constraints strengthen the hypothetical obstruction
and preserve its exact costs. They have not supplied the independent upper or
lower arithmetic bound that contradicts it.

Several concrete compositions were tested:

* Absolute Poisson-remainder estimates give order `x` at the balanced boundary,
  even with arbitrarily fast decay at large arguments. The diagonal alone is
  order `sqrt(x)` and can be removed at that cost.
* GCD regrouping retains signed, cutoff-dependent restricted divisor sums.
  Complete Möbius inversion cannot collapse those weighted truncated sums.
* The existing Schur inverse and forcing bounds lose too much exponent. They
  also do not permit dropping the direct source-energy term.
* Moment compression represents the actual signed expression with a priced
  error; it does not bound the changing arithmetic moments or their combined
  coefficient cost. The full two-dimensional Abel estimate reduces an absolute
  route to a square of maximal Mertens sums, still above the required scale
  without stronger arithmetic cancellation.
* The spectral expression contains a complex square, not an absolute square.
  A double zero of its weight at frequency zero does not control the remaining
  frequencies. The actual auxiliary matrix has negative directions; it is not
  the physical finite Weil parity matrix.

The external [QRH PR #99](https://github.com/GTimG/QuasiRiemannTracker/pull/99)
provides a separately checked half-plane benchmark `0.8733819666133`. Its
source and exact-head admission statuses were inspected. It is not imported
into this pinned project, and its exponent remains above `1/2`.

## Validation and post-green meaning

The [contract register](MADNESS_CONTRACTS.json) binds the exact four new modules.
The [source audit](MADNESS_SOURCE_AUDIT.json) records corpus coverage, attempted
compositions and limitations. The original 500 declarations, 48 modules and 17
semantic controls remain independently mandatory. New complete-type consumers
and intended type-error controls distinguish a valid equality from a closing
estimate. Local Windows compilation is development evidence; current-head
Linux independent acceptance remains a separate requirement.

What becomes possible after these proofs pass is an arithmetic attack on one
literal, source-coupled finite boundary form, with its easy diagonal removed and
its normalization fixed. The most useful next theorem would constrain the
actual Möbius signs in the balanced interior. Rewriting the same expression,
checking more finite samples, or counting supporting declarations does not
supply that theorem. No impossibility of a future proof is asserted.
