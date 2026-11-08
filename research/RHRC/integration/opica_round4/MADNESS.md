# Madness? — the exact arithmetic boundary

**Publication and research break, 2 November 2026:** [Handover](progress/2026-11-02/HANDOVER.md), [reading map](progress/2026-11-02/READING_MAP.md) and [outcomes](progress/2026-11-02/OUTCOME_REGISTER.json) preserve the accumulated positive and negative work. External prototypes remain separate from the production proof inventory.


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
The literal analytic adapter is now proved in `ActualSourceHyperbola.lean`: the
actual flat test is globally C1, including zero, and compactly supported. Its
full natural-number sampling remainder is uniformly bounded at every positive
scale. Thus the diagonal estimate and lower-bound equivalence now apply to the
actual source without an assumed bounded remainder. Neither lower bound follows.

## Further actual-source bounds

The next deduction uses the pinned Mathlib estimate for Chebyshev `psi - theta`.
For the literal compact correlation kernel, every higher prime power together
contributes a uniformly bounded amount at every real observation time. The exact
split retains all these terms. Any unbounded excursion must therefore survive
in the ordinary-prime contribution; the latter has not been bounded.

Differentiating the fixed compact density, rather than the arithmetic inverse,
also proves rapid decay of the literal integer-drive derivative. The flat-test
derivative includes both the drive derivative and half the original drive,
divided by `r * sqrt(r)`, with the negative sign retained. Source decay gives
quadratic vanishing of the flat test and linear vanishing of its derivative at
zero. Global C1 regularity and compact support then give a uniform bound on the
literal Abel sampling remainder. This removes the diagonal's abstract premise;
it does not bound the signed off-diagonal together with the rank-one term. The
coarse support collar used for variation estimates does not replace the exact
half-history cutoff in the hyperbola identity.

The complete Drive metadata inventory covers 1,725 files in 164 folders; this
does not mean every document was read. The focused historical review recovers
fixed-palette covariance bounds but also their uncontrolled moving complement.
Finite Euler filters preserve the same closed native dictionary space. Positive
sieve bounds lose order when passed through the signed detector kernel. None of
these observations supplies the missing bound on the complete signed term.

The actual mass is also proved positive: `actualFlatSamplingMass` equals the
square of the strictly positive half-Laplace integral of the fixed source
density. The original drive at the exceptional damping value is identified by
its analytic continuation before applying the literal convolution and
exponential change of variables. No termwise interchange at the zeta pole is
used. This supplies positivity of the retained rank-one term; it supplies no
sign or lower bound for the complete signed quadratic.

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
at `t`, with `x = exp(t)`, is `actualFlatMobiusTest(a/x)/sqrt(x)`. The full
natural-number sampling sum is now formally identified with the exact finite
history sum. Consequently `sqrt(exp(t)) * hyperbolaT` equals the complete
sampling quadratic at `Nat.sqrt(actualCorrelationCutoff(t)/2)`. Its diagonal is
bounded at this same natural cutoff, without assuming equality to a real-floor
cutoff. Removing that controlled diagonal gives an exact equivalence between
the two eventual **constant** lower bounds after division by `sqrt(exp(t))`.
Both lower bounds remain open; the normalization is part of the theorem.

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
* The attempted absolute forcing estimates lose too much exponent. The compact
  inverse cost was already controlled; the direct source-energy term must
  still be retained.
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

The [contract register](MADNESS_CONTRACTS.json) binds the exact fifteen Madness modules.
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


## Exact conditional RH consequence

`riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower` connects the
literal remaining native bound directly to Mathlib's `RiemannHypothesis`.
It retains the complete actual source, all prime powers, the factor-two
translation, the reflected history until its support threshold, and the
uniform archimedean correction. The contradiction uses the existing two-signed
late-excursion theorem at exponent zero. No separate rightmost zero, visibility,
ground-ray identification or explicit-formula premise is assumed.

The remaining premise is exactly: there exist `C > 0` and a time `T`, chosen
before every `t >= T`, with the actual `hyperbolaT` at
`actualCorrelationCutoff t / 2` at least `-C`. This commit does not prove that
premise. Positive sampling mass, a bounded diagonal, and equivalence of the
two lower-bound formulations do not supply it. Step 4 and RH remain OPEN.

The actual reflection-energy derivation isolates a difference of positive
even and odd energies with all divisor-log weights. It does not compare them:
replacing convolution's complex square by an absolute square would discard
the entire odd-reflection contribution. This is a falsified shortcut, not a
closing estimate.


## Composing the earlier OPICA constraints on the same object

[CommonQuarticGround.lean](../../../../Zeta23/OPICARound4/CommonQuarticGround.lean)
uses the original finite-phase approximation, the Round3 parity cover and
first-simultaneous-negative theorem, and the Round4 joint-ground package.
Fix one actual negative original phase in each parity, then recenter those
fixed functions in a growing aperture. Translation preserves the complete
Weil energy and the existing uniform approximation errors vanish at the
prescribed cutoff `Kd = ceil(L^4)`. Thus both native parities are negative at
that same cutoff for every sufficiently large aperture. This is constant
negative form depth, not a newly established common exponential Rayleigh rate.

The threshold precedes every generated packet. Every sufficiently late actual
packet therefore retains its original exponentially negative unit detector
and also satisfies the joint-ground constraints at its detector cutoff. The
selected Schur cutoff can be smaller. The even and odd first-birth cutoffs
also remain distinct; their maximum is bounded above by Kd, and each keeps
its own PSD predecessor and its regular-or-resonant Schur alternative.

[JointGroundBirth.lean](../../../../Zeta23/OPICARound4/JointGroundBirth.lean)
uses the actual Round3 newborn witness. Its one-dimensional shell and PSD
predecessor imply simplicity of a negative ground and nonnegativity of the
entire orthogonal complement. The shifted complement has gap at least the
negative depth, giving a response norm bound without inverting on the ground
kernel. This theorem applies at an own first birth; it is not silently moved
to the larger detector cutoff.

The earlier corrected-cubic-source and tied-ground identities now give two
further constraints. An active even source at or below the odd floor has
positive source/fourth-moment energy. At a simple even tie, exactly one of the
corrected even source and the whole odd ground projection is active. The
whole projection preserves every odd multiplicity; no selected odd vector or
odd simplicity is substituted for it. These statements constrain ties but do
not rule them out.

The compact inverse and four-history norm bounds were already available.
The remaining problem is to constrain the complete signed arithmetic value,
including its direct source energy and shifted mass, strongly enough to
contradict the actual negative packet. Neither source visibility nor the new
complement bound supplies that conclusion alone. The exact conditional RH
theorem above and its unproved arithmetic premise remain unchanged.

The full support gate now contains 687 declarations in 55 owned modules and
40 intended semantic controls. All 647 preceding complete types and axiom
sets remain mandatory. Eight new independent consumers and seven new
negative controls check the cutoff, threshold, source, carrier and complement
distinctions. Source registration does not itself grant compiler authority.


## Actual regular apertures and full tied-source constraints

The older logarithmic-cover and first-birth results now compose on the actual
native carrier. `RegularCells/NativeZeroRegularity.lean` transports the full
prime-cell source through its moving seed frame, retaining the nonunitary
Gram/congruence factors. Its complex determinant is not identically zero.
For every finite list of parity/cutoff pairs, one can choose a common regular
aperture in any positive open interval. Physical source identification uses
the exact prime cutoff cell; it is not extrapolated across a seam.

`RegularCells/NativeRegularBirthSelection.lean` combines this with the earlier
eventual two-parity negativity at Kd. Under an off-line zero, arbitrarily late
apertures have both parities negative at Kd and every native matrix through Kd
invertible. The finite bound is fixed before selecting the aperture. Each
own first birth therefore has an invertible predecessor, and its same-witness
Schur realization is regular. Negative shared grounds can still occur;
invertibility at zero does not separate equal negative eigenvalues. The new
selection also does not retain a previously selected exponential detector or
create aperture stationarity.

`TiedNewbornResponse.lean`, `NewbornSpectralVisibility.lean`,
`TiedCubicEnergy.lean` and `TiedSilentMoment.lean` retain the full source and
complement. At an odd own-newborn tie, an active even source forces
nonnegative cubic source energy and bounds its fourth moment. Strict negative
cubic energy instead forces source silence, whole odd-ground visibility and
even-ground simplicity, with a quantitative fourth-moment depth inequality.
Opposite nonshared negative modes are source-visible and simple. These are
different branches on the same actual object, not interchangeable assumptions.

The support gate now requires 741 declarations in 63 owned modules, preserving
all 687 preceding complete types and axiom sets. Seven new consumers and twelve
additional source-type controls bring the control total to 52. The controls
reject specific invalid API applications; they are not mathematical
countermodels. In particular the positive-aperture selector now proves the
broader existential conclusion without requiring a prechosen prime cell.

The remaining closing obligation is an independent restriction on the complete
signed arithmetic value that contradicts the surviving actual negative-ground
branches. These constraints remove the resonant own-predecessor alternative
at selected apertures; they do not prove that arithmetic restriction or RH.


## Actual-prime separation on the same deep packet

The atlas identified a real composition gap: choosing a regular aperture did
not automatically retain the previously chosen exponentially deep packet.
`RegularCells/PacketRegularSelection.lean` now reconstructs the genuine packet
after aperture selection, using a strict depth margin on an open interval.
Its finite bound is fixed before selecting the aperture. Under an off-line zero, the final theorem
`cofinally_actual_packet_joint_regular_disjoint_spectra` keeps the literal same
packet, source data, unit detector, exponential depth and quartic cutoff.
Every native matrix through that detector is invertible, and the complete
even and odd spectra are disjoint at each cutoff from three through it.

The separation argument uses the actual arithmetic source. It starts with
the full squared-index compressions on the limiting moment carriers, passes
to a small nonzero cosine phase, and isolates an actual prime in the frozen
prime-power sum. Unique prime factorization and meromorphic-frequency
independence turn the formal nonzero anchor into nonidentity on the genuine
prime-phase path. Analytic continuation and finite open-set selection then
give the required real aperture. The full nonunitary frames, both Gram
matrices, positive source scaling, common scalar shift, all prime powers and
the exact `floor(exp L)` cell remain in the argument.

The full-spectrum bridge removes equal even/odd eigenvalues at these selected
apertures, including negative ties. `SeparatedSourceVisibility.lean` then
forces the two correctly oriented genuine source channels to be nonzero on
every nonzero eigenvector and makes each whole eigenspace at most one
dimensional. This is qualitative: no lower bound on the gap or on source
overlap follows from nonvanishing alone. The reciprocal odd input is still
distinct from the odd eigenray.

The support register has 1066 declarations in 90 owned modules, retaining
all preceding 741 declarations and their types and axiom sets. Eight new
independently stated consumers and 28 source-type controls extend the exact
control inventory from 52 to 80. The declaration parser retains dotted names
such as `HasPrimeLaurentExpansion.constant` instead of truncating them. The
closed mathematical addition is 27 source paths; parent mathematics, pins,
historical registries and all original control bodies are unchanged.

The next arithmetic question is stronger than noncollision. The historical
actual-source examples already have simple separated spectra with signed
residues, so separation cannot by itself establish positive response or
positive residues on the full complement. The complete arithmetic value
must still be bounded in a way that conflicts with the same hypothetical
zero's deep packet. The literal long-term lower bound in
`riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower` remains an
OPEN premise. Step4 and RH remain OPEN.

Local proof receipts qualify the exact freshly compiled Windows roots with
authenticated unchanged parent objects. Fresh current-head Linux production
qualification, all independent replays, semantic controls and the full
canonical materializer remain mandatory. Historical compiler facts are used
only for their explicitly unchanged historical scope.



The fixed original phases now have a uniform finite-mass comparison with the exact squared normalization. Given an actual off-line zero, there is one positive margin chosen before all sufficiently late apertures: at the literal quartic detector cutoff, both parity Rayleigh bottoms lie below its negative. The witnessing even trial has fourth moment zero, and the odd trial has third and fifth moments zero. The moment-restricted trial inequalities keep that same margin without projection or source replacement.

This strengthens the earlier unnormalized two-parity negativity. It does not transfer the margin to a first-birth cutoff or to the packet's selected Schur cutoff. It also does not supply the independent signed arithmetic estimate. RH and Step 4 remain OPEN.

The extension adds eleven mathematical declarations and two complete-type consumers in existing modules, plus four intended source-type controls. The complete gate is 1079 declarations in 90 modules with 84 controls; the 277-method register remains 231 portable and 46 mandatory native methods. Current-head independent native and final acceptance evidence is still required.


## Arithmetic frontier, Increment 1 (7 November 2026)

At the maintainer's explicit instruction, research resumed from the published
handover. The [build specification](arithmetic_frontier/BUILD_SPEC.md) narrows the
closing targets and binds them to the exact native objects. Seven modules under
`Zeta23/OPICARound4/ArithmeticFrontier/` (contracts M43–M49) add 97 declarations.

The even moment slice is the actual even pole-neutral carrier with physical
`M4 = 0`; the odd slice has `M3 = M5 = 0`. The existing seed chart identifies
them with `{M0=M2=M4=M6=0}` and `{M1=M3=M5=M7=0}`, with the full Gram `D²` as the
only admissible metric. Their dimensions are exactly `K-3` and `K-4`; both vanish
at `K = 3`, where a slice bound holds for every tolerance, and are at least 13 and
12 at the literal quartic cutoff.

`riemannHypothesis_of_cofinal_moment_slice_bounds` proves that cofinal
vanishing-error bounds on one parity's whole slice (C1) contradict the fixed
off-line-zero margin at the same state. The selected-packet consumer uses the
packet's full spectral disjointness to exclude every Rayleigh-bottom tie, so only
the two exact ground-response tests remain. Finite consumers prove soundness of
the complete inverse-residual block certificate and of the source-core reduction,
and transport a negative witness to its projected core with margin `d - 3η`.

These are reductions and sound consumers. **No arithmetic sign is supplied; every
closing premise, RH and Step 4 remain OPEN.** The gate is now 1176 declarations
in 97 modules with 96 controls; the preceding 1079/90/84 scope is hash-bound and
mandatory. Local evidence is a pinned Linux compile and audit; current-head
production qualification is still required.

## Arithmetic frontier, Increment 3A: pole-channel annihilation (7 November 2026)

`Zeta23/OPICARound4/ArithmeticFrontier/PoleChannel.lean` (contract M50) adds ten
declarations. It reuses the production theorems
`canonicalPoleMatrix_mulVec_eq_zero_of_profiles` and
`canonicalPoleMatrix_mulVec_poleNeutralEven_eq_zero`, and adds:

* the odd profile orthogonality;
* odd-carrier annihilation of the pole operator;
* vanishing of the pole sesquilinear form on both carriers;
* the exact identity `Q = -arch - prime` for the native energy on both
  pole-neutral carriers.

Both moment-slice lower bounds, and hence (C1), are therefore literally lower
bounds on `-arch - prime`, with the unchanged production channels. This is
dependency compression, not positivity. **The sign remains the OPEN closing
content; RH and Step 4 remain OPEN.** The gate is now 1186 declarations in 98
modules with 98 controls. The two new controls reject pole annihilation without
pole neutrality and the energy identity at a nonpositive aperture.

## Arithmetic frontier, Increment 3F: leakage commutator, certificate soundness and source columns (8 November 2026)

Three modules add 27 declarations (contracts M51–M53).

* `MomentLeakage` (M51) proves the compressed commutator with every term
  retained:
  `[Vᴴ D₀ V, Vᴴ E V] = Vᴴ [D₀, E] V + Z Lᴴ - L Zᴴ`, where the leakage is
  `(1 - V Vᴴ) D₀ V = W Lᴴ` of any finite rank. The one-normal and no-leakage
  cases are included. The term `Vᴴ [D₀, E] V` is not discarded.
* `FiniteCertificateSoundness` (M52) proves, for exact real data:
  * the kernel's shifted-factor rule is sound
    (`0 < τ` and `‖A - τI - RRᵀ‖²_F < τ²` give `xᵀ A x > 0`);
  * `τ > 0` cannot be dropped;
  * an exact negative witness refutes `A ⪰ 0`;
  * a positive pencil `F + εG` gives the checkpoint inequality.
* `SourceColumnTrace` (M53) proves, for `C = H S`:
  * `G = Sᴴ H² S` and `Cᴴ H C = Sᴴ H³ S`;
  * the column projection is self-adjoint and idempotent;
  * `tr(((1 - P) H)ᴴ ((1 - P) H)) = tr(H²) - tr(G⁻¹ Sᴴ H⁴ S)`.

These are supporting identities and soundness results. The native enclosure
bridge from Arb balls to the actual transcendental source is not proved, so no
numerical certificate becomes a Lean fact about the actual source. **No sign of
the source is supplied; every closing premise, RH and Step 4 remain OPEN.** The
gate is now 1213 declarations in 101 modules with 100 controls. The two new
controls reject:

* the commutator without its leakage terms;
* the certificate with `0 ≤ τ` in place of `0 < τ`.

The suite is held at 100. The pinned isolated-worker recipe compiles the
mutation file with Lean's default `maxErrors = 100`, so a 101st control is
reported as the error limit, not as a type rejection. Raising the limit needs a
recipe-version change.

