# W01–W02 source audit and partial implementation

Date: 2026-10-13. Requested baseline: commit
`9583bbcc587aca8d87e74981b222e6813238d670`, tree
`188d1e0ae3a22e66d512c5c807687c6f2fc8d0e0`.

This review concerns the supplied build targets. It does not change the
requested release scope. The full original-source producer and its finite
image remain OPEN until their exact physical construction and consuming
theorems compile. RH remains OPEN.

## Source proof read

The audit read these original-detector package sources directly:

- `dependencies/master_v2_9/08_POST_V26_SOURCE/ANALYTIC_PRESSURE_POINT_EXTRACTED/proofs/01_single_universal_detector.md`.
- `root/01_TWO_SIDED_PHASE_AND_POLE_NEUTRAL_SOURCE.md`.
- `source_transport/01_UNIVERSAL_DETECTOR_FINITE_BRIDGE.md`.
- `contact_provenance/03_HIGH_JET_DEEP_STATE_AND_DIRECT_SOURCE_BRIDGE.md`.

The source family is precisely the infinite convolution of centered uniform
laws with half-widths `s/[r(r+1)]`, not the existing repository bump bank. The
zero-side correlation uses the complex square of the transform, not its
absolute square. The core source scale is fixed at `1/4096`.

## Conservative mathematical assessment

No concrete counterexample to the source targets was found in this audit.
This is a review conclusion, not a formal proof of the targets.

The paper nonvanishing argument correctly uses both nonvanishing of each
sinc factor and summability of its deviation from one. Convergence alone
would be insufficient: for example a convergent product of nonzero factors
can have zero limit. The new Lean component isolates the stronger criterion
on the specified infinite product.

The two-sided phase proof does not assume a rightmost zero exists. Its
argument requires the exact correlation's meromorphic continuation, a
nonzero residue at every off-line zero, and holomorphy at positive real
points. Given those statements, an eventual one-sided exponential bound
would produce a nonnegative Laplace input with abscissa at the supremal
displacement. The positive-Laplace singularity lemma would then contradict
holomorphy at that real abscissa. Both signs follow by applying the same
argument to the negative correlation. The eventual observation times need
not be uniform, and the two signs need not occur at one common time.

The finite source construction retains two separate nonnegative precursor
lobes, Fourier quotient truncation, common positive padding, reflection,
and pole killing. The spec's core `m=4` uses `sin^8(πx/L)`, degree four,
`N=ceil(L^4)-4`. This differs from the degree-three presentation in the basic
finite-bridge note but is supplied by its high-jet extension. A zero of order
eight in the precursor produces vanishing source jets through order five,
which includes the requested order four. Zero extension has this finite
regularity; no claim of infinite smoothness for the finite polynomial is
justified.

For the fixed source, the proposed error exponent
`L/2-c_s sqrt((ceil(L^4)-4)/L)` behaves as
`L/2-c'_s L^(3/2)`. It can pay the displayed polynomial normalization costs.
The physical/Euclidean coefficient normalization still needs its actual
Fourier factor. This review has not silently identified those norms.

## What the implementation actually covers

`Zeta23/CCM/UniversalSincDetector.lean` introduces the exact indexed widths,
the complex sinc with its removable singularity, and the actual infinite
product. Its intended theorem roots establish:

- Positive widths and exact finite telescoping sums.
- Total width `s` and tail width `s/(N+1)`.
- Analyticity of sinc at zero and an actual asymptotic estimate there.
- Absolute summability of the specified factors' deviations from one.
- Convergence and nonreal nonvanishing of the entire infinite product at
  each fixed argument, derived without a caller-supplied tail hypothesis.
- Its value one at zero and even symmetry.
- Prefix-product convergence to the specified infinite product, and the
  frozen original scale `1/4096` with its nonreal nonvanishing instance.
- Uniform convergence on every compact complex set, derived using one
  common summable tail majorant, and entire analyticity of the actual
  infinite product as a locally uniform limit of entire prefixes.

`Zeta23/ExceptionalZero/UniversalSincDetectorVisibility.lean` binds the
specified pole-killing multiplier to the repository's actual nontrivial
zero carrier. Its intended nonvanishing theorem accepts an off-line zero
and positive source scale; it accepts no visibility assumption. Crucially,
it proves a fact about the explicit infinite-product multiplier, not an
unproved identity with a physical Fourier transform.

The extended component also classifies the multiplier's nonreal zero set
as exactly `±i/2` and proves nonvanishing of its actual complex square at
every off-line carrier zero, including the frozen-scale instance. This is a
pointwise zero-set statement. Simplicity/multiplicity requires derivative
authority for the infinite product and is not asserted by that theorem.
The separate derivative extension now supplies explicit derivatives at the
two elementary zeros and proves each is nonzero. If those roots compile,
the usual simple-zero interpretation is DERIVED for the explicit multiplier;
no separate analytic-order or physical-transform claim is hidden in the
pointwise zero-set theorem.

Compiler receipts, rather than this list of intended roots, determine which
statements are PROVED. The initial compilation attempt stopped while
reading a dependency's `.ir` cache file before checking the new proofs; that
attempt provides no new formal theorem authority.
Subsequent Linux validation reached the source proofs and exposed an
instance-coherence mismatch between the direct complex norm and the norm
projected from the complex normed additive group in `IsBigO`. A transparency
option did not repair it. The candidate repair proves the two `Norm ℂ`
instances equal and explicitly rewrites the derived asymptotic statement.
This is a kernel-checked equality target, not an extra source assumption;
its next compiler receipt remains necessary.

### Exact component receipt at `6ae99364`

The Linux component compiler at commit
`6ae99364db66b2c66b1e0bde804f02733907647e`, tree
`3580d29354edccd9682a103beb753cfa9c9df9a6`, reported **Built** for the
entire `UniversalSincDetector` and `NativeIntegerPrimeField` modules under
Lean `4.33.0-rc2`. The authoritative log is the component job in
[run 38469964899](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/38469964899).
Their printed theorem roots contain only `propext`, `Classical.choice`, and
`Quot.sound`. In particular, total widths, summable deviations, nonreal
nonvanishing, compact uniform convergence, entire analyticity, the frozen
coincident factor zeros, local histories, causal delay, exact first-prime
term, and continuous compact-source fields are **PROVED** at this head.
The explicit norm-instance equality and function identities repaired the
earlier import-transparency friction without adding an analytic premise.

That component workflow as a whole **FAILED**. The derivative extension in
`UniversalSincDetectorVisibility` and the multiplication-fiber extension in
`NativeIntegerPrimeConvolution` had proof-engineering errors. Their repaired
versions and the additional bounds and floor-completion modules remain
candidates until a later receipt. Printed axioms from an otherwise failing
module are not substituted for an entire-module success. This paragraph
harvests the source component only; the full workflow inventory and release
status are recorded separately by the integration receipts.

## Remaining mandatory mathematical obligations

The following are OPEN and are not encoded as arbitrary record premises:

1. Construct the infinite-convolution probability law and its actual smooth
   density `q_s`, including positivity, mass, support, symmetry and scaling.
2. Prove the Fourier transform identity with the product above, including
   the normally convergent complex product and the Gevrey bounds.
3. Bind the physical pole-killed source to that transform and prove its
   actual off-line visibility.
4. Formalize the positive-Laplace singularity lemma and its application to
   the actual correlation, obtaining both cofinal phase depth sequences.
5. Construct the finite polynomial, endpoint/pole moments, actual physical
   normalization, norm lower bound, cutoff and the stated H1/form errors.
6. Prove its exact transported two-lobe Gram/energy matrices and positive
   denominators, then consume the error estimate to retain negative depth
   at `ceil(L^4)`.

The existing bank, existential finite negative obstruction and aperture
freedom theorems remain useful independent results. They do not establish
these exact fixed-source, quantitative, phase-preserving constructions.

## Falsification and highest-information next steps

An analogous exponential correlation with an additional positive-real pole
can remain eventually nonnegative; this is why the no-real-zero fact is
essential to the phase proof. Dropping the nonreal-factor hypothesis or
summable-deviation criterion can similarly destroy product nonvanishing.
Changing a source to its finite image can introduce nonreal transform zeros,
so that original zero pattern must not be copied to the finite record.

The first highest-information next proof is the actual probability-density
and Fourier-identification theorem. It connects the new product authority
to the physical dictionary. The second is the positive-Laplace lemma,
whose verified application would strengthen absolute growth to the two
separate original phases. The third is the concrete finite error theorem,
which would finally turn those physical witnesses into the required native
finite vectors. These remain required for the full release.

## Post-green implications for the source component

The exact compiler-verified head and workflow results must accompany this
analysis before any item is labeled PROVED. For a verified product root,
the resulting mathematical change is substantive: infinite-tail
nonvanishing becomes a theorem of the specified source, so physical
visibility can no longer be blocked merely by an unproved tail premise.

Upstream, the nonvanishing proof uses differentiability of sinc at its removable
singularity and summability of the original widths. The local linear
asymptotic estimate suffices for this pointwise product result; the sharper
quadratic tail estimate is unnecessary at this stage. A compact norm bound
then gives one summable majorant for all points in a compact complex set,
allowing a genuine normally convergent, entire-product extension. The
separate `UniversalSincDetectorBounds` candidate now gives an explicit
real-axis estimate `|P_s(x)| <= 2 exp(-(log(2)/2) sqrt(s |x|))` by taking a
head of `floor(sqrt(s|x|)/2)` factors, each of norm at most one half, and
bounding every remaining real factor by one. No tail cancellation is
assumed. Its next receipt is required; the complex-strip estimate, inverse
Fourier density construction and physical derivative bounds remain OPEN.

Downstream, the exact zero-carrier multiplier theorem applies to both sides
of the critical line and preserves the complex-square coefficient. Once
the actual physical transform is identified with that multiplier, universal
visibility is available at the one frozen source scale. The old bank can
then remain a regression/fallback construction without carrying this new
theorem under its name. The two-sided phase theorem still requires its own
Laplace and meromorphic continuation proof, and finite transport still
requires its actual error theorem.

No historical failed RH-closing route has been resurrected merely by this
nonvanishing result. The source visibility obligation is narrowed; the
opposing native growth estimate remains OPEN. The most direct falsification
check is to verify that any downstream consumer uses the physical transform
identity, rather than passing the formal multiplier as though it were
already a constructed physical function. This is the current claim
firewall and the highest-leverage next obligation.

## Proposed amendment: coincident real factor zeros

The newly supplied `NEXT_PR_AMENDMENT.md` labels itself "Proposed only" and
explicitly preserves the original build scope and the D2 obligation. Its
A5/E guards are mathematically justified: nonreal zero exclusion does not
imply simple real-axis zeros of the sinc product.

At the frozen scale `s0=1/4096`, choose `z=6π/s0`. The paper indices `r=1`
and `r=2` (Lean indices zero and one) have widths `s0/2` and `s0/6`, so their
arguments are exactly `3π` and `π`. Both sinc factors vanish at this same
point, and their indices are distinct. The new Lean candidate
`fixed_coincident_factor_zeros` proves those exact factor statements.
It does not assert an unproved multiplicity theorem for the full product.

The imaginary elementary pair remains separate. The multiplier's explicit
nonzero derivatives at `±i/2` support its simple-zero interpretation once
compiled; squaring that multiplier gives the corresponding doubled
elementary zero behavior. That square contains `P_s(z)^2`; the separate
`P^2 q_s` source has multiplier `(z^2+1/4)^2 P_s(z)` and is not identified
with the square or the autocorrelation here. None of these facts imposes simplicity on the
real sinc-product zeros or supplies the physical density/Fourier producer.

## Argon iteration: theorem opportunities and remaining source obligations

The retrieved `RH_Argon_Audit_Iteration_2026-10-13/RESEARCH_NOTE.md`,
Sections 3–5, was read directly together with its exact copied
`NATIVE_POSITIVE_COMPLETION.md` and `COPRIME_MIXED_ENERGY.md` sources.
The archive remains read-only reference evidence. Its authors explicitly
classify the new universal claims as PAPER deductions.

The bilateral source `Q_s(p)` has its zeros on the imaginary axis, whereas
the present Fourier product has them on the real axis. The conventions
are related by `Q_s(p)=P_s(ip)`. Thus the Argon coincident zeros at
`p=6πi/s` correspond to a real Fourier argument; evenness accounts for its
sign. This is consistent with the new exact factor control and does not
require or permit a universal simple-real-zero premise.

Section 3 gives a concrete conditional theorem opportunity: a proved
selected-ground source divisor would determine the derivative of the
auxiliary rational function `R_u(z)` at its elementary root. That derivative
supplies a strictly negative continuum source–fourth-moment pairing and a
strictly positive opposing budget. The relevant derivative holds `L,K,u`
fixed; it is not an aperture derivative of a moving minimizer. The current
source product theorem concerns the original detector and does not prove
that a selected finite ground supplies this divisor. A conditional
root-budget consumer must keep that producer obligation explicit.

The complete budget in Section 3.3 remains valid at a tie with a nonnegative
opposite-parity remainder. It supplies no cutoff-uniform positive budget
and no lower parity gap from negative depth. It is unchanged by the common
scalar shift described in Section 3.4. Consequently it cannot distinguish
positive grounds from prohibited negative states by itself. The missing
native upper inequality for the actual signed remainder, and strict-odd
coverage or a valid bypass, remain OPEN. The modified-prime control can
pay this budget while violating the native divisor identity; it falsifies
a generic root-pattern exclusion, not every native argument.

Section 4's useful native foundation is the exact prime-two history of the
unchanged source. Before the next integer atom enters, both the actual
prime field and logarithmic integer drive contain precisely the prime-two
term. Source mass and weighted Cauchy–Schwarz would then make its norm
strictly positive. The stable-difference decomposition and its exact
initial convention are separately required before this becomes a lower
bound for the actual angle's stable component. Source coefficient
disjointness alone gives no pointwise orthogonality of overlapping fields.

The proposed angle limit `E(T)(1-c_T) -> ||Z||²/2` is mathematically
compatible with exponentially divergent energy. Its corresponding
unnormalized small Gram eigenvalue has a positive limit, rather than
vanishing. The quiet mixed-energy criterion and subexponential angle
criterion are equivalent on the exact native pair under the full inherited
decomposition, with zero/bounded cases handled separately. Neither
criterion is established here. Displaying both does not create independent
restrictions or an RH contradiction.

Section 5 identifies the actual relative-progress ratios as the missing
range information. Strict forward contraction alone does not force their
sum to diverge; the stationary adjoint-kernel component survives. Its
finite-section shift control correctly prevents exchanging the iteration
and discretization limits without an error theorem. Rationally equivalent
completion kernels preserve the shared zero divisor and supply no extra
observability by themselves. Native progress or range membership remains
OPEN; stable completed input is not a proof of stable inverse output.

### New local native-field component

`Zeta23/CCM/NativeIntegerPrimeField.lean` defines the exact unchanged-weight
prime and integer-drive fields with the source argument visible. The
candidate theorems establish a finite inclusive cutoff
`floor(exp(T+s))` that works uniformly for every time at or before `T`,
pointwise summability, continuity for a continuous compact source, and
vanishing before `log(2)-s`. They also isolate the exact prime-two term on
the first-prime source window. The frozen-width spacing guard is proved
from `log(3/2) >= 1/3`, rather than accepted as a numerical assertion.

These local analytic constructions are **PROVED** at the exact component
receipt above. They use no global `L²` or range
premise. The compact source hypothesis is an explicit generic input to
these operators; the actual `j=P²q` source and its support still need their
producer. The analytic convolution equation `N*X=U`, the superexponential
drive estimate, stable-difference decomposition, positive anchor integral,
and all global native upper/range conclusions remain OPEN for the actual
fixed source. Compiler
The receipt does not remove the actual-source producer obligations.

### Source-preserving arithmetic equation

The separate candidate `NativeIntegerPrimeConvolution.lean` advances the
pointwise compatibility obligation. It defines the actual outer integer
translate action `sum_m m^(-1/2) X(t-log m)`, without defining that action
using divisor coefficients. Compact support makes the prime-source double
sum finite on a bounded multiplication rectangle. Its proof regroups by
`m*n`, identifies each nonzero multiplication fiber with the complete
divisor antidiagonal, and consumes the unchanged weighted divisor law.
The infinite zero fiber is annihilated by the zero coefficients. The result
is the exact pointwise source-parametric equation `N*X=U`, plus summability
of the actual action. It accepts no compatibility premise.

The frozen width also gives a proved positive first-prime delay target,
from `log(2) >= 1/2`, and hence the prime and integer-drive fields vanish
for all nonpositive times. This establishes their actual causal histories
before any Hilbert-space membership question.

If those roots compile, an assumed arithmetic compatibility bridge can be
replaced by a construction for every compact source. The remaining step to
the flagship native fields is the exact `j=P²q` producer and its support,
with any desired measure-convolution packaging proved consistently with
these series. No rapid-drive estimate, completed-input decay, inverse,
range membership or opposing native upper bound follows just from this
compatibility equation. All such claims remain OPEN.

### New implications and adversarial checks after the component green

The entire-product theorem and its nonreal zero exclusion can now be
composed with a future physical Fourier identity directly. No further
nonvanishing-tail interface is needed. The weak differentiability estimate
at zero already paid normal convergence; a quadratic Taylor bound is a
possible quantitative refinement, rather than a missing prerequisite for
analyticity. This compresses the source dependency graph.

The exact first-prime formula gives a canonical local anchor for every
compact source before any field-overlap or global-energy calculation. A
nonzero source value on that window gives a nonzero prime field; positivity
of a local integral still requires the actual source, its regularity and a
measurable integration argument. This is a **LEAD**, not a proved stable
energy lower bound. Distinct arithmetic coefficient supports do not make
translated compact functions orthogonal.

The real-axis head estimate is invariant under replacing `x` by `-x` and
scales through `s|x|`, as the prescribed widths require. At zero its right
side is two while the exact product equals one. Thus it survives the basic
normalization and boundary tests, although it is deliberately not sharp.
The estimate controls a Fourier product; using it as though it already
described a probability density would cross the remaining source bridge.

The rational causal kernel candidate satisfies
`c(t)=(-exp(-t/2)+2 exp(-3t/2)) 1_{t>=0}` and its actual integer action is
identified with the positive floor completion through finite history and
the exact weighted exponential identities. This would establish the
native origin `a=c*N` locally. Its kernel has signed integral `-2/3`, while
the integer weights have divergent total mass. Therefore a naive global
Fubini argument for the positive completion's mass is invalid; the positive
floor formula and its own tail estimate are the correct global route.
Laplace identities, completed-source compatibility, inverses, stable range
and any opposing RH bound remain **OPEN**.

No RH-closing dead end has become valid solely from these component gates.
The highest-information next source theorem is still the exact
infinite-convolution density and Fourier identification. The new arithmetic
compatibility and causal floor origin remove separate native-definition
ambiguities but do not pay that theorem, the two-phase Laplace lemma, or the
finite transport error. These are distinct obligations with distinct
falsification tests.

### Constructive candidates prepared after the component receipt

Three additional source modules are ready for a subsequent compiler batch;
none is upgraded to **PROVED** by the earlier component green.

- `UniversalSincDetectorBounds.lean` gives the real-axis norm bound one,
  a quantitative contracting-head bound `2^(-N)`, and the explicit Gevrey
  bound above for the unchanged infinite product.
- `UniversalSincDetectorInverse.lean` uses the standard generalized Gaussian
  integrability theorem at power `1/2`, then reflection and domination, to
  establish every actual product polynomial moment. It defines an actual
  smooth inverse candidate as `(1/(2π)) paperFT(P_s)(-x)` and proves its
  dictionary to the scaled Mathlib Fourier transform. It supplies no
  probability, support, mass or forward-transform identity by assumption.
- `UniversalSincSourceLaw.lean` constructs normalized Lebesgue measure on
  `[-1,1]`, the actual independent `infinitePi` coordinate law, the
  prescribed weighted sum, its deterministic summability and tail
  `s/(N+1)`, and the measurable pushforward probability law with all mass on
  `[-s,s]`. Clamping extends the sample sum to every point and is proved to
  change no sample almost surely. The same space proves exact scaling of
  the actual laws. No alternate finite bump is substituted.

The two constructions now expose a precise connecting obligation: show
that the constructed probability law has characteristic function equal
to the actual sinc product, and identify its measure with the normalized
inverse candidate. Its density's positivity, real-valuedness, support and
mass must follow from that exact connection or independent theorems. The
mere existence of a smooth inverse function is insufficient. The new
measure definition and its pending roots do not silently close that gap.
