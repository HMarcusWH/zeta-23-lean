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

`Zeta23/ExceptionalZero/UniversalSincDetectorVisibility.lean` binds the
specified pole-killing multiplier to the repository's actual nontrivial
zero carrier. Its intended nonvanishing theorem accepts an off-line zero
and positive source scale; it accepts no visibility assumption. Crucially,
it proves a fact about the explicit infinite-product multiplier, not an
unproved identity with a physical Fourier transform.

Compiler receipts, rather than this list of intended roots, determine which
statements are PROVED. The initial compilation attempt stopped while
reading a dependency's `.ir` cache file before checking the new proofs; that
attempt provides no new formal theorem authority.

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
