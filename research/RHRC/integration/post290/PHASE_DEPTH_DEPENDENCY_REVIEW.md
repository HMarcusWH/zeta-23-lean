# Fixed-source phase-depth dependency review

Status on 2026-10-14: **LOCAL PINNED COMPILER PASS / whole-tree CI pending**.
`UniversalSincSignedExcursions`, `UniversalSincOriginalPhaseDepth` and the
canonical `OriginalDetectorPhaseDepth` exports now compile. The printed roots
admit only propext, Classical.choice and Quot.sound. For each actual off-line
zero, each smaller positive beta, each prescribed phase and each R, the actual
fixed-source construction produces an aperture L>max(R,4), unit L2 mass,
support in [1,L-1], and native additive energy at most -exp(beta*L).
The two phase apertures may differ. Finite transport and the filled producer
remain OPEN. The producer's original quantifier order and fixed source remain
unchanged.

The successful proof uses a single visible pole and the infimum of the genuine
positive-tail integrability domain. It does not need a rightmost zero or an
attained displacement supremum. Its unsmoothed compact correction is proved
entire. The actual transform at zero gives integral k=-1/4 and hence strictly
positive k L2 mass. Disjointness pays the literal unit normalization.

The original normalization step also avoids a larger intermediate exponent:
the signed excursion permits an arbitrary multiplier B at the requested beta.
Taking B=n*exp(2*beta*(1+s0))+abs(C(0))+1 pays both the finite diagonal and
the fixed aperture shift. A larger intermediate exponent may still be useful
for retaining depth in finite transport. The Fourier and literal window proofs
now supply all-jet errors below exp(-beta*L) eventually for any fixed beta.
Physical/coefficient norm and native quadratic-form transport remain distinct
obligations. RH and all three Step4 closing laws remain OPEN.

The following earlier paper review is retained as the dependency history; its
compiler-pending descriptions are superseded by the precise local result above.

The source note derives both late signs of the actual correlation from a
positive-Laplace abscissa argument, without a rightmost zero. It uses the
supremum Delta of off-line displacements, absolute summability of the actual
complex-square zero coefficients, normal convergence of the meromorphic
resolvent away from poles, nonzero residues, and no real nontrivial zeros.
These are substantive proof obligations. They are not present merely because
the new multiplier nonvanishing module compiles. The current Mathlib source
search found no ready Laplace-abscissa/Pringsheim module to supply that whole
argument. A proof must port its positive Taylor/moment step and its actual
native correlation continuation, or establish the same conclusion directly.

LEAD: the required quantified conclusion can use a smaller per-zero
abscissa argument. A single actual reflected right zero with displacement
d>beta forces the nonnegative tail's convergence boundary at or to its
right. A boundary-singularity theorem then contradicts the resolvent's
regularity at that positive real boundary. This avoids needing a rightmost
zero, an attained supremum, or equality of the abscissa with the supremal
displacement. New real-strip nonvanishing and actual correlation-realness
candidates address two prerequisites; they remain uncompiled. In the
repository's aperture variable a, physical translation is t=2a and the
target is exp(2*beta*a), not exp(beta*a).

An upstream simplification is available in the later energy conversion.
For disjoint lobes with squared norm `2n>0`, the exact normalized phase
energies are `(C(0)+C(t))/n` and `(C(0)-C(t))/n`. To force energy below
`-E`, it is sufficient to obtain respectively

`C(t)<-|C(0)|-nE` or `C(t)>|C(0)|+nE`.

Thus finiteness of C(0) suffices for this conversion. Its positivity is a
useful independent calibration but is not a missing logical premise of the
two-phase negative-energy deduction. A slightly larger exponent gamma with
`beta<gamma<d_rho` pays the fixed physical-length shift, the source norm, the
self-energy constant and subsequent transport cost. The growth theorem must
still be proved for arbitrarily late times at each original phase. No common
time, all-large-aperture depth, or uniform zero-dependent detection time follows.

The new physical-detector candidate reuses the existing
`TwoTranslateCorrelation.absolutelySummableZeroFilter_squaredWeil` for
the actual correlation coefficients. If its exact source identification
compiles, coefficient summability does not require a new zero-count proof
or a newly assumed strip-decay bridge. Extending the real-axis product
bound to a fixed horizontal strip, retaining `exp(s*abs(Im z))`, remains
an optional quantitative refinement. Real-axis integrability alone does
not establish that refinement. Positivity of the probability source does
not replace the complex square by an absolute square.

The displayed energies use the paper's normalized Weil pairing. The native
finite-matrix normalization still requires its own exact dictionary; a
factor relating those pairings cannot be silently discarded. Unit endpoint
collars also change the physical length from `t+2s` to `t+2s+2`. The fixed
shift can be paid using gamma>beta once the actual signed growth theorem is
proved. Neither normalization bookkeeping nor a norm-growth theorem alone
produces both prescribed signed excursions at arbitrarily late times.

Fast falsification checks are repeated-zero residue cancellation, gamma/rho
sign and translation conventions, endpoint beta=Delta, unattained supremum,
scale-zero degeneracy, finite self-energy with either sign, and an incorrectly
shared time for both phases. The current generic radius-bank result remains
an independent regression; it cannot inhabit this source's quantitative
phase producer. M04, finite transport, the full output theorem, and RH remain
**OPEN**.
