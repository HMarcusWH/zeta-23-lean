# Fixed-source phase-depth dependency review

Status: **PAPER REVIEW / formal construction OPEN**. The producer's original
quantifier order and its fixed source are unchanged.

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
