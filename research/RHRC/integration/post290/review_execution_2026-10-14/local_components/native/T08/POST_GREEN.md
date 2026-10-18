# T08 finite-order drive bound subcomponent

## What became formally true

`Zeta23/CCM/NativeIntegerDriveFiniteOrderBounds.lean` is exact local GREEN at
SHA256 `b4e2280a103c293d86deafa847d974e5f78f983f5ab8c4b86a66e66c1d9af1e4`.
Pinned Lean 4.33.0-rc2 exited zero with unchanged source bytes. Both public
theorems use only `propext`, `Classical.choice` and `Quot.sound`:

* `nativeOriginalIntegerDrive_finiteOrder_bound`: every integer N>=1 supplies
  a nonnegative source-only constant bounding actual U(t), for t>=0, by
  `C_N (1+t+s0) exp(-(N-1/2)t)`.
* `nativeOriginalIntegerDrive_rapid_bound`: for every A>0 there exist C>0 and
  T>=0 with actual `abs(U(t)) <= C exp(-A*t)` whenever t>=T.

No off-line zero, prime-field norm, source decay certificate, inverse or
range assertion is a premise. This is the finite-order subfile of T08; the
other T08 calculus/convolution/public API files remain parent-owned.

## Exact proof and assumptions

The actual source is the unchanged `nativeOriginalSource = j`. The actual
positive-logarithmic summand F_t and its finite integer history are imported
from the existing source. Its smooth zero extension is separated from zero,
and its continuum integral vanishes through both genuine weighted pole jets.

The normalized existing Mathlib Bernoulli polynomials realize the recipe's
canonical periodic primitives. The file proves their unit-cell derivative,
zero mean, matching endpoint values and finite bounds, then defines bounded
1-periodic K_N using the fractional part. Repeated integration by parts is
done on finitely many integer cells. Actual endpoint derivatives vanish by
the actual source's zero neighborhoods; adjacent seam values telescope.
There is no global differentiability assertion at the K_1 jumps.

The two literal source recurrences are
`A_0=j`, `B_0=0`,
`A_(N+1)=-(N+1/2)A_N-A_N'`,
`B_(N+1)=A_N-(N+1/2)B_N-B_N'`.
Their smoothness and compact support are proved. The actual iterated
derivative of F_t is identified before the exact exponential substitution.
Compact integrals of `abs(A_N)+abs(B_N)` give finite source-only constants.
The final theorem chooses N=ceil(A+2), d=N-1/2-A>0, and absorbs the polynomial
factor using `t exp(-dt)<=1/d`. Constants need not be uniform in A.

## Workflow harvest

The final exact compiler log and two axiom roots are formal-validity evidence.
Intermediate stage logs are implementation diagnostics; only the final
checked bytes support these public claims. Ordinary and optimized Python
tests both pass three independent exact-rational controls: zero means and
seams through order seven, integer-cell summation signs through order six
on a nonzero endpoint-flat polynomial, and the A_N/B_N chain rule through
order five in independent u/y coordinates. They supplement the universal
Lean theorem and supply no zeta-zero or RH authority.

The typed check captures both theorem signatures and an explicit term at
the full requested all-rate conclusion. The promoted proof-escape scan is
recorded separately. Parent integration owns the direct public facade,
global typed contract, bindings and remote CI; these are not silently
counted as passed here. The unchanged original first-order source files
and their controls remain available.

## What changed and implications

PROVED: the old first-order rate is strengthened to every prescribed fixed
exponential rate, with the actual source and continuum cancellation paid.
No optimized Gevrey double-exponential estimate is claimed; that would
require controlling the growth of the order-dependent constants.

Upstream, no optimized Bernoulli or Gevrey estimate was needed. Finite-order
compact smoothness and the two source moments suffice. The cellwise proof
avoids an unnecessary global seam differentiability obligation.

DERIVED, not separately formalized here: together with actual causality and
continuity, the all-rate estimate supplies integrability of actual U after
any fixed exponential weighting and polynomial moment. It makes a full-plane
Laplace analyticity port a more accessible downstream task. This would still
be a theorem about the integer drive, whose transform already includes the
actual source factor; it is not a prime-field arithmetic estimate.

The previously missing named rapid-bound route is now solved. The old
stable-Y results required only the weaker rate and need no statement changes.
An attempt to infer A-X from this theorem must be falsified at the coefficient
and operator seam: U has integer log weights, while X has von Mangoldt
weights. A smoothing identity or strict contraction is not bounded
deconvolution, and does not transfer this rate to X.

RH, A-X, B-Y and C-Schur remain OPEN. The authorized next move is the exact
original prime/total Weil-response pairing and local regularity in T09,
after the parent transfers its checked source checkpoint.
