# Direct native floor-kernel mass candidate

Status: **LEAD / finite exact arithmetic calibration**, not a Lean mass theorem.
The actual kernel is unchanged. This supplies a possible shorter proof of the
required `605/621` bound without first formalizing analytic continuation of its
zeta multiplier. It gives no estimate on an inverse or on the original X.

After `u=exp(t)`, the actual kernel measure on the cell `n≤u<n+1` is

`n(n+1-u) u^(-5/2) du`, for every integer `n≥1`.

Its proposed exact cell integral is

`(2/3) ((1-2n)/sqrt(n) + 2n/sqrt(n+1))`.

The finite cells `1,...,N` telescope to

`H_N=(2/3) (2N/sqrt(N+1) - sum_{n=1}^N 1/sqrt(n))`.

Positivity and `u≥n` give a cell upper bound `1/(2 n^(3/2))`.
The decreasing-series integral comparison would bound the tail above N by

`1/sqrt(N+1) + 1/(2 (N+1)^(3/2))`.

At N=128, exact rational enclosures of all 129 inverse square roots give

`H_128 + tail < 605/621`,

with a strictly positive rational gap recorded in
`post290/evidence/native_mass_candidate.json`. All root comparisons are
checked by squaring rational endpoints; no decimal value is acceptance input.
The older exponential envelope gives a larger tail and does not pay this
margin. This guards against relabelling an already proved loose envelope as
the required contraction.

The four analytic obligations remain **OPEN**: actual exp/log measure
substitution, the actual cell integral, countable cell decomposition with
null endpoint sets, and the per-cell/decreasing-series tail comparison. A
passing arithmetic script establishes only its rational certificate. It
cannot mark M18 complete or supply an L2 operator norm theorem. The separate
`NativeRationalCompletionLaplace.lean` candidate derives the real multiplier
of the signed pre-integer-action kernel c and its signed mass -2/3. It does
not exchange a divergent integer sum with integration of c.

The fastest falsification checks are the n=1 cell, adjacent finite-cell
telescoping, exact entering-integer endpoint conventions, tail starting at
N+1 rather than N, and a reversed square-root endpoint in the signed finite
sum. This route retains the full integer lattice and requires no modified
prime weights or negative-state assumption. RH remains **OPEN**.
