# Scalar prime deficit — source-exact first formalization stage

Source.lean defines the exact arithmetic R11 large-prime residual from the
November 20 OPICA Round11 paper: dyadic U(N), fixed z(N)=U(N)^(2/3),
discrete m_p=(p+1)/(2p), complete small-prime center C_z, actual p with
strict z(N)<p<=N, and integer-division fractional part. All integral and
integer windows retain inclusive final endpoints.

The two OPEN targets are LargePrimeDeficitSubpower and
MissingPrimeDeficitToLiteralGBridge. The code defines a literal von Mangoldt G
candidate using Mathlib's Euler-Mascheroni constant; it does not assert that
this new G is definitionally identical to the external proof's Deduction.G.
There is no assumed missing bound, nor an RH theorem, axiom or sorry.

This branch is a SEPARATE source epoch from the rough-Mobius stopped-cut
search. It does not identify the two arithmetic sources. To promote the
conditional bridge, prove exact R12 with all small-prime fluctuation,
proper-prime-power and integer-rounding corrections, the large-sieve
full-window estimate, and an independent same-target type check. Only then
can a genuine source-specific large-prime upper feed the prior conditional
numeric G criterion. An exact nonnegative-energy lemma is support only.

The next CI first proves only that the definitions compile against the
native Lean 4.33.0-rc2 pin. No full 11-lane acceptance is implied.
