# Independent first-cell mathematical review

Read-only review of current uncommitted Stage1 source bytes:

- RenormalizedCoPoisson.lean:
  `ad5546231c74696031e5980dac9b8b445d6ff388326679fd4f8fbd68dedda39f`.
- FirstCellCost.lean:
  `badaa178fb17a03b71b01bbf17372ee73688fcb5f8607cb5a47c0f55412ceeeb`.

Read the complete two proof files, frozen PUBLIC_ROOTS entries, final audited
paper CP1.7--CP1.10/scalar-phase discussion, R2 section6 and H3, the genuine
parent sinc-squared interface, and the independent ExpectedFirstCell consumers.
Read supplied genuine leaf logs `../first-cell/renorm-final.log` and
`../first-cell/first-cell-final.log`: each prints only propext, Classical.choice,
Quot.sound for its original primary root. No compiler was rerun by this reviewer;
these source hashes and logs do not replace the parent task's final same-tree
compiler/export audit. The final `../first-cell/consumer-04.log` was subsequently
read and reported GREEN exit0/warning-free by its compiler owner, covering all8
consumers including the actual-zero and falsification boundaries below.

## Finding

No material mathematical or frozen-scope defect found in the two local roots.

The finite sums are the literal inclusive positive-integer power sums. On
1<x<2 only n=1 remains. The canonical b_rho is 1/rho-1/(1-rho), so with
lambda=delta+i gamma and kappa=1/4-lambda², S_rho/b_rho is exactly
exp(-u/2)*(kappa/lambda)*sinh(lambda*u). The real and imaginary quotient
coefficients, and hence the sign of the gamma*sin(gamma*u) term, are correct.
No synthetic source or assumed desired measure occurs in these computations.

The explicit negative point keeps strict |gamma|>3pi/(2log2). The phase result
keeps delta!=0, nonzero complex scalar and strict |gamma|>2pi/log2. Its two
branches are valid: an imaginary transformed coefficient uses the quarter-cycle
points; any nonzero real transformed coefficient uses pi and2pi where the sine
term vanishes. Multiplication by the nonzero normalizing quotient is a scalar
bijection, so using normalized profiles preserves the all-scalar assertion.

The cost result keeps the entire |delta|<1/2, |gamma|>=16 domain, both signs of
gamma, delta=0 and the closed chosen u-interval. Replacing gamma by |gamma| is
proved from the actual formula. The proof bounds the small oscillatory term by1
rather than the sharper paper bound; -3|gamma|/4+1<=-|gamma|/2 still holds with
ample margin at |gamma|>=16. Thus this relaxation does not weaken the result.

The unweighted integral is the actual Lebesgue negative part in x, with the
exp(u) change-of-variable Jacobian explicitly retained. Its lower bound is
(|gamma|/2)*(u2-u1)=pi/6. The weight is the genuine parent sincSquared,
sin(pi*x)²/(pi*x)². Integer-distance geometry gives16/(9 gamma²) on the whole
interval, yielding8pi/(27 gamma²), with no missing pi, gamma or Jacobian factor.
Continuity and interval integrability are proved on the actual first cell.

## Exact scope and post-green implications

PROVED BY THE SUPPLIED LEAF EVIDENCE: the two displayed local first-cell roots
for the explicit finite-sum profile, with the stated source hashes and all
domain conditions retained. Independent compiler/whole-tree receipts remain
the authority for final formal acceptance.

OPEN: the actual global co-Poisson distribution/measure construction, local
total-variation cutoff convergence, global self-duality, growth and identification
with this profile. The three other RenormalizedCoPoisson primary roots remain
absent. No global measure is smuggled in as an assumption. The actual-zero
consumer instantiates the strip parameters from IsNontrivialZero; it does not
construct the missing measure.

DERIVED, not separately formalized here: once the actual global construction
and profile identification are proved, any correction making this density
nonnegative on the selected interval must pay at least pi/6 positive variation.
The current root proves the actual negative-part integral, not a general Jordan
correction domination theorem. Lattice-only corrections have no effect on the
off-lattice density, but a full measure-level adapter is still required.

Falsification boundaries are retained by the supplied consumers: delta=0 can
have an identically zero scalar projection, so removing the off-line phase
condition would be false; conjugate real profiles can cancel, so one cannot
sum these costs blindly over a family. The sign/cost also holds on the critical
line and therefore supplies no exclusion of off-line zeros or RH proof.

Highest-leverage next move: prove the actual global measure construction and
profile-identification bridge, then use the local quantitative cost as a
conditional correction obstruction. Any multi-zero lower bound needs a genuine
noncancellation or separation estimate. RH, Step4 and the independent closing
inequalities remain OPEN.
