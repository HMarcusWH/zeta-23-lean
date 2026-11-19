# Read-only arithmetic review of A07–A09B

Reviewed 10 November 2026. Scope: six complete mathematical notes and four complete execution summaries, fetched from Final gate part3. No repo or Drive edits, compiler runs, historical experiments, or new arithmetic search were performed. This is a paper-proof audit, conditional on the inherited source/zero-completion inputs explicitly named in the notes; it is not a fresh validation of that entire inherited analytic chain.

## Verdict

The main displayed deductions survive this bounded audit. They make the obstruction more precise and remove unnecessary arithmetic bookkeeping, but do not prove any independent all-positive-exponent upper for the actual prime field. No new Lean theorem became PROVED.

One endpoint qualification needs repair in the A09 continuous comparison-density falsifier (§6), if its “same mask” is intended to include the exact integer upper cutoff. It does not affect the genuine-prime square-root localization theorem. The correction below preserves the falsifier's exponential-growth conclusion.

## What actually changed since the older complete Type II target

1. **A07 pays a whole signed model, not genuine prime discrepancy.** For the fixed source h, phi(x)=x^(-1/2)h(-log x) has zero integral. Its autocorrelation F consequently has zero half-line integral. The explicit singular-series partial-sum discrepancy 0 <= y-A(y) <= 22(1+log_+ y)^3, composed with that zero integral and full prefix kernel, gives |M_h(T)| <= 11 V_h[(1+T)^4-1]. All shifts and both pair orders remain. The lower side of the exact genuine residual is therefore polynomial; its upper side remains the old arithmetic obstacle, equivalent through the paid Type I/diagonal terms to the old frozen-cutoff covariance target. See 63 and 64.

2. **A07 removes all small prime bases together with their mixed terms, at the original subexponential cutoff.** The at-most-one-active-power-per-base fact follows from 2S < log 2. It controls the difference of complete energies at H_T=floor(exp(sqrt(T))). It also pays every odd shift. This is an actual arithmetic support deduction; it does not apply to raw Type II coefficients as if each had one prime base.

3. **A08 makes the power-field issue exact.** The proper-power field tends to 1/32: the square density contributes one half of integral h=1/16, while all higher powers have an absolute O_h((1+t)^2 exp(-t/6)) envelope. The bounded power field can still have an exponentially large absolute mixed interaction with the prime field under a hypothetical off-line zero. Relative energy comparisons remain valid; a cheap additive absolute mixed-term budget does not follow. See 65.

4. **A08 exposes the stronger weighted input functional already inside completion.** The norm lower comes from the retained terminal convolution estimate before Cauchy–Schwarz, not by reversing an L2-to-L1 implication. Conditional on the inherited centered zero-jet identity, it gives an eventual lower at every sufficiently late real horizon for A_Z(T)=integral_0^T exp(-(T-t)/2)|Z(t)|dt, for every finite zero multiplicity. See 66.

5. **A09 removes the zero-dependent cutoff parameter.** Set N_T=floor(exp(T+S)), B_T=floor(sqrt(N_T)), and retain ordinary primes B_T<p<=N_T. Every surviving base has p^2>N_T, exactly. Deleting the complementary prime-base field costs at most (1/2)||h||_infinity exp(S) T(T+S) in weighted L1. That polynomial cost is negligible against every hypothetical exp(delta T) lower, with the same mask for all delta>0. Only the threshold depends on the zero. This is a genuine simplification beyond A08's alpha in (1/2,1/2+delta). See 73.

6. **A09B identifies an exact local diagnostic, but supplies no arithmetic upper.** With E(s)=exp(-s/2)(theta(exp(s))-exp(s)) and g=h'+h/2, P(t)=integral g(u)E(t-u)du for t>=S. The two source moments annihilate the weighted two-dimensional span of exp(-u/2),u exp(-u/2). Projecting E onto that span gives |P(t)|^2 <= W V_h(t). A cofinal subexponential upper for integral V_h is sufficient and potentially stronger than the filtered-energy target; it is not shown easier or equivalent. The comparison density defeats the generic positivity/PNT argument. See 83.

## Checks performed on the displayed proofs

- Checked singular-series parity normalization, Euler-product cancellation, floor error plus divisor-tail cost, and the constant 22.
- Checked the change of variables and half-line autocorrelation integral; the source zero moment removes the continuous main without absolute-value splitting.
- Checked initial and terminal prefix treatment, full ordered pair multiplicity, the exact residual identities, and both directions of the paid comparison to the old Type II target.
- Checked small-base complete mixed-term deletion, prime-square Jacobian 1/2, higher-power exponent -t/6, weighted completion constants, and the signed-versus-absolute counterexample.
- Checked the floor at a perfect square, collar factor exp(S), weighted L1/L2 direction, Abel sign and factor 1/2, diagonal cost, same-horizon quantifier order, and the local weighted projection.
- No arithmetic upper is inferred from the finite control counts in the execution summaries; those programs were not rerun in this review.
- No new full-read credit is claimed for the original Single Source ZIP, its inherited Lean interfaces, or numerical archives referenced by these notes.

## The exact remaining arithmetic theorem

For the original fixed h, S=1/2048, define

N_T = floor(exp(T+S)),
B_T = floor(sqrt(N_T)),
omega_T(t) = exp(-(T-t)/2),

P_T^square(t) = sum_{B_T<p<=N_T} (log p)/sqrt(p) h(t-log p).

Let E^square(T)=integral_0^T omega_T(t)|P_T^square(t)|^2 dt. Retain the exact diagonal D^square(T) and the same full original singular-series cumulative model, time-weighted by Abel integration:

M_h^omega(T) = M_h(T) - (1/2) integral_0^T omega_T(t)M_h(t)dt.

Define the complete signed residual R^square=E^square-D^square-M_h^omega. The independent sufficient supplier still needed is:

**For every eta>0, there exists C_eta>0 such that for every R>0 there exists T>=max(R,16) with R^square(T)<=C_eta exp(eta T).**

C_eta must be fixed before the chosen horizon. Every term, both orders, the moving mask, and the terminal collar stay in the expression. A fixed positive exponent saving does not cover zeros with arbitrarily small positive displacement.

The weaker sufficient target is the same every-positive-exponent, cofinal upper for A_{P_T^square}(T). Its conditional lower grows as exp(delta T), while E^square has a lower of order exp(2 delta T). Either upper must use genuine additional arithmetic information; neither has been proved.

The mask comparison is paid in weighted L1 only. No additive weighted-energy bound for the deleted sector is available from it. The new route is not asserted equivalent to the older unweighted residual at H_T=exp(sqrt(T)). A09B's unweighted local-variance supplier is yet another sufficient contract, not an automatic estimate for this masked weighted target.

## One endpoint qualification in the A09 falsifier

The report defines the genuine masked field using both cutoffs:

> P_T^square(t) = sum_{B_T<p<=N_T} (log p)/sqrt(p) h(t-log p).

In §6 it says:

> “On [T−1,T] ... the entire source support lies above B_T ... The masked comparison field equals the full field there.”

This checks the lower cutoff only. For the continuous comparison measure, if “masked” means the same **B_T < x <= N_T**, full source support at t=T extends to exp(T+S), which can exceed N_T by a nonzero fractional part. Unlike an integer prime sum, a continuous density has mass in that interval. Equality with the full field on all of [T−1,T] is therefore not supplied by the stated argument. If the comparison was intended to use only a lower mask, that must be said; it is not literally the same upper-cutoff object.

A direct repair keeps the intended two-sided mask and uses the shorter late interval [T−1,T−1/2]. For T>2+3S:

- The lower support endpoint satisfies t-S >= T-1-S > (T+S)/2 >= log B_T.
- Let X=exp(T+S). Then X>exp(2), and X(1-exp(-1/2))>1. Hence the upper support endpoint is at most exp(T-1/2+S)=X exp(-1/2) <= X-1 <= floor(X)=N_T.

Thus equality with the full comparison field is exact on that shortened interval. For a=1/2+2delta, the corrected lower is

integral_0^T omega_T(t)|Ptilde_T^square(t)|^2dt
>= epsilon^2 H(delta)^2 exp(2delta T) [exp(-a/2)-exp(-a)]/a.

The bracket is a fixed strictly positive constant. The falsifier's exponential-growth conclusion survives. This is a proof-detail correction to a generic comparison diagnostic, **not** a counterexample to the genuine-prime localization or the residual definition, and not a proof of an actual prime upper.

## What should be done next

1. Correct or explicitly qualify the continuous comparison mask endpoint, retaining the floor and the exact scope of the diagnostic.
2. Concentrate mathematical work on an independent actual-prime estimate for the precise weighted residual or weighted L1 supplier. Any proposed input must distinguish actual primes from the positive PNT-strength comparison measure; positivity, source moments, recoverability and the paid singular-series model alone have already been tested and are insufficient.
3. Treat a proof of the required estimate as mathematical work distinct from formalization. The weighted completion consumer, exact source binding, floor split, norm bounds, Abel model, same-horizon contradiction and actual RH claim must subsequently be checked by the formal gates.
4. Keep finite K3 and finite response-rank work separate from this all-scale supplier. Those may support alternative native routes, but they do not discharge this arithmetic upper merely by sharing the word “positivity.”

## Execution-summary reconciliation

The A07–A09/A09B execution summaries agree that these arithmetic results are paper-level and that the PR head/formal scope were unchanged. A09B's internal title says A09 and retains a historical “publication pending” state; its presence in the live folder does not turn that old execution sentence into a fresh absence claim. Likewise A09 and A09B credit the same three historical content hashes; this review does not add their reading counts.

The reviewed summaries report finite-control passes, rather than new analytic proof authority. Their CI and large numerical-archive claims are inherited evidence in this child review, not independently rerun checks. The parent review handles live repository identity, numerical frontier and A10 response ranks.

**Final disposition: valid new localization and signed-model deductions, one endpoint qualification to repair, genuine arithmetic upper OPEN, formal weighted consumer OPEN, Step 4/RH OPEN.**
