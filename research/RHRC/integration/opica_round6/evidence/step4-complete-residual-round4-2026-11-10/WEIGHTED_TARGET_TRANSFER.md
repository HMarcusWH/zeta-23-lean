# Keep the actual weighted target: a weaker sufficient covariance and a paid prime-power transfer

11 November 2026. **DERIVED paper mathematics, pending independent review. No new formal theorem or closing upper.** The source h and the full Mangoldt field Z are unchanged. This note prevents the new covariance analysis from inadvertently requiring a stronger unweighted energy theorem than the original target needs.

## 1. The direct target and an auxiliary weighted energy

Retain

\[
A_Z(T)=\int_0^T e^{-(T-t)/2}|Z(t)|dt.
\]

The requested independent upper is cofinal for every positive rate, with the source and constant fixed first. For any fixed 0<gamma<1 define

\[
W_\gamma(T)=\int_0^T e^{-\gamma(T-t)}|Z(t)|^2dt.
\]

Cauchy with the two factors exp(-(1-gamma)(T-t)/2) and exp(-gamma(T-t)/2)|Z(t)| gives

\[
A_Z(T)^2\le\frac{1-e^{-(1-\gamma)T}}{1-\gamma}W_\gamma(T).
\tag{1}
\]

Thus an every-positive-rate cofinal upper for W_gamma is sufficient. For a visible zero displacement delta, an independently proved cofinal W_gamma upper with exponent strictly below 2delta would contradict the inherited eventual lower A_Z(T)>=c_rho exp(delta T), at a common sufficiently late horizon. No eventual bound is inferred from a cofinal one.

This auxiliary energy is at most the unweighted prefix energy. Its upper is not asserted equivalent to an upper for the latter. It retains every past time with a positive weight, and does not replace the source kernel, truncate history, or assume a bound on a running maximum. A direct proof of the original A_Z target remains acceptable and may be weaker still.

## 2. The exact clipped covariance survives this change of test weight

Write X=exp(T), nu_X=X^(-1) sum Lambda(n) delta_(n/X), and Delta_X=nu_X-dr on the whole positive continuum. Define

\[
K_{\gamma,-}(u,v)=\int_{-\infty}^0e^{\gamma t}h(t-u)h(t-v)dt,
\qquad F_{h,\gamma}(r,s)=\frac{K_{\gamma,-}(\log r,\log s)}{\sqrt{rs}}.
\]

The literal source starts after zero, so the same change of variables as in COMPLETE_COVARIANCE_ATTEMPT.md gives exactly

\[
\boxed{\frac{W_\gamma(\log X)}X
=\iint F_{h,\gamma}\,d\nu_Xd\nu_X
=\iint F_{h,\gamma}\,d\Delta_Xd\Delta_X.}
\tag{2}
\]

Every prime power and every partial terminal pulse remains. The continuum row cancellation follows before any estimate from

\[
\int_0^\infty s^{-1/2}h(t-\log s)ds
=e^{t/2}\int e^{-v/2}h(v)dv=0.
\]

The extra factor exp(gamma t) is independent of s and leaves this equality intact. The complete positive continuum, including values below one, is necessary.

The support remains r,s<=exp(S), with exp(-2S)r<=s<=exp(2S)r. Since exp(gamma t)<=1 on the clipped time interval, Cauchy gives |F_(h,gamma)(r,s)|<=||h||_2^2/sqrt(rs). The same cumulative Chebyshev estimate therefore controls the small-coordinate absolute integral by C_h epsilon, uniformly in X. This justifies all signed product integrals and the continuum subtraction; it is not a formal exchange of divergent pieces.

The diagonal contribution D_(gamma,T) is nonnegative and bounded by the already paid O_h((1+T)^2) unweighted diagonal. If P_(gamma,T) and N_(gamma,T) denote the positive and negative parts of the complete ordered off-diagonal, then

\[
W_\gamma(T)=D_{\gamma,T}+P_{\gamma,T}-N_{\gamma,T}.
\tag{3}
\]

Ordinary PNT, product-measure convergence away from zero, and the uniform small-coordinate estimate give

\[
P_{\gamma,T}=c_{h,\gamma}e^T+o_h(e^T),\qquad
N_{\gamma,T}=c_{h,\gamma}e^T+o_h(e^T),\qquad c_{h,\gamma}>0.
\tag{4}
\]

For completeness, strict positivity requires no unsupported sign claim about a weighted autocorrelation: F_(h,gamma)(r,r)>0 wherever a nonzero portion of the pulse is before zero, hence it is positive on an open set. Its total continuum integral is zero by row cancellation, so its negative part also has positive integral. Both are finite by the preceding bounds. The vanishing normalized diagonal transfers these continuum limits to the ordered off-diagonal.

The sufficient target is therefore the same kind of signed discrepancy, but for this weaker weighted observable:

\[
\forall\eta>0\ \exists C_{h,\gamma,\eta}\ \forall R>1\ \exists X\ge R:
\quad\iint F_{h,\gamma}\,d\Delta_Xd\Delta_X
\le C_{h,\gamma,\eta}X^{-1+\eta}.
\tag{5}
\]

No estimate of (5) is established here. In particular the difference of the two known order-X terms is retained, rather than either term being declared small. For fixed gamma, the same full-history rough-echo pairing from ROUGH_ECHO_NATIVE_PAIRING.md may be weighted by exp(-gamma(T-t)); its independent absolute bound remains valid because this weight is at most one. Its mixed correlations must receive the same weight. No coercive comparison follows merely from weighting.

## 3. Every proper prime power has a uniform, paid cost in this target

Let J denote the literal prime-only field and R_2=Z-J the sum of all proper prime-power pulses, with their actual coefficients log(p)/p^(k/2). This is an exact decomposition, not a source substitution.

Chebyshev's theta bound gives

\[
|R_2(t)|\le C_h e^{-t/2}
\sum_{2\le k\le (t+S)/\log2}\vartheta(e^{(t+S)/k})
\le C_h[1+(1+t)e^{-t/6}].
\]

Constants absorb the fixed source support factors. The k=2 term is bounded; all k>=3 terms have the displayed decaying bound, and the compact initial interval is finite. Consequently |R_2(t)|<=C_R for every t>=0. Hence

\[
|A_Z(T)-A_J(T)|\le 2C_R(1-e^{-T/2})\le2C_R,
\tag{6}
\]

and, for fixed gamma>0,

\[
\|R_2\|_{\gamma,T}^2:=\int_0^T e^{-\gamma(T-t)}|R_2(t)|^2dt
\le C_R^2/\gamma.
\tag{7}
\]

For every fixed epsilon>0 the full mixed term is paid through

\[
W_{\gamma,Z}(T)\le(1+\epsilon)W_{\gamma,J}(T)
+(1+\epsilon^{-1})C_R^2/\gamma,
\tag{8}
\]

and the reverse inequality follows by J=Z-R_2. Neither separate mixed quadratic is declared bounded. These inequalities make the every-positive-rate cofinal weighted target equivalent for the literal prime field and the complete Mangoldt field, while preserving all proper powers through an explicit cost.

## Qualification and next use

This note strengthens the bookkeeping, not the arithmetic upper: it allows attacking a weaker sufficient weighted covariance and pays the ordinary-prime/full-field transfer at constant cost. It does not prove cancellation of the remaining large signed terms. The exact full-source canonical connection, finite physical Gram metric, source moments, and completion histories remain as established in the preceding notes.

Sources: COMPLETE_COVARIANCE_ATTEMPT.md and COVARIANCE_REVIEW.md for the unchanged field, clipped kernel and Chebyshev/PNT arguments; NATIVE_SIGNED_TARGET.md in the round-two package for A_Z and its exact closing consumer; the current exact source head is b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7. No new Lean or CI run was performed. Step 4 and RH remain OPEN.
