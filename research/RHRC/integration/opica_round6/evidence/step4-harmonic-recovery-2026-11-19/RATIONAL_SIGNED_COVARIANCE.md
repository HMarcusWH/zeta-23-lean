# A single rational signed covariance on the native Möbius labels

**DERIVED on paper, 19 November 2026.** One integer cutoff determines this graph. Its weights are rational. There is no frequency to select, no optimization over test vectors and no choice of cutoff depending on a hypothetical zero's height in the definition. The analytic argument below shows why this particular graph detects the obstruction. The independent arithmetic upper for it remains **OPEN**.

## Definition and precise target

Take an integer \(X\ge2\). Put \(s=\lceil\sqrt{\lceil\log_2 X\rceil}\rceil\). Keep all integers \(q\) with \(q^{100}>X^{99}\) and \(q\le X\); attach \(\mu_6(q)=\mu(q)\mathbf1_{(q,6)=1}\). At shell \(k=\lfloor\log_2 q\rfloor\), use bins of width \(w=2^{\max(0,k-s)}\) anchored at integer multiples of \(w\). The shell and exclusive upper endpoint \(Q=w(\lfloor q/w\rfloor+1)\) identify the bin. In it \(q<Q\le2q\); asymptotically \(0<(Q-q)/Q\le2^{-s}\) throughout the terminal shells. Define
\[
 \mathcal C(X)=2\sum_{\mathcal I}
  \sum_{\substack{q<r\ \mathrm{in}\ \mathcal I\\\gcd(q,r)^{100}<X}}
  \mu_6(q)\mu_6(r)\frac{Q}{Q^2-2(Q-q)(Q-r)} .
\]
All comparisons, labels and weights are computable with integer arithmetic. For \(B=\sup_\rho\Re\rho\) over nontrivial zeta zeros the conclusion is
\[
 \lim_{X\to\infty,\ X\in\mathbb N}
 \frac{\log(1+\max\{0,\mathcal C(X)\})}{\log X}=2B-1.
\]
Thus the remaining sufficient upper is: **for every \(\epsilon>0\) there are arbitrarily large integer \(X\) with \(\mathcal C(X)\le X^\epsilon\)**. This is one signed statistic, with a one-sided bound. No finite table settles that quantifier.

## Why the rational weights capture the true response

In a bin write \(z_q=(Q-q)/Q\in[0,1/2]\), and use \(z^0=1\). The full local form
\[
 A_{\mathcal I}=\frac1Q\sum_{n\ge0}2^n
    \left|\sum_{q\in\mathcal I}\mu_6(q)z_q^n\right|^2
 =\sum_{q,r\in\mathcal I}\mu_6(q)\mu_6(r)
       \frac{Q}{Q^2-2(Q-q)(Q-r)}
\]
is nonnegative. The equality is a convergent geometric series for every pair in a finite set. For fixed real frequency \(t\), let \(c_n(t)\) be the Taylor coefficients of \((1-z)^{-1/2-it}\). Uniformly for \(t\) in any fixed compact interval \(J\), Cauchy's formula on \(|z|=3/4\) gives \(\sup_{t\in J}\sum |c_n(t)|^2/2^n<\infty\). Expanding the **original** Dirichlet field in this bin and applying Cauchy–Schwarz therefore gives
\[
 \left|\sum_{q\in\mathcal I}\mu_6(q)q^{-1/2-it}\right|^2
 \le C_J A_{\mathcal I}\qquad(t\in J).
\]
The expansion is exact and applies to the original signs. Its constant can depend on the fixed frequency band. It is independent of the bin and horizon.

Let \(b=B-1/2>0\) hypothetically. For each sufficiently small loss \(\lambda>0\), the fixed-band theorem supplies a single fixed interval where the full energy is \(\gg X^{2b-\lambda}\) at all sufficiently large \(X\). The signed partial-summation bound in PRIMITIVE_BAND_COVARIANCE.md pays the portion \(q\le X^{0.99}\), whose norm is \(O_\eta(X^{0.99(b+\eta)})\). The terminal field is the sum of \(O(2^s\log X)=X^{o(1)}\) bin fields. Cauchy–Schwarz across bins, then the preceding exact comparison, gives \(\sum_{\mathcal I}A_{\mathcal I}\gg X^{2b-\lambda-o(1)}\) for \(\lambda<0.02b\) and sufficiently small \(\eta\). Although the detecting band may depend on the requested loss, every such lower is now an estimate for the **same** rational form. Fixed-band proof

For the opposite bound, summation against the monotone weight \(z_q^n\) in an interval costs at most a constant times \(2^{-n}\) times the largest absolute Möbius prefix there. The arithmetic estimate \(M_6(u)=O_\eta(u^{B+\eta})\) gives \(A_{\mathcal I}\ll_\eta Q^{2b+2\eta}\sum_{n\ge0}2^{-n}\). Summing the bins costs \(X^{o(1)}\).

## Exact-GCD removal

Group the ordered expansion of each weighted moment square by \(d=\gcd(q,r)\). Expand coprimality of the primitive labels by Möbius inversion at \(e\), exactly as in the signed band proof. For each \(n,d,e\), the new inner sum is over consecutive \(k'\) with \(dek'\in\mathcal I\), coprime to \(6de\), and has weight \(z_{dek'}^n\). Restricted partial summation gives
\[
 \left|\sum_{k'}\mu(k')z_{dek'}^n\right|
 \ll_\eta 2^{-n}(de)^\eta(Q/(de))^{B+\eta}.
\]
This uses the usual restricted Mertens upper, proved by Euler-factor removal, and monotonicity of the exact weights. The square includes a factor \(1/Q\); the outer coefficient magnitudes are at most one. Thus the contribution of all \(d\ge D=X^{0.01}\) is at most
\[
 O_{\eta,b}\!\left(
 Q^{2b+2\eta}\sum_{n\ge0}2^{-n}
 \sum_{d\ge D} d^{-1-2b}\sum_{e\ge1}e^{-1-2b}
 \right)=O_{\eta,b}(X^{2b+2\eta}D^{-2b})
\]
per bin when \(b>0\). The sums in the actual expansion are finite in \(d,e\). For \(b=0\), retaining their cutoffs \(de\le Q\) costs at most \(O(\log^2(2X))\), and every contribution above is \(O_\epsilon(X^\epsilon)\). The diagonal of the complete form is \(O(\sum_{q\le X}1/q)\), since \(1/(1-2z_q^2)\le2\). Subtract the large-GCD terms, followed by the diagonal still present. The exact remaining form is \(\mathcal C(X)\). The removed terms are smaller by a fixed power when \(b>0\). This proves the displayed limit after taking \(\lambda\) arbitrarily small, including the case of an unattained supremum. For \(b=0\) the baseline one gives the lower logarithmic exponent zero.

## A second check using the trigonometric graph

The earlier same-bin covariance \(C_j(X)\) uses width \(\exp(-\sqrt{\log X})\) and the sinc kernel on \([j-5,j+5]\). Even in that construction \(j=0\) alone suffices. Demodulate by a bin endpoint. On any fixed \([-M,M]\), degree \(\lceil4\sqrt{\log X}\rceil\) Taylor expansion in the frequency variable has uniform absolute error at most \(2\sqrt X\exp(Mh)(Mh)^{n+1}/(n+1)!=O_M(X^{-2})\), \(h=\exp(-\sqrt{\log X})\). A polynomial's \(L^2[-M,M]\) norm costs at most \(C_M^{n+1}\) times its \(L^2[-5,5]\) norm: expand in orthonormal Legendre polynomials on the latter interval and use their exponential bound on the larger fixed interval. The aggregate factor is \(X^{o(1)}\); summing the squared errors over \(X^{o(1)}\) bins is harmless. Therefore the same near-full lower transfers to the single zero-centered *sum of within-bin energies*. Remove the large-GCD sector **after** this transfer. A single point evaluation of the whole Dirichlet polynomial gives a different observable. The finite zero-centered sinc covariance was positive at \(X=1045,8494\) and negative at \(2048\). Sinc-sector proof

The rational formula above also bypasses frequency extrapolation. The proof of its lower requires the complete original signed field and its zero detector; replacing the Möbius coefficients would discard that premise. The arithmetic problem now is controlling the signed correlations of the actual high-primitive neighbors. Taking absolute values, retaining only a diagonal, or checking individual finite cutoffs has not supplied the required upper.
