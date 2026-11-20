# Quantitative comparison of two prime-pair cuts on a single observation window

**19 November 2026. Step 4 OPEN.** The two half-pole zeros of OPICA's original source force alternating signs in the cumulative signed prime-pair curves. Unique factorization makes each jump of the ordinary-prime curve exponentially small. Together these facts permit a *data-selected cut*, a fixed positive distance from the diagonal, below which the total interaction is exponentially small. They also tie the still-open energy bound to the distance between two explicitly defined cut locations.

### Source identities and fixed widths

Use the one-copy \(j\), signed limit \(g=e^{-v/2}j(v)\), and near-pair limit \(K_\Delta\) of [the dense pair calculation](DENSE_PRIME_PAIR_CANCELLATION.md). Put \(A=2s=2/4096\) and \(Q(z)=\int e^{-zv}q_s(v)dv\). With \(m_r=\int v^r g(v)dv\),
\[
 M(z)=\int e^{zv}g(v)dv=z^2(z-1)^2 Q(1/2-z),\qquad
 m_0=m_1=0,\quad m_2=2Q(1/2)>0 .
\]
Two applications of the zero mass and Fubini give
\[
 \int_0^A \Delta^3 K_\Delta\,d\Delta
 =-\tfrac14\iint(v-w)^4g(v)g(w)dv\,dw
 =-\tfrac32 m_2^2=-6Q(1/2)^2.
\]
In particular there is an interior negative width with \(K_\Delta\le-24Q(1/2)^2/A^4\). The other calculation gives strict positivity near zero. Select fixed source-dependent \(0<l<r<A\) with \(K_l>0>K_r\). These constants precede every horizon and any hypothetical zero.

In fact the complete source forces at least three changes of sign, although one suffices here. Integrating over widths exactly gives
\[
 \int_0^A\sinh(z\Delta)K_\Delta\,d\Delta
 =-z^3(z^2-1)^2Q(1/2-z)Q(1/2+z)\quad(z>0).
\]
Take the coefficient of \(z\) at zero, then the value and first derivative at \(z=1\). The three integrals with weights \(\Delta,\sinh\Delta,\Delta\cosh\Delta\) all vanish. Divide those weights by \(\Delta\). For \(a=\sinh(\Delta)/\Delta\) and \(b=\cosh(\Delta)\), \(a\) is increasing and \(b\) is strictly convex as a function of \(a\). Indeed the ratio of their derivatives with respect to \(u=\Delta^2\) is strictly increasing: the Taylor coefficients in numerator and denominator are positive and their ratios at degree \(k\) are \(2k+3\), so the cross products of coefficients in the derivative of the quotient have positive sum. If \(K\) had at most two sign changes, one of \(1\), \(a-a_1\), or \(b\) minus its secant through the two changes would have its sign pattern up to an overall sign. The integral against the corresponding weight times \(\Delta\) would then have strict sign. This contradicts the three vanishing moments. No zero-location assumption enters here.

### Make the cut in the actual finite graph

Use the positive terminal quadrature at the integer horizon \(n\) from the [native graph deduction](NATIVE_WINDOW_GRAPH_DEDUCTION.md). For each unordered pair of *distinct ordinary primes* \(p<q\) define the single signed weight
\[
 w_{pq}=2\frac{\log p\log q}{\sqrt{pq}}\sum_i w_i
 j(t_i-\log p)j(t_i-\log q).
\]
Set \(B_n(x)=\sum_{\log(q/p)\le x}w_{pq}\), and \(S_n=B_n(A)\), the complete ordinary-prime off-diagonal. The [PNT limits](DENSE_PRIME_PAIR_CANCELLATION.md) give
\[
 B_n(l)\sim K_l e^n,\quad B_n(r)\sim K_r e^n,\quad S_n=o(e^n).
\]
The last statement uses the full zero-mass limit. Thus both levels \(0\) and \(S_n\) lie strictly between the endpoint values for all sufficiently large \(n\). Equivalently, the cumulative near and far graphs each have a crossing of zero in the *same* fixed width interval. The complementary curve is the actual sum over \(\log(q/p)>x\), and can be evaluated directly from those edges.

For pairs contributing at any node, \(p,q\in[e^{n-2\log n-s},e^{n+s}]\). Hence each weight satisfies
\[
 |w_{pq}|\le b_n=C_j n^4\log(n)e^{-n}.
\]
No two threshold ratios coincide: equality \(q/p=q'/p'\) of these fractions in lowest terms gives \(p=p'\) and \(q=q'\). This argument needs ordinary primes, so all proper powers are restored separately with the proved comparison of field norms. Sort the nonzero weights in \((l,r]\) by their distinct log ratios. Define \(x_0\) by the first downcrossing of the near curve through zero and \(x_1\) by the first upcrossing of the far curve through zero as \(x\) increases. Both use the post-jump value and include equality. In symbols, \(x_1\) is the first \(B_n(x)\le S_n\) while \(x_0\) is the first \(B_n(x)\le0\).

A crossing overshoots its level by at most one actual edge weight. Therefore
\[
 -b_n\le B_n(x_0)\le0,\qquad
 -b_n\le B_n(x_1)-S_n\le0.
\]
The first inequality is an **independent signed bound for a genuinely dense part of the actual prime graph**, selected by its own data. Every pair with \(\log(q/p)\le l\) is included, along with all other edges exposed up to \(x_0\); only the *sum over this entire selected prefix* is known to be tiny. The remaining signed task may be restricted to \(q>e^{x_0}p\), with \(q/p\le e^A\). Restoring the prefix, the diagonal and all proper powers recovers the original complete energy. The value of \(x_0\) is chosen from the near curve alone.

### What would close the gap

One sufficient arithmetic inequality is a cofinal upper \( \sum_{\log(q/p)>x_0}w_{pq}\le C_\eta e^{\eta n}\) for each \(\eta>0\). Equivalently for closing purposes one can target the following stronger geometric condition on *both* curves. If the indices of \(x_0,x_1\) differ by \(k\), telescoping and the two overshoots give
\[
 |S_n|\le(k+1)b_n .
\]
Unique rational ratios with denominators at most \(X=e^{n+s}\) have distinct numerical values separated by at least \(X^{-2}\). Since every ratio here is at most \(e^A\), successive log ratios are separated by at least \(e^{-A}X^{-2}\). It follows that
\[
 |S_n|\le C_j n^4\log(n)e^{-n}
         \left(1+e^{A+2s}e^{2n}|x_0-x_1|\right).
\]
Consequently it suffices to show, **from independent prime arithmetic**, that for every \(\eta>0\) there are arbitrarily large \(n\) where \(|x_0-x_1|\le C_\eta e^{(-1+\eta)n}\). The polynomial prefactor can be absorbed by starting with half the target exponent. The true diagonal is \(O(n\log n)\), and the exact all-prime-power norm differs from the ordinary-prime norm by \(O_j(\sqrt{\log n})\). This would force zero displacement by the merged native window theorem.

Conversely, if the zero-displacement supremum \(d\) is positive, \(S_n=\exp((2d+o(1))n)\) at every sufficiently late integer horizon. The two crossings must then be separated by at least \(\exp((1+2d-o(1))n)\) edge positions and by at least \(\exp((-1+2d-o(1))n)\) in log ratio. This is a quantitative prediction for the same cutoff and the same observed arithmetic graph. An independent estimate of the crossing separation on the \(e^{-n+o(n)}\) scale would contradict it. Ordinary PNT proves the existence of the crossings and the sharp jump bound comes from unique factorization. Neither supplies their relative locations to the required precision. Inferring this precision from the sought energy upper would be circular.

**Qualification.** The analytic reduction, the sign alternation and the proposed closing implication are paper deductions. No cofinal locking estimate for these two actual-prime crossings has been proved. [Original source](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/OriginalSincNativeSource.lean) · [Fixed native window theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154)
