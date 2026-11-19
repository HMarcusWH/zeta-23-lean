# Exact rate of the separation of two actual prime cutoffs

**Paper result, 19 November 2026.** There is a source-fixed interval of widths on which the signed separation of the two arithmetic crossings measures the genuine zero-displacement supremum \(d\). This strengthens the earlier one-sided implication to a two-sided growth-rate identity. It still leaves the independent all-positive-exponent arithmetic upper open.

Use the original one-copy prime field, with the ordinary-prime part \(P_1\), the frozen positive quadrature on \([n-2\log n,n]\), the ordinary-prime cumulative \(B_n(x)\) over \(p\ne q\) with \(|\log(q/p)|\le x\), and the complete off-diagonal \(S_n=B_n(2s)\). Here \(x\) is the physical log ratio, \(s=1/4096\) and \(n\) is an integer horizon. Write \(W_n=\sum_i w_i e^{t_i}\sim e^n\). Work on the fixed physical interval \(J=[s(1-10^{-8}),s]\), which [the source computation](TRANSVERSE_NATIVE_CUT.md) proves has a unique simple zero \(\Delta_*\) of its continuum cumulative \(K\), with \(K'<0\) throughout. Use only the first crossing in this interval. Earlier crossings elsewhere in the full width range are irrelevant. The quantities \(x_0\) and \(x_1\) are the first downcrossings of \(B_n\) through levels \(0\) and \(S_n\), respectively. Equivalently \(x_1\) is the first upcrossing of the complementary far-pair sum through zero. Native rate and source restoration · Earlier cut definition and jump bounds

The conclusion is
\[
 \boxed{\displaystyle
 \lim_{n\to\infty}\frac{\log(1+e^n|x_1-x_0|)}{2n}=d .}
\]
If \(d>0\), there is also a signed calibration
\[
 \boxed{\displaystyle \frac{S_n}{W_n(x_1-x_0)}\ \longrightarrow\ K'(\Delta_*)<0 .}
\]
The estimates concern the native source at the same terminal window and arithmetic sample nodes. The proof combines an ordinary-prime pair annulus with a zero-density estimate, the independently established native energy rate, and the exact box structure of the source.

## Uniform location in the transverse interval

Let \(P_{\mathrm{err}}(X)=\sup_{cX\le y\le CX}|\vartheta(y)-y|/X\) for absolute fixed \(c,C\) covering the compact ratios used here. Uniformly in \(x\in[0,2s]\), the ordinary-prime cumulative at time \(t\), divided by \(X=e^t\), differs from \(K(x)\) by \(O_j(P_{\mathrm{err}}(X)+(1+t)/X)\). To see this, the difference \(r_t\) between the normalized signed prime measure and \(e^{-v/2}j(v)dv\) has interval-discrepancy \(O_j(P_{\mathrm{err}}(X)+(\log X)/X)\) by one partial summation. The signed prime measure has bounded total variation by Chebyshev. Integrate the inner interval-discrepancy against this finite measure. For the remaining outer error the test \(v\mapsto\int_{v-x}^{v+x} e^{-w/2}j(w)dw\) has uniformly bounded variation. The removed diagonal is \(O_j((1+t)/X)\).

It follows that \(B_n(x)/W_n\to K(x)\) uniformly and \(S_n/W_n\to0\). Both crossings exist and tend to \(\Delta_*\), even though \(B_n\) itself is a signed staircase. Indeed before any fixed neighborhood of \(\Delta_*\) the continuum cumulative is bounded strictly above zero on \(J\) up to that neighborhood, and immediately beyond the neighborhood it is bounded strictly below zero. Uniform convergence handles all first crossings. The external zero ceiling \(\theta=0.8733458561\ldots\) also gives \(P_{\rm err}(X)\ll_\epsilon X^{\theta-1+\epsilon}\) by the truncated explicit formula, zero counting and prime-power removal. Dividing by the *exact* \(W_n\) gives \(|x_i-\Delta_*|\ll_{j,\epsilon}\exp(-(1-\theta-\epsilon)n)\). The normalized levels satisfy this bound as well. The stronger result about their mutual separation requires finer information about short intervals.

## A mean-square estimate at the scale of the actual displacement

Let \(\alpha\) be fixed with \(2d/3<\alpha<1\). The external ceiling ensures \(d<1/2\). Uniformly for \(0<\lambda=o(1)\) with \(H=\lambda X\ge X^\alpha\),
\[
 \int_{cX}^{CX}
 \big|\psi((1+\lambda)y)-\psi(y)-\lambda y\big|^2dy
 \ \ll_{c,C,\alpha,d}\ XH^2 X^{-\delta}
 \tag{1}
\]
for some \(\delta>0\). This use of \(d\) imposes no additional zero-free hypothesis. By its definition all zeta zeros have real part at most \(1/2+d\). We explicitly keep this parameter on both sides of the final rate calculation.

Here are the details following the explicit-formula second-moment argument of Guth and Maynard. Take \(T=X^{1-\alpha+\kappa}\) with sufficiently small fixed \(\kappa>0\). The truncation error is \(O(X\log^3 X/T)=O(H X^{-\kappa}\log^3 X)\). Each zero has coefficient \(((1+\lambda)^\rho-1)/\rho=O(\lambda)\). Integration of \(y^{\rho_1+\overline{\rho_2}}\) costs \(O(X^{1+\beta_1+\beta_2}/(1+|\gamma_1-\gamma_2|))\), uniformly over nontrivial zeros. The row sum of the denominator factors over \(|\gamma|\le T\) is \(O(\log^2 T)\) by the local zero count with multiplicities. The inequality \(2X^{\beta_1+\beta_2}\le X^{2\beta_1}+X^{2\beta_2}\) now bounds the normalized mean-square error, apart from the truncation term, by
\[
 O\left(\log^C X\;\sup_{1/2\le\sigma\le1/2+d} X^{2\sigma-2}N(\sigma,T)\right)+O(X^{-1}T\log^C X).
\]
Use bins of width \(1/\log X\) in \(\beta\). The last term covers zeros left of the half-line. For right-hand bins use Ingham's density estimate \(N(\sigma,T)\ll T^{3(1-\sigma)/(2-\sigma)+o(1)}\). The exponent of \(X\) is at most
\[
 (1-\sigma)\left(\frac{3(1-\alpha+\kappa)}{2-\sigma}-2\right)+o(1)<-\delta'
\]
uniformly, since \(3(\alpha-\kappa)>2d\) and \(1-\sigma\ge1/2-d>0\). Choose also \(\kappa<\alpha\). This proves (1). One can obtain an unrestricted but coarser version for \(H\ge X^{2/15+\epsilon}\) directly from Guth–Maynard. [Ingham's density estimate](https://doi.org/10.1093/qmath/os-11.1.201) · [Guth–Maynard, equations (1.2) and (13.4) and the proof in §13.2](https://arxiv.org/html/2405.20552#S13.SS2)

## Sample the actual distinct-prime strip

Fix a physical \(u\in J\), and take \(h\to0\) with \((e^h-1)X\ge X^\alpha\). For \(p\asymp X\) in the original pulse, the permitted \(q>p\) have \(e^u p<q\le e^{u+h}p\). Set \(\lambda=e^h-1\) and \(H=\lambda X\). The bases \(e^u p\) are separated by at least one. Replacing any base \(y\) by a point within distance one changes the short-interval discrepancy in (1) by \(O(\log X)\). The intervals of length one starting at the bases are disjoint. Cauchy–Schwarz and (1) imply
\[
 \sum_{p\asymp X}
 \left|\psi((1+\lambda)e^up)-\psi(e^up)-\lambda e^up\right|
 \ll XH X^{-\delta/2}+X\log X .
\]
This estimate is uniform in the starting width, including adaptively selected widths. To pass from \(\psi\) to \(\vartheta\), there are \(O(\sqrt X\log X)\) proper powers in the full compact-ratio range. Each such integer belongs to at most \(O(1+H)\) of these intervals by their separated bases. Their total cost with logarithms is \(O(\sqrt X(1+H)\log^2 X)\). All these errors remain \(o(XH)\) even after fixed powers of \(\log X\).

In the inner prime sum one can replace \(j(t-\log q)/\sqrt q\) by \(j(t-\log p-u)/\sqrt{e^up}\), at pointwise cost \(O_j(h/\sqrt X)\). The absolute prime mass over these intervals, weighted at the outer primes by \(\log p\), is \(O(XH)\) by the preceding estimate and \(\sum_{p\asymp X}\log p=O(X)\). Consequently the replacement costs \(O_j(hH)\) in the actual unnormalized pair sum. Replacing the inner \(\vartheta\) increment by \(\lambda e^u p\) then costs \(o_j(H)\). With \(v=t-\log p\) the main term becomes
\[
 2\lambda e^{u/2}\sum_p(\log p)j(v)j(v-u).
\]
Ordinary PNT for the outer sum, uniformly in \(u\) on the compact interval, and the identity \(g(v)=e^{-v/2}j(v)\) give
\[
 B_t(u+h)-B_t(u)
 = X h\left(2\int g(v)g(v-u)dv+o_j(1)\right)
 = X h(K'(u)+o_j(1)).
 \tag{2}
\]
Here \(B_t\) denotes the single observation at \(t\), with the factor two for the two orders. Every distinct ordinary-prime pair in the strip is included. With \(t_i\ge n-2\log n\), (2) applies after positive summation over the whole quadrature whenever
\(h\ge\exp((-1+\alpha')n)\) with any fixed \(\alpha'>2d/3\), using a fixed intermediate \(2d/3<\alpha<\alpha'\) to absorb the polynomial loss at the earliest node. The multiplier \(X\) becomes \(W_n\). For \(h<0\) interchange the endpoints.

## Complete the calibration

By the merged native window theorem and the paid diagonal and prime powers, if \(d>0\) then \(S_n=\exp((2d+o(1))n)\) at all late horizons. The earlier determinant-spacing and jump estimate shows
\[
 |S_n|\ll_j n^4\log n\,e^{-n}(1+C_s e^{2n}|x_1-x_0|).
\]
Thus \(|x_1-x_0|\ge\exp((-1+2d-o(1))n)\). Choose \(2d/3<\alpha'<2d\). The actual gap then exceeds the required strip resolution. At each crossing the overshoot is \(O_j(n^4\log n\,e^{-n})\), so \(B_n(x_1)-B_n(x_0)=S_n+O_j(n^4\log n\,e^{-n})\). Since both endpoints tend to the same simple root, (2) proves the signed calibration and the rate formula.

If \(d=0\), \(|S_n|\le e^{o(n)}\) in the usual upper-rate sense, by the native time-window theorem and the same diagonal and higher-power bounds. For any fixed \(0<\alpha'<1\), either \(|x_1-x_0|<e^{(-1+\alpha')n}\) or (2) applies and the fixed negative slope gives \(|x_1-x_0|\ll (|S_n|+o(1))/W_n\). This proves upper rate zero on all horizons. Nonnegativity of \(\log(1+e^n|x_1-x_0|)\) finishes the proof. All constants are fixed before taking the indicated horizon limit.

**Remaining arithmetic.** The native displacement now has an exact second reading from the horizontal separation of the cumulative graphs. The short-interval estimate proves that the cut slope stays genuinely negative on the scale of any putative exponential signal. It does not bound the level offset \(S_n\) at subexponential size independently. To close Step 4 by this route it still suffices, and is now necessary, that for every \(\epsilon>0\) there are arbitrarily large native common horizons with \(|x_1-x_0|\le \exp((-1+\epsilon)n)\). The comparison of cut locations is an analytic paper deduction, with no new formal RH or zero-free theorem.
