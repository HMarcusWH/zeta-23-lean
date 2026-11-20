# The deterministic cone complement has signed covariance of exponent one

**DERIVED on paper, unconditionally.** Fix \(0<\kappa<.01\), \(Z=X^\kappa\), \(y=\lceil\log_2 X\rceil^2\), and \(P_y=\prod_{p\le y}(1-p^{-1})^{-1}\). Retain the all-rough Möbius signs on their original dyadic tree. Write \(S=\{q:q/P^+(q)\le Z\}\) for the deterministic cone on its nonzero labels, and \(R\) for the full complement. On every whole terminal shell \([U,2U)\) with \(U\asymp X\),
\[
 \sum_{q\in S\cap[U,2U)}\mu_y(q)
 = \frac{P_y U}{(\log U)^2}
 \left(1+O_\kappa\left(\frac{1+\log y}{\log U}\right)\right).
\]
The signed total of \(R\) in the shell has the opposite main term. The genuine primitive covariance \(C(R)\) is consequently positive of order \(X^{1-o(1)}\) at **every** sufficiently large cutoff. This supplies a falsification check on replacing a source-balanced selector by a cutoff on largest-prime cofactors. The deterministic complement cannot by itself satisfy a cofinal subpower upper. [Native dyadic graph](../step4-harmonic-recovery-2026-11-19/DYADIC_TREE.md) · [Earlier signed gcd analysis](DETERMINISTIC_CONE_GCD.md)

## Prime dilation and the nonzero coefficient

Write \(\mu_y(a)=\mu(a)\mathbf 1_{P^-(a)>y}\), with \(\mu_y(1)=1\). Enumerate every target as \(q=ap\), \(a\le Z\), \(p\) an ordinary prime in \([U/a,2U/a)\). Then \(p>a,y\), its representation is unique and the source sign is \(-\mu_y(a)\). The quantitative prime number theorem \(\pi(u)=\operatorname{li}(u)+O_K(u/(\log u)^K)\), for arbitrary fixed \(K\), yields the exact shell charge up to \(O_{\kappa,K}(U(\log U)^{1-K}+Z)\) as
\[
 -\int_U^{2U} \sum_{a\le Z}\frac{\mu_y(a)}{a\log(u/a)}\,du .
\]
This error follows from \(\log(U/a)\asymp\log U\) and \(\sum_{a\le Z}1/a\ll\log U\). The term \(Z\) covers endpoint conventions. [Johnston and Yang, Corollary 1.3](https://arxiv.org/pdf/2204.01980)

Set \(L=\log u\). We prove the uniform signed reciprocal expansion
\[
 \sum_{a\le Z}\frac{\mu_y(a)}{a(L-\log a)}
   = -\frac{P_y}{L^2}
      + O_\kappa\left(\frac{P_y(1+\log y)}{L^3}\right).
\]
The exact convolution \(\mu_y=\mu*\mathbf1_{\{p\mid d\Rightarrow p\le y\}}\) gives \(a=dm\); call such \(d\) smooth below. For large \(y\), the elementary Rankin estimate at \(\alpha=1/\log y\) gives
\[
 \sum_{\substack{d>W\\d\ {\rm smooth}}}d^{-1}
 \le e^{-\log W/\log y}\prod_{p\le y}(1-p^{-1+\alpha})^{-1}
 \ll (\log y)^C e^{-\log W/\log y}.
\]
The Euler product estimate follows from \(p^\alpha\le e\), the prime harmonic sum, and a uniformly summable contribution from higher powers. In particular \(d>\sqrt Z\) costs \(O_{\kappa,K}(L^{-K})\) for every fixed \(K\), even after the inner absolute sum is taken: \(\sum_{m\le Z/d}1/[m(L-\log(dm))]\ll_\kappa1\).

For \(d\le\sqrt Z\) put \(W=Z/d\), \(L'=L-\log d\). Thus \(\log W\gg_\kappa L\), \(L'\asymp L\), and \(\log W/L'\le v_\kappa<1\) uniformly. Write \(M(t)=\sum_{m\le t}\mu(m)\). Use the unconditional bound \(M(t)\ll_A t/(1+\log t)^A\) for arbitrary fixed \(A\). For \(A=7\), partial summation gives the convergent moments and tails
\[
 \sum_{m\le W}\frac{\mu(m)}m=O((1+\log W)^{-6}),\qquad
 \sum_{m\le W}\frac{\mu(m)\log m}{m}
       =-1+O((1+\log W)^{-5}).
\]
The complete moments are \(0\) and \(-1\) since \(1/\zeta(s)\) has a simple zero at 1 and derivative 1 there. Passage from the series and its derivative at \(s>1\) to the boundary follows from these summatory bounds. [Green–Tao, constant nilsequence case](https://arxiv.org/abs/0807.1736) · [Laurent expansion at one](https://dlmf.nist.gov/25.2)

Use the exact second-order remainder in the geometric expansion:
\[
 \frac1{L'-\log m}=\frac1{L'}+\frac{\log m}{(L')^2}
   +\frac{(\log m)^2}{(L')^3(1-\log m/L')}.
\]
The signed sum of the last numerator divided by \(m(1-\log m/L')\) is \(O_\kappa(1)\) uniformly in \(d\). Indeed \(g(t)=(\log t)^2/[t(1-\log t/L')]\) on \([1,W]\) satisfies \(|g'(t)|\ll_\kappa(1+\log^2 t)/t^2\). Both the boundary term \(M(W)g(W)\) and \(\int_1^W|M(t)g'(t)|dt\) are bounded. Consequently
\[
 \sum_{m\le W}\frac{\mu(m)}{m(L'-\log m)}
   =-\frac1{(L')^2}+O_\kappa((L')^{-3}).
\]
Summing this over smooth \(d\le\sqrt Z\) with weight \(1/d\) gives the claimed expansion. In detail, \(\sum_{d\ {\rm smooth}}1/d=P_y\) and \(\sum_{d\ {\rm smooth}}\log(d)/d=P_y\sum_{p\le y}\log p/(p-1)\ll P_y\log y\) by the elementary Chebyshev estimate and partial summation. Thus replacing \((L-\log d)^{-2}\) by \(L^{-2}\) costs \(O_\kappa(P_y\log y/L^3)\). Integration proves the displayed positive cone main term. Replacing the prime density by \(1/\log u\) before summing over cofactors would erase precisely its first nonzero coefficient.

## Compensating shell and the native mask

By the same smooth convolution,
\[
 \left|\sum_{n\le T}\mu_y(n)\right|
 \ll_A T P_y(1+\log T)^{-A}
    +T(\log y)^C e^{-\log T/(2\log y)},\qquad T\asymp U.
\]
Apply the \(M(T/d)\) bound for \(d\le\sqrt T\) and the Rankin tail above for \(d>\sqrt T\). Hence the full rough shell sum is \(o(P_yU/\log^2 U)\) and the complement shell sum is \(-(1+o(1))P_yU/\log^2 U\). This proof uses absolute convergence of the *smooth* harmonic Euler product for each fixed mask and preserves the changing \(y\) in its estimates.

At each \(X\) choose one whole shell with \(X/4\le U\le X/2\) (for example \(U=2^{\lfloor\log_2 X\rfloor-1}\)). For late \(X\) it lies inside the native terminal interval. Applying Cauchy's inequality over its \(2^s\) base cells to the genuine charges in \(R\) gives the positive tree energy
\[
 A(R)\gg \frac{U P_y^2}{2^s(\log U)^4}.
\]
To bound the excluded ordered distinct pairs in **any** subset, let \(D=X^{.01}\). Within a shell the diameter of any base cell is less than \(H_0=U2^{-s}\). The total weight of any ordered pair across all depths is less than \(2/U\). If its gcd is \(\ge D\), a divisor \(D\le d\le H_0\) divides both the first label and their nonzero difference. Thus the entire unsigned correction in the shell is
\[
 \ll U^{-1}\sum_{D\le d\le H_0}(2U/d)(2H_0/d)
 \ll H_0/D.
\]
This estimate covers clipped cells as well. Summing shells costs \(O(X/D)\), and the diagonal costs \(O(\log X)\). Alternatively one may subtract the deterministic cone's signed gcd correction from the existing signed estimate on the full rough graph; its bound retains a strict exponent saving even in the case \(B=1\). In either calculation, \(X^{.99}=o(U2^{-s}/(\log U)^4)\). The trivial unsigned tree upper is \(O(X)\). Therefore
\[
    C(R)>0,\qquad \frac{\log C(R)}{\log X}\longrightarrow1 .
\]
The cone alone has the same exponent by the same argument, with opposite sign of the *linear* shell charge. The square makes both standalone covariances large. These are genuine lower bounds on the primitive signed statistics. They do not transfer to their sum without the mixed term.

Any selector that removes the whole cone with zero combined charge in the shell requires at least \((1-o(1))P_yU/\log^2 U\) additional genuine labels, since each has absolute weight at most one. The same lower bound holds if its residual shell charge is \(o(P_yU/\log^2 U)\). In particular a correction of subpower *cardinality* cannot balance this cone. Earlier matching bounds control the cost in signed covariance while allowing many genuine partners.

The proof also applies to the subpower cofactor cutoff \(Z=2^{s/200}\) from the first matching construction. Then \(\log W\gg\sqrt{\log U}\); the arbitrary log savings in \(M\) still put both moment errors inside \(O_\kappa((L')^{-3})\), and the smooth tail still beats every fixed inverse power of \(L\). The compensated selector removes all targets together with chosen opposite-sign partners and is fully consistent with this obstruction. Bounding its remaining signed covariance is a different and still open problem. [Source-balanced selector](PRIME_SPLIT.md)

## The arithmetic logarithmic share cancels the prime-density term

On each nonzero \(y\)-rough \(q\), the divisor identity \(\mu_y(q)\log q=-(\mu_y*\Lambda_{>y})(q)\) splits its coefficient exactly into the prime shares \(\mu_y(q)\log p/\log q\), \(p\mid q\). Here \(\Lambda_{>y}\) retains every positive power of every prime exceeding \(y\); the convolution identity also holds on the squareful integers. For \(q=ap\) in the cone, take its largest-prime share and leave the complementary share \(\mu_y(q)\log a/\log q\) explicit. For every node \(J\) in a terminal shell \([U,2U)\) the largest-prime share charge equals
\[
 -\sum_{a\le Z}\mu_y(a)\!\int_{J/a}\!\frac{d\vartheta(t)}{\log(at)}
 =-\left(\sum_{a\le Z}\frac{\mu_y(a)}a\right)\int_J\frac{du}{\log u}
    +\mathcal E(J).
\]
Use the half-open interval convention corresponding to the node; endpoints otherwise cost \(O(Z)\). Partial summation of the genuine \(\vartheta(t)-t\) error yields \(\mathcal E(J)\ll_{K,\kappa} U/(\log U)^K\) for any fixed \(K\), uniformly in both endpoints, by the quantitative PNT at \(U/a\) and \(\sum_{a\le Z}1/a\ll\log U\). The rough Mertens shell proof above, now applied for every \(T\ge Z\) with the same \(y\), gives \(\sum_{a\le Z}\mu_y(a)/a\ll_{K,\kappa}(\log U)^{-K}\): the complete sum is zero and the complementary tail is small by partial summation. Thus the largest-prime share has charge \(O_{K,\kappa}(U/(\log U)^K)\). The full positive main term in the original cone therefore occurs in the cofactor-log share. A replacement of the full coefficient by its largest-prime share would discard that source term.

For \(B<1\) the same argument gives a polynomial estimate on every such \(J\),
\[
 \left|\sum_{ap\in J,\ a\le Z}\mu_y(ap)\frac{\log p}{\log(ap)}\right|
 \ll_{\kappa,\epsilon} X^\epsilon
 \left(|J| Z^{B-1}+ U^B Z^{1-B}\right).
\]
The restricted Mertens bound at fixed mask, valid for every \(T\ge Z\), prices the reciprocal tail by \(X^\epsilon Z^{B-1}\) upon taking a preliminary exponent smaller than \(1-B\). The classical explicit formula gives \(\vartheta(t)-t\ll_\epsilon t^{B+\epsilon}\): truncate at height comparable with \(t\), sum \(1/|\rho|\ll\log^2 t\) up to that height, and pay proper prime powers by \(O(\sqrt t\log^2 t)\). Integrating by parts against \(1/\log(at)\) and summing \((U/a)^{B+\epsilon}\) over \(a\le Z\) gives the second term. For a whole shell this is a power saving relative to the original cone drift, but for \(Z=X^\kappa\) it still allows a larger exponent than \(B\). It yields no square-root bound for the original signed sum. [Classical truncated explicit formula in the proof of Corollary 1.3](https://arxiv.org/pdf/2405.20552)

Retaining the cofactor signs in that error gives the stronger uniform bound \(\mathcal E(J)\ll_\epsilon U^B X^\epsilon\) for \(B<1\), including sharp native endpoints. To see this, fix \(B<v<1\) and put \(D_Z(s)=\sum_{a\le Z}\mu_y(a)a^{-s}\), \(P(s)=\sum_p(\log p)p^{-s}\) initially for \(\Re s>1\). The inherited sharp twisted Mertens estimate gives \(\sum_{n\le u}\mu(n)n^{-it}\ll u^{B+\eta}X^\xi\) for \(u\le2X\), \(|t|\le X^3\), with any fixed positive \(\eta,\xi\) (decrease the preliminary slacks there). Smooth convolution at \(B+\eta>1/2\) gives the same bound for \(\mu_y\), up to \(X^{o_\eta(1)}\), since \(\prod_{p\le y}(1-p^{-B-\eta})^{-1}=X^{o_\eta(1)}\). Partial summation therefore gives \(D_Z(s)\ll X^{2\xi}\) on \(\Re s\ge v\), \(|\Im s|\le X^3\), upon choosing \(B+\eta<v\). [Height-uniform Perron proof](../step4-matched-fibres-2026-11-19/FACTORIAL_TERMINAL_MASS_EXPONENT.md)

On that strip \(P(s)=-\zeta'(s)/\zeta(s)-\sum_{p,k\ge2}(\log p)p^{-ks}\) has only a simple pole at 1 of residue 1. The prime-power correction converges absolutely and the logarithmic derivative has subpower height growth on each fixed strip a positive distance right of \(B\), away from the pole. The coefficients \(\beta(n)=\sum_{ap=n,\,a\le Z}\mu_y(a)\log p\) of \(D_ZP\) satisfy \(|\beta(n)|\le\log n\). Apply truncated Perron to their prefix at the half-integer \(V=\lfloor x\rfloor+1/2\) for \(x\in[U,2U]\), height \(X^2\) and initial line \(1+1/\log V\). The coefficient bound gives truncation error \(O(V\log^3 V/X^2)\) by splitting at distances from \(V\). Moving to \(v\), the horizontals are \(O(VX^{-2+O(\xi)})\); the new vertical is \(O(V^v X^{O(\xi)}\log X)\). The pole contributes \(VD_Z(1)\), and moving its endpoint back to \(x\) costs \(O(1+\log Z)\). Choosing \(v-B\) and then the height losses within the desired \(\epsilon\) proves
\[
 \sum_{n\le x}\beta(n)=xD_Z(1)+O_\epsilon(U^B X^\epsilon).
\]
Another partial summation against \(1/\log n\) gives the asserted sharp-node result. In particular the largest-prime share has a single explicit continuum coefficient \(D_Z(1)\); after subtracting that continuum its error is at the inherited exponent \(B\). This is a bound on the genuine share with a specified centering. The rest of the divisor identity and the full arithmetic covariance still require independent control. [Earlier logarithmic-derivative and prime-series bounds](../step4-matched-fibres-2026-11-19/FACTORIAL_TERMINAL_MASS_EXPONENT.md)
