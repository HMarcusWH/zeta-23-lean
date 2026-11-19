# What a fixed low-frequency interval sees in the sharp Möbius prefix

**DERIVED on paper.** At every fixed real frequency, the sharp prefix has limsup growth exponent \(B-1/2\). Every fixed interval of positive length has squared-energy limsup exponent \(2B-1\), including intervals far below the height of any hypothetical off-line zero. If \(B>1/2\) is attained, the interval energy has that exponent at **every** large integer cutoff. For an unattained edge, a cofinal power saving on one fixed interval would impose a height-dependent exclusion near the edge. The general cofinal problem on one prescribed low interval remains open.

Throughout, \(B=\sup_\rho\Re\rho\in[1/2,1]\), \(b=B-1/2\), \(\mu_6(n)=\mu(n)\mathbf1_{(n,6)=1}\), \(Z_6(s)=\zeta(s)(1-2^{-s})(1-3^{-s})\), and
\[
 D_X(w)=\sum_{q\le X}\mu_6(q)\,q^{-1/2-iw},\qquad
 E_I(X)=\int_I |D_X(t)|^2dt
\]
for a fixed bounded real interval \(I\) of positive length. The exact finite Gram form for \(E_I\) includes every signed product of the true coefficients.

## A remote zero survives at each prescribed frequency

For fixed \(\tau\in\mathbb R\), absolute convergence and a direct integration on \(\Re s>1/2\) give
\[
 \int_1^\infty D_x(\tau)x^{-s-1}dx
 = \frac1{sZ_6(s+1/2+i\tau)} .                                         \tag{1}
\]
At any off-line zero \(\rho=\beta+i\gamma,\ \beta>1/2\), this has a pole at \(s=\beta-1/2+i(\gamma-\tau)\), regardless of the separation \(|\gamma-\tau|\). Both removed Euler factors are nonzero at \(\rho\). An eventual growth exponent strictly below \(\beta-1/2\) would force absolute convergence and analyticity there, contradicting (1).

For the upper use \(M_6(y)=\sum_{q\le y}\mu_6(q)\ll_\epsilon y^{B+\epsilon}\), from the inverse-zeta bound on fixed lines right of \(B\) and the convergent correction for powers of 2 and 3. When \(B=1\) use \(|M_6(y)|\le y\). Partial summation against \(q^{-1/2-it}\) gives \(D_X(t)\ll_\epsilon(1+|t|)X^{b+\epsilon}\) at every real \(t\); a log at the borderline is absorbed by using a smaller preliminary epsilon. Partial summation with the extra \(\log q\) gives \(\sup_{t\in I}|\partial_tD_X(t)|\ll_{\epsilon,I}X^{b+\epsilon}\). [Source and sharp-cutoff Perron bound](../step4-matched-fibres-2026-11-19/FACTORIAL_TERMINAL_MASS_EXPONENT.md)

It follows from (1), by taking fixed actual zeros approaching \(B\), that every fixed \(\tau\) has
\[
 \limsup_{X\to\infty}\frac{\log(1+|D_X(\tau)|)}{\log X}=b .
\]
The sequence can be taken at integers because \(D_X\) is constant between integers. If \(b=0\) the baseline one gives the lower. For \(b>0\), fix \(\tau\) in the interior of \(I\). At cutoffs with \(|D_X(\tau)|\ge X^{b-\epsilon}\), the derivative upper keeps at least half that magnitude on a radius \(X^{-3\epsilon}\), for all sufficiently large such \(X\). Applying the pointwise upper for the reverse direction gives
\[
 \limsup_{X\to\infty}\frac{\log(1+E_I(X))}{\log X}=2b .                 \tag{2}
\]
Thus a finite-height zero verification, by itself, does not justify an eventual subpower upper for this sharp-prefix energy even on a low interval free of rightward zeros. Such an upper would imply RH.

## An every-horizon lower in a fixed interval around a zero

Use the causal source \(g\), its transform \(G\), and the centered finite identity (1) in [the delayed-gain theorem](DELAYED_GAIN.md). In particular \(G(\rho)\ne0\). Fix a rightward zero \(\rho=\beta+i\gamma\), write \(\delta=\beta-1/2>0\), \(g_0=B-\beta=b-\delta\), and let \(J_\rho=[\gamma-4,\gamma+4]\). Let \(T=\log X,\ N=\lfloor\eta T\rfloor\) for \(0<\eta<1\), and use \(N\) causal convolution factors
\[
 p_\gamma(t)=e^{i\gamma t}\mathbf1_{[0,1]}(t)
\]
on the square-root-normalized logarithmic source. Multiplying back by \(e^{t/2}\) replaces the original drive by its convolution with \((e^{t/2}p_\gamma(t))^{*N}\). Its support in log coordinates is \([0,N+\log(1/a)]\). At \(\rho\) its Mellin transform is \(G(\rho)A_\delta^N\), where \(A_\delta=\int_0^1 e^{-\delta t}dt\ge e^{-\delta/2}\ge e^{-1/4}\). For all sufficiently large \(X\), the full drive fits already at \(X/2\). The centered test kernel in that identity depends only on the integer source and \(\rho\); its uniform bound is independent of \(N\). Cauchy–Schwarz as in equation (3) of the linked proof therefore bounds the squared energy of the smoothed normalized response on \([0,T]\) below by \(c_\rho X^{2\delta}A_\delta^{2N}\).

For \(t\le T\), that causal response is unchanged if the Möbius impulses are truncated at \(q\le X\). The Fourier transform on the whole line of this truncated response is \(D_X(u)\widehat h_0(u)\widehat p_\gamma(u)^N\), where \(h_0(t)=e^{-t/2}g(e^t)\) is bounded and compactly supported. With the angular-frequency convention \(\widehat f(u)=\int f(t)e^{-iut}dt\), \(|\widehat p_\gamma(u)|\le\min(1,2/|u-\gamma|)\). On the complement of \(J_\rho\), reserve two factors for integrability and bound each other factor by \(1/2\). The all-frequency partial summation bound for \(D_X\) then gives
\[
 \int_{\mathbb R\setminus J_\rho}
 |D_X(u)\widehat h_0(u)\widehat p_\gamma(u)^N|^2du
 \ll_{\rho,\epsilon} X^{2b+2\epsilon} 2^{-2N}.
\]
The reserved fourth power of \(|u-\gamma|^{-1}\) is integrable against \((1+|u|)^2\) there. The new point is to use \(b+\epsilon\) in this bound even at unbounded real frequencies while keeping the factor \(1+|u|\). If
\[
 g_0+\epsilon<\eta\log(2A_\delta),                                    \tag{3}
\]
this tail is smaller by a fixed power than the centered lower. By Plancherel and boundedness of the other inside-band multipliers,
\[
 E_{J_\rho}(X)\gg_\rho X^{2\delta} A_\delta^{2N}
 \quad\text{at every sufficiently large integer }X,                    \tag{4}
\]
with threshold also depending on the fixed slack parameters.

If \(\beta=B\), choose every arbitrarily small fixed \(\eta>0\), then \(\epsilon\) satisfying (3). This gives \(1+E_{J_\rho}(X)=X^{2b+o(1)}\) at every \(X\). For \(0<g_0<1/6\), choose \(\eta=3g_0,\ \epsilon=g_0/10\). Since \(3(\log 2-1/4)>1.1\), (3) holds, and the square-root exponent lower in (4) is at least \(\delta-3g_0/4=b-7g_0/4\).

## Propagating a hypothetical saving on a low interval

Suppose \(b>0\) and there is a fixed \(a_0>0\) and an unbounded sequence \(X\) with \(E_I(X)\le X^{2b-a_0}\). Shrink \(a_0\) if necessary to \(a_0\le b\). Recenter the polynomial by \(U_X(w)=X^{iw}D_X(w)\), which has the same modulus on the real axis. Choose a positive-length closed subinterval \(E\) in the interior of \(I\). For arbitrarily small \(\epsilon>0\), the derivative bound for \(U_X\) on \(I\) is \(O_{\epsilon,I}(X^{b+\epsilon})\), including the factor \(\log X\) from differentiating \(X^{iw}\). A value \(M\) on \(E\) keeps at least \(M/2\) on an interval in \(I\) of length \(\gg_I\min(1,M/X^{b+\epsilon})\). It follows from the hypothesized energy that
\[
 \sup_E |U_X|\ll_I X^{b-a_0/4}
\]
after taking \(\epsilon<a_0/8\) and \(X\) sufficiently large.

Put \(h=b/2\). On the whole half-plane \(\Im w=v\ge-h\), summation by parts gives
\[
 |U_X(w)|\ll_\epsilon X^{b+\epsilon}
    \left(1+\frac{1+|w|}{b+v+\epsilon}\right).
\]
Indeed the boundary term is \(\ll X^{b+\epsilon}\), and the integral before multiplying by \(|X^{iw}|=X^{-v}\) is bounded by \((1+|w|)\int_1^X y^{b+v+\epsilon-1}dy\). Thus \(U_X(w)/(w+i(h+1))\) is analytic and bounded by \(C_{\epsilon,b}X^{b+\epsilon}\) even at infinity in this half-plane.

Here is an explicit propagation weight. In \(\Im w>-h\) with \(E\) removed take
\[
 P(w)=\frac1M\int_E\log\left|\frac{w-t+2ih}{w-t}\right|dt ,
\]
with \(M\ge1\) large enough that \(P\le1\) on \(E\). The logarithmic singularity is integrable; the resulting single-layer potential is continuous up to both sides of the slit. It is positive and harmonic off the slit, zero on \(\Im w=-h\), and tends to zero at infinity. Thus \(0<P\le1\) there by the maximum principle. At every real \(w\in J_\rho\), including points of the slit, \(P(w)\ge c_{I,b}/(1+\gamma^2)\). This follows by using \(\tfrac12\log(1+4h^2/(w-t)^2)\) in the integral and \(|w-t|\le |\gamma|+C_I\).

Apply the subharmonic maximum principle to the logarithm of \(|U_X(w)/(w+i(h+1))|\), using the global bound on the lower boundary and at infinity and the smaller bound on the slit. Equivalently, subtract \((b+\epsilon)\log X+\log C\) and add the harmonic function \((a_0/4)P(w)\log X\). The boundary upper is nonpositive after increasing \(C\). Zeros of \(U_X\) cause no problem for this upper bound. For each fixed \(\rho\), choose a sufficiently small preliminary \(\epsilon\) in terms of \(I,b,a_0,\gamma\). On that same subsequence,
\[
 \sup_{w\in J_\rho}|D_X(w)|
 \ll_{\rho,I,b,a_0} X^{b-c'_{I,b}a_0/(1+\gamma^2)}.                  \tag{5}
\]

If \(B>1/2\) is attained at a finite-height zero, (4) and (5) contradict each other. Thus in this case **every** prescribed \(I\) of positive length has
\[
 1+E_I(X)=X^{2b+o(1)}
\]
at every sufficiently large integer cutoff, wherever \(I\) lies. If \(b=0\) the same exponent-zero statement is automatic from the upper and the baseline one.

If the right edge is unattained, compare (4) for \(0<B-\beta<1/6\) with (5). A necessary condition for the stipulated cofinal saving on \(I\) is
\[
 (B-\beta)(1+\gamma^2)\ \gg_{I,b}\ a_0
 \quad\text{for each such near-edge zero.}
\]
In particular the saving is also impossible if a sequence of actual zeros approaches \(B\) with \((B-\beta_j)(1+\gamma_j^2)\to0\). No such approach rate for a general unattained right edge is assumed or established here. A fixed sufficiently high band around a chosen zero detects its own displacement through the centered source test. The distinct question of a cofinal subpower upper on one prescribed, remote low band has been settled here only under the stated edge conditions. A verified finite zero height alone proves neither that upper nor a Step 4 closure.
