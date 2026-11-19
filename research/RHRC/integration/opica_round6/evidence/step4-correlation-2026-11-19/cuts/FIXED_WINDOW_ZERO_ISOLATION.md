# The complete native energy is detectable on every fixed time window

**Paper theorem, 19 November 2026.** Let \(P(t)\) be the genuine one-copy OPICA prime-power field. Let \(d=\sup_\rho(\Re\rho-1/2)_+\), and let \(W>0\) be any fixed number. Then
\[
 \lim_{t\to\infty}\frac{\log(1+\int_{t-W}^t P(v)^2dv)}{2t}=d .
\]
The same statement holds with the fixed rule \(W(t)=1/\log(2+t)\), or with any \(0<W(t)\le1\) satisfying \(\log(1/W(t))=o(\log t)\). All terminal times are allowed. No attainment of the supremum is assumed. This sharpens the merged fixed-source theorem's logarithmically growing window on the genuine Riemann zeta configuration by adding an external zero-density estimate. [Native field and explicit formula](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean) · [Merged window theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154)

### Sparse shifted zeros admit an arbitrarily short isolation filter

Write \(p=\rho-1/2\), \(\gamma=\Im p\), \(J(z)=(z^2-1/4)^2Q_s(z)\) for the bilateral Laplace transform of \(j\), and \(A_p=m_\rho J(p)\), combining multiplicities. The native explicit formula at sufficiently late times is \(P(t)=-\sum_p A_p e^{pt}+D(t)\), with \(D(t)\) the decaying trivial-zero term. The two pole contributions vanish. By fixed-order integration by parts on the compact smooth source \(J(\sigma+i\gamma)\ll_j(1+|\gamma|)^{-3}\) uniformly over \(|\sigma|\le1/2\). Standard zero counting proves \(\sum_p|A_p|<\infty\). Also \(A_p\ne0\) whenever \(\Re p>0\): the individual sinc factors of \(Q_s\) are nonzero off the imaginary Laplace axis, their deviations from 1 are absolutely summable at fixed \(p\), and \(p=\pm1/2\) is excluded. Hence \(|P(v)|\ll_j e^{dv}\) at all late \(v\).

Fix one actual shifted zero \(p_0=\delta+i\gamma_0\) with \(\delta>0\), and any \(0<\alpha<\delta\). Ingham's estimate gives \(N(1/2+\alpha,T)\ll T^\kappa\) for any fixed \(\kappa\) strictly between \(3(1/2-\alpha)/(3/2-\alpha)\) and 1. Consequently for the distinct \(p\ne p_0\) with \(\Re p\ge\alpha\),
\[
 \sum_{|\gamma-\gamma_0|>R} \frac{\pi}{|\gamma-\gamma_0|}
 \le C_{\alpha,p_0,\kappa} R^{\kappa-1}\qquad(R\ \text{sufficiently large}).
\]
This follows by dyadic summation, counting both signs. Distinct zeros in a fixed compact set are finite, so \(|p-p_0|\) has a positive lower bound over these other zeros. [Ingham, zero-density theorem](https://doi.org/10.1093/qmath/os-11.1.201) · [Modern statement, equation (1.2)](https://arxiv.org/html/2405.20552#S1)

Given \(0<W\le1\), choose \(R\asymp_{\alpha,p_0,\kappa}W^{-1/(1-\kappa)}\) sufficiently large that the tail sum is at most \(W/2\). For each corresponding high-ordinate zero set \(z=p-p_0\) and \(h=\pi/|\Im z|\). The two-point probability
\[
 \frac{e^{-h\Re z}\delta_0+\delta_h}{1+e^{-h\Re z}}
\]
has unit mass and Laplace transform zero at \(z\) because \(e^{-hz}=-e^{-h\Re z}\). The convolution of all these probabilities exists as the distribution of an absolutely convergent sum of independent bounded random variables, supported in \([0,W/2]\). Call it \(\nu\). Its Laplace transform vanishes at every one of the tail offsets, by independence of the member factor and the rest. Probability is used only to build this compact filter.

List the remaining \(M=O(R^\kappa)\) nonzero offsets as \(z_1,\ldots,z_M\). This includes every potential same-ordinate, different-real-part exception. Convolve \(M+2\) uniform probability densities on \([0,w]\) with \(w=W/(2(M+2))\) to obtain \(\eta\). For \(0\le k\le M\), taking the distributional derivative on \(k\) separate boxes gives
\(\|\eta^{(k)}\|_1\le(2/w)^k,\ \|\eta^{(k)}\|_2\le(2/w)^k w^{-1/2}\).
Indeed each differentiated box is \((\delta_0-\delta_w)/w\); at least two undifferentiated boxes remain. The compactly supported function
\[
 \psi=\left[\prod_{j=1}^M(1-D/z_j)\eta\right]*\nu
\]
has support in \([0,W]\) and unit mass. With Laplace convention \(\int e^{-zu}\psi(u)du\), each derivative multiplies by \(+z\), so the transform vanishes at all the listed offsets and all tail offsets. This construction handles the ordinate coincidences separately from the half-turn factors. Taking \(b=\min(1,\inf_j|z_j|)>0\) over all distinct other zeros in the set (use \(b=1\) if the set is empty), the \(L^1\) norm is bounded by \((1+2/(wb))^M\). The \(L^2\) bound has the extra factor \(w^{-1/2}\).

Finally put \(f_W(u)=e^{p_0u}\psi(u)\). Its transform at \(p_0\) is 1 and at every \(p\ne p_0\) with \(\Re p\ge\alpha\) is 0. Its size satisfies the independent filter estimate
\[
 \log(2+\|f_W\|_1+\|f_W\|_2)
 \ll_{\alpha,p_0,\kappa} (1+W^{-\kappa/(1-\kappa)})\log(2/W).
\]
The choice of filter depends on the actual zero configuration being tested. It is a lower-bound probe under a hypothetical zero, not an upper for the prime field.

### Apply the filter to the full arithmetic history

Causality and the compact support of \(f_W\) use only the field on \([t-W,t]\). For \(t>W+1\), integrate its native explicit formula to obtain
\[
 \int_0^W f_W(u)P(t-u)du
 =-A_{p_0}e^{p_0t}+O_{j}\big(\|f_W\|_1(1+e^{\alpha t})\big).
\]
At fixed \(t,W\), absolute summability with the factor \(e^{dt}\) justifies exchanging the integral and the zero sum. The remaining low-real-part zeros obey \(|e^{p(t-u)}|\le e^{\alpha t}\); no restriction on their ordinates is made. The bounded trivial-zero series is included. For fixed \(W\) the filter norms are fixed; for the stated shrinking rules their logarithms are \(o(t)\). Thus the main oscillation in modulus exceeds \(\frac12|A_{p_0}|e^{\delta t}\) at every sufficiently late end time. By Cauchy–Schwarz the local energy is at least \(\exp((2\delta-o(1))t)\), including when \(p_0\) has arbitrary multiplicity. For each \(\delta<d\) below a realized displacement use a fixed zero with real part above \(\delta\); then take the supremum. The earlier upper completes the limit when \(d>0\). The uniform upper and nonnegative logarithm cover \(d=0\). For a fixed \(W>1\) use width 1 in the lower probe and the original width in the upper.

A quantitative hypothesis-dependent version also follows. If \(d>0\) and \(0\le\lambda<2d/[3(1/2-d)]\), widths \(W=t^{-\lambda}\) still have the same rate. Choose \(\alpha<\Re p_0\) close enough to \(d\) and \(\kappa\) close enough to Ingham's exponent to have \(\lambda\kappa/(1-\kappa)<1\). The same proof yields the lower for zeros with displacement arbitrarily near \(d\). The previously imported ceiling gives \(d<1/2\).

### Which sign could close Step 4

Use precisely \(Y=10^7\) and \(E_Y\) of the [fixed-sieve proof](../FIXED_SIEVE_SIGN.md). Define
\[
 R_{Y,W}(n)=\int_{n-W(n)}^n\big(P(v)^2-E_Y(v)\big)\,dv.
\]
For every fixed \(W>0\), and for the specified shrinking windows, the preceding result gives
\[
 d=0\quad\Longleftrightarrow\quad R_{Y,W}(n)\le0
                   \ \text{for arbitrarily large integers }n .
\]
If \(d>0\), the first integral grows at exponential rate \(2d\). The comparison density \(E_Y\) tends to a finite constant, so its integral costs \(O_Y(W)\). If \(d=0\), the genuine pointwise estimate \(P(v)^2<10^{62}\) and \(E_Y(v)\to L_Y>10^{73}\) make the integrand uniformly negative at all sufficiently late times. The latter implication uses the quantitative arithmetic source certificate. The formula retains all prime powers and all cross terms of the genuine divisor decomposition.

In particular it suffices to prove a cofinal signed recurrence on **one-unit** intervals \([n-1,n]\), or even on \([n-1/\log(2+n),n]\). Arbitrary late choices of real center also work if the closing criterion uses real horizons throughout. Isolated zeros or small individual values of \(P\) have no proved control on even this shrinking-window energy: the unconditional derivative estimate still permits exponentially steep excursions near a zero.

### The narrow sign on 94,551 consecutive actual horizons

For \(Y=10^7\) and \(W(n)=1/\log(2+n)\), the complete signed integral obeys
\[
 R_{Y,W}(n)<-4\cdot10^{73}\quad\text{for every integer }50000\le n\le144550 .
\]
This uses published finite zero-height verification and the external zero ceiling for the upper part of the range. It does not extrapolate the finite sign to a cofinal sequence.

Indeed \(1/12<W(n)<1\) on this range. For \(0\le u\le42000\) put \(X=e^{n-u}\), so \(\log X\ge8000\). Every prime in \((Xe^{-W},X]\) exceeds \(Y\) and places \(u+\log p\) in the required narrow window. Rosser–Schoenfeld give \(\pi(X)>X/\log X\) for \(X\ge17\) and \(\pi(x)<x/(\log x-3/2)\) for \(x>e^{3/2}\), their inequalities (3.5) and (3.4) respectively. Hence
\[
 \sum_{Xe^{-W}<p\le X}\frac1p
 \ge\frac{\pi(X)-\pi(Xe^{-W})}{X}
 >\frac1{\log X}
 \left(1-e^{-W}\frac{\log X}{\log X-W-3/2}\right)
 >\frac{0.07}{\log X}\ge\frac{0.07}{n}.
\]
For the numerical margin use \(e^{-W}<12/13\) and the displayed ratio at most \(8000/(8000-5/2)\). [Rosser–Schoenfeld, p. 69](https://doi.org/10.1215/ijm/1255631807)

Tonelli on these nonnegative square terms of \(E_Y\), with the actual certified \(\int_0^{42000}V_Y^2>10^{80}-1\), gives \(\int_{n-W}^n E_Y>(0.07/n)(10^{80}-1)\). Through \(144000\) the full field satisfies \(|P|<10^{31}\) by the finite-height estimate with \(d<0.374\); through \(100000\) the ordinary elementary strip suffices. For the overlap and extension through \(144550\), the separately verified field bound is \(|P|<10^{34}+10^{31}\), using \(d<0.37335\). Since \(W<1\), even \((0.07/144550)(10^{80}-1)-(10^{34}+10^{31})^2>4\cdot10^{73}\). The [pointwise signed bound](../divisor/FIXED_SIEVE_RECURRENCE_AUDIT.md) also gives the strict sign directly whenever the narrow window lies wholly in \([70000,144550]\). [Finite mass and original field bounds](../FIXED_SIEVE_SIGN.md)

**Status.** The sparse-zero filter and the strengthened window detection are paper results. Neither the zero-dependent probe nor recurrence of a finite frequency list establishes the arithmetic sign occurrence at unbounded horizons.
