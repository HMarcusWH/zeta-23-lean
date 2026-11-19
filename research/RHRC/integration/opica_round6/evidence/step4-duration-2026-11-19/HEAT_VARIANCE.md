# Complete covariance after Gaussian averaging, and the variance required to undo it

**Paper deduction, 19 November 2026.** The prime cutoff stays permanently at \(Y=10^7\). Put \(G_s(u)=(4\pi s)^{-1/2}e^{-u^2/(4s)}\) for \(s>0\). At observation time \(t\), average each actual signed divisor contribution with \(G_{at}\), *then* square. For every fixed \(5\cdot10^{-26}\le a\le1/8\) the resulting complete covariance is strictly negative at **every sufficiently late time**, independently of RH. An exact variance identity below identifies the missing contribution to the unsmoothed problem. The Gaussian uses the full time history, including times after \(t\). This observation has different weights from the original native window.

## What is being averaged

Use the native one-copy \(j\), the prime-power field \(P\), and the integer drive \(U\) with coefficient \(\log k\). Write \(V=\prod_{p\le Y}(1-S_p)U\), \(c_r(v)=\mu(r)r^{-1/2}V(v-\log r)\) for \((r,\prod_{p\le Y}p)=1\). Then \(P=\sum_r c_r\), \(E_Y=\sum_r c_r^2\) and \(E_Y(v)\to L_Y>10^{73}\). All fields vanish before zero. Define
\[
 P_a(t)=(G_{at}*P)(t),\qquad
 E_a(t)=\sum_r[(G_{at}*c_r)(t)]^2,\qquad H_a(t)=P_a(t)^2-E_a(t).
\]
Every prime power and every ordered pair between different groups is present in \(H_a\). Absolute Fubini for fixed \(t>0\) follows since the finite divisor filter is fixed, \(V\) vanishes on the negative half-line, decays faster than any exponential on the right, and the Gaussian suppresses arbitrarily large \(\log r\). Equivalently, the full field can be computed directly as \(P_a(t)=\sum_m\Lambda(m)m^{-1/2}(G_{at}*j)(t-\log m)\). [Native prime field](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean) · Earlier fixed-sieve proof

## The diagonal can be evaluated independently

Let \(c_Y\) be the positive density of squarefree integers having no prime factor at most \(Y\). For fixed \(a>0\),
\[
 E_a(t)\sim \frac{c_Y|\int V|^2}{\sqrt{8\pi at}}.                         \tag{1}
\]
To verify, put \(D=at,\ f_D=G_D*V\). The exact sum is \(\sum_r \mu(r)^2 r^{-1} f_D(t-\log r)^2\) with the same coprimality restriction. The elementary count for these integers is \(c_Y x+O_Y(\sqrt x)\). On \(\log r\ge t/2\), partial summation gives an error \(O_Y(e^{-t/4})(\|f_D\|_\infty^2+\|f_D\|_2^2+2\|f_D\|_2\|f_D'\|_2)\) in replacing the sum by the corresponding integral of \(c_Yf_D^2\). These norms are bounded for large \(D\) by convolution with a probability density. For \(v\ge t/2\), exponential weighting gives \(|f_D(v)|\le C_{Y,\lambda}D^{-1/2}e^{-\lambda v+D\lambda^2}\), for any \(\lambda>0\). Choose \(a\lambda<1/4\). Then both the omitted genuine discrete sum (harmonic mass \(O(t)\)) and the omitted integral are exponentially small. By Fourier Plancherel and dominated convergence, \(\sqrt{8\pi D}\|G_D*V\|_2^2\to|\int V|^2\).

The coefficient is nonzero on the actual input. The integer-drive transform gives
\[
 \int V=-\tfrac1{16}\zeta'(1/2)\prod_{p\le Y}(1-p^{-1/2}).
\]
Indeed the source has \(J(0)=1/16\). The alternating zeta series gives \(\zeta(1/2)<0\), and differentiation of the functional equation at the symmetry point gives \(\zeta'/\zeta(1/2)=(\log\pi-\psi(1/4))/2>0\). For example \(\psi(1/4)<\psi(1)=-\gamma_E\) by positivity of the trigamma series. [Completed zeta function](https://dlmf.nist.gov/25.4) · [Digamma and polygamma identities](https://dlmf.nist.gov/5.15)

## The exact positive smoothing threshold

For each nontrivial zero let \(p=\rho-1/2=\delta+i\gamma\). Define
\[
 a_* = \sup\left(\{0\}\cup
            \{\delta/(\gamma^2-\delta^2):\delta>0\}\right).
\]
In the second set every denominator is positive since every rightward zero would have \(|\gamma|>3\cdot10^{12}\). The verified height and the external ceiling \(\delta<0.37335\) give \(a_*<4.15\cdot10^{-26}\). If \(a_*>0\), it is attained by a finite nonempty set, even if the supremum of \(\delta\) is unattained: the displayed ratios tend uniformly to zero as \(|\gamma|\to\infty\). [Platt–Trudgian](https://arxiv.org/abs/2004.09765) · [External zero-free ceiling](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean#L274-L290)

The native explicit formula and Gaussian integration give, for \(0<a\le1/8\),
\[
 P_a(t)=-\sum_p m_\rho J(p)e^{(p+a p^2)t}+O_a(e^{-c t}) .                \tag{2}
\]
Here the sum is over distinct zeros with multiplicities displayed, and \(c>0\) may be taken uniformly on compact subintervals of the indicated parameter range. To justify the formula on the full line, the native expansion holds for \(v\ge1\) with an exponentially small trivial-zero remainder \(O_j(e^{-2v})\). Its Gaussian integral costs \(O(e^{(-2+4a)t})\). Subtract the exponential sum on \(v<1\) using \(\sum m_\rho|J(p)|<\infty\), \(|\delta|\le1/2\), and zero native history for \(v<0\). The bounded initial interval and the negative half-line then have exponentially small Gaussian integrals. On the latter the exponent includes \(-t/(4a)+v/(2a)-v^2/(4at)+|v|/2\). Full-line integration of each exponential yields (2). Rightward residues are nonzero by the native sinc product. [Actual explicit formula](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean)

For every \(a>a_*\) in the given range, (2) decays exponentially. The real exponent is \(\delta-a(\gamma^2-\delta^2)\). For leftward zeros \(\delta+a\delta^2\le0\), and the zeros with bounded ordinate form a finite set. No nontrivial real zero occurs. Thus (1) proves
\[
 H_a(t)\sim-\frac{c_Y|\int V|^2}{\sqrt{8\pi at}}\qquad(t\to\infty).
\]
For \(0<a<a_*\), the maximal real exponent \(b_a\) is strictly positive and is attained by finitely many visible modes, separated from the rest. For that finite set the imaginary frequencies are distinct. Indeed \(p\mapsto p+a p^2\) is injective on the original strip: a collision between distinct \(p,q\) would require \(p+q=-1/a\). On each interval of length one their exponential Gram matrix has strictly positive minimum eigenvalue, by linear independence. Shifting the window changes just the phases after the common growth factor is extracted. Consequently the integrated complete covariance on every sufficiently late unit interval is positive, with rate \(2b_a\). In the boundary case \(a=a_*>0\), the same argument gives a positive lower bound on every late unit integral while the diagonal tends to zero. In particular, cofinal nonpositive unit integrals for any sequence of fixed \(a\downarrow0\) would exclude all rightward zeros. The independently paid interval \(a\ge 5\cdot10^{-26}\) stops short of this quantifier.

There is also a quantitative obstruction to continuing the paid interval simply by continuity. If \(a_*>0\), write \(S_*\) for the attaining distinct shifted zeros. Then
\[
 \lim_{a\downarrow a_*}(a-a_*)\int_1^\infty P_a(t)^2\,dt
 =\sum_{p\in S_*}\frac{m_\rho^2 |J(p)|^2}{2(\gamma^2-\delta^2)}>0 .
\]
The remaining modes have uniform negative real exponent for \(a\) in a small right-hand neighborhood of \(a_*\). After expanding the squared complex modulus, each equal-frequency diagonal integral has the displayed simple pole. The unequal-frequency denominators remain bounded away from zero by injectivity, and cross terms with the exponentially small remainder stay bounded. This proves the limit without assuming simple zeros or a unique top pair.

## The arithmetic quantity erased by averaging

For \(D=at\), sample two times \(v,w\) independently with common density \(G_D(t-\cdot)\). Write \(\mathbb E\) for this explicit integration only. Set
\[
 B_a(t)=\tfrac12\,\mathbb E\sum_{r\ne l}
       [c_r(v)-c_r(w)][c_l(v)-c_l(w)] .
\]
Then, identically, \(G_D*(P^2-E_Y)(t)=H_a(t)+B_a(t)\), by expanding the two independent averages. Gaussian tails justify the sum exchanges by the earlier absolute bounds (the total absolute rough-source mass grows at most exponentially in time). For fixed \(5\cdot10^{-26}\le a\le1/8\) the term \(H_a\) has been paid at every late time. Under \(d>0\) the *full* variance term satisfies
\[
 \lim_{t\to\infty}\frac{\log(1+\max(B_a(t),0))}{2t}=d+2ad^2 .
\]
In fact \(|P(v)|\ll e^{dv}\) for \(v\ge0\), so \(G_D*P^2(t)\ll e^{(2d+4ad^2)t}\). For the lower bound take one genuine unit window ending at \((1+4ad)t\). Its native energy is \(\exp(2d(1+4ad)t+o(t))\) by the short-window theorem. The least Gaussian density there is \(\exp(-4ad^2t+o(t))\). The same conclusion follows with the merged logarithmic window. The independent diagonal average tends to \(L_Y\) by boundedness, its fixed limit, and Gaussian escape to positive infinity in probability. Under RH, \(G_D*P^2(t)\) tends to the critical-line mean \(\sum_{\gamma\text{ distinct}}m_\rho^2 |J(i\gamma)|^2<10^{62}\). For finite sums, all unequal frequencies acquire \(e^{-at(\gamma-\gamma')^2}\); the absolutely summable remainder permits passage to the full series. Thus under RH \(B_a\) tends to this mean minus \(L_Y\). A cofinal nonpositive bound on this explicit signed *increment* covariance for just one such fixed \(a\) would suffice. The argument does not establish that bound. Short-window theorem · Earlier graph and quantitative comparison
