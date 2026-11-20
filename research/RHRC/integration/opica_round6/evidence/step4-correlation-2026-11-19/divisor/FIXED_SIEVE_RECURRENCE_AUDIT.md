# Uniform squarefree sampling and 29,001 consecutive genuine negative windows

**Paper result with a fresh rational and Arb certificate.** For the fixed cutoff \(Y=10^7\), \(E_Y(t)>1.1\cdot10^{73}-2\) for **every real \(t\ge70000\)**. Combined with the verified native prime-field bound \(|P(t)|<10^{31}\) through \(t=100000\), the total distinct-core covariance \(P(t)^2-E_Y(t)\) is strictly below \(-10^{73}\) throughout the interval \([70000,100000]\). This covers every continuous and positive-quadrature terminal gate with integer \(71000\le n\le100000\). The finite interval gives no cofinal recurrence. A separate growing-cutoff result below shows which translation limits cannot give that recurrence.

## Effective squarefree sampling

Write \(\Pi_Z=\prod_{p\le Z}p\), \(N_Z(x)=\#\{r\le x:\mu(r)^2=1,\ (r,\Pi_Z)=1\}\), and
\[
 c_Z=\zeta(2)^{-1}\prod_{p\le Z}(1+1/p)^{-1},\qquad
 L_Z=c_Z\int_0^\infty V_Z(v)^2dv .
\]
For squarefree \(d\), the count of squarefree multiples of \(d\) up to \(x\ge1\) equals
\[
 \frac{x}{\zeta(2)}\prod_{p\mid d}\frac1{p+1}
       +O^*(3\,2^{\omega(d)}\sqrt{x}).
\]
Here \(O^*(B)\) denotes an error of absolute value at most \(B\). To verify, write each multiple as \(d m\) with \(m\) squarefree coprime to \(d\); expand \(\mu^2(m)=\sum_{k^2\mid m}\mu(k)\). For \(X=x/d\ge1\) the count of integers up to \(X/k^2\) coprime to \(d\) differs from \((X/k^2)\phi(d)/d\) by at most \(2^{\omega(d)}\). Summing this error and then extending the absolutely convergent main series in \(k\) costs at most \((2^{\omega(d)}+2)\sqrt X\). For \(X<1\) the main term is at most \(\sqrt x\) and the count is zero.

Apply lower and upper Bonferroni at orders 1023 and 1024 to the primes up to \(Y\). The missing terms in the main product, in absolute value and as a fraction of \(x\), cost at most
\[
 e^{B}B^{1024}/1024!,\qquad B=\sum_{p\le Y}(p+1)^{-1}<17 .
\]
The covered squarefree-multiple errors together cost at most
\[
 3\cdot1025(2e\,664579/1024)^{1024}\sqrt x .
\]
The count of small primes is exact; the combinatorial bound follows from \(\binom{M}{j}\le(eM/j)^j\) and monotonicity of the upper bound up to order 1024. The accompanying certificate verifies
\[
 |N_Y(x)-c_Yx|\le e^{-3000}x+e^{8500}\sqrt x. \tag{1}
\]

## Deterministic finite-window upper for the signed covariance

The [original fixed-cutoff calculation](../FIXED_SIEVE_SIGN.md) proves \(c_YI_Y\ge e^{200}/[2\pi\,1000\,32^2(Y+1)]>1.1\cdot10^{73}\), with \(I_Y=\int |V_Y|^2\), and \(\int e^{v/5}|U(v)|^2dv<10^{82}\). The already established \(\sum_{p\le Y}p^{-2/5}<4000\) gives
\[
 \int_{45000}^\infty |V_Y(v)|^2dv
 \le 10^{82}\exp(-9000+8000)<1 .
\]
For a bound on sampling variation also use \(U'\). Both \(j\) and \(j'\) have two canceled moments at the required half-pole because their transforms are \(J(z)\) and \(zJ(z)\). Differentiating the original finite histories identifies \(U'\) as the drive with source \(j'\). The checked box bounds give \(\max_{0\le m\le3}\|j^{(m)}\|_\infty<10^{39}\). For either \(b=j,j'\) and \(F(w)=w^{-1/2}b(-\log w)\),
\[
 F''(w)=w^{-5/2}\bigl(3b/4+2b'+b''\bigr)(-\log w).
\]
Also \((\log(w)F)''=(\log w)F''+2F'/w-F/w^2\). Their second-derivative \(L^1\) norms together cost at most \(120\cdot10^{39}<10^{42}\) on \([1/2,2]\). Second-order Euler summation thus gives \(|U(u)|,|U'(u)|\le10^{42}(1+u)e^{-3u/2}\) for \(u\ge0\); both vanish before zero. In particular \(\int(U^2+U'^2)<10^{86}\).

The certified weighted prime sum \(\sum_{p\le Y}1/\sqrt p\le84063/128<657\) comes from summing actual prime counts in \([4^k,4^{k+1})\) with weight \(2^{-k}\). Minkowski under translation gives
\[
 \int(V_Y^2+V_Y'^2)\le e^{1314}10^{86}<e^{1600}.
\]
Set \(F(v)=V_Y(v)^2\). Cauchy gives \(\int |F'|\le\int(V_Y^2+V_Y'^2)\), and the vanishing early history gives the same bound on \(\|F\|_\infty\).

For \(t\ge70000\) retain just \(e^{t-45000}<r\le e^t\) in the positive sum \(E_Y(t)\). Here \(x\ge e^{25000}\), so (1) gives \(|N_Y(x)-c_Yx|\le 2 e^{-3000}x\). Apply Stieltjes partial summation to \(x^{-1}F(t-\log x)\) on this interval, with the lower endpoint excluded. The upper endpoint is zero. The total error versus \(c_Y\int_0^{45000}F(v)dv\) is at most \(2 e^{-3000}(\|F\|_\infty+\int |F|+\int|F'|)<1\). Therefore
\[
 E_Y(t)> 1.1\cdot10^{73}-2\qquad(t\ge70000).
\]
The [finite zero-height estimate for the genuine field](../FIXED_SIEVE_SIGN.md) now gives \(P(t)^2-E_Y(t)<-10^{73}\) for all \(70000\le t\le100000\). Every listed native terminal window lies wholly inside this interval. The assertion also holds under its positive quadrature, since the pointwise sign holds at all nodes. [Executable scalar certificate](check_rough_density.py) · [Checked constants](ROUGH_DENSITY_CONSTANTS.json)

Using the external all-character ceiling already checked at modulus one gives \(d<0.37335\). The original finite high-ordinate tail then costs at most \(\exp(0.37335\,t-53890)<e^{78}<10^{34}\) throughout \(t\le144550\). The critical-line and trivial terms stay below \(10^{31}\). The new certificate verifies
\[
 1.1\cdot10^{73}-2-(10^{34}+10^{31})^2>10^{73}.
\]
Consequently the **pointwise** signed inequality \(P(t)^2-E_Y(t)<-10^{73}\) holds for every \(70000\le t\le144550\), and all **73,551** integer native windows \(71000\le n\le144550\) inherit it, both under integration and at the positive quadrature nodes. This count uses the external zero-free ceiling in addition to the finite-height input. The preceding 29,001-window count uses only the elementary strip in this high-ordinate bound. [Mellin test and finite-window comparison](../COUNTERSIGN_ZERO_HEIGHT.md)

## Independent cofinal recurrence at instants

For the unchanged arithmetic source there is an exact *unconditional* recurrent scalar value
\[
 \liminf_{t\to\infty}\big(P(t)^2-E_Y(t)\big)=-L_Y .              \tag{4}
\]
This applies to every fixed finite \(Y\), with the negative level above for the specified \(10^7\).

To prove it, first \(\liminf_{t\to\infty}|P(t)|=0\). Otherwise the continuous real \(P\) would eventually have a constant sign and \(|P(t)|\ge c>0\). The genuine full Laplace transform on \(\Re z>1/2\) is
\[
 -J(z)\frac{\zeta'(1/2+z)}{\zeta(1/2+z)} .
\]
It is analytic on a neighborhood of each real \(z\ge0\). At \(z=1/2\) the double half-pole source zero removes the simple logarithmic-derivative pole, and \(\zeta\) has no real zero for positive argument. For \(0<s<1\), this last fact follows from the alternating eta series and \(1-2^{1-s}\ne0\). All omitted initial history contributes an entire function.

For completeness, the Laplace transform of a positive tail has a real singularity at any finite convergence abscissa \(a\). If analytic there, take \(s_0>a\) sufficiently close that its Taylor disk reaches a point \(s_0-h<a\). Expansion and monotone convergence, using positive integrands \(e^{-s_0t}(ht)^k/k!\), force convergence at that point. A constant-sign tail of \(P\) would therefore converge for every real \(z>0\), and there its Laplace transform would equal the stated analytic continuation (with sign and finite prefix restored). As \(z\downarrow0\), the lower bound \(c\) makes the transform diverge with the eventual sign, whereas the continuation is finite at zero. This proves the asserted liminf for \(|P|\). Equation (2) of the [fixed-sieve sign test](../FIXED_SIEVE_SIGN.md), or (2) below at fixed \(Z=Y\), gives \(E_Y(t)\to L_Y\); nonnegativity of \(P^2\) finishes (4).

These arbitrarily late negative instants include actual short intervals. Differentiating the source explicit formula for \(t\ge1\) gives \(|P'(t)|\le C_j e^{dt}\). Absolute summation follows because the native single-sinc multiplier has Gevrey decay in the ordinates even after multiplication by \(p=\rho-1/2\); the differentiated trivial-zero series is uniformly summable as well. For any sufficiently late selected \(t\) with \(|P(t)|\le1\), the mean value theorem makes \(|P|\le2\) on \([t-c_j e^{-dt},t+c_j e^{-dt}]\) for some fixed \(c_j>0\). Together with the lower floor for \(E_Y\), these intervals have the same strict pointwise sign \(<-10^{73}\). One may replace \(d\) by the external \(b\) in the guaranteed lengths. The result proves actual cofinal recurrence of the sign at individual real times. It cannot prove recurrence on the full terminal windows. Indeed (4) holds even under \(d>0\), when the terminal covariances at all sufficiently large integers are positive by the native energy theorem.

## Growing translation limits have the opposite sign

For every fixed \(0<A<2\) the uniform estimate
\[
 E_Z(t)=L_Z+O_{A,j}(e^{-c_A n}),\qquad
 2\le Z\le n^A,\quad n-2\log n\le t\le n                         \tag{2}
\]
holds for all sufficiently large integers \(n\), for some \(c_A>0\). This uses the actual arithmetic throughout.

Here are details of the uniformity. Take a small fixed \(\eta>0\) and an even Bonferroni order \(K\sim\eta n/\log n\). The same squarefree-multiple count and the crude bound \(B\le2\log n+1\) give, uniformly for \(Z\le n^2,\ x\ge1\),
\[
 |N_Z(x)-c_Zx|\ll x e^{-\eta n/2}+\sqrt{x}\,e^{3\eta n}.
\]
Indeed the factorial tail has log cost at most \(-\eta n+o(n)\), and the included finite errors have multiplier bounded by \(3(K+1)(2n^2)^K\). Truncate the sampling to \(0\le v=t-\log r\le n/2\); throughout that portion \(x\ge e^{n/2}/n^2\). Choose \(3\eta<1/8\). The Stieltjes relative error is exponentially small. The variation factor costs only \(e^{o(n)}\) since \(\|V_Z\|_2+\|V'_Z\|_2\ll_j\prod_{p\le Z}(1+p^{-1/2})\) and \(Z\le n^2\).

For the omitted part take \(h>0\) small with \(A(1/2+h)<1\). The superexponential decay of \(U\) and \(U'\) and the finite Euler filter give
\[
 |V_Z(v)|+|V'_Z(v)|\ll_{h,j}e^{-hv}
     \prod_{p\le Z}(1+p^{-1/2+h})\ll e^{-hv+o(n)}
\]
uniformly for \(Z\le n^A\). The continuous and discrete tails above \(n/2\) then cost \(O(e^{-c_A n})\), using total active harmonic mass \(O(n)\). This proves (2).

In fact for each fixed \(0<\kappa<1\),
\[
 E_Z(t)/L_Z\longrightarrow1\quad\hbox{uniformly for }2\le Z\le\kappa^2 n^2/4,
       \quad t\in[n-2\log n,n].                                  \tag{3}
\]
For \(Z\le n\) this follows from (2) and \(L_Z\) bounded away from zero (there are finitely many small distinct cutoffs, and \(L_Z\to\infty\)). For \(Z>n\) choose \(\kappa<\gamma<1\) and use a sufficiently small \(\eta\) to bound absolute Stieltjes error below \(v=\gamma n\) as above. The [borderline Euler asymptotic](ROUGH_CORE_PHASE_TRANSITION.md) and \(c_Z\ge1/(Z+1)\) give \(\log L_Z\sim4\sqrt Z/\log Z\). On \(v\ge\gamma n\), take a small fixed \(a>0\). The pointwise tilted filter bound gives
\[
 |V_Z(v)|^2\ll
 \exp\big(-2av/\log Z+(4e^a+o(1))\sqrt Z/\log Z\big).
\]
For the discrete tail this costs at most \(O(n)\) times the bound at \(\gamma n\); for the continuous tail it costs \(O_a(\log Z)\) times that bound. Since \(2\sqrt Z\le\kappa n\) and \(e^a-a\gamma/\kappa<1\) for sufficiently small \(a>0\), both tails are \(o(L_Z)\). The limits as \(Z\to\infty\) are uniform over this range since \(Z>n\). This proves (3).

The implication for the cofinal sign is precise. For fixed \(Y\), \(E_Z-E_Y\) is exactly the ordered contribution from pairs of different cores above \(Y\) having the same core above \(Z\), by expanding each coarser grouping. Take \(Z=n^A\) with \(0<A<2\), or \(Z=\kappa^2n^2/4\). For every sufficiently late \(n\) that complete partial covariance is **positive**, and its terminal average per unit length is \((1+o(1))L_Z\) where \(\log L_Z\sim4\sqrt Z/\log Z\). Thus the required negative covariance for fixed \(Y\), wherever it recurs, must overcome this growing positive contribution using pairs whose cores remain different even above these near-quadratic cutoffs. Summing successively more fixed-ratio translation limits alone yields the wrong sign. No independent estimate for that last signed contribution has been proved here.
