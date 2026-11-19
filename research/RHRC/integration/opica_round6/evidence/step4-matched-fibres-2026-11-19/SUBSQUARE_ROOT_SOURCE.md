# Complete prime-area observations with sub-square-root summation cutoffs

**DERIVED on paper.** Write \(A(x)=\int_2^x(\vartheta(u)-u)du\). There are two different conclusions.

* At the **original, unsmoothed horizon**, the supplied zero ceiling \(r=0.873346\) permits an observation on ordinary summation primes \(p<x^{0.485}\) that equals \(A(x)+(2/3)x^{3/2}+o(x^{3/2})\).
* At **one fixed, compactly smoothed horizon** with nonzero transfer coefficient at every rightward zeta zero, there is an **unconditional** observation on ordinary primes \(p\le\sqrt x\) with \(o(x^{3/2})\) reconstruction error. It even allows a subpower reduction below \(\sqrt x\). With the external ceiling it allows \(p<x^{0.42748922+\epsilon}\) for every fixed \(\epsilon>0\).

All observables are specified below. Their weights use integer divisor arithmetic extending beyond their largest summation prime. None of these estimates bounds the signed observable itself.

## A common finite divisor construction

Fix an integer \(K\ge7\) and let \(\mathcal K=\{1\le k\le K:\mu(k)\ne0\}\). Put

\[
 \eta(w)=(1-2^{1-w})\zeta(w),\quad N_K(s)=\prod_{k\in\mathcal K,\ k>1}\eta(ks),
 \quad H_K(s)=\zeta(s)N_K(s),\quad \frac1{H_K(s)}=\sum c_K(n)n^{-s}\quad(\Re s>1).
\]

Take an integer \(L\ge2\). Begin with the polynomial \(D^0(s)=\sum_{n\le L} c_K(n)n^{-s}\); in the unsmoothed-horizon proof only, smoothly taper these coefficients past \(L\) as specified below. Put \(R=2L+1\). Add terms \(b_i(R2^i)^{-s}\), \(0\le i<n_0=1+|\mathcal K|\), obtaining \(D(s)\) with the exact conditions

\[
 D(1)=0,\quad D'(1)=1/N_K(1),\quad D(1/2)=1/H_K(1/2),\quad
 D(1/k)=0\quad(k\in\mathcal K,\ k\ge3).                               \tag{1}
\]

All constants in these equations are real. The normalization at \(1/2\) is defined since real \(\eta(u)>0\) for \(u>0\), and \(\zeta(1/2)\ne0\). Moreover \(1/N_K(1)\) and \(1/H_K(1/2)\) stay bounded independently of \(K\), since the fixed first factors are nonzero and \(1-\eta(u)=O(2^{-u})\) for \(u\ge2\).

For \(G(s)=D(s)H_K(s)=\sum g(n)n^{-s}\) at \(\Re s>1\), let \(J(y)=\sum_{n\le y}g(n)(y-n)\), zero for \(y<1\). At real \(v\ge2\) use the exact observable

\[
 S_D(v)=\sum_{p\le v}\big[(v-p)-pJ(v/p)\big]\log p.                   \tag{2}
\]

The initial coefficients of \(D\) through \(L\) equal those of \(1/H_K\), so \(g(1)=1\) and \(g(n)=0\) for \(2\le n\le L\). Thus every term for \(p\ge v/(L+1)\) is zero, including equality. No prime coefficient is discarded. The original lower integration endpoint 2 gives \(A(v)=\sum_{p\le v}(v-p)\log p-v^2/2+2\).

The true projected ramp \(Q_D(v)=\sum_{p\le v}p\log p\,J(v/p)\) is the inverse Mellin integral of

\[
 \frac{v^{1+s}D(s)H_K(s)P(s)}{s(s+1)},\qquad
 P(s)=\sum_p\frac{\log p}{p^s}=-\sum_{j\ge1}\mu(j)\frac{\zeta'(js)}{\zeta(js)} . \tag{3}
\]

Initially integrate on \(\Re s=2\), with absolute convergence. In (3) every prime-power divisor is retained since \(\sum_{j\mid a}\mu(j)\) is 1 at exponent 1 and zero above. The factors of \(H_K\) cancel the denominators for \(j\in\mathcal K\). Each differentiated factor is then accompanied by the corresponding eta polynomial, except the \(j=1\) factor uses \(\zeta'(s)\) directly. For remaining \(j\), use absolute convergence wherever \(j\Re s>1\). At \(s=1\), \(H_K\) and \(P\) each have a simple pole. Equations (1) give the sole residue \(v^2/2\) there. At \(s=1/k\) for included \(k>1\), the logarithmic-derivative sum has residue \(\mu(k)/k\); the projected ramp residue is

\[
 \mu(k)\frac{k}{k+1}D(1/k)H_K(1/k)v^{1+1/k}.
\]

Its square term is exactly \(-(2/3)v^{3/2}\), with every cubic and later included residue zero. This uses the whole primorial-source measure. The [earlier three-factor derivation](../step4-area-runs-2026-11-19/ETA_FILTERED_PRIME_LOCALIZATION.md) gives the underlying ramp conventions.

## Original horizon with the external ceiling

Take \(K=7\), \(\sigma=0.101\) and \(L=\lfloor x^{0.515}\rfloor\). The first nonzero Möbius index above 7 is 10. Thus the rest of the sum in (3) converges absolutely on \(\Re s\ge\sigma\). Fix \(b=0.874>r\). For \(u\ge b\) the external ceiling gives \(1/\zeta(u+it)\ll_\epsilon(1+|t|)^\epsilon\) (see the disk proof and external theorem link in [the earlier localization](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md)). The same disk argument for \(|\log\zeta|\) gives \(\zeta(u+it)\ll_\epsilon |t|^\epsilon\) away from its pole at 1. All reciprocals of \(\eta(ks)\), \(k\ge2\), on \(\Re s\ge b\) are uniformly bounded by absolute convergence and the geometric series in \(2^{1-ks}\). Hence \(1/H_K(s)\ll_\epsilon (1+|t|)^\epsilon\) there.

Choose a real \(C^\infty\) cutoff \(w\) equal to 1 for \(0\le u\le1\) and 0 for \(u\ge2\); use \(D^0(s)=\sum c_K(n)w(n/L)n^{-s}\). Its Mellin kernel \(W(z)=\int_0^\infty w(u)u^{z-1}du\) extends meromorphically with residue 1 at 0 and decays faster than every fixed inverse power on bounded vertical strips, by integration by parts in the compactly supported derivative. Mellin inversion gives

\[
 D^0(s)=\frac1{2\pi i}\int \frac{W(z)L^z}{H_K(s+z)}\,dz
\]

initially on \(\Re z>\max(0,1-\Re s)\). Moving to \(\Re(s+z)=b\) proves \(|D^0(\sigma+it)|\ll_\epsilon L^{b-\sigma}(1+|t|)^\epsilon\) uniformly in real \(t\). At the fixed real nodes \(v=1/k< b\) it gives \(O(L^{b-v})\). Near 1 one crosses the pole of \(W\), getting \(D^0(s)=1/H_K(s)+O(L^{b-\Re s})\) uniformly there; differentiating the integral with a fixed contour at \(s=1\) gives the same error with an arbitrarily small factor \(L^\epsilon\) for the derivative (alternatively apply Cauchy's estimate on radius \(1/\log L\)). Since \(1/H_K\) has value 0 and derivative \(1/N_K(1)\) at 1, both deficits in (1) are \(O_\epsilon(L^{b-1+\epsilon})\). Rescale each interpolation equation by \(R^v\), absorbing \(\log R\) times its value equation in the derivative row. The fixed confluent Vandermonde matrix with nodes \(2^{-1/k}\), derivative at 1 in the \(s\) variable, now yields \(|b_i|\ll_\epsilon L^{b+\epsilon}\). Hence also

\[
 |D(\sigma+it)|\ll_\epsilon L^{b-\sigma+\epsilon}(1+|t|)^\epsilon .    \tag{4}
\]

For (3) on \(\Re s=\sigma\), use the functional equation on the factors with \(k=1,2,3\). Their total power cost at height \(T\ge2\) is \(T^{0.399+0.298+0.197}=T^{0.894}\), allowing a logarithm for a differentiated gamma factor. Among the six remaining ordinary zeta or zeta-derivative factors the real parts, now reflected where necessary, are \(0.899,0.798,0.697,0.505,0.606,0.707\). The first costs \(T^\epsilon\) pointwise by the external ceiling, and the second costs at most \(T^{0.101+\epsilon}\) by classical convexity. On the other four apply Hölder and the fourth-moment bound \(\int_T^{2T}|\zeta(u+ikt)|^4dt\ll_\epsilon T^{1+\epsilon}\) on each fixed line \(u>1/2\). This bound follows from the classical critical-line fourth moment and interpolation between vertical mean values; it also holds for derivatives on fixed lines strictly to the right of \(1/2\) by Cauchy's formula on small circles and the same bound on the neighboring lines. Rescaling fixed \(k\) changes constants only. Reflected factors have conjugate arguments and the same absolute bounds. The total dyadic mean of the absolute product in (3), BEFORE its ramp denominator, is \(O(T^{0.995+\epsilon})\), where mean means integral divided by \(T\). The denominator contributes \(O(T^{-2})\), so the vertical integral is absolutely convergent with (4). On horizontal sides between \(\sigma\) and 2, classical convexity alone gives growth at most \(T^{(6-24\sigma)/2+\epsilon}=T^{1.788+\epsilon}\) for these six factors, and \(D\) is a finite polynomial bounded at each fixed \(x\) uniformly in height on the strip. The horizontals vanish. These bounds also handle the bounded higher-index logarithmic-derivative tail. [Ivić, mean-value estimates](https://hrj.episciences.org/164/pdf) · [Zeta functional equation](https://dlmf.nist.gov/25.4)

The projected remainder costs \(O_\epsilon(x^{1+\sigma}L^{b-\sigma+\epsilon})\). Here \(1+0.101+0.515(0.874-0.101)=1.499095<1.5\). Using (2), (3) and the calculated residues proves the first assertion for the original horizon. No independence is assumed for the primes in (2) and the inverse coefficients, which have nontrivial arithmetic content through \(2L\).

## One fixed positive smoothed horizon

Fix \(a_j=1/j^2\) and let \(h\) be the law on log scale of \(\sum_{j\ge1}U_j\), independent uniforms on \([-a_j,a_j]\). This merely constructs a deterministic positive smoothing kernel. It has support \([-d,d]\), \(d=\sum_j a_j\), and transform

\[
 V(w)=\int e^{wt}dh(t)=\prod_{j\ge1}\frac{\sinh(a_jw)}{a_jw}.
\]

The product converges locally uniformly and is nonzero for \(\Re w\ne0\) since every factor is nonzero there and its departure from 1 is summable for fixed \(w\). For \(0\le\Re w\le3\), each factor is bounded by \(e^{3a_j}\min(1,1/(a_j|\Im w|))\) when \(\Im w\ne0\), by the uniform integral and the two endpoints of the exponential. Using the first \(\lfloor\sqrt{|\Im w|}/2\rfloor\) factors gives \(|V(w)|\ll\exp(-c\sqrt{|\Im w|})\) uniformly. Fourier inversion gives a compact smooth density. The smoothed observable is \(\bar A(x)=\int A(xe^t)dh(t)\). A zero mode \(x^{1+\rho}\) retains the multiplier \(V(1+\rho)\ne0\). The calculation does not identify \(\bar A(x)\) with the sharp area at that same \(x\).

## Uniform inverse bounds with an increasing number of filters

Let \(\ell=\log x\), \(K=\lfloor\sqrt\ell\rfloor\), \(\sigma=1/(K+1/2)\) and \(L=\lceil e^d\sqrt x\rceil\). Use the sharp prefix \(D^0(s)=\sum_{n\le L}c_K(n)n^{-s}\) in this part. Define \(F(u)=(\log u)^{3/5}(\log\log u)^{-1/5}\) for sufficiently large \(u\). The unconditional Vinogradov–Korobov Mertens estimate gives \(\sum_{n\le u}\mu(n)\ll u\exp(-c F(u))\) for some absolute \(c>0\). [Lee and Leong, primary estimate](https://arxiv.org/abs/2208.06141)

Write \(c_K=\mu*b_K\). Uniformly in \(K\), \(\sum_n |b_K(n)|n^{-3/4}\ll1\): each reciprocal eta factor at \(k\ge2\) contributes at most \(\zeta(3k/4)/(1-2^{1-3k/4})\) in absolute Dirichlet norm; their infinite product converges. In \(\sum_{d\le u}b_K(d)M(u/d)\), terms \(d\le\sqrt u\) inherit \(\exp(-c'F(u))\) since \(F(\sqrt u)\asymp F(u)\). Terms \(d>\sqrt u\) cost \(O(u^{7/8})\). Consequently \(\sum_{n\le u}c_K(n)\ll u\exp(-c'F(u))\) uniformly. With a smaller absolute \(c'>0\) as necessary, partial summation gives

\[
 |D^0(v+it)|\ll (1+|t|)L^{1-v}e^{-c'F(L)}\quad(0\le v\le1/2).
\]

For the integral in partial summation split at \(\sqrt L\) and use \(1-v\ge1/2\). At \(s=1\), partial summation on the infinite tails also gives value and derivative errors \(O(e^{-c'F(L)})\) against \(1/H_K\) and its derivative. Indeed \(\int_L^\infty (1+\log t)e^{-cF(t)}dt/t\ll e^{-c'F(L)}\), and the summed series and derivative at 1 agree by continuity from the right. This estimate is uniform in \(K\).

After multiplying each interpolation row at \(v\) by \(R^v\), its deficit is \(O(Le^{-c'F(L)}\log(2L))\), including the derivative row and the prescribed bounded square value. For completeness, the interpolation unknowns are the coefficients of \(B(z)=\sum b_i z^i\), evaluated at the distinct nodes \(z_k=2^{-1/k}\); at \(z_1=1/2\) prescribe both value and derivative. Distinct nodes have separation \(\gg K^{-2}\) by the mean-value theorem. The ordinary Lagrange basis polynomials have coefficient norm \(\ll(CK^2)^{n_0}\) since their numerator coefficient norms are at most \(2^{n_0}\). To allow the single repeated node, first interpolate the values, then add a multiple of \(\prod_k(z-z_k)\) to fit the derivative there. Its derivative at \(z_1\) has magnitude \(\ge(c/K^2)^{n_0}\). Polynomial differentiation and multiplication in this procedure cost at most another \(\exp(O(K\log K))\). Therefore the exact solution satisfies

\[
 |D(\sigma+it)|\ll (1+|t|) L^{1-\sigma}\exp[-c'F(L)+O(K\log K+\log\log L)]. \tag{5}
\]

## Uniform contour and square-scale error

The smoothed version of (3) has an extra factor \(V(1+s)\). Only \(j>K\) remain in the logarithmic-derivative tail. For \(K<j\le 2K+2\), \(j\sigma-1\gg K^{-1}\) and absolute convergence gives each term \(O(K^2)\), for example via \(\sum (\log n)n^{-1-c/K}\). For larger \(j\) the geometric decay costs \(O(K)\) in total. This tail is uniformly polynomial in \(K\), including at bounded heights. On the new vertical line all \(1\le k\le K\) satisfy \(|1-k\sigma|\gg K^{-1}\), so no pole occurs on the line. Euler summation in the form \(\zeta(w)=w/(w-1)-w\int_1^\infty\{y\}y^{-1-w}dy\) and its derivative bound every \(\zeta(ks),\zeta'(ks)\) by \(K^{O(1)}(1+|t|)^{O(1)}\), with absolute exponents. The factors \(1-2^{1-ks}\) are bounded by 3. After cancellation in (3) there are at most \(K+1\) terms, each with at most \(K\) such factors and the bounded tail where applicable. The same polynomial bounds hold on the horizontals for high \(|t|\), since those heights avoid all real poles. The factor \(1/|s(s+1)|\) costs at most \(O(K)\) at low heights. The smoothed contour is absolutely convergent. The integral of \((1+|t|)^{CK+1}e^{-c\sqrt{|t|}}\) is \(\exp(O(K\log K))\) by the gamma integral. For each fixed \(x,K\) all horizontals tend to zero, and the displayed bounds on the new vertical line are uniform in both.

The residues at \(1\) and \(1/2\) give \(V(2)x^2/2\) and \(-(2/3)V(3/2)x^{3/2}\); all other included ones vanish by (1). By (5) the vertical error is at most

\[
 x^{1+\sigma} L^{1-\sigma}\exp[-c'F(L)+O(K\log K+\log\log L)].         \tag{6}
\]

Here \(\sigma\ell=O(\sqrt\ell)\), \(F(L)\asymp\ell^{3/5}(\log\ell)^{-1/5}\) and \(K\log K=o(F(L))\). Thus (6) is \(O(x^{3/2}e^{-c''F(x)})\) for some \(c''>0\). With (2) we obtain

\[
 \bar A(x)+\tfrac23 V(3/2)x^{3/2}
 =\int S_D(xe^t)\,dh(t)+O(x^{3/2}e^{-c''F(x)}).
\]

All summation primes in this last integral satisfy \(p<e^d x/(L+1)\le\sqrt x\). The same proof works for \(L=\lceil e^d\sqrt x\exp(c_0F(x))\rceil\) with sufficiently small fixed \(c_0>0\), leaving summation primes below \(\sqrt x\exp(-c_0F(x))\). The small original lower-endpoint constant is included in the error.

## What further smoothing can buy with the external ceiling

For each fixed \(b>r\) close to \(r\), \(M(t)\ll_b t^b\) by the [disk and Perron argument](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md). Since \(b>3/4\), the uniform convolution estimate above yields \(\sum_{n\le t}c_K(n)\ll_b t^b\). For fixed \(K\), repeat the sharp-cutoff partial summation and interpolation with this power saving. On the new contour \(D(s)\ll_{b,K}(1+|t|)L^{b-\sigma}\log^2(2L)\); the fixed positive smoothing absorbs its linear height cost. Taking any \(\lambda<1/(2r)\), choose \(b>r\) and then \(K\) large enough that \(1+\sigma+\lambda(b-\sigma)<3/2\). With \(L=\lceil e^d x^\lambda\rceil\), the smoothed observation has summation primes below \(x^{1-\lambda}\) and error \(o(x^{3/2})\). The limiting summation exponent from this bound is \(1-1/(2r)=0.4274892196\ldots\).

Even ideal vertical decay does not remove the factor \(L^{b-\sigma}\) from this argument. Nor does small summation support give small arithmetic weights. If a rightward zero yields a signed centered peak of order \(x^{1+a}\) in a particular tested observable and if only \(p\le x^\nu\) are summed there with square-scale reconstruction error, Chebyshev's \(\sum_{p\le x^\nu}\log p\ll x^\nu\) forces some effective weight to be \(\gg x^{1+a-\nu}\). For the smoothed test the effective weight includes its full horizon integral. The coefficient sieve, common normalizations and genuine prime arithmetic still couple the results. There is no independent size bound for the residual and no conclusion here excluding a zero. Step 4 and RH remain OPEN.
