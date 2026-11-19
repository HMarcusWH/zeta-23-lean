# What the projected divisor graph contributes at each prime-factor ratio

**DERIVED on paper for the complete one-copy source.** Fix the original cutoff \(Y=10^7\). Every fixed primitive ratio in the squarefree divisor graph has an independently calculable complex limit after applying the localized [Laguerre probe](POISSON_PRIME_RANGE.md). All common divisors of the two endpoints enter the limit. Even if the primitive ratios retained are allowed to grow subexponentially in the order, their total cannot carry a hypothetical exponentially growing response. The unresolved part is a signed sum between groups with larger primitive products.

## One diagonal for the exact projected graph

Write \(V=\prod_{p\le Y}(1-S_p)U\) for the finite Möbius transform of the true integer drive. Put \(f_n(t)=\ell_n(t)e^{-i\tau_n t}W_n(t)\) for \(t\ge0\), zero otherwise. Here \(W_n\) is exactly the positive Poisson weight from the localization. This calculation works both for the cube-root modulation and for the logarithmically slow modulation in the [recurrence calculation](jets/SINGLE_SCALAR_CAYLEY.md), since only \(\tau_n\to0\) is needed here. Define
\[
 h_n(x)=\int_\mathbb R V(t-x)f_n(t)\,dt,\qquad
 z_{n,r}=\frac{\mu(r)}{\sqrt r}\mathbf1_{(r,\Pi_Y)=1}\,h_n(\log r).
\]
All of \(V\), its first derivative and their translates are fixed independently of the order. The drive and its derivatives are causal, smooth and rapidly decreasing at positive infinity by fixed-order Euler summation to any required order with the vanishing source moments. These properties pass through the fixed finite sieve. For each \(n\), the taper decays exponentially in \(t\) times a polynomial of fixed degree, as does the Laguerre function. This gives absolute convergence of the projected arithmetic sum and its square. In particular \(\sum_r z_{n,r}=\int f_nP\) retains the original prime powers.

There is an order-independent bound for the diagonal \(D_n=\sum_r |z_{n,r}|^2\). Indeed \(\|f_n\|_2\le1\) and
\[
 D_n\le \|V\|_1\int |f_n(t)|^2\sum_{r\ge1}r^{-1}|V(t-\log r)|\,dt\le C_Y .
\]
Each unit interval of \(\log r\) has harmonic mass at most two, and the sum of unit-interval suprema of \(|V|\) is finite. The bound also applies to \(h_n(\log r+u)\) with harmonic weights \(1/r\), uniformly in every real shift \(u\).

## The limit from the actual filters

Let \(\alpha=2.27\cdot10^{-19}\), \(\lambda=10^6\). Define \(w(v)=1\) for \(v\le\alpha\), \(w(v)=0\) for \(v\ge1.01\alpha\), and interpolate linearly on the intervening interval. Set
\[
 \mathcal K(s)=\frac1{2\pi}\int_\mathbb R e^{i\xi s}
 \frac{2|\widehat V(\xi)|^2}{1+\xi^2}
 w\!\left(\frac{2\lambda}{1+\xi^2}\right)^2d\xi .
\]
The kernel is real and even. It is positive definite as a function of differences; its value at zero is strictly positive. Indeed \(V\ne0\), its Fourier transform is entire by the drive's decay, and the passband contains real intervals. This establishes positivity without assigning an unverified numerical lower to the high-frequency mass.

For clarity, the magnitude of the Fourier multiplier has a pointwise limit even though its phase generally has none. At each fixed frequency \(\xi\), the Taylor coefficients \(c_j\) in [the stable-mode calculation](jets/POISSON_STABLE_MODES.md) satisfy
\[
 \sum_j|c_j|=O_\xi(1),\qquad
 \sum_j(j-nv_n)^2|c_j|^2=O_\xi(\sqrt n),\qquad
 v_n=\frac{2\lambda}{1+(\xi\pm\tau_n)^2}.
\]
The sign depends on the chosen Fourier convention and disappears in the limit. Outside \(|j-nv_n|\le\epsilon n\), Cauchy–Schwarz bounds the absolute tail by \(O_\xi(n^{-1/4}/\sqrt\epsilon)\). Within this interval the fraction of Poisson partial sums that retain coefficient \(j\) is within \(O(\epsilon/\alpha)+o(1)\) of \(w(v_n)\), including at the two endpoints. First take \(n\to\infty\), then \(\epsilon\downarrow0\). The multiplier is thus \(w(v_n)\) times the full critical-mode multiplier plus \(o(1)\). The Fejér bound \(201\sqrt2\) holds uniformly at every real \(\xi\). Plancherel and dominated convergence give, for fixed \(u,v\),
\[
 \int_{\mathbb R}h_n(x+u)\overline{h_n(x+v)}\,dx
 \longrightarrow\mathcal K(u-v).
\]

It remains to check that sampling at the actual integers has this same limit times the correct density. If \(A\) is any fixed finite set of primes, its admissible squarefree integers have counting function \(c_A X+O_A(\sqrt X)\). On \(x\ge R\), partial summation against their harmonic counting measure differs from \(c_A\,dx\) by at most \(O_A(e^{-R/2})(\|\phi\|_\infty+\|\phi\|_1+\|\phi'\|_1)\) for the test \(\phi(x)=h_n(x+u)\overline{h_n(x+v)}\). For example the primitive of the difference tends to a constant with error \(O_A(e^{-x/2})\); remove that constant before integration by parts. The test norms are uniformly bounded by Young's inequality and \(\|V'\|_1<\infty\). On compact \(x\)-intervals \(h_n(x)\to0\) uniformly. In fact \(f_n\rightharpoonup0\) by orthonormality of \(\ell_n\) and pointwise convergence of the bounded taper and modulation to one, and the translates of \(V\) form a compact family there in \(L^2\). The negative half-line of the continuous integral costs \(o(1)\): the map \(f\mapsto h|_{x<0}\), with \(f\) supported on the positive half-line, is Hilbert–Schmidt since \(\int_0^\infty u|V(u)|^2du<\infty\). The same holds for each fixed translated boundary. First send \(n\to\infty\) and then \(R\to\infty\). This proves in particular \(D_n\to c_Y\mathcal K(0)>0\), with \(c_Y\) the squarefree density excluding the primes up to \(Y\). [Squarefree sampling proof](../step4-correlation-2026-11-19/ALL_HORIZON_DIAGONAL.md)

The [slow-modulation recurrence proof](jets/UNSHIFTED_COFINAL_GRAPH.md) uses this same positive diagonal limit.

## The graph on primitive ratios

For an ordered pair of nonzero squarefree endpoints write \(r=ga,\ l=gb\), \((a,b)=1\). Both \(a,b\) are squarefree, supported above \(Y\), and \(g\) is squarefree and coprime to \(\Pi_Y ab\). Its sign cancels exactly between the two endpoints. Denote the sum of \(z_{n,r}\overline{z_{n,l}}\) over this whole class by \(C_n(a,b)\). The preceding sampling calculation yields
\[
 \lim_{n\to\infty} C_n(a,b)
 =\frac{\mu(a)\mu(b)c_Y}{\sqrt{ab}}
   \prod_{q\mid ab}\frac{q}{q+1}\;\mathcal K(\log(a/b)).
\]
In particular, for any fixed finite prime set \(A\) above \(Y\), summing all directions with \(ab\mid\prod_{q\in A}q\), including the diagonal, gives the actual limit
\[
 \frac{c_Y}{2\pi}\int_\mathbb R
 \frac{2|\widehat V(\xi)|^2}{1+\xi^2} w\!\left(\frac{2\lambda}{1+\xi^2}\right)^2
 \prod_{q\in A}\left(1-\frac{2\sqrt q}{q+1}\cos(\xi\log q)\right)d\xi>0.
\]
Each prime can appear on the first endpoint, the second, or neither. Those three choices produce exactly one factor in the integral. This is an exact family of finite prime-pattern calculations on infinitely many common divisors of the **original** graph.

As a check, the [finite calculation](PRIMITIVE_PATTERN_CHECK.json) used the eight smallest primes above \(10^7\). It evaluated all \(3^8=6561\) ordered primitive directions independently and compared their sum with the product at eight frequencies inside the passband. At six frequencies the factor exceeded the diagonal value one, and at two it was smaller. This checks a frequency multiplier; the full graph also integrates it against the actual source spectrum. [Reproduce the calculation](check_primitive_patterns.py)

There is also a bound uniform in both primitive endpoints. Apply Cauchy–Schwarz to the complete common-divisor sum and use the uniform shifted diagonal bound above to obtain \(|C_n(a,b)|\le C_Y/\sqrt{ab}\). The same proof bounds the sum of the absolute edge weights within the entire class. Therefore
\[
 \sum_{ab\le X}\sum_g |z_{n,ga}z_{n,gb}|
 \le C'_Y\sqrt X(1+\log X).
\]
Here the inner sum has the same admissibility conditions as the class. The elementary last bound follows by summing \((ab)^{-1/2}\) first over \(b\le X/a\). This prices all primitive products through \(X=\exp(o(n))\), including arbitrarily large \(g\).

If a rightward zero exists, the complete scalar \(\sum_r z_{n,r}\) grows with base \(R>1\) from the Cayley criterion. For any \(0<\epsilon<4\log R\), the signed sum over primitive products \(ab>\exp((4\log R-\epsilon)n)\) then has real value \(\exp((2\log R+o(1))n)\) at every sufficiently large order. The remaining classes have smaller exponential rate by the absolute bound. This conclusion preserves both orientations. Conversely, at any chosen \(X_n=\exp(o(n))\), an independent cofinal subexponential upper for the real signed sum above \(X_n\) would exclude every rightward zero. No such estimate follows by taking the limit for each fixed ratio. Its uniformity as new prime patterns enter is the unresolved arithmetic.

## A finite residual after removing two independently controlled sets of edges

Use the bound \(C_Y/\sqrt{ab}\) before summing signs. For an arbitrary finite set \(A\) of allowed unmatched primes it gives, at every order,
\[
 \sum_{\mathrm{supp}(ab)\subset A}\sum_g |z_{n,ga}z_{n,gb}|
 \le C_Y\prod_{q\in A}(1+2/\sqrt q).
\]
The finite product has one choice for omission and two possible endpoints for each prime. Thus *all* directions made from primes \(\le Q_n=n^2\log(n+2)\) cost \(\exp(o(n))\) jointly, even when their primitive product is large. Indeed partial summation with the ordinary prime number theorem gives \(\sum_{q\le Q}q^{-1/2}\sim2\sqrt Q/\log Q\). This uses only squarefree factorization, the fixed-source frame bound and classical prime counting.

The graph itself can be cut off above \(r,l\le e^{T_n}\), \(T_n=2.33\cdot10^{-25}n+2\), with total **absolute** deleted edge weight \(o(1)\). On \(\log r> T_n\) the causal drive forces \(t\ge T_n\). The harmonic-bin translation estimate for the absolute drive gives \(\sum_r r^{-1/2}|V(t-\log r)|\le C_Y e^{t/2}\) by summing first on unit intervals in \(t-\log r\). Above \(T_n\) the taper costs at most \(e^{-40t}\). Cauchy–Schwarz with \(\|\ell_n\|_2=1\) now bounds the total high-endpoint weight by \(O_Y(e^{-39.5T_n})\). The total absolute weight of *all* endpoints is \(O_Y(e^{T_n/2}+1)\), using \(W_n\le1\) below \(T_n\). Multiplying these bounds pays both deleted orientations.

For a precise remaining arithmetic target take \(X_n=\exp(n/\log(n+2))\). Form the finite real sum of \(z_{n,r}\overline{z_{n,l}}\) over the ordered pairs satisfying all three conditions
\[
 r,l\le e^{T_n},\qquad
 m=rl/\gcd(r,l)^2>X_n,\qquad
 P^+(m)>Q_n .
\]
Here \(P^+(m)\) is the largest prime factor; \(m=1\) is excluded by the product condition. Both orientations enter, making the sum real. Call it \(S_n\). The preceding bounds on absolute weights pay the **union** of discarded sets by \(\exp(o(n))\), without a sign assumption. Under a rightward zero \(S_n=\exp((2\log R+o(1))n)\) at every sufficiently large order. Under RH its positive part is at most \(\exp(o(n))\) because the complete scalar is bounded and the complement is paid. Accordingly the independent target is
\[
 \liminf_{n\to\infty}\frac{\log(1+\max(S_n,0))}{n}=0 .
\]
This statement keeps the actual Möbius signs and allows common prime factors of any size permitted by the endpoint bounds. The lower product cutoff becomes useful asymptotically. It can exceed the available product range at finite orders. The estimates give no cofinal cancellation for the displayed residual.
