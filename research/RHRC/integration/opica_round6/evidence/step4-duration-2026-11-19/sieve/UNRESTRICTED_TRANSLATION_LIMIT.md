# The optimum over all finite prime extensions in the translation limit

**DERIVED on paper.** Let \(B_p=\{q\text{ prime}:q<p\}\), \(\ell=\log p\), and \(A=\sum_{q<p}q^{-1/2}\sim 2\sqrt p/\ell\). For the actual causal drive \(U\) and its squarefree translation limit \(L_M\), every finite set of primes \(M\supset B_p\) satisfies, for sufficiently large \(p\),
\[
  \log L_M\ \ge\ A-C_U A/\ell^2.                                      \tag{1}
\]
The constant is independent of the number, sizes and total mass of the added primes. In particular,
\[
 \lim_{p\to\infty}\ \frac1A\inf_{M\supset B_p,\ M\text{ finite}}\log L_M=1.    \tag{2}
\]
The earlier sharp constant under the cap \(q\le p^K\) is \(\sec(\pi/(K+2))\). Sending \(K\) to infinity in its upper bound proves the upper half of (2). Inequality (1) supplies the missing lower bound even when the maximum prime grows faster than any fixed power. [Finite-layer optimum and construction](OPTIMAL_PRIME_MASKS.md)

## A frequency average that pays for each additional prime

Use the cosine-transform convention \(\widehat w(\lambda)=\int_{\mathbb R}w(x)\cos(\lambda x)\,dx\) for even real densities. Let \(r\) be the probability density proportional to \((\sin(x/32)/(x/32))^8\), with its continuous value at zero. Its transform \(T\) is nonnegative and supported on \([-1/4,1/4]\). Indeed \(\sin(x/32)/(x/32)\) is the characteristic function of the uniform law on \([-1/32,1/32]\), so its eighth power corresponds to the eightfold convolution. Also \(T(0)=1\) and \(1-T(y)\le y^2\int x^2r(x)\,dx/2\). The functions \(r,r',r''\) are all \(O((1+|x|)^{-8})\).

The even function \(w_0(x)=(1-\cos x)r(x)\) is a probability density since \(T(1)=0\). Its transform is
\[
 W_0(\lambda)=T(\lambda)-\tfrac12T(\lambda-1)-\tfrac12T(\lambda+1).
\]
It is nonpositive for every \(\lambda\ge1\) and equals \(-1/2\) at \(1\). For \(0\le\lambda\le1\), the quadratic estimate on \(T\) near zero, followed by boundedness on \([0,3/4]\), gives
\[
 W_0(\lambda)\le-1/2+C(1-\lambda)^2.                              \tag{3}
\]

For strict negativity at every large frequency, set \(a=1/2\) and take the probability density \(w_1(x)=(a^2/2)|x|e^{-a|x|}\). Its cosine transform satisfies
\[
 W_1(\lambda)=\frac{a^2(a^2-\lambda^2)}{(a^2+\lambda^2)^2}
 \le-\frac{3}{25\lambda^2}\quad(\lambda\ge1).
\]
Choose \(\epsilon=\ell^{-3}\), \(R=\sqrt\ell\) and \(b=(1-\epsilon)w_0+\epsilon w_1\). Let \(\chi\) be any fixed smooth even cutoff taking values in \([0,1]\), one on \([-1,1]\) and zero outside \([-2,2]\). Set \(g=(1-\chi(x/R))b(x)\). For large \(R\), direct differentiation gives \(\|g\|_1+\|g''\|_1=O(R^{-7})\) uniformly in \(\epsilon\in[0,1]\). The cutoff vanishes in \(g\) near the cusp of \(w_1\), and the contributions of \(w_1\) and its first two derivatives outside \([-R,R]\) decay exponentially. Twice integrating by parts bounds \(|\widehat g(\lambda)|\le C R^{-7}/\lambda^2\) for \(\lambda\ne0\).

Normalize \(w=(b-g)/\int(b-g)\), and write \(W=\widehat w\). Since \(R^{-7}=o(\epsilon)\) and \(\int(b-g)=1-O(R^{-7})\), the following estimates hold with constants independent of \(p\):
\[
 \begin{split}
 W(\lambda)&\le -c\epsilon/\lambda^2 &&(\lambda\ge1),\\
 W(\lambda)&\le -1/2+C(1-\lambda)^2+O(\epsilon) &&(0\le\lambda\le1).
 \end{split}                                                        \tag{4}
\]
The second inequality follows by comparing with (3) in \(L^1\) before taking transforms. The density is uniformly bounded and supported on \([-2R,2R]\).

For a prime \(q\), put \(z=q^{-1/2}\) and \(\lambda=(\log q)/\ell\). Its contribution to the averaged logarithm of the squared Euler modulus, after the squarefree density is included, is exactly
\[
 H_q=-2\sum_{m\ge1}\frac{z^m}{m} W(m\lambda)-\log(1+z^2).          \tag{5}
\]
Absolute convergence justifies integration term by term. For \(q\ge p\), every term of the sum with its leading minus sign is nonnegative by (4). The \(m=1\) term alone pays \(\log(1+z^2)\le z^2\), because
\[
 \sup_{\lambda\ge1}\lambda^2p^{-\lambda/2}=p^{-1/2}\le2c\ell^{-3}
\]
for all sufficiently large \(p\). The supremum is at \(1\) for \(\ell>4\). Thus \(H_q\ge0\) simultaneously for every added prime, with no loss proportional to their number.

For the prefix, (4) and absolute summation of the higher harmonics in (5) give
\[
 \sum_{q<p}H_q\ge A-O\!\left(\ell^{-2}\sum_{q<p}q^{-1/2}\log^2(p/q)
                    +\epsilon A+\sum_{q<p}q^{-1}\right)
             \ge A-O(A/\ell^2).                                      \tag{6}
\]
For the last inequality the weighted second moment is \(O(A)\). Below \(\sqrt p\), bounding by all integers gives \(O(p^{1/4}\ell^2)=o(A)\). Above \(\sqrt p\), split at \(pe^{-j}\). The prime-counting upper bound \(\pi(y)\ll y/\log y\) makes the contribution of each shell \(O((\sqrt p/\ell)(1+j)^2e^{-j/2})\). Also \(\sum_{q<p}q^{-1}\le1+\ell=o(A/\ell^2)\).

## The native source and sharpness

The actual transform \(\widehat U(s)\) is entire and nonzero as a function, so for some integer \(d\ge0\), \(|\widehat U(i\tau)|\ge c_U|\tau|^d\) on a punctured neighborhood of zero. All \(x/\ell\) in the support of \(w\) lie there for large \(p\), except the single point zero. Uniform boundedness of \(w\) gives \(\int w(x)\log|x|\,dx\ge-C\) by integrability on \([-1,1]\). Consequently \(\int w(x)\log|\widehat U(ix/\ell)|^2\,dx\ge-O_U(\log\ell)\). [Source and squarefree density definitions](INDIVIDUAL_PRIME_ECHO.md)

By Plancherel and the substitution \(\tau=x/\ell\), \(L_M\) is \((2\pi\ell\zeta(2))^{-1}\) times the Lebesgue integral of
\[
 G(x)=|\widehat U(ix/\ell)|^2\prod_{q\in M}\frac{|1-q^{-1/2-ix/\ell}|^2}{1+1/q}.
\]
Jensen gives \(\int G\,dx\ge\|w\|_\infty^{-1}\int w G\,dx\ge \|w\|_\infty^{-1}\exp(\int w\log G\,dx)\). Combining this with (5), (6) and the source bound proves (1). This uses only frequencies within \(2/\sqrt\ell\) of zero.

For each fixed integer \(K\), the deterministic finite-layer construction gives \(\limsup_p A^{-1}\inf_M\log L_M\le\sec(\pi/(K+2))\). Letting \(K\to\infty\) proves (2). A single sequence can also realize this limit. Choose increasing thresholds for successive \(K\) beyond which each fixed-degree construction has relative log rate within \(1/K\) of its limiting constant. Increase the degree at these thresholds. This diagonal sequence gives a first-order optimum and (1) gives a one-sided second-order estimate. The order and coefficient of the actual optimum's next term remain open.

## Why the horizon restriction matters

The uniform lower bound in (1) concerns translation limits. Its unrestricted analogue for the pointwise native energy \(E_M(t)\) is false. At integer horizon \(n\), choose \(M\) to contain all primes up to \(e^n\). At every \(t\le n\), causality leaves only the rough core \(r=1\). All active terms of the finite Möbius expansion are present, so \(V_M(t)=P(t)\) and \(E_M(t)=P(t)^2\). The actual source has \(\liminf_{t\to\infty}|P(t)|=0\). Taking \(n=\lceil t\rceil\) along such instants places them in native terminal windows, even with a growing prefix such as \(p\sim n\). This rules out a uniform pointwise floor over unrestricted masks. The sign on an entire cofinal window and the positive native quadrature remain **OPEN**. [Cofinal recurrence at instants](../../step4-correlation-2026-11-19/divisor/FIXED_SIEVE_RECURRENCE_AUDIT.md)
