# A one-sided prime-count criterion on every fixed power grid

**DERIVED on paper.** Fix an integer \(k\ge1\). Write \(C(x)=\pi(x)-\operatorname{li}(x)\) for the ordinary, unnormalized prime count with the principal-value logarithmic integral. Then
\[
 \mathrm{RH}\quad\Longleftrightarrow\quad
 C(n^k)\ge-\frac{k}{8\pi}\,n^{k/2}\log n
 \quad\text{for all sufficiently large integers }n .
\]
In the converse direction any fixed implied constant in the lower bound \(C(n^k)\ge-O_k(n^{k/2}\log n)\) suffices. The new step in this calculation compares the integral of the genuine prime error with a positively weighted sum of its values on the grid. It gives an estimate on what the sampling loses. The lower bound on the sampled arithmetic quantity itself remains **OPEN**.

## Comparison on a dyadic shell

Let \(B=\sup_{\zeta(\rho)=0}\Re\rho\), taking the supremum over nontrivial zeros, and let \(X\ge4\), \(N=X^{1/k}\), \(X\le Y\le2X\). Define
\[
 {\cal D}_{X,Y}(G)=
 \sum_{X<n^k\le Y} k n^{k-1}G(n^k)-\int_X^Y G(x)\,dx .
\]
For each fixed \(k,\epsilon>0\) (with \(k\) integral),
\[
 |{\cal D}_{X,Y}(C)|
 \ll_{k,\epsilon} X^{1+B-1/(3k)+\epsilon}+X^{3/2+\epsilon}.       \tag{1}
\]
All estimates below are uniform in the position of the upper endpoint. Write \(L=\log(2X)\). Powers \(L^c\) with fixed \(c\) are absorbed by \(X^\epsilon\).

Use the truncated von Mangoldt explicit formula for \(E(x)=\psi(x)-x\) with \(U=X^2\):
\[
 E(x)=-\sum_{|\Im\rho|\le U}x^\rho/\rho+O(L^2),
 \qquad X\le x\le2X .
\]
The standard cutoff error is bounded by \(O(x\log^2(xU)/U+\log x+1)\) in this range. Its local prime-power proximity factor is at most one. Passing from midpoint \(\psi_0\) to the right-continuous function costs \(O(\log x)\). Zeros are counted with multiplicity and their number in each unit height interval is \(O(\log(2+|t|))\). In particular \(|E(x)|\ll_\epsilon x^{B+\epsilon}\). [Truncated explicit formula and zero count, Theorems A.2 and A.3](https://www.rivmat.unipr.it/fulltext/2016-7-1/pdf/6_Zaccagnini.pdf)

We estimate \({\cal D}_{X,Y}(E/\log)\). Under \(x=u^k\), the Jacobian is \(k u^{k-1}\). After taking out \(X^{1+\beta}\) in the contribution of a zero \(\rho=\beta+i\gamma\), the difference to estimate is
\[
 \frac1N\left(\sum_{N<n\le Y^{1/k}}-\int_N^{Y^{1/k}}du\right)
 b_\beta(u)(u/N)^{ik\gamma},
 \qquad b_\beta(u)=\frac{k(u/N)^{k-1+k\beta}}{\log(u^k)} .
\]
There is an additional complex constant of modulus one, \(N^{ik\gamma}\). On this fixed dyadic range \(\sup|b_\beta|+N\sup|b'_\beta|\ll_k1\), uniformly for \(0\le\beta\le1\).

For \(|\gamma|\le R=N^{2/3}\), the elementary rectangle rule on an interval, including both endpoint discrepancies, bounds this normalized difference by \(O_k((1+|\gamma|)/N)\). After summing with weight \(1/|\rho|\) the total is \(O_k(N^{-1/3}L^2)\).

## The higher zeros

For an octave \(T\le|\gamma|\le2T,\ T\ge R\), the normalized integral is \(O_k(1/T)\) by one integration by parts in \(u\). Partial summation bounds the discrete term for each zero by \(O_k(1/N)\) times the largest absolute value of
\[
 \sum_{N<n\le v}(n/N)^{ik\gamma},\qquad N\le v\le (2X)^{1/k}.
\]
The following elementary mean-square estimate controls these partial sums:
\[
 \sum_{T\le|\gamma|\le2T}
   \max_v\left|\sum_{N<n\le v}(n/N)^{ik\gamma}\right|^2
 \ll_k (T+N)N L^c, \qquad 1\le T\le X^2 .                       \tag{2}
\]
To verify it, enclose the available integers, beginning with the first integer greater than \(N\), in an interval of length a power of two, padding by zero coefficients. Each prefix is a disjoint union of at most \(O_k(\log(2N))\) intervals in its dyadic subdivision. Cauchy bounds the square of the maximum by \(O_k(\log(2N))\) times the sum of squared Dirichlet polynomials over all subdivision intervals \(I\).

For one interval write \(D_I(t)=\sum_{n\in I}(n/N)^{ikt}\) over the nonzero entries. On any ordinate interval of length \(O(T+1)\) we have
\[
 \int\big(|D_I(t)|^2+|D'_I(t)|^2\big)\,dt
 \ll_k (T+N\log(2N))\,\# I .
\]
Indeed the absolute value of each cross integral is at most \(2/(k|\log(m/n)|)\ll_k N/|m-n|\); its sum costs \(O_k(N\log(2N)\# I)\). The derivative coefficients \(ik\log(n/N)\) are bounded. Averaging the fundamental theorem of calculus on \([\gamma-1,\gamma+1]\) gives \(|D_I(\gamma)|^2\ll\int_{\gamma-1}^{\gamma+1}(|D_I|^2+|D'_I|^2)\). These intervals overlap \(O(\log(2T))\) times, including multiplicity. At each dyadic subdivision level the total number of nonzero entries is \(O_k(N)\); there are \(O_k(\log(2N))\) levels. This proves (2).

Cauchy and the zero count \(O(T\log(2T))\) now give
\[
 \frac1{NT}\sum_{T\le|\gamma|\le2T}\max_v
 \left|\sum_{N<n\le v}(n/N)^{ik\gamma}\right|
 \ll_k L^c\sqrt{\frac1N+\frac1T}
 \ll_k L^c N^{-1/3}.
\]
The normalized integral costs \(O_k(L^c/T)\) after the same \(1/|\rho|\) summation. Summing the \(O(L)\) octaves, including the short final one, proves
\[
 |{\cal D}_{X,Y}(E/\log)|\ll_{k,\epsilon}
 X^{1+B-1/(3k)+\epsilon}+XL^2.
\]

## Ordinary primes, signs and the converse

By partial summation and \(0\le\psi(x)-\vartheta(x)\ll\sqrt x\log^2 x\),
\[
 C(x)=\frac{E(x)}{\log x}
   +V(x)+O(\sqrt{x}\log^2x),\qquad
 V(x)=\int_2^x\frac{E(u)}{u\log^2u}\,du .
\]
The harmless lower-end constant is included in the remainder. On each shell, \(V=O_\epsilon(X^{B+\epsilon})\) and \(V'=O_\epsilon(X^{B-1+\epsilon})\) almost everywhere. Applying the rectangle rule in \(u=x^{1/k}\), with its Jacobian, gives \({\cal D}_{X,Y}(V)\ll_{k,\epsilon} X^{1+B-1/k+\epsilon}\). The higher-power remainder costs \(O_k(X^{3/2}L^2)\) across the sum and integral because the grid weights are positive and have total \(O_k(X)\). This proves (1).

Under RH the stated eventual lower follows from Schoenfeld's continuous bound. For the converse suppose \(B>1/2\), and fix \(0<\epsilon<\min(B-1/2,1/(3k))/4\). Johnston's Lemma 2.8 with \(c=0\) gives negative oscillations of order \(x^{1+B-\epsilon}\) in the integral of \(\Pi-\operatorname{li}\), where \(\Pi\) includes all prime powers with their \(1/r\) weights. Since \(\pi\le\Pi\), the same negative lower excursions hold for \(A(x)=\int_2^x C(u)\,du\). If the one-sided grid bound held eventually, positivity of \(kn^{k-1}\) would give
\[
 \sum_{2<n^k\le x} k n^{k-1} C(n^k)\ge-O_k(x^{3/2}\log x).
\]
Apply (1) over dyadic intervals partitioning \([4,x]\), absorbing finite initial terms. Along the same negative sequence it would give \(A(x)\ge-O_{k,\epsilon}(x^{3/2+\epsilon}+x^{1+B-1/(3k)+\epsilon})\). Both exponents are strictly below \(1+B-\epsilon\), a contradiction. The use of \(B\) needs no zero attaining its supremum. [Schoenfeld's bound and its hypotheses](https://arxiv.org/pdf/2109.02249#page=1) · [Johnston, Lemma 2.8](https://arxiv.org/pdf/2201.06184#page=5)

This is a transfer using the actual prime explicit formula and its frequency distribution. A monotone counting function with matching values at all grid points can fail the comparison; [the counterexample and finite fourth-power check](ENDPOINT_CHECK.md) give both facts explicitly. The converse does not prove the sampled lower bound or Step 4.

## Composition with the actual OPICA field

Keep the native smooth compactly supported pulse \(j\) and write its transform as \(J(z)=\int e^{-zv}j(v)\,dv\). Its support is \([-s,s]\) with \(s=1/4096\), and \(J(1/2)=0\). On sufficiently late times set
\[
 f_t(x)=x^{-1/2}\log(x)\,j(t-\log x),\qquad
 K_t(x)=-f'_t(x)
 =x^{-3/2}\big[(\tfrac12\log x-1)j(t-\log x)+\log x\,j'(t-\log x)\big].
\]
The ordinary-prime field is \(P_1(t)=\sum_p f_t(p)\). Integration by parts against \(d\pi=dC+dx/\log x\) has zero boundary terms and gives
\[
 P_1(t)=\int C(x)K_t(x)\,dx
       +\int f_t(x)\frac{dx}{\log x}.
\]
The second integral equals \(e^{t/2}J(1/2)=0\), exactly. The finite initial interval can be retained in its original form.

On shells meeting the support \(x\asymp X=e^t\), we have \(\sup |K_t|+\operatorname{Var}(K_t)\ll_j(1+t)X^{-3/2}\), by differentiating once more and using the fixed support length in \(\log x\). Abel summation against arbitrary prefixes in (1) therefore gives
\[
 \left|P_1(t)-\sum_n k n^{k-1} C(n^k)K_t(n^k)\right|
 \ll_{j,k}(1+t)^c\big[1+\exp((d-1/(3k))t)\big],
 \qquad d=B-\tfrac12 .
\]
Here one can keep powers of \(\log(2X)\) throughout (1): the explicit formula gives \(|E(x)|\ll x^B\log^2(2x)\), and the remaining estimates above have only logarithmic losses. For every fixed \(k\) and every actual \(d>0\), the error thus has upper exponential rate at most \(\max(0,d-1/(3k))<d\). If the native field has upper exponential rate \(d\), this signed grid projection has that same rate. This transfer uses the cumulative discrepancy \(C(n^k)\) of ordinary primes at each cut.

The full source \(P(t)=\sum_m\Lambda(m)m^{-1/2}j(t-\log m)\) is recovered by adding
\[
 H(t)=\sum_{p^r,\ r\ge2}(\log p)p^{-r/2}j(t-\log(p^r))
\]
on both sides of the comparison. All proper prime powers remain in \(H(t)\). Even elementary counting gives \(|H(t)|\ll_j(1+t)^2\): the support forces \(p^r\asymp e^t\), permits \(O(1+t)\) exponents and at most \(O_j(e^{t/2})\) bases per exponent. The previously derived, sharper estimate identifies the limiting constant \(1/32\) and a square-integrable remainder. The source and \(K_t\) above use the original one-copy \(j\), including its sign. [Native one-copy field, source support, and proper-power calculation](../step4-duration-2026-11-19/jets/SINGLE_SCALAR_CAYLEY.md) · [Repository explicit formula](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean)

## How many endpoint exceptions the comparison permits

It suffices that the lower bound hold outside \(O_k(M^{1-\nu})\) exceptions on every sufficiently late dyadic interval \(M<n\le2M\), for any one fixed \(\nu>0\). We may take \(0<\nu<1\), decreasing it if necessary. By the same explicit formula and partial summation, \(|C(u)|\ll_\epsilon u^{B+\epsilon}\). Writing \(X=M^k\), the total adverse weight of the exceptional nodes in the quadrature is therefore
\[
 O_{k,\epsilon}(M^{1-\nu}M^{k-1}X^{B+\epsilon})
 =O_{k,\epsilon}(X^{1+B-\nu/k+\epsilon}).
\]
A subinterval of a dyadic block inherits this bound; a shell meeting two consecutive blocks uses their sum. Choosing \(\epsilon\) also smaller than \(\nu/(4k)\) preserves the contradiction with the negative oscillation. Consequently, if RH fails, for each fixed \(k\), each fixed constant multiplying the square-root logarithmic lower tolerance, and every \(\nu>0\), the count of violations is not \(O(M^{1-\nu})\) on dyadic blocks. This makes a uniform power saving in exceptional endpoint counts a sufficient arithmetic target in its own right.
