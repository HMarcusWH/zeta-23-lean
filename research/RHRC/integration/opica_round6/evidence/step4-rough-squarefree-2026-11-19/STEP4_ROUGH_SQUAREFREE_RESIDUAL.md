# Step 4 and squarefree composites with large prime factors

19 November 2026. **Step 4 OPEN. RH OPEN.** The analytic results below have **DERIVED** paper status. The source is the complete signed cutoff-five aperture integral. The inspected repository revision is [c867a8f1](https://github.com/HMarcusWH/zeta-23-lean/tree/c867a8f15320ad6ac69177e0a498de4cb9d744f9), tree 573cda1f06d2d7a0e61349a53183311e4ba621fc.

## What the reduction buys

One can pay for the full weighted count of squarefree integers with no prime factor at most \(T^2\), at every positive exponential rate. Its prime part therefore equals minus its composite part up to an admissible error. Within that composite part the entire two-prime contribution is explicitly negative and the entire contribution from three or more primes is positive to the same leading order. Their **signed sum** remains the arithmetic obstacle. A bound on the relative error of these leading terms by any fixed inverse power of \(T\) would still fall short.

The preceding aperture report gives the complete Euler-transform implication used here. The source map for the three merged PRs, five-mode computation and [native packet theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICARound4/QuarticErrorReduction.lean#L414) identify the distinct source objects and their evidence.

## 1. Source and endpoint moments

Let \(f(v)=\sin^8(\pi v)-(10/9)\sin^{10}(\pi v)\) on \([0,1]\), extended by zero. Write \(v_L=L^{-2} f''-f/4,\ b(L)=\int_0^1 v_L^2\) and \(b(L)C_L(t)=\int_0^{1-t/L}v_L(v)v_L(v+t/L)dv\) for \(0\le t\le L\). Define
\[
 W_T(t)=\int_t^T L^{17}b(L)C_L(t)dL,\qquad
 I(T)=\sum_{n\le e^T}\frac{\Lambda(n)}{\sqrt n}W_T(\log n)-\int_0^T e^{t/2}W_T(t)\,dt .
\]
All cutoffs in what follows are frozen at the specified horizon. The usual prime powers, the continuum, the signed kernel and its behavior at the moving endpoint are included.

Write \(G_T(h)=e^{-h/2}W_T(T-h)\) on \(0\le h\le T\). For a uniform constant, \(|G_T(h)|\le C e^{-h/2}(1+h)^{18}\). The integrals of \(G_T\) and \(hG_T\) are \(O(\mathrm{poly}(T)e^{-T/2})\). At finite \(L\), the bilateral transform of the even autocorrelation has a double zero at \(1/2\). Splitting at zero gives the signed moment identities behind these bounds. The endpoint kernel converges at each fixed \(h\) to
\[
 W_T(T-h)\longrightarrow K\left(\frac{h^{14}}{14!}-\frac{h^{16}}{2\,16!}+\frac{h^{18}}{16\,18!}\right),\qquad K=\pi^{16}(8!)^2.
\]
The Laplace transform of the limit is \(K(s^2-1/4)^2/s^{19}\). Differentiating twice at \(s=1/2\) and applying dominated convergence yields \(\int h^2G_T(h)\,dh\to B=2^{20}K>0\). We also use \(\sup_{[0,T]}(|W_T|+|W'_T|)\ll(1+T)^{18}\). Full endpoint computations and the finite carrier definitions appear in the preceding report.

## 2. Pay the whole squarefree count

Set \(Y=\lfloor T^2\rfloor\), \(P_Y=\prod_{p\le Y}p\), and let \(S_Y(x)\) count squarefree \(n\le x\) coprime to \(P_Y\), including 1. Its density is \(c_Y=\prod_{p\le Y}(1-1/p)\prod_{p>Y}(1-1/p^2)\). For all \(x\ge1\),
\[
 |S_Y(x)-c_Yx|\ll \sqrt{x}\prod_{p\le Y}(1+p^{-1/2}) . \tag{1}
\]
Indeed expand the inclusions and exclusions for \(p\mid n\) at small primes and \(p^2\mid n\) at large primes. This gives exactly
\[
 \sum_{a\mid P_Y}\mu(a)\sum_{(b,P_Y)=1}\mu(b)
            \left\lfloor x/(ab^2)\right\rfloor .
\]
For \(z=x/a\ge1\), replacing the inner sum by \(z\sum_{(b,P_Y)=1}\mu(b)/b^2\) costs at most \(\sqrt z+z\sum_{b>\sqrt z}1/b^2=O(\sqrt z)\). For \(z<1\), the count is zero and its main term has size at most \(z\). Sum the errors over \(a\). Chebyshev's prime-counting bound and partial summation give \(\log\prod_{p\le Y}(1+p^{-1/2})\ll \sqrt Y/\log Y\).

Now integrate (1) against \(F(x)=(\log x)W_T(\log x)/\sqrt x\). The endpoints \(F(1), F(e^T)\) vanish. The error is at most \(\prod_{p\le Y}(1+p^{-1/2})\int_1^{e^T}\sqrt x |F'(x)|dx\), a polynomial in \(T\) times the product. The main term is the already paid signed moment \(c_Y\int_0^T t e^{t/2}W_T(t)dt\). Consequently the whole squarefree count, with this exact signed weight, costs at most
\[
 E(T)=\mathrm{poly}(T)\exp(CT/\log T). \tag{2}
\]
The primes at most \(Y\) cost polynomially using the supremum of \(W_T\). Proper prime powers also cost polynomially since squares contribute at most \(\sum_{m\le e^{T/2}}\log(m)/m\) before multiplication by \(\|W_T\|_\infty\), and the higher-power mass is uniformly bounded. The source continuum is paid by the zeroth signed moment. The weight at \(n=1\) is zero.

Let \(C_2\) and \(C_{\ge3}\) be the sums of \(F(n)\) over squarefree composites with every prime factor greater than \(Y\), having exactly two or at least three distinct prime factors respectively. We have
\[
 I(T)=-C_2(T)-C_{\ge3}(T)+O(E(T)). \tag{3}
\]
Every original prime power has been accounted for. Equation (3) uses the collective estimate for the sieve, with no sparsity assumption about the individual signed terms.

## 3. The signs and sizes of both full sectors

For \(a=\log Y\) we find
\[
 C_2(T)\sim-\frac{B e^{T/2}}{2(T-a)^2},\qquad
 C_{\ge3}(T)\sim+\frac{B e^{T/2}}{2(T-a)^2}. \tag{4}
\]
These estimates cover the whole range of factor ratios. The thinner fixed-ratio calculation in the preceding report had order \(e^{T/2}/T^3\).

For the first formula sum over \(Y<p<q\). Products with \(t=\log(pq)<T/2\) contribute \(O(\mathrm{poly}(T)e^{T/4})\) by unique factorization and the size of \(W_T\). On the rest \(q\ge e^{T/4}\). For each \(p\le e^{T/2}\), apply the effective prime number theorem and partial summation in \(q\), with the restrictions \(q>p,\ T/2\le\log(pq)\le T\). The error per \(p\) is \(O(\mathrm{poly}(T)e^{T/2-c\sqrt T}/p)\). Indeed the error in the prime count at \(q\) is \(O(qe^{-c\sqrt T})\), and the integrand and its derivative in \(\log q\) are bounded by \(\mathrm{poly}(T)/\sqrt{pq}\). Summing the endpoint and integral errors costs only another polynomial. Equality at an endpoint \(q=p\) could contribute at most polynomially. Thus the desired double sum is, up to this error,
\[
 \int_{T/2}^T e^{t/2}W_T(t)\,H_Y(t)dt,\qquad
 H_Y(t)=\sum_{Y<p\le e^{t/2}}\frac{t}{p(t-\log p)} .
\]
An effective PNT with the needed error follows from [Johnston and Yang](https://arxiv.org/abs/2204.01980).

Put \(D(u)=\sum_{p\le e^u}1/p-\log u-B_M\), where \(B_M\) is the prime reciprocal constant. Partial summation from effective PNT gives \(D(u)=O(\mathrm{poly}(u)e^{-c\sqrt u})\) at large \(u\). Replacing the prime density by \(du/u\) gives \(H(t)=\log((t-a)/a)\) exactly. To keep the discrete error from small \(p\) at the required precision, split at the fixed midpoint in log-prime coordinate \(u_0=T/8\). On \((u_0,t/2]\), integration by parts against \(D\) costs \(O(\mathrm{poly}(T)e^{-c'\sqrt T})\) uniformly. On \((a,u_0]\) write the difference as
\[
 D_0(t)=\int_{(a,u_0]} \frac{t}{t-u}\,dD(u).
\]
Here \(D_0(T),D_0'(T)\) cost at most polynomially. The second \(t\)-derivative of the integrand is \(2u/(t-u)^3\). It is monotone in \(u\) and its supremum plus total variation on the interval is \(O(T^{-2})\). A second integration by parts, using \(\sup_{u\ge a}|D(u)|=o(1)\), gives \(\sup_{T/2\le t\le T}|D_0''(t)|=o(T^{-2})\). The constant and linear Taylor terms integrate against the two paid endpoint moments. Their tails over \(h>T/2\) are exponentially small after normalization by \(e^{T/2}\). The quadratic remainder contributes \(o(e^{T/2}/T^2)\).

Finally \(H''(T)=-1/(T-a)^2\), and its third derivative is \(O(T^{-3})\) throughout the late range. Expanding at \(T\) and using the same two paid moments leaves exactly \(H''(T)B e^{T/2}/2\) to leading order. This proves the first assertion of (4). For the second, effective PNT applied directly to \(I(T)\) gives \(I(T)=O(e^{T/2-c''\sqrt T})\). Partial summation uses the same derivative bound and split at \(T/2\) as above. Substituting this and (2) into (3) gives the higher-factor asymptotic. This second asymptotic uses the full prime estimate and the exact decomposition. It gives no independent higher-precision control of their difference.

## 4. The precise remaining inequality

The still-unproved assertion is
\[
 \forall\eta>0\ \exists C_\eta,T_\eta\ \forall T\ge T_\eta:
 \quad C_2(T)+C_{\ge3}(T)\ge -C_\eta e^{\eta T}. \tag{5}
\]
The error (2) is absorbed by every fixed positive exponential, so (5) is equivalent to the eventual upper for \(I\). The aperture report gives a paper implication to exclusion of every rightward zero, with multiplicities retained and with no rightmost-zero assumption. A cofinal upper for this **signed** primitive cannot replace the eventual upper. The complete-source weighted response in the companion note has different quantifiers because a visible zero gives an eventual positive lower there.

The following checks constrain possible approaches.

* Discarding three-or-more-prime products leaves a negative term of the wrong exponential scale. Bounding the sectors separately in absolute value fails by (4). Retaining only finitely many more powers in the endpoint expansion leaves the exponential scale in the error estimate.
* Enlarging \(Y=T^b\) for fixed \(b>2\) is costly even if one truncates the absolute sieve error to \(a\le e^T\). Choose \(k=\lfloor T/\log Y\rfloor\) primes from \([Y/2,Y]\). Each product lies in range, costs at least \(Y^{-k/2}\), and the binomial coefficient with the PNT gives an aggregate at least \(\exp((1/2-1/b+o(1))T)\). Signed cancellation in a different estimate would need its own proof.
* The finite verification checks the arithmetic decomposition independently. The analytic inequalities, their error rates and the link from (5) to the zero set have paper authority. The native Lean theorem supplies the complementary lower on legal generated packets. An independent arithmetic upper for that same observable is a separate possible closing route. [Native lower](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICARound4/QuarticErrorReduction.lean#L414)

**Research conclusion.** The full squarefree background and the leading compensation between two and higher prime factors are now priced. The first unpaid step is a uniform one-sided estimate on their genuinely coupled residual in (5). The work produced no independent bound at that scale and no closing Lean theorem.
