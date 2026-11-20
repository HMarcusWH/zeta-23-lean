# Complete terminal composite blocks after matching every prime cofactor

19 November 2026. **DERIVED on paper.** Each genuine observation has a fixed terminal outer-prime interval in which the **entire remaining signed composite sum** is positive of order \(x^2/\log x\). Their full cross product is positive of order \(x^4/\log^2 x\). These equivalents persist if every remaining cofactor in these blocks must have least prime factor greater than \(\exp(\log L/\log\log L)\). The proof uses the native integer coefficients, including repeated factors, and the ordinary prime number theorem and Mertens estimates. Step 4 remains **OPEN**.

## Exact arithmetic in the first interval

Use the two distributed calibrations and the precise label selector in [All prime cofactors](ALL_PRIME_COFACTORS.md). For each \(x\), \(L=L_i=\lfloor x^{\lambda_i}\rfloor\), with \((\lambda_1,\lambda_2)=(.11,.37)\). The four exceptional positions for each centre \(R\) are \(4^kR\), \(2L<R\le3L\), \(9\mid R\). Fix constants \(1<a<b<2\) and take **every** eligible outer prime \(q\) with \(aL\le Y=x/q\le bL\). This interval lies inside both native ranges for all sufficiently large \(x\), using the respective \(L_i\). Set \(u=Y/L\).

Let \(c_1=\mu\) and let \(c_2\) be defined, for \(\Re s>1\), by

\[
 C_2(s)=\sum_j c_2(j)j^{-s}
       =[\zeta(s)\eta(2s)\eta(3s)]^{-1},
 \qquad \eta(s)=(1-2^{1-s})\zeta(s).
\]

Write \(C_1=1/\zeta\). Below \(2L\), the multiplier giving the projected weights is exactly the native multiplier \(1/C_i\) times the truncation of \(C_i\) at \(L\). Indeed all correction indices exceed \(2L\), matching fixes the unit coefficient, and every uncorrected coefficient through \(L\) agrees with \(c_i\). For \(L<j<2L\) every proper divisor is at most \(L\), so the only missing term in the complete divisor convolution \((1/C_i)C_i=1\) is \(c_i(j)\), multiplied by the unit coefficient of \(1/C_i\). Consequently the residual coefficient is **exactly \(c_i(j)\)** on this entire interval and zero through \(L\). In particular it is \(-1\) at each prime there. [Factorial coefficients](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md) · [Eta coefficients](../step4-area-runs-2026-11-19/ETA_FILTERED_PRIME_LOCALIZATION.md)

The specified terminal selector removes every prime cofactor and takes its compensating positive composite labels solely from \(Y\ge100L\). Thus in the present block it retains **every** composite label in the complementary sum \(T_i\). Its value at a given \(q\), before multiplication by \(\log q\), is

\[
 \sum_{\substack{L<j\le Y\\ j\ \mathrm{composite}}}(x-qj)c_i(j)
 =\sum_{L<j\le Y}(x-qj)c_i(j)
  +\sum_{\substack{L<p\le Y\\p\ \mathrm{prime}}}(x-qp).                 \tag{1}
\]

Different prime labels of the same integer product retain their original weights. Formula (1) accounts also for every vanishing coefficient and multiple prime power in the interval.

## Complete signed equivalent

For both coefficients and each fixed \(A>0\),

\[
 N_i(t):=\sum_{j\le t}c_i(j)\ll_A t/\log^A(2t),\qquad t\ge1 .
\]

For \(\mu\) this follows from the classical unconditional Mertens estimate. For \(c_2=\mu*d\), the absolute Dirichlet norm \(\sum |d(n)|n^{-3/4}\) is finite. Each \(1/\eta(ks)\), \(k=2,3\), expands into inverse zeta coefficients times the geometric series in \(2^{1-ks}\), both absolutely convergent at \(s=3/4\). Split the convolution at \(d\)'s index \(\sqrt t\). The smaller indices inherit arbitrary logarithmic savings and the larger ones contribute \(O(t^{7/8})\) by the absolute norm. The same argument gives \(\sum_{j\le t}|c_i(j)|\ll t\). [Lee and Leong, unconditional Mertens estimates](https://arxiv.org/abs/2208.06141)

Partial summation on \([L,uL]\) bounds the first sum in (1) by \(O_{A,b}(xL/\log^A L)\), uniformly for \(u\in[a,b]\). Ordinary PNT and partial summation in the second sum give, uniformly on this compact interval,

\[
 \frac{xL}{\log L}\left[\int_1^u(1-v/u)\,dv+o(1)\right]
 =\frac{xL}{\log L}\left[\frac{(u-1)^2}{2u}+o(1)\right].
\]

For instance, the normalized measures \((\log L/L)\sum_{L<p\le vL}1\) converge to \(v-1\) uniformly for \(1\le v\le b\), directly by PNT. The integrand and its first derivative are bounded. Summing over outer primes with weight \(\log q\) uses \(\vartheta(t)\sim t\) on the fixed ratio interval. With \(q=x/(Lu)\) the outer Jacobian is \(x/(Lu^2)\). Hence the complete remaining terminal block satisfies

\[
 T_i^{[a,b]}(x)\sim \frac{x^2}{\log L_i}\,I(a,b),\qquad
 I(a,b)=\int_a^b\frac{(u-1)^2}{2u^3}\,du>0 .                          \tag{2}
\]

The result holds for every sufficiently large real horizon in the asymptotic sense. The factor \(1/\log L_i\) comes from the inner ordinary primes. The outer logarithm is part of the original observable. [Ordinary prime number theorem](https://dlmf.nist.gov/27.12.E5)

For any two independently fixed subintervals \([a_i,b_i]\subset(1,2)\), the cross product of the complete remaining blocks is therefore

\[
 T_1^{[a_1,b_1]}(x)T_2^{[a_2,b_2]}(x)
 \sim I(a_1,b_1)I(a_2,b_2)\frac{x^4}{\log L_1\log L_2}.              \tag{3}
\]

The paid absolute bounds on small shift and small least common multiple apply to any such label subset. Removing those intersections leaves the equivalent (3) intact. All other blocks remain in \(T_1T_2\). With the project's fixed-power reconstructions and external upper on the total, the signed sum of the other remaining far, large-lcm pairs is the negative of this block to relative \(o(1)\). An error bound at \(x^{3+o(1)}\) is still missing. The external power estimate on \(\vartheta(t)-t\) enters that comparison with the total and the old factorial reconstruction. Formulae (1)–(3) for the specified arithmetic blocks are unconditional. [Complement and paid intersections](ALL_PRIME_COFACTORS.md) · [External source bounds](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md)

## A uniform least-prime saving inside the same composite blocks

Put \(z=\exp(\log L/\log\log L)\) for all sufficiently large \(L\). In either observation the sum over least primes \(\ell\le z\) of the **absolute value after summing all cofactor labels of that least prime** costs \(O_{A,b}(xL/\log^A L)\) per outer prime, before its logarithm. This is an unconditional signed saving for these rows. In particular (2) and (3) persist if on each side only \(P^-(j)>z_i\) is retained, with \(z_i\) defined from its own \(L_i\).

Here are the uniform estimates. Write \(\mathcal C_{i,p}\) for the Euler factor of \(C_i\) at \(p\). Below, products and differences refer to Dirichlet series. The coefficient restriction \(P^-(j)=\ell\) has series \(C_iG_{i,\ell}\) for

\[
 G_{i,\ell}=\left(\prod_{p<\ell}\mathcal C_{i,p}^{-1}\right)
             (1-\mathcal C_{i,\ell}^{-1}).
\]

This follows by subtracting the restrictions that forbid all prime factors below \(\ell\) and at most \(\ell\), respectively. It retains repeated powers of \(\ell\). With \(w=p^{-s}\), \(\mathcal C_{1,p}=1-w\). For \(i=2\) the odd-prime factor is \((1-w)(1-w^2)(1-w^3)\), and at 2 it is that same numerator divided by \((1-2w^2)(1-2w^3)\).

Let \(\|D\|_v=\sum |D_n|n^{-v}\). Uniformly for \(3/4\le v\le1\), at odd \(p\) the inverse local factors have norm \(1+p^{-v}+O(p^{-2v})\) and the differences \(1-\mathcal C_{i,p}^{-1}\) have norm \(O(p^{-v})\). At 2 both inverse factors have bounded norm on this entire range. Fix \(H>0\). At \(v=1\) and \(v=1-H/\log z\) (the latter eventually exceeds \(3/4\)) this gives

\[
 \sum_{\ell\le z,\ \ell\ {\rm prime}}\|G_{i,\ell}\|_v
       \ll_H \log z\,\big(1+\log\log z\big).
\]

Indeed \(\sum_{p\le z}1/p=\log\log z+O(1)\) by effective PNT and partial summation. Replacing \(p^{-1}\) by \(p^{-v}\) adds at most \(O_H((\log z)^{-1}\sum_{p\le z}\log(p)/p)=O_H(1)\). The quadratic errors are summable. Summing the local difference costs at most another \(O_H(1+\log\log z)\).

Let \(t\in[L,bL]\). Split the prefix convolution \(\sum_d(G_{i,\ell})_d N_i(t/d)\) at \(d=\sqrt L\), interpreting the prefix as zero if \(t/d<1\). Sum absolute values over \(\ell\le z\). On the first part use the arbitrary-log saving for \(N_i\) and the 1-norm bound. For \(d>\sqrt L\) use \(N_i(t/d)=O(t/d)\) and the \(v\)-norm bound; the extra factor \(L^{-(1-v)/2}=(\log L)^{-H/2}\) pays any fixed log power after choosing \(H\) large enough. This proves a total \(O_{A,b}(L/\log^A L)\) for the restricted prefixes. Partial summation and the triangle inequality give the stated weighted bound. No inner prime \(p>L\) occurs in the removed least-prime bins because \(z<L\). Thus these are complete signed sums of remaining composites for the actual selector.

The positive main term survives on \(z_i\)-rough composites, each having at most \((1+o(1))\log\log L_i\) prime factors counted with multiplicity since \(j\le b_iL_i\). Its cancellation with other blocks remains necessary at each horizon. The test supplies no closing theorem or fresh Lean/CI qualification.
