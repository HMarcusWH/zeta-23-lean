# Which weighted prime-factor inequalities hold for every squarefree integer?

**DERIVED on paper, 19 November 2026.** Let \(B=\sup_\rho\Re\rho\) for the nontrivial ordinary zeta zeros. For every fixed \(1/2\le a<1\), the following are equivalent:
\[
\begin{split}
 B&\le a,\\
 \int_2^x(\vartheta(t)-t)t^{-1-a}\,dt&<0\quad (x>2),\\
 (1-a)\sum_{p\mid n}(\log p)p^{-a}
  &<(\log n)^{1-a}-a\,2^{1-a}
       \quad (n\ge8,\ n\text{ squarefree}).
\end{split} \tag{1}
\]
This is a criterion for the complete ordinary prime source at every intermediate exponent. It allows a zero on the boundary \(\Re\rho=a\). At \(a=1/2\) the integer assertion reads \(\sum_{p\mid n}(\log p)/\sqrt p<2\sqrt{\log n}-\sqrt2\). An independent proof of this last assertion would settle RH. The supplied external ceiling proves an all-integer member of the family at \(a=0.873346\). The endpoint \(1/2\) remains open. We make no priority claim for a criterion of this type.

## Exact passage to ordinary prime factors

Write \(K_a(p,x)=(p^{-a}-x^{-a})/a=\int_p^x t^{-1-a}dt\). This is positive exactly for primes \(p<x\). For a squarefree \(n\) with \(z=\log n\), put
\[
 D_a(n,x)=\sum_{p\mid n}\log p\,K_a(p,x)-
                    (x^{1-a}-2^{1-a})/(1-a).
\]
The signed prime integral \(I_a(x)\) in (1) is the maximum of \(D_a(n,x)\) over all finite squarefree products, attained by the primorial through \(x\). Omitting a prime below \(x\) or adding a prime above \(x\) costs exactly \(\log p\,|K_a(p,x)|\). Each prime retains its original weight and its actual cutoff. Also \(\partial_x D_a(n,x)=x^{-1-a}(z-x)\), so \(D_a(n,z)\) is its largest value on \(x>0\) when \(z>0\). Substitution at \(z\) gives exactly the integer inequality in (1). If \(I_a<0\) globally, take \(x=\log n>2\). Conversely, for \(x\ge5\) use the primorial through \(x\), which is at least 30, and maximize in \(x\) with that same prime set. On \(2<x<5\), \(\vartheta(t)<t\) directly. Testing the integer assertion only at primorials from 30 on already suffices.

## Why an existing zero ceiling gives a strict upper on the entire integral

Keep all powers in \(\psi\). Integration of the explicit formula on the compact interval \([2,x]\) gives the exact identity
\[
 I_{\psi,a}(x)=
 -\sum_\rho\frac{x^{\rho-a}-2^{\rho-a}}{\rho(\rho-a)}
 -\int_2^x\left(\log(2\pi)+\tfrac12\log(1-t^{-2})\right)t^{-1-a}\,dt. \tag{2}
\]
One can integrate by parts from the absolutely convergent once-integrated formula. The two endpoint terms and the integral of the weight derivative combine, zero by zero, to the displayed difference. The constant term of the integrated formula cancels, and the convergent series for the trivial zeros gives the displayed logarithm. This justification avoids termwise differentiation of a conditionally convergent zero sum. A prime-power jump at the endpoint has measure zero in this integral. The exact ordinary-prime correction is
\[
 I_a(x)=I_{\psi,a}(x)-\sum_{p^k\le x,\ k\ge2}\log p\,K_a(p^k,x). \tag{3}
\]
Every summand on the right after the minus sign is nonnegative. [Integrated formula in Johnston, proof of Lemma 2.6](https://arxiv.org/html/2201.06184v2#S2)

Assume \(B\le a\). Each of \(x^{\rho-a}\) and \(2^{\rho-a}\) has modulus at most one. Both factors of the denominator have modulus at least \(|\Im\rho|\). Brent, Platt and Trudgian bound the sum of reciprocal squared ordinates over **both signs**, with multiplicity, by \(0.04621\). Thus the entire zero term in (2) has absolute value less than \(0.09242\), including at \(a=B\). For \(x\ge4\) the last integral in (2) is at least
\[
  \bigl(\log(2\pi)+\tfrac12\log(3/4)\bigr)\int_2^4t^{-2}dt>0.42.
\]
It follows that \(I_a(x)<-0.32\) for all \(x\ge4\), even before crediting any prime-power subtraction. For \(2<x<4\), \(\psi(t)<t\) directly. This proves the first implication in (1) with a uniform strict margin on the unbounded range. [Brent, Platt and Trudgian, Corollary 1](https://arxiv.org/abs/2009.13791)

## Why the weight cannot be reduced independently of the zero ceiling by this calculation

If \(B>a\), fix an actual real part \(b>a\) and a threshold \(a<d<b\). At this real part spare the zero with least positive ordinate \(\gamma_*\) and its conjugate. Use the compact positive convolution of the [paired-zero isolation argument](DENSITY_ISOLATOR.md), now with two-point factors of shifts \(u=\pi/\gamma\) and positive weights proportional to \(e^{(\beta-a)u},1\), over every other distinct rightward pair with \(\beta\ge d\). Ingham's density estimate gives \(\sum_{\beta\ge d,\gamma>0}1/\gamma<\infty\) since \(d>1/2\). This bounds the support and ensures the nonzero product at the spared mode. An unintended zero at \(b-a+i\gamma_*\) would require \(\beta=b\) and \(\gamma_*/\gamma\) a positive odd integer. The least-ordinate choice rules this out.

In log time, applying the positive convolution to (2) leaves an oscillating term of size \(e^{(b-a)t}\), a nonzero constant multiple of a cosine, and an \(O(e^{(d-a)t})\) error from the other zeros and endpoints. Equation (3) retains a complete prime-power correction of size \(O((1+t)^3)\) for \(a\ge1/2\): integrate \(\psi(u)-\vartheta(u)\ll\sqrt u\log^2(2u)\) against \(u^{-1-a}\) and use the bounded log-width of the averaging measure. The polynomial cost is absorbed in the latter error. At both cosine extrema, positivity therefore forces the actual \(I_a(x)\) to have the corresponding strict sign with magnitude \(\gg x^{b-a}\) in every sufficiently late \([X,KX]\), for a fixed \(K=K_{a,b}\). In particular the second line of (1) fails. This includes a nonattained \(B\).

## Numerical endpoint and what remains to prove

At tracker commit 42cf5415cfaa4205caaa25ab11160724606cdc33, the declarations Candidate.bound and Candidate.bound_le give an all-moduli zero ceiling and a rational upper bound on its exact algebraic endpoint. Taking the modulus-one character includes ordinary zeta. The rational upper \(r\) satisfies \(0.8733458561067185768011\le r<0.8733458561067185768012\), by integer division of the two literals in Candidate.bound_le. Thus (1) holds, for example, at \(a=0.873346\). This propagation uses the external result as stated. Its dependency tree was not recompiled in this project. Liu's earlier preprint gives the separate numerical ceiling \(0.874957019420098946\ldots\). [Pinned tracker theorem and rational](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean) · [Liu, Theorem 27.1](https://arxiv.org/abs/2610.12234)

The same \(r\) improves the [exception count](SQUAREFREE_COST.md) for the original unweighted integer inequality. For \(Z=\log Y\), the integrated explicit formula bounds \(A(j)_+\ll j^{1+r}\): the prime-power subtraction is nonnegative and the integrated zero coefficients are absolutely summable. A violating integer in the unit bucket \(\log n\in[j,j+1)\) has mismatch budget \(T\le A(j)_++1\). The prime-density product bound in the count proof gives log cardinality \(O(h/\log j)\), \(h=\max(j^{3/5},\sqrt T)\). Sum the cardinalities of the buckets and take the logarithm. It follows that \(\log(2+N(Y))\ll Z^{(1+r)/2}/\log Z\), with \((1+r)/2<0.936672928053359289\). The target power for this count is \(3/4+o(1)\). Returning from the count exponent via \(b=2((1+b)/2)-1\) recovers exactly the input ceiling. No iteration to \(1/2\) follows.

The previous finite-area sign result and partial integration give \(I_a(x)<0\) for every \(2<x\le1.21\cdot10^{48}\), including \(a=1/2\). The integral-to-integer identity transfers this to all squarefree \(8\le n\le\exp(1.21\cdot10^{48})\). Beyond that verified-on-paper range, controlling the actual critical sum over prime factors independently remains the unresolved step. Previous finite sign bound
## Finite checks at the source

At 160-bit interval precision we compared the independently integrated prime staircase with the weighted finite prime sum at 1,999 integer horizons per weight. The full prime-power correction was checked independently at every horizon. The stationary score and the displayed divisor inequality agreed for all 1,209 squarefree integers from 8 to 2,000 at each of the three weights 0.5, 0.75, and 0.873346. These are finite checks of signs, normalization, and lower endpoints. [Reproducer](check_weighted_factors.py) · [Receipt](WEIGHTED_FACTORS_CHECK.json)
