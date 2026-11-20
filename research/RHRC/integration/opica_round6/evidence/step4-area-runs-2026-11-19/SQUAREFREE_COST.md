# An equivalent inequality on squarefree integers and an unconditional count

**DERIVED on paper.** Define the additive cost \(W(n)=\sum_{p\mid n}p\log p\) on squarefree integers. The following precise inequality is equivalent to RH:
\[
 \boxed{\quad (\log n)^2+4<2W(n)\quad\text{for every squarefree integer }n\ge8.\quad}       \tag{1}
\]
This is an elementary change of the actual prime graph in Johnston's criterion. It needs no zero-density theorem, limiting model, or assumption about which zero has largest real part. It gives a direct integer target. The universal inequality is **OPEN**.

## Exact equivalence

Write \(z=\log n=\sum_{p\mid n}\log p\), \(D(n)=z^2/2-W(n)+2\), and \(A(z)=\int_2^z(\vartheta(u)-u)du\). For \(z>2\) subtraction of the two finite sums gives
\[
 A(z)-D(n)=
 \sum_{\substack{p\le z\\p\nmid n}}(z-p)\log p+
 \sum_{\substack{p>z\\p\mid n}}(p-z)\log p\ \ge0.                     \tag{2}
\]
The earlier unconditional finite-range sign proof and (2) give (1) for **every** squarefree integer \(8\le n\le\exp(1.21\cdot10^{48})\). This is a deduction from the sign for every real argument in that finite interval. It requires no enumeration of those integers. Prior finite-range proof and checks

Under RH Johnston's theorem \(A(z)<0\) proves (1) for every eligible integer. Conversely, for any real \(x\ge5\) take \(n=\prod_{p\le x}p\). It is squarefree and at least 30. Completing the square gives the exact identity
\[
  A(x)=D(n)-\tfrac12(x-\log n)^2 .
\]
Therefore (1) forces \(A(x)<0\). On \(2<x<5\), \(\vartheta(x)<x\) directly, so the same strict sign holds. Johnston's converse then proves RH. Indeed testing (1) just on primorials from 30 onward suffices. [Johnston, Theorem 1.2](https://arxiv.org/abs/2201.06184)

## An independent arithmetic upper on the number of possible exceptions

Unconditionally, the number of squarefree \(8\le n\le Y\) violating (1) is at most
\[
  \exp\!\left(O\!\left(\frac{\log Y}{\log\log Y}\right)\right)
  \qquad (Y\to\infty).                                                 \tag{3}
\]
This is subpolynomial in \(Y\). Put \(Z=\log Y\). A violating subset of ordinary prime factors satisfies \(W(n)\le Z^2/2+2\). For \(\lambda=(Z\log Z)^{-1}\), the exact squarefree partition product bounds the number of such subsets by
\[
 \exp(\lambda(Z^2/2+2))\prod_{p}(1+e^{-\lambda p\log p}).
\]
Take logarithms. The terms with \(p\le Z\) cost \(O(Z/\log Z)\) by the elementary upper bound on \(\pi(Z)\). For \(2^j Z<p\le2^{j+1}Z\), each summand \(\log(1+e^{-\lambda p\log p})\le e^{-2^j}\). There are \(O(2^j Z/\log Z)\) primes in the interval. The convergent sum over \(j\ge0\) and the prefactor prove (3). These are the same integers and the same cost as in (1). This upper still allows every relevant primorial to be exceptional. Merely counting all subsets below the cost threshold cannot improve the exponent in its logarithm beyond order \(Z/\log Z\): every subset of primes up to \(cZ\), for a sufficiently small fixed \(c>0\), has both log product at most \(Z\) and cost at most \(Z^2/2\). PNT supplies \(\exp(\Omega(Z/\log Z))\) such subsets. That last lower bound is for *low cost*, and supplies no violations.

## How many genuine integer violations a positive peak would force

Let \(z=S(p)\) be a true stopped maximum from [the prime-gap calculation](STOPPED_PRIME_GRAPH.md), so the primorial \(P=\prod_{q\le p}q\) has \(\log P=z\). Put \(V=D(P)=A(z)>0\). For any subset \(T\) of primes immediately **below** \(z\), all dividing \(P\), set \(n_T=P/\prod_{q\in T}q\) and \(L_T=\sum_{q\in T}\log q\). Direct expansion yields
\[
 D(n_T)=V-\sum_{q\in T}(z-q)\log q+\tfrac12 L_T^2.                  \tag{4}
\]
In particular if all primes in \((z-h,z]\) have total mismatch cost \(<V\), each of their subsets gives a distinct squarefree violation with \(n_T\le e^z\), provided \(L_T<z-2\). There is no sign or independence assumption here. By the short-interval PNT, for \(z^{3/4}\ll h\ll z^{1-\epsilon}\) with fixed \(\epsilon>0\), the entire mismatch cost is \(O(h^2)\), the number of primes is \(\gg h/\log z\), and their log mass is \(O(h)=o(z)\). When \(h>z^{0.99}\), split into equal pieces of length comparable to \(z^{0.7}\); each piece lies in the published range with a fixed margin. The same bounds hold at \(h\asymp z^{3/4}\). [Guth and Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552#page=2)

If a zero has real part \(1/2<b<1\), the stopped-peak proof supplies arbitrarily large \(z\) with \(V\gg_b z^{1+b}\). Fix a small positive constant depending on the true excursion margin and take \(h=c_b z^{(1+b)/2}\). The mismatch cost is then \(<V\); all subsets in (4) are actual violations. For \(Y=e^z\) on these scales their count is at least
\[
 \exp\!\left(\Omega_b\!\left(\frac{(\log Y)^{(1+b)/2}}{\log\log Y}\right)\right).
\]
Hence a uniform upper of the form \(\exp((\log Y)^{3/4+o(1)})\) on *violations* would rule out every off-line zero. The positive \(L_T^2/2\), the full prime prefix, and distinctness of all resulting integers have been retained.

## Enforcing the signed coupling gives a stronger unconditional count

Let \(N(Y)\) denote the actual number of violations of (1) up to \(Y\). Place \(z=\log n\) in the unit bucket \([j,j+1)\), \(j\ge2\), and let \(P_j=\prod_{p\le j}p\). The cost of changing its prime subset to that of \(n\) is
\[
 T_j(n)=\sum_{p\in\{q:q\mid n\}\,\triangle\,\{q:q\mid P_j\}}|p-j|\log p
       = A(j)-D(n)+(z-j)^2/2 .
\]
This uses only the symmetric difference of the two prime sets. In particular any violation in this bucket costs at most \(T=\max(A(j),0)+1\). For each fixed \(j\), the distinct integers correspond to distinct sets of flipped primes. The number with this cost budget is at most
\[
 \exp(\tau T)\prod_p(1+\exp[-\tau|p-j|\log p]) .
\]
Bound the logarithm of the product by \(\sum_{m\ge2}\exp[-\tau |m-j|\log 2]\ll1+\tau^{-1}\) using at most two integers at a given positive distance. Taking \(\tau=T^{-1/2}\) proves the upper \(\exp(O(1+\sqrt T))\) per bucket. The zero-cost bit when \(j\) itself is a prime is included.

Unconditional PNT gives \(|A(j)|\ll j^2\exp[-c\sqrt{\log j}]\) with a fixed \(c>0\). Integrate the unconditional bound for \(\psi(t)-t\), splitting at \(\sqrt j\), and include the \(O(\sqrt t\log t)\) prime powers to obtain this form. Summation over at most \(1+\log Y\) buckets gives, for some \(c'>0\),
\[
 \boxed{\quad\log(2+N(Y))\ll
 (\log Y)\exp[-c'\sqrt{\log\log Y}].\quad}                            \tag{5}
\]
This uses the signed mismatch condition and improves (3) by more than any fixed power of \(\log\log Y\). The known PNT estimate is unconditional. The saving still falls short of the power \(3/4\) in \(\log Y\). [Fiori, Kadiri and Swidinsky, unconditional Chebyshev bound](https://arxiv.org/abs/2204.02588)

There is a sharper diagnostic if RH is false. The integrated explicit formula gives \(|A(j)|\ll j^{1+B}\). The same bucket argument then gives \(\log(2+N(e^Z))\ll Z^{(1+B)/2}\). For every actual \(b>1/2\), (4) gives the matching lower logarithmic exponent for every sufficiently large \(Z\): choose the three isolator windows at a fixed multiple of \(Z\) small enough that their terminal point is at most \(Z\). The interior stop then has \(z\asymp_b Z\) and \(n_T\le e^Z\). Finally let \(b\) approach \(B\). Thus
\[
 \lim_{Y\to\infty}\frac{\log\log(2+N(Y))}{\log\log Y}=\frac{1+B}{2}
 \quad\text{if RH fails}.
\]
If RH holds, \(N(Y)=0\) for every \(Y\). A cofinal upper \(\log(2+N(Y))\le(\log Y)^{3/4+o(1)}\) would therefore suffice. The fixed-power gap in (5) is the precise missing arithmetic saving; counting the great majority of ordinary squarefree integers again cannot settle it.

The prime density improves the bucket estimate by a further logarithm on large budgets. Let \(h=\max(j^{3/5},\sqrt T)\) and \(\tau=1/(h\log j)\). The primes below \(\sqrt j\) cost \(O(\sqrt j)\) in the logarithm of the product. For each other prime the weight is at most \(\exp[-|p-j|/(2h)]\). Split each side of \(j\) into intervals of length \(h\). The uniform Brun–Titchmarsh upper for each interval is \(O(h/\log h)\); extending a clipped interval to length \(h\) is harmless. Sum the resulting geometric tails. Including \(\tau T\) gives \(O(h/\log j)\) for the logarithm of the number in the bucket. [Montgomery and Vaughan, *The large sieve*](https://doi.org/10.1112/S0025579300004708)

If \(B>1/2\) is attained, this upper and (4) show \(\log(2+N(e^Z))\asymp Z^{(1+B)/2}/\log Z\) for all large \(Z\). If \(B>1/2\) is unattained, the zero expansion gives \(A(j)=o(j^{1+B})\) by dominated convergence of the absolutely summable zero coefficients. The bucket estimate then yields \(\log(2+N(e^Z))=o(Z^{(1+B)/2}/\log Z)\). To pass to a uniform maximum split \(j\le\sqrt Z\) from \(j>\sqrt Z\), then use the late little-oh bound on the latter range. This distinction supplies no fixed saving below the exponent in the previous limit.

The finite computation checked (1), (2), and the unit-bucket identity on all 24,304 squarefree integers from 8 through 40,000 with 160-bit interval arithmetic. None violated (1). The smallest margin \(W(n)-(\log n)^2/2-2\) was approximately 4.78253 at \(n=10\). The count bounds above use the analytic arguments. [Code](check_squarefree_cost.py) · [Finite check](SQUAREFREE_CHECK.json)
