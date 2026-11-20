# The price of one-sided inclusion and exclusion on the actual rough graph

**DERIVED on paper.** The highest factor-count layers of the true squarefree rough input can be paid at subpower cost throughout the complete tree. The degree needed by the elementary inclusion–exclusion majorant is sharp to first order in \(\log U/\log\log U\). A second result rules out a low-divisor-level shortcut on the true even and odd labels, without constructing a surrogate sequence. The one-sided signed bound on the remaining layers is **OPEN**.

Use the native terminal interval \(X^{.99}<n\le X\), cutoff \(y=\lceil\log_2 X\rceil^2\), shells \(U=2^j\) and the original node weights \(w_J=2^{-k}/U\) at descendant depth \(k\). A true nonzero label is a squarefree \(n\) with no prime divisor through \(y\). Its sign is \(\mu(n)=(-1)^{\omega(n)}\). Write \(S(J)\) for these labels in a node \(J\), and \(f_J=\sum_{n\in S(J)}\mu(n)\). [Definition and one-sided criterion](../step4-prime-transport-2026-11-19/ONE_SIDED_NODE_CHARGES.md)

## A genuine subpower bound for the entire high-factor error

For a nonnegative even integer \(m\) set
\[
 L_m(n)=\sum_{\substack{d\mid n\\\omega(d)\le m}}(-2)^{\omega(d)}
       =\sum_{i=0}^{\min(m,r)}(-2)^i{r\choose i},\qquad r=\omega(n),\quad n\in S(J).
\]
This equals \(\mu(n)\) for \(r\le m\). For \(r\ge m\), define \(T_m(r)=(-1)^m\sum_{i=0}^m(-2)^i{r\choose i}\). Then \(T_m(m)=1\), \(T_0(r)=1\), and Pascal's identity gives \(T_m(r+1)=T_m(r)+2T_{m-1}(r)\) for \(m\ge1\). Induction gives \(T_m(r)\ge1\). Thus \(L_m(n)\ge\mu(n)\) on every native row. In every case \(|L_m(n)|\le3^r\).

For late shells choose \(m=m(U,X)\) as the largest even integer at most
\[
 \left(1-\frac1{\sqrt{\log\log U}}\right)
       \frac{\log U}{\log y}.
\]
Any convention on the finitely many initial shells is immaterial to the bound. Uniformly on native shells \(m=(1/2-o(1))\log U/\log\log U\). Every true label satisfies \(r\le\log(2U)/\log y\), so \(3^r=U^{o(1)}\). The number \(N_m\) of shell labels with \(r>m\) satisfies
\[
 N_m\le \sum_{n\le2U}{\omega(n)\choose m}
 \le \frac{2U}{m!}\left(\sum_{p\le2U}\frac1p\right)^m=U^{1/2+o(1)}\ \text{as an upper bound}.
\]
Indeed each fixed product \(d\) of \(m\) distinct primes divides at most \(2U/d\) integers; Stirling's lower bound and the prime harmonic sum imply the last estimate. The use of all integers in this particular bound is an upper estimate on the actual omitted labels.

Write \(e_J=\sum_{n\in S(J)}(L_m(n)-\mu(n))\ge0\). At each depth the nodes partition a subset of the shell; their total error is bounded by \(N_m(3^{\log(2U)/\log y}+1)\). Hence their sum of squared errors is at most \(U^{1+o(1)}\). Summing \(2^{-k}/U\) over depths gives \(U^{o(1)}\) per shell. The shell count is logarithmic. In particular
\[
  \boxed{\ \sum_J w_J e_J^2\le X^{o(1)}\ }.
\]
This includes clipped nodes and both signs of every omitted label. The same proof bounds the unsigned tree energy of **all** original rows with \(r>m\) by \(X^{o(1)}\), even without the polynomial bound. Since \(0\le [f_J+e_J]_+-[f_J]_+\le e_J\), the weighted root-mean-square cost of replacing the exact positive excess by this degree-truncated upper is subpower. The evaluated majorant itself still needs a signed bound.

## A fixed fraction below that degree has a power-sized error

Fix \(0<c<1/2\). Choose even \(m=(c+o(1))\log U/\log\log U\) and a whole terminal shell \(U\asymp X\). Take distinct primes \(\ell_1,\ldots,\ell_m\in(y,2y]\), put \(a=\prod_i\ell_i\), and choose a prime \(p\in[U/a,2U/a)\). Since \(a\le(2y)^m=U^{2c+o(1)}\), \(p>2y\) uniformly and every resulting \(ap\) has exactly \(m+1\) distinct rough prime factors. The large prime identifies its cofactor uniquely. The ordinary prime number theorem gives \(\gg U/(a\log U)\) choices of \(p\) uniformly, with \(U/a\) tending to infinity by a fixed power of \(U\).

Writing \(P=\#\{y<\ell\le2y:\ell\text{ prime}\}\gg y/\log y\), there are \({P\choose m}\ge(P/m)^m\) possible cofactors, all at most \((2y)^m\). Their total reciprocal mass is at least \((c_0/(m\log y))^m=U^{-c-o(1)}\) for an absolute \(c_0>0\). Thus **at least \(U^{1-c-o(1)}\) native rows** in this shell have \(r=m+1\). On each the majorant excess is \(2^{m+1}\) exactly, by omitting the last binomial term. The excess on every other row is nonnegative. Distribute these rows over the \(2^s\) base cells, whose weights are \(1/U\). Cauchy's inequality gives
\[
  \boxed{\ \sum_{\text{bases in shell}}w_J e_J^2
     \ \ge\ U^{1-2c-o(1)}\ } .
\]
This is a lower bound on the cost of the proposed *overestimate* itself; it does not presume that a native node has positive charge. For direct sign-blind deletion, using \(m+2\) rather than \(m+1\) produces at least \(U^{1-c-o(1)}\) genuine positive labels and gives the same lower exponent for their standalone positive energy. It does not bound the signed contribution after adding other factor-count layers.

## Divisor-level barrier on true source labels

Let \(J\) be any complete native base cell in a terminal shell, \(H=U2^{-s}=U^{1-o(1)}\), and let \(S=S(J)\). For every fixed \(\delta>0,\ K\ge0\), consider arbitrary real coefficients, including choices depending on the observed cell, satisfying
\[
  L(n)=\sum_{\substack{d\mid n\\d\le U^{1-\delta}}}\lambda_d,\qquad
  |\lambda_d|\ll (\log U)^K\tau(d)^K .
\]
Assume \(L(n)\ge\mu(n)\) on the **actual** \(S\). Then uniformly in the cell and coefficients (at fixed implicit constant),
\[
     \boxed{\quad\sum_{n\in S} L(n)\ \ge\ (1-o(1))\,\#S,\qquad
             \#S=(1+o(1)) H\prod_{p\le y}(1-p^{-1}).\quad}
\]
The pointwise majorant \(L=1\) attains \(\#S\). Thus the best possible upper of this form is still of order \(H/\log y\) on these cells. Selectors depending on parity inside the cofactor, or coefficients exceeding the divisor bound, are outside this result. A Selberg square with divisor-bounded coefficients supported on divisors up to \(U^{(1-\delta)/2}\) is covered: grouping products under their lcm costs at most \(\tau(d)^2\) additional pairs per resulting divisor. The claim concerns pointwise divisor majorants for the true signed labels.

To prove it, inspect the signed divisibility tests themselves. For nonsquarefree \(d\) or \(\gcd(d,\prod_{p\le y}p)>1\), the test vanishes. Otherwise
\[
  \sum_{\substack{n\in S\\d\mid n}}\mu(n)
    =\mu(d)\sum_{\substack{k\in J/d\\(k,d\prod_{p\le y}p)=1}}\mu(k).
\]
Put \(V=U/d\ge U^\delta\). The interval length \(h=H/d=V^{1-o_\delta(1)}\) and its left endpoint is comparable to \(V\). Removing the Euler factors for all primes through \(y\) and all primes dividing \(d\) gives the **exact** convolution of ordinary \(\mu\) with the indicator of all integers supported on those primes, including repeated factors. The resulting short-interval sum is \(O_{A,\delta}(h(\log U)^{-A})\) for every fixed \(A\), uniformly in \(d\). Here are the estimates for the extra divisors in this extension of the original rough-source proof.

* For smooth divisors \(b\le V^{1/10}\), apply the all-interval Möbius estimate to the interval \(J/(db)\) at scale \(V/b\) and length \(h/b=(V/b)^{1-o_\delta(1)}\), subdividing into pieces of fixed power length as needed. The constant test function in Matomäki–Shao–Tao–Teräväinen suffices. The sum of the harmonic weights costs \(\prod_{p\le y\text{ or }p\mid d}(1-1/p)^{-1}\ll\log y\), since \(d\le U\) has \(O(\log U/\log y)\) additional primes greater than \(y\). [Theorem 3.1(i) and the interval extension](https://arxiv.org/pdf/2204.03754) · [Prior exact rough convolution](../step4-strip-2026-11-19/ROUGH_INTERVAL_CANCELLATION.md)
* For \(V^{1/10}< b\le 2V\) use the actual absolute bound \(h/b+1\). At \(\sigma=3/4\) the smooth Euler product \(\prod_{p\le y\text{ or }p\mid d}(1-p^{-\sigma})^{-1}\) is \(V^{o_\delta(1)}\): the small factors cost \(\exp(O(y^{1/4}))\), the added factors cost \(\exp(O(\log U\,y^{-3/4}/\log y))\). Rankin's inequality bounds the total tail by \(V^{o_\delta(1)}(hV^{-1/40}+V^{3/4})\). This is absorbed in \(h/\log^A U\).

Summing the signed tests against \(\lambda_d\) therefore costs \(O_{A,\delta,K}(H/\log^A U)\). Indeed only squarefree \(d\) occur and \(\sum |\mu(d)|\tau(d)^K/d\le\prod_{p\le U}(1+2^K/p)\ll_K(\log U)^{2^K}\); start with a suitably larger log saving. Taking \(d=1\) also gives \(\sum_{n\in S}\mu(n)=O_A(H/\log^A U)\).

For the unsigned normalization, truncate inclusion and exclusion for primes through \(y\) at adjacent even and odd orders \(k\asymp20(1+\sum_{p\le y}1/p)\). The Euler tail is \(\ll(\log y)^{-3}\) from \((\sum 1/p)^k/k!\); all floor errors cost at most \(O(y^{k+1})=U^{o(1)}\). Among the resulting rough integers the nonsquarefree ones cost \(O(H/y+\sqrt U)\), by summing \(H/p^2+1\) for \(y<p\le\sqrt{2U}\). This gives the asserted \(\#S\), so the even labels \(E\) and odd labels \(O\) each contribute \((1/2+o(1))\#S\) *in number*. The signed tests above say that \(\sum_E L-\sum_O L=O_A(H/\log^A U)\). But \(L(n)\ge1\) on \(E\), forcing \(\sum_S L\ge2\#E-O_A(H/\log^A U)\), as claimed. This argument works at every large cutoff on the indicated cells.

The degree truncation and the divisor-level truncation are distinct. The former keeps products close to \(n\), even at relatively small degree, and the latter restricts the size of each divisor. Allowing all divisors recovers \((-1)^{\omega(n)}=\sum_{d\mid n}(-2)^{\omega(d)}\) exactly, with \(|(-2)^{\omega(d)}|=\tau(d)\) on squarefree divisors. The truly open part is the signed sum after the high-factor error has been paid; the positivity of a sieve majorant alone does not bound it at the critical scale.

Exact finite checks compared divisor enumeration with the binomial formula and independent ordered-pair reconstruction of the complete tree error at \(X=8192,16384\). At the former cutoff the degree-zero weighted squared error was \(758551/262144\). Separate genuine rough rows with \(r=1,3,5,7,9\) at their respective cutoffs checked the exact \(r=m+1\) error from \(2\) through \(512\). Those larger cutoffs are individual row tests. [Script](check_parity_truncation.py) · [Finite results](PARITY_TRUNCATION_CHECK.json)
