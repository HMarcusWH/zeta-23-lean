# A thin strip of primitive ratios with every unmatched prime large

**DERIVED on paper, 19 November 2026.** The genuine projected response forces a signed interaction in a much smaller part of the arithmetic graph if a rightward zero exists. Both endpoints must be almost equal in ratio, share exactly the same set of small primes, and differ by a primitive additive gap outside any prescribed subexponential list. The new test uses a nonnegative averaging kernel. Cauchy–Schwarz transfers a large full response to this observable. No off-diagonal edge of the original graph is assumed to have either sign.

Use the fixed \(Y=10^7\), complete one-copy field, source \(V\), projection \(h_n\), and \(z_{n,r}=\mu(r)r^{-1/2}h_n(\log r)\) on \(Y\)-rough endpoints from the [projected graph proof](../step4-duration-2026-11-19/PROJECTED_DIVISOR_GRAPH.md). Write \(T_n=\kappa n+2,\ \kappa=2.33\cdot10^{-25}\), and restrict to \(r\le e^{T_n}\). The total deleted absolute weight in the original squared graph is \(o(1)\). A rightward zero forces \(|\sum_r z_{n,r}|=\exp((\log R+o(1))n)\) at every sufficiently large order for a fixed \(R>1\). The projection has \(\|h_n\|_{H^1}\le C_Y\) and \(\sup_x(|h_n(x)|+|h_n'(x)|)\le C_Y\) by convolution with \(V,V'\in L^2\). All displayed modulus squares use complex conjugation and both edge orientations.

## The positive graph with local prime matching

Choose \(B=B_n=\exp(n/\log(n+2))\), and any \(Q=Q_n=n^{2+o(1)}\), eventually \(Q>Y\). A concrete choice is \(Q=n^2\exp(\sqrt{\log(n+2)})\). Set \(s(r)=\prod_{Y<p\le Q,\ p\mid r}p\) for squarefree \(r\); \(\mu(r)=0\) removes all other endpoints. Define \(k_B(u)=(1-B|u|)_+\) and the finite real sum
\[
 J_n=\sum_{\substack{r,l\le e^{T_n}\\s(r)=s(l)}}\sqrt{s(r)}\,
      z_{n,r}\overline{z_{n,l}}\, k_B(\log(r/l)).
\]
Partition \([0,T_n]\) by translating a regular grid of step \(1/B\), using half-open cells; any translation meets at most \(N= \lceil B T_n\rceil+2\) cells. Let \(L_{s,j}=\sum_{s(r)=s,\ \log r\in I_j}z_{n,r}\). Weighted Cauchy–Schwarz gives
\[
 \left|\sum_r z_{n,r}\right|^2\le N H_n\sum_{s,j}\sqrt{s}\,|L_{s,j}|^2,\qquad
 H_n=\sum_{\substack{s\le e^{T_n}\\s\ \mathrm{squarefree}\\p\mid s\Rightarrow Y<p\le Q}}s^{-1/2}.
\]
Average the grid origin uniformly over a single grid step. The chance of two points sharing a cell is exactly \(k_B(\log(r/l))\); endpoints have no effect on the expectation. This gives \(0\le|\sum z|^2/(NH_n)\le J_n\). No independence assumption on prime signs was introduced. For every \(0<\eta<1/2\), Rankin's inequality gives
\[
 H_n\le e^{\eta T_n}\prod_{p\le Q}(1+p^{-1/2-\eta})
        \le \exp(\eta T_n+o_\eta(n)).
\]
The elementary sum over all integers through \(Q\) already gives \(O_\eta(Q^{1/2-\eta})=o_\eta(n)\) in the logarithm. Letting \(\eta\downarrow0\) proves \(H_n=e^{o(n)}\); \(N=e^{o(n)}\) also. A rightward zero therefore forces \(\liminf_n n^{-1}\log J_n\ge2\log R\).

For comparison, without the prime colors a compact Fourier weight gives a second strip. Set \(F(\theta)=\sum_r z_{n,r}e^{-i\theta\log r}\), \(g(\theta)=\mathrm{sinc}^2(\theta/B)\) with \(\mathrm{sinc}(x)=\sin(x)/x\). The Fourier transform of \(gF\) has support in an interval of length \(T_n+4/B\). Point evaluation at zero and Plancherel give \(|F(0)|^2\le (T_n+4/B)\|gF\|_2^2/(2\pi)\). Expansion of this integral gives \(B(\int \mathrm{sinc}^4)\sum z_{n,r}\overline{z_{n,l}}K(B\log(r/l))\) with \(K(0)=1\), \(0\le K\le1\), supported on \([-4,4]\) by fourfold convolution of the Fourier interval indicators. The triangular version above is sufficient and has the narrower support.

## Which primitive directions can be removed independently

Write any matched pair \(r=sga,\ l=sgb\), with \(g,a,b\) squarefree and composed entirely of primes \(>Q\), and pairwise coprime. The sign of \(g\) and \(s\) cancels, while \(\mu(a)\mu(b)\) remains. The weighted absolute total in a fixed primitive direction is bounded by \(C_Y H_n/\sqrt{ab}\), uniformly in \(a,b,n,Q\). Indeed for each \(s\) the common-divisor sum has the factor \(s^{-1/2}/\sqrt{ab}\), with two shifted samples of \(h_n\) weighted by \(1/g\). Cauchy–Schwarz in \(g\) and the uniform translated harmonic sampling bound from the projected graph proof give \(C_Y\) for the remaining sum. Dropping coprimality restrictions and bounding the kernel by one are legitimate for this absolute estimate.

The diagonal costs at most \(C_Y H_n\). For each fixed primitive gap \(d=|b-a|>0\), the entire sum of absolute weights in both orientations is at most
\[
 2 C_Y H_n\sum_{a\le e^{T_n}}\frac1{\sqrt{a(a+d)}}
 \le 2 C_Y H_n(1+T_n).
\]
Thus every gap from any set \(\mathcal D_n\) of size \(e^{o(n)}\) can be deleted, even if the set contains very large gaps or is chosen from the observed graph. Likewise \(ab\le X_n=e^{o(n)}\) costs \(O_Y(H_n\sqrt{X_n}(1+\log X_n))=e^{o(n)}\). For a concrete residual take \(\mathcal D_n=[1,\lfloor B\rfloor]\). Every surviving pair satisfies
\[
 a\ne b,\quad P^-(ab)>Q,\quad |\log(a/b)|<1/B,\quad
 B<|a-b|\le (e^{1/B}-1)\min(a,b),
\]
where \(P^-\) denotes least prime factor. In particular \(\min(a,b)> B/(e^{1/B}-1)\sim B^2\), and all allowed common prime factors and common divisors remain. Let \(S_n\) denote this retained signed weighted sum in both orientations. Then \(J_n-S_n\) has absolute value \(e^{o(n)}\). A rightward zero requires a positive \(S_n\) of exponential size at every sufficiently large order; exponentially many distinct primitive gaps must participate since the bound for a single gap is subexponential.

## A converse and an integer-only version

Under RH, the classical Mertens bound is \(M(x)=O_\eta(x^{1/2+\eta})\) for each fixed \(\eta>0\). Define \(M_Q(x)=\sum_{k\le x,\ p\mid k\Rightarrow p>Q}\mu(k)\), including \(k=1\). The convolution identity
\[
 M_Q(x)=\sum_{\substack{d\le x\\p\mid d\Rightarrow p\le Q}} M(x/d)
\]
follows prime by prime, including every power of the small primes in \(d\). Hence
\[
 |M_Q(x)|\le C_\eta x^{1/2+\eta}
        \prod_{p\le Q}(1-p^{-1/2-\eta})^{-1}
 \le C_\eta x^{1/2+\eta}e^{o_\eta(n)} .
\]
The constant in the first inequality is independent of \(Q,n\). This uses RH only for the converse. [Soundararajan's RH bound for the sum of Möbius](https://deepblue.lib.umich.edu/bitstream/handle/2027.42/135214/blms0213.pdf?sequence=1)

In the cell with smooth part \(s\), write \(r=sk\). The prime factors of \(k\) all exceed \(Q\). The column is \(\mu(s)/\sqrt{s}\) times a rough Möbius sum weighted by \(k^{-1/2}h_n(\log(sk))\). On a cell of width at most \(1/B\), with lower \(k\)-endpoint \(x\ge1\), this weight has supremum and total variation \(O_Y(x^{-1/2})\), uniformly in \(s\). This follows by differentiation and the uniform bounds for \(h_n,h_n'\). Truncate at \(x=1\) as necessary and handle the single \(k=1\) term explicitly.

Define the positive quantity
\[
 A_n=1+\sup_{\substack{1\le x\le y\le e^{T_n}\\y\le x e^{1/B}}}
       \frac{|M_Q(y)-M_Q(x)|}{\sqrt{x}} .
\]
Partial summation on each cell gives \(\sqrt{s}|L_{s,j}|\le C_Y A_n\), including endpoint changes of at most two summands. Consequently \(|\sum z|\le C_Y N H_n A_n\) and \(J_n\le C_Y^2 N H_n A_n^2\). Under RH the preceding estimate gives \(\limsup n^{-1}\log A_n\le\eta\kappa\) for each \(\eta>0\), so this limsup is zero. Conversely a rightward zero forces \(\liminf n^{-1}\log A_n\ge\log R>0\). This proves the two paper criteria
\[
 d_{\rm zero}=0
 \quad\Longleftrightarrow\quad
 \liminf_{n\to\infty}\frac{\log A_n}{n}=0
 \quad\Longleftrightarrow\quad
 \liminf_{n\to\infty}\frac{\log(1+\max(S_n,0))}{n}=0 .
\]
Here \(d_{\rm zero}\) is the rightward displacement supremum, distinct from a primitive gap. The integer test asks for uniformity over short intervals at each selected order. The gain in narrowing the interval does not itself prove cancellation of rough Möbius signs there.

## Cost of increasing the unmatched-prime threshold

For \(Q=n^{A+o(1)}\) with fixed \(A>0\), the actual profile mass satisfies
\[
 \lim_{n\to\infty} \frac{\log H_n}{n}
   =\kappa\max(1/2-1/A,0).
\]
Rankin's argument gives the upper using any \(\eta>\max(1/2-1/A,0)\) with \(\eta<1/2\). For \(A>2\) let \(k=\lfloor T_n/\log Q\rfloor\); products of \(k\) distinct primes in \([Q/2,Q]\) have admissible weight at least \(e^{-T_n/2}\). The ordinary prime number theorem gives \(M=\pi(Q)-\pi(Q/2)\sim Q/(2\log Q)\). The logarithm of their count is at least \(k\log(M/k)=(1-1/A)T_n+o(n)\), from \(\binom{M}{k}\ge(M/k)^k\). This proves the matching lower; in the remaining range \(s=1\) suffices. The exponent two is the sharp threshold for the subexponential cost of this color comparison. It does not assert that the full genuine signed sum grows beyond that prime threshold.

## The exact exponent from the original unsmoothed source

There is a stronger integer statement that avoids the attenuation of large ordinates by the fixed-center Cayley transform. Keep \(Q_n=n^{2+o(1)}\), \(B_n=\exp(n/\log(n+2))\), but set the endpoint ceiling to \(e^n\) directly. Put
\[
 A_n^{\rm nat}=1+\sup_{1\le x\le y\le e^n,\ y\le x e^{1/B_n}}
   \frac{|M_{Q_n}(y)-M_{Q_n}(x)|}{\sqrt x},\qquad
 d=\sup_\rho(\Re\rho-1/2)_+ .
\]
Then the **full limit exists** and
\[
 \lim_{n\to\infty}\frac{\log A_n^{\rm nat}}{n}=d.
\]
The source needed for the lower is precisely Lean's \(\texttt{primeFieldFamily 0}\), which uses the original one-copy \(j\). The limiting exponent measures the entire zero configuration, with no attainment hypothesis. The same argument works for any fixed schedule \(B_n\ge1\) with \(\log B_n=o(n)\); choosing it to tend to infinity restricts the relative interval lengths.

**Lower.** When \(d>0\), the merged native theorem at \(C=2\) gives energy \(\exp((2d+o(1))n)\) on every sufficiently late interval \([n-2\log n,n]\). Continuity and the length of the interval give an actual \(v_n\) there with \(|P(v_n)|\ge\exp((d-o(1))n)\). The exact identity is \(P(v_n)=\sum_{r\le e^n}\mu(r)\mathbf1_{(r,\Pi_Y)=1}r^{-1/2}V(v_n-\log r)\), using causality. Apply the cell argument with this translated \(V\) in place of \(h_n\), this time directly to its linear sum. The derivative and supremum bounds are independent of \(n\) because the source is fixed. For each \(s,j\), partial summation gives \(\sqrt s\,|L_{s,j}|\le C_Y A_n^{\rm nat}\) exactly as above. Summing over \(s\le e^n\) and over the at most \(\lceil nB_n\rceil+2\) cells costs \(\exp(o(n))\); the same Rankin bound applies with \(T_n=n\). Thus \(A_n^{\rm nat}\ge\exp((d-o(1))n)\) at all sufficiently large orders. For \(d=0\) the lower is immediate from \(A_n^{\rm nat}\ge1\). [Merged theorem, including its normalization and interval](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154-L1158) · [Original source index](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean#L16-L24)

**Upper.** Write \(\sigma_0=1/2+d\). The zero-free region strictly to the right of \(\sigma_0\) gives \(|M(x)|\ll_\eta x^{\sigma_0+\eta}\) for every fixed \(\eta>0\). Here this is a conclusion from the definition of the actual supremum, without fixing its value. For completeness, if \(\sigma_0=1\) the elementary count suffices. Otherwise set \(G(s)=(s-1)\zeta(s)/(s+2)\), including its removable nonzero value at 1. This has an analytic logarithm on \(\Re s>\sigma_0\), chosen to be bounded at \(\Re s=2\) using the Euler series and the elementary rational factor. On \(\Re s=\sigma_0+\eta/4\), for small fixed \(\eta>0\), Borel–Carathéodory on disks centered at \(2+it\), with slightly wider disks still within \(\Re s>\sigma_0\), gives \(|\log G|\ll_\eta\log(2+|t|)\), and the same bound through the strip to \(2\). This uses the ordinary polynomial vertical bound for \(\zeta\) from Euler summation. Apply the three-lines inequality to \(\exp((s-it_0)^2)\log G(s)\) on these vertical boundaries. On the right it is uniformly bounded; on the left its supremum is \(O_\eta(\log(2+|t_0|))\) by Gaussian decay. At \(\Re s\ge\sigma_0+\eta/2\) this yields \(|\log G|\ll_\eta(\log(2+|t|))^{1-c_\eta}\) for some \(c_\eta>0\). Consequently throughout that inner strip \(|1/\zeta(s)|\ll_{\eta,\epsilon}(2+|t|)^\epsilon\) for every \(\epsilon>0\).

One can now use truncated Perron on the absolutely convergent line \(1+1/\log x\) at half-integer \(x\) and height \(x^2\). Since \(|\mu(k)|\le1\), the usual truncation error \(O(x\log^2(2x)/x^2)\) follows by summing \(1/|k-x|\) for \(x/2<k<2x\) and using absolute convergence outside. When the initial line lies to the left of \(\sigma_0+\eta/2\) the trivial bound already suffices. Otherwise move to \(\sigma_0+\eta/2\); \(1/\zeta\) is holomorphic throughout, including at 1. The vertical integral costs \(O_{\eta,\epsilon}(x^{\sigma_0+\eta/2}(x^2)^\epsilon\log(2x))\), and the two horizontals cost \(O_{\eta,\epsilon}(x(x^2)^{-1+\epsilon})\). Choosing \(\epsilon<\eta/8\) gives the stated \(M(x)\) bound. Taking neighboring half-integers covers all real \(x\).

Use the smooth-number convolution for \(M_Q\) above. Uniformly for \(x\le e^n\), it gives
\[
 |M_Q(x)|\le C_\eta\,x^{1/2+d+\eta}\exp(o_\eta(n)).
\]
Indeed \(\sum_{p\le Q}p^{-1/2-d-\eta}=o_\eta(n)\); all inverse Euler products are finite. The difference over an interval with \(y\le x e^{1/B_n}\le e x\) is at most the two endpoint bounds. Therefore its normalized size is at most \(C'_\eta x^{d+\eta}\exp(o_\eta(n))\). Take the limsup, then \(\eta\downarrow0\). If \(d>0\), the discrepancies attaining the lower rate must have \(\log x=n-o(n)\): any \(x\le e^{(1-\delta)n}\) incurs a fixed exponent gap when \(\eta\) is small enough relative to fixed \(\delta>0\). At these actual late scales, the interval has relative width at most \(e^{1/B_n}-1\), and every counted nonzero term is the exact sign of a squarefree integer composed entirely of primes above \(Q_n\). The integer test still needs an independent cofinal subexponential upper. Computing the exact exponent in terms of \(d\) does not establish that \(d=0\).
