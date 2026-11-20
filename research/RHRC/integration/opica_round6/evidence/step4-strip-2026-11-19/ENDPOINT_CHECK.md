# What a fourth-power endpoint measures

**DERIVED on paper.** Let \(C(x)=\pi(x)-\operatorname{li}(x)\), counting ordinary primes with their full weight, and use the principal-value normalization of \(\operatorname{li}\). The current pointwise target is its lower bound at \(x=m^4\). A second target, with an independently justified transfer on every fixed power grid, uses its integral.

## Finite range of the pointwise target

Johnston's Corollary 3.3 and Theorem 3.2 give \(|C(x)|<\sqrt{x}\log(x)/(8\pi)\) for \(2657\le x\le 1.101\cdot10^{26}\). Substituting \(x=m^4\) gives \(C(m^4)>-m^2\log(m)/(2\pi)\) for \(8\le m\le 3{,}239{,}267\). There is no prime at a fourth-power endpoint with \(m>1\), so the possible half-jump convention contributes zero. The stronger upper endpoint in the paper's Theorem 4.1 uses a different coefficient. [Johnston, Corollary 3.3](https://arxiv.org/pdf/2109.02249#page=8)

The exact integer comparisons are \(7^4=2401<2657<4096=8^4\) and
\[
 3{,}239{,}267^4=110099915755598253511949521
 <110100000000000000000000000
 <110100051712241209250078976=3{,}239{,}268^4.
\]
The first integer beyond this particular published range is \(3{,}239{,}268\). A finite range alone cannot settle the eventual bound.

## Direct comparison for the raw count

If the lower bound holds at all sufficiently large fourth powers, monotonicity gives, uniformly for \(m^4\le x<(m+1)^4\),
\[
 C(x)\ge C(m^4)-\int_{m^4}^x\frac{du}{\log u}
       \ge -O(x^{1/2}\log x+x^{3/4}/\log x).
\]
The ordinary Landau negative oscillation for the prime error then excludes zeros of real part strictly greater than \(3/4\). Any strictly finer transfer here requires additional arithmetic information.

There is an exact obstruction to deriving that improvement from endpoint sampling and monotonicity alone. Fix \(1/2<\beta<3/4\), \(\gamma\ne0\), and define, for large \(x\),
\[
 F(x)=\operatorname{li}(x)+x^\beta\sin^2(\pi x^{1/4})\cos(\gamma\log x).
\]
The derivative of the correction is \(O_{\beta,\gamma}(x^{\beta-3/4})=o(1/\log x)\). Eventually \(0<F'(x)<1\), so \(\lfloor F(\lfloor x\rfloor)\rfloor\) is an integer-valued counting function with jumps in \(\{0,1\}\). Its error at each sufficiently large fourth power is at most one. Its continuous error nevertheless has Mellin poles at \(\beta\pm i\gamma\). Indeed \(\sin^2(\pi x^{1/4})=(1-\cos(2\pi x^{1/4}))/2\). The first term produces those poles, while substitution \(u=x^{1/4}\) followed by integration by parts continues the oscillatory term across \(\Re s=\beta\). The rounding discrepancy is \(O(1)\) and holomorphic after Mellin transformation for \(\Re s>0\). The model counts a constructed subset of integers. It identifies the information lost if the actual prime arithmetic is discarded.

## A one-sided integral that transfers on every fixed power grid

For integer \(k\ge1\) and \(x\ge2\) put
\[
 A(x)=\int_2^x C(u)\,du
 =\sum_{p\le x}(x-p)-x\operatorname{li}(x)+\operatorname{li}(x^2)
     +2\operatorname{li}(2)-\operatorname{li}(4).
\]
The integral antiderivative follows from \((x\operatorname{li}(x)-\operatorname{li}(x^2))'=\operatorname{li}(x)\). The prime term follows by finite summation and retains every prime through the cut. Then
\[
 \mathrm{RH}\quad\Longleftrightarrow\quad
 A(n^k)\le0\ \text{for all sufficiently large integers }n .
\]

Under RH, Johnston's Theorem 1.1 gives strict negativity at every real \(x>2\). For the converse, suppose \(B=\sup_{\zeta(\rho)=0}\Re\rho>1/2\). Choose \(0<\epsilon<\min(B-1/2,1/(2k))\). Lemma 2.8 with \(c=0\) gives arbitrarily large \(x\) at which the corresponding prime-power integral exceeds \(c_\epsilon x^{1+B-\epsilon}\). Removing higher powers costs \(O(x^{3/2})\) by Lemma 2.3, so \(A(x)\ge (c_\epsilon/2)x^{1+B-\epsilon}\) along the resulting sequence. This uses the actual supremum and permits it to be unattained. [Johnston, Lemmas 2.3 and 2.8 and proof of Theorem 1.1](https://arxiv.org/pdf/2201.06184#page=5)

The ordinary explicit formula gives \(C(u)=O_\epsilon(u^{B+\epsilon})\). For example, at half-integers truncate the formula for \(\psi(u)\) at height comparable to \(u\); use \(u^{\Re\rho}\le u^B\) and \(\sum_{0<|\Im\rho|\le 2u}|\rho|^{-1}\ll\log^2 u\), then remove higher powers and use partial summation. Monotonicity transfers from half-integers to all real \(u\), and \(B=1\) is also covered by elementary counting. Let \(n=\lfloor x^{1/k}\rfloor\). Since \(x-n^k=O_k(x^{1-1/k})\), direct integration gives
\[
 |A(x)-A(n^k)|\ll_{k,\epsilon} x^{1+B-1/k+\epsilon}
   =o(x^{1+B-\epsilon}).
\]
Thus \(A(n^k)>0\) for arbitrarily late grid endpoints. The two inequalities above apply at the same \(x\) and its associated \(n\).

The identical argument applies to the logarithmically weighted ordinary-prime observable
\[
 A_\vartheta(x)=\sum_{p\le x}(x-p)\log p-(x^2-4)/2 .
\]
Johnston's Theorem 1.2 gives the RH implication and the \(\psi\) version of Lemma 2.8 and Lemma 2.3 give the opposite oscillation. In the full von Mangoldt field the explicit term to subtract is \(\sum_{p^r\le x,\ r\ge2}(x-p^r)\log p\). It retains the square-power bias that determines the sign of the ordinary-prime result. Native data containing the two prefix sums \(\sum_{p\le x}\log p\) and \(\sum_{p\le x}p\log p\) suffice to evaluate \(A_\vartheta(x)\) exactly. [Johnston, Theorem 1.2 and proof](https://arxiv.org/pdf/2201.06184#page=6)

**OPEN.** The sign at arbitrarily large integer-grid endpoints still requires an independent arithmetic inequality. The direct transfer proves that checking the integrated observable at all sufficiently late fourth powers would suffice. It does not derive that sign from the raw pointwise lower bound or the finite verification.
