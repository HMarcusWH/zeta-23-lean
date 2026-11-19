# A positive average for the actual integrated prime discrepancy

**DERIVED paper result, 19 November 2026.** For every sufficiently large \(X\), some \(x\) in
\[
 [X/\sqrt{C\log X},\,X\sqrt{C\log X}]
 \quad\text{satisfies}\quad
 A_\vartheta(x):=\int_2^x(\vartheta(v)-v)\,dv\le-\tfrac12 x^{3/2}.
\]
Here \(C\) is an absolute constant and \(\vartheta(x)=\sum_{p\le x}\log p\). The result uses the complete ordinary-prime measure and holds without a zero-free-half-plane assumption. For every fixed \(N>0\), each such witness has a one-sided neighborhood containing \(\gg_N(\log x)^N\) consecutive negative quartic endpoints. This establishes recurrent negative blocks on an unbounded range. It leaves open the maximum length of positive runs at the power scale required by the proposed closure. There has been no Lean or CI qualification of these deductions.

## The exact filter

Set \(F(t)=e^{-3t/2} A_\vartheta(e^t)\) for \(t\ge\log 2\) and set \(F(t)=0\) otherwise. For all real \(t\), put
\[
 V(t)=-\sum_\rho\frac{\exp((\rho-\tfrac12)t)}{\rho(\rho+1)},
\]
with every nontrivial zero repeated according to multiplicity. The sum is absolutely convergent at each \(t\) and \(|V(t)|\le D e^{|t|/2}\) since \(\sum_\rho |\rho(\rho+1)|^{-1}<\infty\).

The unconditional integrated explicit formula gives
\[
 \int_2^x(\psi(v)-v)\,dv
 =-\sum_\rho \frac{x^{1+\rho}}{\rho(\rho+1)}+O(x).
\]
Next \(\psi(v)-\vartheta(v)=\vartheta(\sqrt v)+\sum_{3\le k\le \log_2 v}\vartheta(v^{1/k})=\sqrt v+o(\sqrt v)\). The first term follows from the ordinary prime number theorem. Chebyshev's bound controls the sum of all higher powers by \(O(v^{1/3}\log v)\). It follows by integration that \(F(t)-V(t)\to-2/3\). The square term supplies this sign. The unconditional formula used here is the first display in the proof of Lemma 2.6. The RH-dependent upper bound later in that lemma is unnecessary. [Johnston, equations and proof on p. 4](https://arxiv.org/pdf/2201.06184#page=4)

For \(u\ge0\), define
\[
 K(u)=\sum_{n\ge1}
 (4\pi^2 n^4e^{9u/2}-6\pi n^2e^{5u/2})\exp(-\pi n^2e^{2u}),
\]
and extend evenly. Each summand is positive on \(u\ge0\). We have \(K(u)\ll\exp(-c e^{2|u|})\) for some \(c>0\). In the usual normalization of Riemann's xi function,
\[
 \int_{\mathbb R}K(u)e^{-zu}\,du=\xi(1/2+z)
\]
for every complex \(z\). In the normalization of Rodgers and Tao this is \(K(u)=2\Phi(u/2)\), with the transform initially a cosine transform and extended by entire continuation. In particular \(M_K:=\int K=\xi(1/2)>0\). [Rodgers and Tao, equations (1)–(3)](https://arxiv.org/pdf/1801.05914#page=2)

The sum of the absolute majorants in \(K*V\) is at most \(D e^{|t|/2}\int K(u)e^{|u|/2}du\). Interchanging the sum and integral therefore gives \(K*V=0\) identically, since the multiplier on each term is \(\xi(\rho)\). There is no assumption on where the zeros lie within the strip. Dominated convergence gives
\[
  \boxed{\lim_{t\to\infty}(K*F)(t)=-\tfrac23 M_K.}
\]
Indeed \(F-V\) is bounded for nonnegative arguments and is \(O(e^{|v|/2})\) at \(v<0\). If \(t\ge0\) and \(v=t-u<0\), then \(|v|\le |u|\). These estimates give a single integrable majorant against \(K\).

## From the signed observation to negative quartic endpoints

Chebyshev's bound gives \(|F(v)|\ll e^{v/2}\) on its support. For \(L=\tfrac12\log(Ct)\) with an absolute \(C\) chosen sufficiently large, the contribution from \(|u|>L\) is
\[
 \ll e^{t/2}\int_{|u|>L}K(u)e^{|u|/2}du=o(1).
\]
If \(F(t-u)>-1/2\) everywhere on \(|u|\le L\), the truncated average is at least \(-M_K/2\). This contradicts its limit. Taking \(X=e^t\) proves the asserted location and depth. The same argument works for any fixed depth constant strictly between \(0\) and \(2/3\).

To keep the depth when rounding to the quartic mesh, let \(D(z)=\vartheta(z)-z\) and \(H=x^{3/4}(\log x)^N\), with \(N>0\) fixed. For any fixed \(B>0\) and all \(|u|\le H\),
\[
 |D(x+u)-D(x)|\ll_B H(\log x)^{-B}+x^{0.65}\log x.
\]
For \(x^{0.65}\le |u|\le H\), apply the unconditional all-interval prime-counting estimate of Guth and Maynard at the smaller endpoint. Multiplying its count by \(\log x\) incurs \(O(H^2/x)\) using Chebyshev or the trivial count, hence this error is absorbed by \(H(\log x)^{-B}\). For shorter intervals use the elementary count of at most \(|u|+1\) integers and the largest log weight. [Guth and Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552#page=3)

The fundamental theorem of calculus now gives, uniformly for \(|u|\le H\),
\[
 A_\vartheta(x+u)=A_\vartheta(x)+uD(x)
    +O_B(H^2(\log x)^{-B}+Hx^{0.65}\log x).
\]
Taking \(B>2N+2\), the remainder is \(o(x^{3/2})\). Choose the side on which \(uD(x)\le0\). All its points then have \(A_\vartheta(x+u)\le-0.4x^{3/2}\) for sufficiently large \(x\). Consecutive fourth powers there have spacing \((4+o(1))x^{3/4}\), giving the stated consecutive runs. A constant enlargement of the original multiplicative window contains the whole neighborhood.

## A conditional obstruction for both ordinary-prime observables

Write \(b=\sup_\rho\Re\rho\). If \(b>1/2\) **and some zero attains \(b\)**, dominated convergence in the integrated explicit formula yields
\[
  x^{-1-b}A_\vartheta(x)=
  -\sum_{\Re\rho=b}\frac{e^{i\,\Im(\rho)\log x}}{\rho(\rho+1)}+o(1).
\]
The top-line sum is a uniformly almost periodic real function with mean zero, by absolute convergence of its Fourier coefficients and the absence of a real zero on \((0,1)\). It is nonzero by Fourier-coefficient uniqueness, with equal frequencies on that line contributing their positive integral multiplicities times the same nonzero coefficient. A nonzero continuous real almost periodic function of mean zero takes both signs: a strictly positive peak would recur on intervals of fixed positive length with bounded gaps, which contradicts mean zero if the function is nonnegative. The same argument applies to a negative peak. Thus intervals of both bounded-away-from-zero signs recur on the log scale, with positive fixed length and bounded gaps.

The corresponding ordinary unweighted area \(A_\pi(x)=\int_2^x(\pi(v)-\mathrm{li}(v))dv\) satisfies
\[
  A_\pi(x)=\frac{A_\vartheta(x)}{\log x}
         + O_b(x^{1+b}/\log^2 x).
\]
To verify the error, ordinary prime partial summation gives \(\pi(x)-\mathrm{li}(x)=D(x)/\log x+\int_2^x D(v)/(v\log^2v)\,dv+O(1)\). Integrate in \(x\) and integrate by parts against \(D=A_\vartheta'\). Apart from \(O(x)\), the error is
\[
 \int_2^x A_\vartheta(v)\left[
  \frac1{v\log^2v}+\frac{x}{v^2\log^2v}
    +\frac{2(x-v)}{v^2\log^3v}\right]dv.
\]
The bound \(|A_\vartheta(v)|\ll v^{1+b}\) follows from absolute convergence of the explicit formula. Splitting at \(\sqrt x\) proves the claimed error.

Consequently, under this attained-boundary hypothesis, both actual areas admit positive runs and negative runs each containing \(\gg M\) consecutive quartic endpoints with initial index \(M\) along unbounded sequences. These are sign intervals of fixed length in \(\log x\). This is compatible with the negative-block theorem above and conflicts with any unconditional upper \(O(M^{1-\delta})\) on positive run length. A proof of that upper would therefore exclude every attained rightmost zero with real part greater than \(1/2\). If the supremum is unattained, the normalized sum tends to zero and this top-line argument gives no sign intervals.

## Remaining gap

There is a rigorous obstruction to replacing \(K\) by a fixed compactly supported filter that exactly removes every zero. The bilateral Laplace transform of any \(L^1\) function supported on \([-R,R]\) is entire and bounded by \(\|K\|_1e^{R|z|}\). If it is nonzero, apply Jensen's formula on disks about a point at which it is nonzero, using outer radius twice the inner one. The number of its zeros of modulus at most \(T\) is \(O(T)\). But the Riemann–von Mangoldt count and the positive proportion of simple critical-line zeros already give \(\gg T\log T\) distinct target zeros. Thus even a signed compactly supported kernel cannot eliminate all modes exactly. This obstruction concerns all-zero annihilation; it leaves open methods bounding selected modes while retaining the others. [Bui, Conrey and Young, Theorem 1.1](https://arxiv.org/pdf/1002.4127#page=1)

The unconditional negative windows above have width of order \(\log\log X\) in log coordinates. A block of \(M^{1-\delta}\) consecutive quartic endpoints has log width \(O(M^{-\delta})\). The positive averaging kernel has a fixed width and its transform vanishes at every possible off-line zero. This makes its sign compatible with growing zero modes in the original area. In particular, convolution gives neither recovery of sign between the recurrent negative windows nor the pointwise upper required for closure. The unconditional sign result here is for \(A_\vartheta\). The partial-summation error for \(A_\pi\) can exceed the unconditional \(x^{3/2}\) depth when \(b>1/2\). Step 4 and RH remain open.
