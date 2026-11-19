# The complete prime-power aperture integral and the missing Step 4 estimate

19 November 2026. **Step 4 OPEN. RH OPEN.** This is a paper derivation and a bounded arithmetic check. The repository head inspected was [c867a8f1](https://github.com/HMarcusWH/zeta-23-lean/tree/c867a8f15320ad6ac69177e0a498de4cb9d744f9). Its tree was 573cda1f06d2d7a0e61349a53183311e4ba621fc. No Lean theorem or CI status was changed.

## Result

For the specific cutoff-five carrier in the latest Drive work, a one-sided subexponential upper on a *signed integral over apertures*, at all sufficiently late horizons, is equivalent on paper to the Riemann hypothesis. The implication to RH follows directly from the Euler logarithmic derivative. This avoids the proposed continuation of an infinite sum over zeros and preserves each genuine prime power with its original weight. The upper itself is still unproved.

A genuine divisor calculation bounds the whole short Möbius-divisor contribution. I also find exponentially large, opposite-signed contributions among the real primes when the remaining sum is bounded by signs separately. The cancellation these terms need is arithmetic.

Inputs were the bird’s-eye report, second report, third report and merged PR harvest. The earlier reports give the five Fourier modes, the centered 15-real-moment identity and the summable entering-prime shell.

## 1. The precise arithmetic object

Set \(f(y)=\sin^8(\pi y)-(10/9)\sin^{10}(\pi y)\) on \([0,1]\), extended by zero. For \(L>0\) put
\[
v_L(y)=L^{-2}f''(y)-f(y)/4,\qquad b(L)=\int_0^1 v_L(y)^2\,dy.
\]
The physical unnormalized carrier on \([0,L]\) is \(v_L(t/L)\). Its squared norm is \(Lb(L)>0\). Its normalized autocorrelation \(C_L\) is even, supported on \([-L,L]\), bounded by one and satisfies
\[
 b(L)C_L(t)=\int_0^{1-t/L}v_L(y)v_L(y+t/L)\,dy \quad(0\le t\le L).
\]
Use the centered genuine measure
\[
 d\nu(t)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}(dt)
          -e^{t/2}\,dt\quad(t\ge0).
\]
Write
\[
 B(L)=L^{17}b(L)\int_0^L C_L(t)\,d\nu(t),\quad
 I(T)=\int_0^T B(L)dL,\quad
 W_T(t)=\int_t^T L^{17}b(L)C_L(t)\,dL .
\]
Take \(W_T(t)=0\) for \(t>T\). Finite Fubini gives \(I(T)=\int W_T\,d\nu\).

**The unproved arithmetic statement** is
\[
 (\mathrm{A})\qquad \forall\eta>0\ \exists C_\eta,T_\eta\
 \forall T\ge T_\eta:\quad I(T)\le C_\eta e^{\eta T}.
\]
An estimate on one common sign over the entire aperture primitive suffices. A different unbounded subsequence for each \(\eta\) would be insufficient here.

Proper powers have at most \(O((1+T)^2)\) total mass on \([0,T]\). Squares are bounded by \(\sum_{n\le e^{T/2}}\log(n)/n\), and all powers of order at least three have bounded total mass by the geometric series. Also \(L^{17}b(L)=O(L^{13}+L^{17})\) and \(\|W_T\|_\infty=O((1+T)^{18})\). Thus the full and ordinary-prime versions differ by \(O((1+T)^{20})\). This comparison keeps the proper powers explicit.

## 2. Direct Euler-transform implication

For \(0\le u\le1\), write \(g,h=\int_0^{1-u}g(y)h(y+u)dy\). Define
\[
 k_{13}=[f'',f''],\qquad
 k_{15}=-([f'',f]+[f,f''])/4,\qquad k_{17}=[f,f]/16 .
\]
Then \(L^{17}b(L)C_L(t)=\sum_{m\in\{13,15,17\}}L^m k_m(t/L)\) exactly. Since \(f(y)=\pi^8 y^8+O(y^{10})\) at the left endpoint and \(f(1-y)=f(y)\), the endpoint beta integrals give
\[
 k_m(1-v)=c_m v^m+O(v^{m+2}),\quad
 (13!c_{13},15!c_{15},17!c_{17})=
 K(1,-1/2,1/16),\quad K=\pi^{16}(8!)^2 .
\]

Let \(D(w)=\int e^{-wt}\,d\nu(t)\) initially for \(\Re w>1/2\). The full Euler product gives
\[
 D(w)=-\frac{\zeta'}{\zeta}(1/2+w)-\frac1{w-1/2}.
\]
The pole at \(w=1/2\) cancels. There is no other positive-real singularity. In particular \(\zeta(s)<0\) for real \(0<s<1\), by the alternating eta series. At \(p=\rho-1/2\) in \(\Re p>0\), this meromorphic continuation has residue \(-m_\rho\), with the genuine multiplicity.

For \(\Re s>1/2\), substitute \(u=t/L\) in the Laplace transform of \(B\) and apply absolute Fubini to the prime-power and continuum parts individually:
\[
 {\cal B}(s)=\sum_m(-1)^{m+1}\int_0^1
 k_m(u)u^{-m-2} D^{(m+1)}(s/u)\,du. \tag{1}
\]
This gives holomorphic continuation away from radial segments \((0,p]\) in the open right half-plane. On a compact subset with \(\Re s\ge d>0\), a pole on the integration path requires \(u\ge2d\) and \(|p|\le\max|s|/(2d)\), so only finitely many poles matter locally. As \(u\downarrow0\), the differentiated continuum is \(O(u^{m+2})\) and the differentiated atomic sum is exponentially small in \(1/u\), uniformly on this compact set. These bounds also justify local holomorphy on the positive real axis.

If there is a rightward zero, take the furthest shifted zero \(p\) on its ray from the origin. Such a choice exists since this ray meets the strip in a bounded set and zeros are isolated. For \(s=(1+\epsilon)p,\ \epsilon>0\), the exterior ray connects to the half-plane of absolute convergence. Locally at the endpoint the singular term of (1) equals
\[
 -m_\rho\sum_m (m+1)!\int_0^1\frac{k_m(u)}{(s-pu)^{m+2}}\,du
\]
up to contributions bounded near the endpoint from a local splitting. Distinct poles on that ray, closer to the origin, cannot lie on this path, and other rays are locally separated. With \(v=1-u\) one has
\[
 \int_0^1\frac{v^m}{(\epsilon+v)^{m+2}}dv
 =\frac1{(m+1)\epsilon(1+\epsilon)^{m+1}} .
\]
The higher-order endpoint errors vanish after multiplication by \(s-p\). Therefore
\[
 \lim_{\epsilon\downarrow0}(s-p){\cal B}(s)
 =-m_\rho K\frac{(p^2-1/4)^2}{p^{18}}\ne0 . \tag{2}
\]
This is a radial limit. It establishes a nonremovable singularity without assuming that the full transform has an isolated meromorphic pole. No global rightmost zero, spectral truncation or synthetic zero is used.

The Laplace transform of \(I\) initially equals \({\cal B}(s)/s\). Suppose (A) holds and choose \(0<\eta<\Re p\). On increasing the constant to cover a compact interval, \(C_\eta e^{\eta T}-I(T)\) is nonnegative for all \(T\ge0\). Its transform continues analytically through every real \(s>\eta\) by (1). Landau’s theorem for the Laplace transform of a nonnegative function now bounds its abscissa of convergence by \(\eta\). Indeed a larger finite abscissa would be a real singularity. Thus \({\cal B}(s)/s\) must extend holomorphically throughout \(\Re s>\eta\), contradicting (2) on the exterior ray. Reflection excludes leftward zeros as well. [Landau’s theorem, Lemma 1](https://doi.org/10.4153/CMB-1990-053-4) · [Zeta zero symmetries](https://dlmf.nist.gov/25.10)

Conversely, RH gives \(\psi(x)-x=O_\epsilon(x^{1/2+\epsilon})\) for every \(\epsilon>0\). Partial summation gives \(\nu([0,t])=O_\epsilon(e^{\epsilon t})\). Integrating \(k_m(t/L)\) by parts costs at most its endpoint values and its fixed total variation. After summing \(m\) and integrating \(L\), the polynomial factors are absorbed by choosing \(\epsilon<\eta\). This proves (A) *conditional on RH* and identifies its arithmetic strength. Moreover the same Landau argument applies to \(-I\). Under a rightward zero of displacement \(\delta\), both signs have arbitrarily late excursions beyond every fixed multiple of \(e^{\eta T}\), for every \(0<\eta<\delta\). This explains why cofinal sign selection is ineffective here. [Classical prime-error equivalence](https://dlmf.nist.gov/25.16#E4)

## 3. An actual short-divisor bound

The bilateral transform of \(C_L\) has a double zero at \(z=1/2\). Indeed it is the product of the physical carrier transforms at \(z\) and \(-z\) divided by the norm squared, and integrating \(f''-f/4\) at the physical scale supplies a factor \(z^2-1/4\) to each. Consequently
\[
 \int_0^L e^{t/2}C_L(t)dt=-\int_0^L e^{-t/2}C_L(t)dt,\qquad
 \int_0^L t e^{t/2}C_L(t)dt=\int_0^L t e^{-t/2}C_L(t)dt .
\]
The two right sides are bounded in absolute value by 2 and 4. The analogous two moments of \(W_T\) consequently cost \(O((1+T)^{18})\). Differentiating the finite kernel formula gives \(\|W_T'\|_\infty+\|W_T\|_\infty=O((1+T)^{18})\), with a vanishing moving-endpoint term.

Use the exact integer identity \(\Lambda(n)=\sum_{dm=n}\mu(d)\log m\). For \(1\le D\le e^T\) let \(S_{\le D}\) denote the entire atomic contribution from \(d\le D\). Then
\[
 |S_{\le D}|\ \ll (1+T)^{18}\sqrt D . \tag{3}
\]
To see this, in each row replace \(\sum_{m\ge1}m^{-1/2}\log m\,W_T(\log d+\log m)\) by the integral in \(m\ge1\). The absolute derivative of the summand extended to real \(y\) is at most \(C(1+T)^{18}y^{-3/2}(1+\log y)\), an integrable bound uniform in \(d\). After including \(1/\sqrt d\), the row error costs \(O((1+T)^{18}/\sqrt d)\). Its continuum part, including this factor, is
\[
 d^{-1}\int_{\log d}^T (t-\log d)e^{t/2}W_T(t)dt.
\]
Extend to zero and use the two signed moments above. The omitted interval costs at most \(4\|W_T\|_\infty/\sqrt d\), and the full moments cost \(O((1+T)^{18}(1+\log d)/d)\). Summing gives (3). In particular, at a prescribed rate \(\eta\), taking \(D=\min(e^T,e^{\eta T})\) absorbs the short rows within \(O_\eta(e^{\eta T})\). The bound for the long rows, after restoring their signs, remains unpaid. [Dirichlet convolution and inversion](https://dlmf.nist.gov/27.5)

## 4. Testing cancellation against the actual primes

For a prime with \(\log p=T-h\) at fixed age \(h>0\), the aperture weight has the limit
\[
 W_T(T-h)\longrightarrow J(h)=\sum_m c_m h^{m+1}/(m+1)
 =K\frac{h^{14}}{14!}\left(1-\frac{h^2}{480}+\frac{h^4}{1175040}\right).
\]
This follows from the three endpoint expansions, uniformly for \(h\) in compact intervals. The original finite source therefore assigns opposite signs to genuine prime bands. In particular \(J(1)>0,\ J(30)<0,\ J(50)>0\). Its Laplace transform is \(K(s^2-1/4)^2/s^{19}\), with a double zero at \(s=1/2\).

More quantitatively, let \(W_\pm=\max(\pm W,0)\). The ordinary prime number theorem gives, for either sign,
\[
 e^{-T/2}\sum_{p\le e^T}\frac{\log p}{\sqrt p}(W_T(\log p))_\pm
 \ \longrightarrow\ \int_0^\infty e^{-h/2}(J(h))_\pm\,dh .
\]
For a fixed \(h\)-interval the prime measure converges to \(e^{-h/2}dh\) by partial summation. On \(j\le h<j+1\), the normalized prime mass is \(O(e^{-j/2})\) by Chebyshev, including the last partial interval. Globally \(|k_m(1-v)|\le C v^m\) on \(0\le v\le1\), so \(|W_T(T-h)|\le C(1+h)^{18}\). These two bounds justify passing to the limit. The two displayed limits are equal and strictly positive by the signs of \(J\) and its Laplace-transform zero. Proper powers add only a polynomial, and the signed continuum in \(I\) also costs only a polynomial by §3. This proves actual compensation at the leading \(e^{T/2}\) scale. PNT gives \(I(T)=o(e^{T/2})\) here. Condition (A) requires every positive exponential rate. [Prime number theorem](https://dlmf.nist.gov/25.16#E3)

The long divisor rows expose the same obstruction another way. Take fixed \(0<h_0<h_1<\log(3/2)\) sufficiently small that \(J>0\) there. For \(e^{T-h_1}/2\le d\le e^{T-h_0}/2\), only \(m=2\) contributes in the entire inner sum. The term with \(m=1\) vanishes and \(m\ge3\) lies outside support. The rows \(d=p\) and \(d=2p\) for odd primes give opposite signs, each with subtotal magnitude \(\gg e^{T/2}/T\) by PNT. Bounding these sign classes separately fails at the required scale. Grouping by the original \(n\) still cancels composite coefficients exactly. For instance for \(n=2^j u,\ j\ge1,\ u\) odd, pairing \(d\) with \(2d\) gives \(\log 2\sum_{d\mid u}\mu(d)=\log 2\,\mathbf1_{u=1}\). Neither calculation estimates the remaining signed sum at every positive exponent.

## 5. Signed compensation inside a genuine semiprime sector

One can go further than isolating signs at the endpoint. Let \(D(T)=e^{o(T)}\), with \(D\ge1\). For \(n=pq\) with distinct primes \(D<p<q\), the short coefficient of \(\mu*\log\) is \(\log n\), whereas its full coefficient is zero. Consequently the coefficient of \(n\) in the long part is exactly \(-\log n\), after grouping all its long divisors. Put \(t=\log(pq)\), \(r=\log(q/p)\) and fix \(0<r_0<r_1\). For the strip \(r_0\le r\le r_1\) the signed contribution to the long part satisfies
\[
 S_{\rm strip}(T)\sim -2(r_1-r_0)\,2^{20}K\,e^{T/2}/T^3 .
\]
For any fixed \(0<\kappa<1\) the entire cone \(0<r\le\kappa t\) contributes \(O_\kappa(e^{T/2-c_\kappa\sqrt T})\) for some \(c_\kappa>0\). Removing the fixed strip from that cone therefore gives an opposite-signed asymptotic with the same magnitude. The bounded initial part of a strip outside the cone has no effect. This is actual cancellation among genuine rough composites in the *divisor expansion*. In the original Mangoldt sum each such composite has coefficient zero.

Here is a proof. All terms with \(t<T/2\) cost \(O((1+T)^{20}e^{T/4})\) by counting integers with their unique representation as two distinct unordered primes. For \(t\ge T/2\) in the cone, \(\log p,\log q\ge(1-\kappa)T/4\); in a fixed strip an analogous bound holds for sufficiently large \(T\). Both primes therefore exceed \(D(T)\). The effective prime number theorem in both variables replaces the sum by the negative of the integral with weight
\[
 \frac{2t}{t^2-r^2}\,e^{t/2}W_T(t)\,dt\,dr
\]
with an error \(O_\kappa(e^{T/2-c_\kappa\sqrt T})\). Indeed \(p=e^{(t-r)/2},q=e^{(t+r)/2}\); the continuum counting measure is \(dp\,dq/(\log p\log q)\). One justification of the uniform error is to partition the two log-prime coordinates into intervals of length \(\ell=e^{-a\sqrt T}\). Throughout the retained range, the effective PNT gives a relative error \(O(\operatorname{poly}(T)e^{-b\sqrt T}/\ell)\) for the mass of each complete interval, for some \(b>0\). Choose \(0<a<b/2\). The weight and its first log-coordinate derivatives are bounded by \(\operatorname{poly}(T)e^{-t/2}\). Freezing it on a box costs a factor \(O(\ell)\) against the absolute counting measure with this envelope. Boxes meeting the finite straight boundary segments have total continuum area \(O(T\ell)\), and the same interval bounds apply to their prime masses. These errors are absorbed in the stated estimate with a smaller positive constant. [Effective prime number theorem](https://arxiv.org/abs/2204.01980)

For the cone the \(r\)-integral of \(2t/(t^2-r^2)\) equals \(\log((1+\kappa)/(1-\kappa))\) exactly. Section 3 bounds the resulting continuum by a polynomial on restoring the early range. For the strip put \(h=T-t\). Uniformly for \(h\le T/2\),
\[
 \frac{t}{t^2-r^2}=\frac1T+\frac h{T^2}+\frac{h^2+r^2}{T^3}
                  +O_{r_1}((1+h)^3/T^4).
\]
The zeroth and first \(h\)-moments of \(e^{-h/2}W_T(T-h)\) on \([0,T]\) are polynomial times \(e^{-T/2}\) by §3, including the factor \(T\) when converting between \(t\) and \(h\). Removing \(h>T/2\) changes them exponentially little. The second moment tends by dominated convergence to
\[
 \int_0^\infty h^2 e^{-h/2}J(h)dh
 =\left.\frac{d^2}{ds^2}K\frac{(s^2-1/4)^2}{s^{19}}\right|_{s=1/2}
 =2^{20}K .
\]
The polynomial envelope in §4 bounds the integrated remainder uniformly. This gives the strip asymptotic and explains its sign. The opposite contribution lies among the other factor ratios, on the same aperture range.

Finally the effective PNT and one integration by parts also give \(I(T)=O(e^{T/2-c\sqrt T})\) for the **entire centered field**, for some \(c>0\). Use \(\psi(x)-x=O(xe^{-c_1\sqrt{\log x}})\) with a reduced constant; split the log variable at \(T/2\) and use the bounds on \(W_T,W_T'\) from §3. Polynomial factors are absorbed by reducing \(c\). Its exponential rate is still \(1/2\). The genuine cone cancellation and the full estimate leave (A) open.

## Verification and the native Step 4 boundary

The companion checker verifies the divisor identity as exact integer vectors of log-prime coefficients for \(1\le n\le4096\). It also checks the combined radial coefficient algebra, the signs of the limiting primitive at 1, 30 and 50, nine carrier-kernel comparisons and six weighted carrier moments. These finite checks can catch normalization mistakes. The proof of the implication in §2 is analytic and has paper authority only.

The merged Lean result gives a lower bound \(\mathrm{smoothSourceMain}(g)>e^{\beta L}/4\) on each sufficiently late legal generated packet with its specified positive \(\beta\). An independent signed upper for the *same* native field is one direct way to contradict it. The scalar implication in §2 would exclude a rightward zero by a different, direct argument if (A) were proved. It does not identify the K5 trial with a generated native packet and does not transfer finite K5 signs to a growing-cutoff detector. No proof of (A) or of the complete native upper was obtained. [Exact native theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICARound4/QuarticErrorReduction.lean#L414) · [Genuine finite-carrier identity](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/ExceptionalZero/BoundaryFlatFiniteWeil.lean)
