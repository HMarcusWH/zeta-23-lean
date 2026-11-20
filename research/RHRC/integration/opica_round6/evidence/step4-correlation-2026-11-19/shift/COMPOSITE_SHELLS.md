# Six genuine composite shells for the zero-visible theta tilt

**Derived on paper.** The arithmetic estimate for the [visible tilted observation](THETA_SHIFT_AND_GRAM.md) can be stated using only positive weights on strict composites. Its actual smooth test has exactly five simple sign changes. An upper bound on the deficit between its three negative and three positive shells, on a fixed set of \(O(n)\) observation times per unit log-time block, suffices. The independent subexponential bound for this deficit is OPEN.

Set \(w=1/2+z\). Inverting \(G(w+1)=\tfrac12w(w+1)\pi^{-(w+1)/2}\Gamma((w+1)/2)\) gives the real kernel
\[
 k_+(u)=e^{-3u/2-a}(4a^2-6a),\qquad a=\pi e^{-2u}.
\]
Indeed \(D+1/2\) followed by \(D+3/2\) applies the polynomial \(w(w+1)\) to \(e^{-3u/2-a}\) under the bilateral transform. Put \(W=j*k_+\), so its transform is \(J(z)G(w+1)\). Then
\[
 F_1(t)=\sum_{m\ge2}\frac{c(m)}{\sqrt m}W(t-\log m),\qquad
 c(m)=\sum_{d\mid m}\frac{\Lambda(m/d)}{d}.
\]
The sum converges absolutely at every finite \(t\). The test has double-exponential decay as its argument tends to \(-\infty\) and exponential decay towards \(+\infty\). The theta observation over all genuine prime powers, and the expression using these weighted divisor coefficients, have the same transform on their common half-plane of absolute convergence. This proves the time identity.

Put \(b(m)=\log m-c(m)=\sum_{d\mid m}(1-1/d)\Lambda(m/d)\). These weights are nonnegative, vanish at ordinary primes and are positive for every composite. For a composite \(m\), a prime divisor \(p<m\) yields a positive term with \(m/d=p\). The integer comparison \(I(t)=\sum_{m\ge2}m^{-1/2}\log(m)W(t-\log m)\) has transform \(-J(z)G(w+1)\zeta'(w)\). The double pole of \(\zeta'\) at \(w=1\) is canceled by \(J\). The shifted gamma factor is regular at \(w=-1\), and its first possible pole is at \(w=-3\). Moving to \(\Re z=-3\) gives \(|I(t)|\ll_j e^{-3t}\) for \(t\ge0\). Therefore, exactly,
\[
 F_1(t)=I(t)-\sum_{m\ \mathrm{composite}}\frac{b(m)}{\sqrt m}W(t-\log m).
\]

### The sign computation on the actual source

Write \(W=q_s*\widetilde W\) with \(\widetilde W=(D^2-1/4)^2 k_+\). Then \(\widetilde W(u)=e^{-3u/2-a}P(a)\), where
\[
 P(a)=-864a+8136a^2-13384a^3+6704a^4-1184a^5+64a^6.
\]
On a polynomial \(p\), the derivative after factoring out \(e^{-3u/2-a}\) is \(Tp=(2a-3/2)p-2ap'\). Applying \((T^2-1/4)^2\) to \(4a^2-6a\) gives the displayed result. Its five nonzero roots occur one each in
\[
 (.133,.134),\quad(.817,.818),\quad(2.387,2.388),\quad(5.190,5.191),\quad(9.971,9.972).
\]
The [exact rational certificate](SHELL_CERTIFICATE.json) proves opposite signs at each bracket's endpoints and strict derivative signs throughout all five brackets enlarged multiplicatively by \(1001/1000\) at both ends. Degree leaves no additional roots. The proof applies to the actual convolution as follows. Because \(q_s\) is a nonnegative probability on \([-s,s]\), at argument \(u\) its integrand uses \(a e^{2v}\) for \(|v|\le s\). Outside the five brackets expanded by \(e^{2s}\), every integrand has the same strict sign. Inside each such bracket every derivative samples the bracket expanded by \(e^{4s}<1.001\), where the certificate gives a common strict sign. Thus the true \(W\) is strictly monotone throughout each transition and has exactly one zero in each expanded bracket. The five zeros are simple. This uses the smooth original density, with no point-mass replacement.

Label the resulting six shells in order of increasing \(a=\pi m^2e^{-2t}\). Their signs are \(-,+,-,+,-,+\). For each shell let \(B_j(t)\) be the sum of \(b(m)|W(t-\log m)|/\sqrt m\) over its composites. Assign boundary atoms to either adjacent shell since their weights vanish. The one-sided deficit needed for the visible observer is
\[
 B_1(t)+B_3(t)+B_5(t)-B_2(t)-B_4(t)-B_6(t).
\]
This has the sign of \(F_1-I\) and is exactly equal to it. The shell gates retain all composite weights. A bound on each positive mass separately loses the leading cancellation. For example, on any fixed compact subinterval of a shell with \(|W|\ge\epsilon\), the subset \(m=2p\) already contributes \(\gg_j e^{t/2}\) by ordinary PNT since \(b(2p)\ge(\log p)/2\).

The related \(c(m)\) sum has another independent bound. Split its contributing prime-power divisors \(k=m/d\) at \(\sqrt m\). For the smaller divisors their full contribution to \(c(m)\) is at most \((\log m)/\sqrt m\), since \(c(m)=m^{-1}\sum_{k\mid m}k\Lambda(k)\) and \(\sum_{k\mid m}\Lambda(k)=\log m\). With weights \(W(t-\log m)/\sqrt m\) this costs \(O_j(1+t)\) in absolute value, using the exponential tails and summing in unit intervals of \(\log m\). Distinct prime bases cannot both have prime-power divisors greater than \(\sqrt m\) for the same \(m\). A single base may have several such powers; each is retained. Hence the unbounded signed cost lies in the complementary large-prime-power divisor contribution.

### A positive quadrature gate with linearly many observations

Equation (1) of the companion note and the contours there extend \(F_1\) holomorphically to \(|\Im t|<\pi/4\), with \(|F_1(t)|\ll_{j,a}e^{b\Re t}\) on any narrower strip \(|\Im t|\le a<\pi/4,\ \Re t\ge1\). The factor \(e^{i\gamma t}\) costs at most \(e^{a|\gamma|}\); gamma decay leaves a summable margin for both the residue series and the remaining vertical integral. The integer comparison \(I\) is holomorphic with analogous bounds by its absolutely convergent displaced integral.

Subdivide \([n,n+1]\) into a fixed number of equal panels of width less than \(a/4\). On each take a positive \(m_n=\lceil K n\rceil\)-node Gauss rule with \(K\) a sufficiently large fixed constant. Let \((t_{ni},w_{ni})\) be these \(O_j(n)\) observations of total weight one. On any compact set of Laplace parameters \(\lambda\), Cauchy's estimate on disks of radius \(a/2\) bounds the degree-\((m_n-1)\) Taylor remainder of \(F_1(t)e^{-\lambda t}\) on each panel by \(C_{j,a,\lambda} e^{(b-\Re\lambda)n}2^{-m_n}\). The constant is locally uniform in \(\lambda\). The quadrature is exact for the Taylor polynomial. Taking \(K\log 2>b+2\) makes the block errors summable as analytic functions on \(\Re\lambda>-1\). Thus the Laplace series formed from the *full signed observations* equals the transform of \(F_1\) up to a holomorphic correction on that half-plane, initially identifying them where both converge absolutely. The negative-time and bounded initial contributions are entire.

Let \(D(t)=B_1+B_3+B_5-B_2-B_4-B_6\) be the complete six-shell deficit above. A sufficient closing arithmetic estimate is
\[
 \forall\eta>0\quad\exists C_\eta,n_\eta\quad\forall n\ge n_\eta:
 \qquad \sum_i w_{ni}\max(D(t_{ni}),0)\le C_\eta e^{\eta n}.
\]
Indeed \(I(t)\) has the independent exponentially small bound. Under the displayed condition the positive-part discrete measure has Laplace transform holomorphic on \(\Re\lambda>0\). Its negative-part counterpart continues across each positive real point by (1), the analytic quadrature correction, and the absence of real poles there. The positive-measure singularity argument in the companion note forces holomorphy of both parts on \(\Re\lambda>0\). At any hypothesized rightward zero the known nonzero residue contradicts this conclusion. The condition choosing \(\max(-D,0)\) works equally well by reversing signs. Arbitrary cofinal values of a signed scalar or separate observations of the positive and negative shells do not imply this gate.

### Eight finite checks with the genuine smoothing density

The [interval calculation](SIX_SHELL_SAMPLES.json) uses the eight successive powers of two \(X=e^t=16,\ldots,2048\). It restores every omitted composite and prime-power term by a tail estimate. The six unsigned shell masses at \(X=128\), rounded here, are \(4.97,334.66,2863.16,7747.04,7936.78,2723.33\). The actual complete signed deficit lies in \(-0.1224615\pm8.46\cdot10^{-8}\). The signs for the eight samples in order are \(+,-,+,-,-,+,-,+\).

For reproducibility, \(\int v^2 q_s(v)dv=(s^2/3)(\pi^2/3-3)\). This follows either by differentiating the native sinc product twice or by adding variances of its centered uniforms of half-width \(s/[k(k+1)]\), since \(\sum_{k\ge1}k^{-2}(k+1)^{-2}=\pi^2/3-3\). Evenness annuls the odd Taylor terms. The experiment encloses \(W(u)\) by \(\widetilde W(u)+(\int v^2q_s/2)\widetilde W''(u)\) plus a symmetric error at most \(s^4\sup_{|h|\le s}|\widetilde W^{(4)}(u+h)|/24\), using the same \(T\) polynomial operation as above. It enumerates every integer up to \(12X\) with directed Arb balls. For the remaining \(y=m/X>12\) and \(|v|\le s\), the Gaussian argument lies between \(3y^2\) and \(4y^2\). The total tail in each arithmetic observer is bounded by \(10^9 X^{-1/2}\sum_{m>12X}\log(m)y^{13}e^{-3y^2}\le10^9 X^{3/2}e^{-288}<10^{-100}\) at these apertures. Its sign is in the sixth shell. The values are finite arithmetic enclosures. They rule out a constant sign for this visible observer and do not establish its asymptotic size. [Sample code](sample_shells.py)

The analytic statements have paper status. The root brackets and finite observations are reproducible computations. The unpaid inequality concerns the actual six-shell composite deficit on the stated observation schedule.
