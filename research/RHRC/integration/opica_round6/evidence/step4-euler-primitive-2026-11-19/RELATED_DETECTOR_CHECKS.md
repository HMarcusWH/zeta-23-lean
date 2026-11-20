# Checks on the physical detector and the weighted single-source field

These are supporting paper deductions from the 19 November aperture-integral investigation. They concern different observables. Neither estimate supplies the independent arithmetic upper in the main report.

## Projection onto the parity subspace

Let \(\phi_L\) be the genuine unit two-lobe trial in the repository. Its support has total length at most \(4s_0\), with each point a fixed distance \(d\le1+2s_0\) from the closest periodic endpoint. Take the even physical quartic subspace at cutoff \(K\). A unit coefficient vector in it has \(x_n=(b+n^2)u_n\), \(b=(L/4\pi)^2\), and \(\sum n^j u_n=0\) for \(0\le j\le7\). Odd moments vanish by symmetry. In the normalized Fourier realization,
\[
 h_x(d)=L^{-1/2}\sum_{|n|\le K}(b+n^2)u_n e^{2\pi ind/L}.
\]
Taylor-expand the two terms separately, to degrees 7 and 5 respectively. For real phase the Taylor remainder is at most its absolute argument to the first omitted power divided by the factorial. Since \(\sum|u_n|\le\sqrt{2K+1}/b\), on the support
\[
 |h_x|\le\sqrt{(2K+1)/L}\left[
 \frac{(2\pi Kd/L)^8}{8!}+\frac{K^2}{b}\frac{(2\pi Kd/L)^6}{6!}\right].
\]
The same bound holds at the other endpoint by periodicity. As \(\|\phi_L\|_1\le2\sqrt{s_0}\), taking the supremum over the unit sphere gives squared projected mass \(O((K/L)^{17})\) for \(1\le K=o(L)\). This applies in particular to the complete two-dimensional even plane at \(K=5\). A fixed positive overlap with that plane cannot transfer a late original trial without an estimate on its complement. The prime-side scalar criterion in the main report requires no such projection. [Physical coordinates](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/research/RHRC/integration/opica_round5/K5_MIXED_SOURCE_SPEC.md) · [Literal normalized trial](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/ExceptionalZero/UniversalSincOriginalPhaseDepth.lean)

## Frequency averaging in genuine Möbius inversion

For the earlier frozen compact pulse \(h\), let \(U(t)=\sum_{n\ge2}(\log n)n^{-1/2}h(t-\log n)\). Write \(Z_v(t)=\sum_d\mu(d)d^{-1/2-iv}U(t-\log d)\) and \(A_v(T)=\int_0^T e^{-(T-t)/2}|Z_v(t)|dt\). At \(v=0\) this is the actual Mangoldt field, by the full divisor identity. Other values of \(v\) are auxiliary twists. For each finite \(T\) all sums use finite causal histories. Retain the source's known rapid decay of \(U\) at every fixed exponential order and its vanishing near \(t=0\).

At any fixed \(t\) the infinite-interval mean of \(|Z_v(t)|^2\) over \(v\) is exactly \(\sum_d\mu^2(d)d^{-1}|U(t-\log d)|^2\), by orthogonality of the distinct frequencies \(\log d\). Squarefree density gives its limit as \(t\to\infty\), namely \(\|U\|_2^2/\zeta(2)>0\). Indeed set \(x=e^t\) and use the continuous profile \(y^{-1}|U(-\log y)|^2\), extended by zero at 0. Thus the mean is uniformly bounded in \(t\); weighted Cauchy–Schwarz and finite-horizon integration yield a bound on the frequency mean of \(A_v(T)^2\) independent of \(T\).

If a rightward zero exists, *every fixed interval of frequencies with positive length* instead has an exponentially growing integral. To see this write \(a=c*N\) for the literal floor kernel, where \(N\) is the weighted integer action. Set \(a_v=e^{-ivu}a(u)\), \(c_v=e^{-ivu}c(u)\). Twisting the convolution identities and using finite inversion gives
\[
 W_v=a_v*Z_v=c_v*U,\qquad \|W_v\|_2\le\|c\|_1\|U\|_2 .
\]
For \(p=\rho-1/2\), \(\delta=\Re p>0\), set \(p_v=p-iv\). Then \(\widehat a_v(p_v)=0\) and \(\widehat W_v(p_v)=\widehat c(p)\widehat U(p_v)\). Truncate the input at \(T\). The prefix is unchanged by causality and the full transform of the completed truncated input at \(p_v\) is zero. Its output tail is bounded by \(e^{-(t-T)/2}A_v(T)\) for \(t\ge T\). Removing the actual \(W_v\) tail costs at most \(e^{-\delta T}\|c\|_1\|U\|_2/\sqrt{2\delta}\). This gives
\[
 A_v(T)\ge(\delta+1/2)\left(e^{\delta T}|\widehat c(p)\widehat U(p-iv)|-
             \|c\|_1\|U\|_2/\sqrt{2\delta}\right).
\]
The rational factor \(\widehat c(p)=(p-1/2)/((p+1/2)(p+3/2))\) is nonzero there. The rapidly decaying causal \(U\) has a nonzero entire transform. In each fixed frequency interval some closed subinterval of positive length therefore has the absolute transform bounded below. Integrating the squared lower bound there gives \(\int_I A_v(T)^2dv\ge c_{I,\rho}e^{2\delta T}\) eventually. This proof needs no simple-zero assumption.

The bounded mean takes the frequency-interval limit at each fixed \(T\). It cannot give the missing bound on a fixed interval across arbitrarily late \(T\). The latter bound would exclude every rightward zero. The earlier weighted argument already yields an eventual lower for the untwisted field with multiplicities retained. Weighted argument and original source archive · [Native floor kernel](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/NativeFloorCompletionSource.lean)

There is also an exponent check on the untwisted observable. Put \(d=\sup_\rho(\Re\rho-1/2)\) over all nontrivial zeros. The smoothed explicit formula for the complete Mangoldt field gives \(Z_0(t)=O_h(e^{dt})\). For the Mellin test \(e^{(s-1/2)t}H(s-1/2)\), compact smoothness yields arbitrary polynomial decay in ordinate on bounded vertical strips. A contour shift from 2 to \(-1\) gives the absolutely convergent nontrivial-zero sum after factoring \(e^{dt}\), using classical zero counting and good contour heights. The pole at 1 is killed by \(H(1/2)=0\); the new vertical integral is \(O_h(e^{-3t/2})\). The reviewed weighted lower for each visible rightward zero, and the genuine source visibility, then give \(\lim_{T\to\infty}T^{-1}\log(1+A_0(T))=d\). The nonnegative logarithm covers \(d=0\); taking the supremum needs no rightmost zero. This equality uses the zero side and cannot supply an independent proof that \(d=0\). Actual weighted zero lower · [Classical prime and zero relation](https://dlmf.nist.gov/25.16)
