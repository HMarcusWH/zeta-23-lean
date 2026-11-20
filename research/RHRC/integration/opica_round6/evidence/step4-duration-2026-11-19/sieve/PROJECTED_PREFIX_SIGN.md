# The lower passband edge fixes the sign of each late projected prefix insertion

**DERIVED on paper.** Apply the [localized Laguerre projection](../PROJECTED_DIVISOR_GRAPH.md) at the original \(Y=10^7\). Sum all signed primitive directions supported on \(Y<q<p\), including the diagonal. First send the Laguerre order \(n\to\infty\) for each fixed prime \(p\). Denote this limit by \(D_{p-}\), and the limit after including \(p\) by \(D_p\). Define
\[
 h=\tfrac12,\quad \ell=\log p,\quad A_p=\sum_{q<p}q^{-1/2},\quad
 \Omega=\sqrt{2\lambda/(1.01\alpha)-1},\qquad
 r=\frac{h}{\sqrt{h^2+\Omega^2}}>0,
\]
where \(\lambda=10^6,\ \alpha=2.27\cdot 10^{-19}\) are the actual taper parameters. Then
\[
 \frac{\log D_{p-}}{2A_p}\longrightarrow r,\qquad
 \frac{D_p-D_{p-}}{D_{p-}}
 =\frac{2\sqrt p}{p+1}\big(r+o(1)\big)>0
 \quad (p\to\infty).
 \tag{1}
\]
The gain uses the actual high-pass observable; \(r\) is very small because its first available frequency is large.

Let \(B_p=\{q:q<p\}\), \(V_{p-}=\prod_{q<p}(1-S_q)U\), \(c_{p-}=\zeta(2)^{-1}\prod_{q<p}(1+1/q)^{-1}\), and \(g(\xi)=2w(2\lambda/(1+\xi^2))^2/(1+\xi^2)\). The all-directions finite-prefix formula and the identity \(1-2\sqrt q\cos(\xi\log q)/(q+1)=|1-q^{-1/2-i\xi}|^2/(1+1/q)\) give exactly
\[
 D_{p-}=\frac{c_{p-}}{2\pi}\int_{\mathbb R} g(\xi)
      |\widehat U(i\xi)|^2\prod_{q<p}|1-q^{-1/2-i\xi}|^2\,d\xi .
\]
Here \(g=0\) for \(|\xi|\le\Omega\), and \(g>0\) for \(|\xi|>\Omega\). The log of \(c_{p-}\) is \(o(A_p)\). By the [uniform twisted prime estimate](INDIVIDUAL_PRIME_ECHO.md), on \(|\xi|\le p^2\) the log modulus of the product **before squaring**, divided by \(A_p\), is
\[
 -\operatorname{Re}\!\left[\frac h{h-i\xi}\,e^{-i\xi\ell}\right]+o(1)
\]
uniformly. This is at most \(r+o(1)\) on the passband, and has a fixed gap below \(r\) whenever \(|\xi|\ge\Omega+\epsilon\), for every fixed \(\epsilon>0\). The part beyond \(p^2\) costs \(O(\exp(2A_p+O(\ell)-c_jp))\) by the absolute Euler product and the native Gevrey decay of \(\widehat U\).

For the lower, fix any \(\epsilon>0\). Inside \((\Omega,\Omega+\epsilon)\) take a closed interval of positive length on which \(g|\widehat U|^2\) has a positive minimum. Such an interval always exists: \(g\) is continuous and positive inside, the nonzero entire \(\widehat U\) has isolated zeros, and a closed interval can be chosen away from them. On this interval the phase \(\xi\ell-\arg(h/(h-i\xi))\) has derivative \(\ell+O_h(1)\). For all sufficiently large \(p\) it crosses an odd multiple of \(\pi\) in the interior, remaining within \(O(1/\ell)\) of that value on a subinterval of length \(\ell^{-2}\). Its log-width cost is \(o(A_p)\). This gives \(\liminf \log D_{p-}/(2A_p)\ge h/\sqrt{h^2+(\Omega+\epsilon)^2}\); letting \(\epsilon\downarrow0\) proves the first limit.

Under the probability measure proportional to the integrand, \(|\xi|\) therefore concentrates at \(\Omega\). The phase also concentrates where \((h/(h-i\xi))e^{-i\xi\ell}\) approaches the negative real number \(-r\). Indeed a fixed phase mismatch on any fixed bounded part of the passband reduces the real-part maximum by a fixed positive amount, and the rest was excluded by the preceding gap and tail estimates. It follows that \(\cos(\xi\log p)\to-r\) in probability and hence in expectation; at the optimizing phase the cosine equals \(-h/\sqrt{h^2+\xi^2}\). Multiplying the exact integrand by the one-prime insertion factor now gives the second limit in (1). At any fixed real translation \(s\), its expected \(\cos(s\xi)\) also tends to \(\cos(s\Omega)\).

This computes a positive signed contribution from the complete set of corresponding primitive directions, including arbitrarily large common divisors. The limits take \(n\) first at each fixed \(p\). They supply no uniform upper for the unresolved moving primitive-product sector, and Step 4 remains open.
